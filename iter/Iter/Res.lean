import Iter.CLoop
import Iter.CStmt
/-!
# A second abstraction through the same recipe: `Result` chains

`std::expected<T, E>::and_then`, Rust's `?` and Haskell's `>>=` let you write a validation as a chain of
small steps that each may fail. The plain program is straight-line code that returns at the first failure.
This file runs the recipe on it:

1. **Law.** The only fact the lowering needs is the monad law for `>>=` (associativity, and `pure` as unit):
   `flat_correct` holds for *every* lawful monad, so any nesting of `then` is the flat list of steps.
2. **Equals the plain program.** `lower_correct`: for `Except`, the flat list run as early-return code
   (`lrun`, written without `>>=`) gives the chain's result.
3. **Zero cost, in a cost model.** `lower_wraps`: the lowered code builds 0 intermediate `Result` values;
   `lower_steps`: it runs exactly the steps the chain runs (it stops at the same failure).
   Two result-preserving mutants are rejected by those counts (`mut_eager`, `mut_boxed`).
4. **Printed C++.** `lowerC` builds a C statement tree (`Iter/CStmt.lean`); `printed_chain` proves the
   tree's C meaning is `lrun`, including that no `%` by 0 is reached. Only `CS.print`/`CE.print` (one rule
   per node) and the compiler stay trusted.
-/
namespace Iter.Res
open Iter.Gen Iter.C

/-! ## 1. The law: Kleisli chains in any lawful monad -/

section
variable {m : Type → Type} {α : Type}

/-- a chain of steps `α → m α`, nested any way: `seq a b` is `a >=> b` -/
inductive KTree (m : Type → Type) (α : Type) where
  | step (f : α → m α)
  | seq (a b : KTree m α)

def KTree.eval [Monad m] : KTree m α → α → m α
  | .step f => f
  | .seq a b => fun x => a.eval x >>= b.eval

def KTree.flat : KTree m α → List (α → m α)
  | .step f => [f]
  | .seq a b => a.flat ++ b.flat

def runList [Monad m] : List (α → m α) → α → m α
  | [] => pure
  | f :: fs => fun x => f x >>= runList fs

theorem runList_append [Monad m] [LawfulMonad m] :
    ∀ (fs gs : List (α → m α)) (x : α), runList (fs ++ gs) x = runList fs x >>= runList gs
  | [], gs, x => by simp [runList]
  | f :: fs, gs, x => by
    simp only [List.cons_append, runList, bind_assoc]
    congr; funext y; exact runList_append fs gs y

/-- any nesting of the chain equals its flat list of steps; uses only the monad laws -/
theorem flat_correct [Monad m] [LawfulMonad m] : ∀ (t : KTree m α) (x : α), runList t.flat x = t.eval x
  | .step f, x => by simp [KTree.flat, runList, KTree.eval]
  | .seq a b, x => by
    rw [KTree.flat, runList_append, flat_correct a, KTree.eval]
    congr; funext y; exact flat_correct b y

end

/-! ## 2. The instance: word validation chains, and the plain early-return program -/

/-- one step on the word `x` with parameter `k`: replace `x`, or fail with `err` unless `p` holds -/
inductive St where
  | set (e : E)
  | ensure (p : P) (err : UInt64)

def St.run (k : UInt64) : St → UInt64 → Except UInt64 UInt64
  | .set e, x => pure (e.eval k x)
  | .ensure p err, x => if p.eval k x then pure x else throw err

/-- the user-facing chain: steps joined by `then`, in any nesting -/
inductive Chain where
  | st (s : St)
  | then (a b : Chain)

def Chain.toK (k : UInt64) : Chain → KTree (Except UInt64) UInt64
  | .st s => .step (s.run k)
  | .then a b => .seq (a.toK k) (b.toK k)

/-- what the chain means: `and_then` all the way down -/
def Chain.run (c : Chain) (k x : UInt64) : Except UInt64 UInt64 := (c.toK k).eval x

def Chain.flat : Chain → List St
  | .st s => [s]
  | .then a b => a.flat ++ b.flat

/-- the plain program: straight-line code that returns at the first failed check (no `>>=`) -/
def lrun (k : UInt64) : List St → UInt64 → Except UInt64 UInt64
  | [], x => .ok x
  | .set e :: ss, x => lrun k ss (e.eval k x)
  | .ensure p err :: ss, x => if p.eval k x then lrun k ss x else .error err

theorem flat_toK (k : UInt64) : ∀ c : Chain, (c.toK k).flat = c.flat.map (St.run k)
  | .st s => rfl
  | .then a b => by simp [Chain.toK, KTree.flat, Chain.flat, flat_toK k a, flat_toK k b]

theorem lrun_eq (k : UInt64) : ∀ (ss : List St) (x : UInt64), lrun k ss x = runList (ss.map (St.run k)) x
  | [], x => rfl
  | .set e :: ss, x => by simp [lrun, runList, St.run, lrun_eq k ss] <;> rfl
  | .ensure p err :: ss, x => by
    by_cases h : p.eval k x
    · simp [lrun, runList, St.run, h, lrun_eq k ss] <;> rfl
    · simp [lrun, runList, St.run, h] <;> rfl

/-- the early-return program computes the chain -/
theorem lower_correct (c : Chain) (k x : UInt64) : lrun k c.flat x = c.run k x := by
  rw [lrun_eq, ← flat_toK, flat_correct]; rfl

/-! ## 3. Zero cost in a cost model

`steps` counts step evaluations; `wraps` counts `Result` values built and inspected between steps.
`Chain.runC` is `and_then` as a library does it: every step returns a `Result` (one wrap), and every
`then` inspects its left result. `lrunC` is the early-return code: it builds none. -/

structure RCost where
  steps : Nat
  wraps : Nat
deriving DecidableEq, Repr

instance : Add RCost := ⟨fun a b => ⟨a.steps + b.steps, a.wraps + b.wraps⟩⟩

def Chain.runC (k : UInt64) : Chain → UInt64 → Except UInt64 UInt64 × RCost
  | .st s, x => (s.run k x, ⟨1, 1⟩)
  | .then a b, x =>
    let (r, ca) := a.runC k x
    match r with
    | .error e => (.error e, ca)
    | .ok y => let (r', cb) := b.runC k y; (r', ca + cb)

def lrunC (k : UInt64) : List St → UInt64 → Except UInt64 UInt64 × RCost
  | [], x => (.ok x, ⟨0, 0⟩)
  | .set e :: ss, x => let (r, c) := lrunC k ss (e.eval k x); (r, ⟨c.steps + 1, c.wraps⟩)
  | .ensure p err :: ss, x =>
    if p.eval k x then let (r, c) := lrunC k ss x; (r, ⟨c.steps + 1, c.wraps⟩) else (.error err, ⟨1, 0⟩)

theorem lrunC_fst (k : UInt64) : ∀ (ss : List St) (x : UInt64), (lrunC k ss x).1 = lrun k ss x
  | [], x => rfl
  | .set e :: ss, x => by simp [lrunC, lrun, lrunC_fst k ss]
  | .ensure p err :: ss, x => by by_cases h : p.eval k x <;> simp [lrunC, lrun, h, lrunC_fst k ss]

theorem lower_wraps (k : UInt64) : ∀ (ss : List St) (x : UInt64), (lrunC k ss x).2.wraps = 0
  | [], x => rfl
  | .set e :: ss, x => by simp [lrunC, lower_wraps k ss]
  | .ensure p err :: ss, x => by by_cases h : p.eval k x <;> simp [lrunC, h, lower_wraps k ss]

theorem lrunC_append (k : UInt64) : ∀ (ss ts : List St) (x : UInt64),
    (lrunC k (ss ++ ts) x).2.steps = (lrunC k ss x).2.steps +
      (match lrun k ss x with | .ok y => (lrunC k ts y).2.steps | .error _ => 0)
  | [], ts, x => by simp [lrunC, lrun]
  | .set e :: ss, ts, x => by
    rw [List.cons_append]; simp only [lrunC, lrun]; rw [lrunC_append k ss ts]; omega
  | .ensure p err :: ss, ts, x => by
    by_cases h : p.eval k x
    · rw [List.cons_append]; simp only [lrunC, lrun, h, if_true]; rw [lrunC_append k ss ts]; omega
    · simp [lrunC, lrun, h]

theorem runC_fst (k : UInt64) : ∀ (c : Chain) (x : UInt64), (c.runC k x).1 = c.run k x
  | .st s, x => rfl
  | .then a b, x => by
    have ha := runC_fst k a x
    simp only [Chain.runC, Chain.run, Chain.toK, KTree.eval] at *
    rw [← ha]
    rcases (a.runC k x) with ⟨r, ca⟩
    cases r with
    | error e => rfl
    | ok y => simp only []; rw [runC_fst k b y]; rfl

/-- the early-return code runs exactly the steps `and_then` runs: same short-circuit, nothing extra -/
theorem lower_steps (k : UInt64) : ∀ (c : Chain) (x : UInt64), (lrunC k c.flat x).2.steps = (c.runC k x).2.steps
  | .st (.set e), x => by simp [Chain.flat, lrunC, Chain.runC]
  | .st (.ensure p err), x => by
    by_cases h : p.eval k x <;> simp [Chain.flat, lrunC, Chain.runC, h]
  | .then a b, x => by
    rw [Chain.flat, lrunC_append, lower_steps k a, lower_correct]
    have ha := runC_fst k a x
    simp only [Chain.runC]
    generalize a.runC k x = q at ha ⊢
    obtain ⟨r, ca⟩ := q
    simp only at ha ⊢
    subst ha
    cases h : a.run k x with
    | error e => rfl
    | ok y => simp only []; rw [lower_steps k b y]; rfl

/-- mutant: run every step, then report the first failure. Same result, more steps -/
def eagerC (k : UInt64) : List St → UInt64 → Except UInt64 UInt64 × RCost
  | [], x => (.ok x, ⟨0, 0⟩)
  | .set e :: ss, x => let (r, c) := eagerC k ss (e.eval k x); (r, ⟨c.steps + 1, c.wraps⟩)
  | .ensure p err :: ss, x =>
    let (r, c) := eagerC k ss x; (if p.eval k x then r else .error err, ⟨c.steps + 1, c.wraps⟩)

/-- mutant: early return, but every step boxes its result. Same result and steps, more wraps -/
def boxedC (k : UInt64) (ss : List St) (x : UInt64) : Except UInt64 UInt64 × RCost :=
  let (r, c) := lrunC k ss x; (r, ⟨c.steps, c.steps⟩)

def demo : Chain :=
  .then (.st (.ensure (.lt .x (.lit 1000)) 1)) (.then (.st (.ensure (.lt .x (.lit 10)) 2)) (.st (.set (.add .x .k))))

theorem mut_eager : (eagerC 0 demo.flat 500).1 = demo.run 0 500 ∧
    (eagerC 0 demo.flat 500).2.steps ≠ (demo.runC 0 500).2.steps := ⟨rfl, by decide⟩

theorem mut_boxed : (boxedC 0 demo.flat 5).1 = demo.run 0 5 ∧ (boxedC 0 demo.flat 5).2.wraps ≠ 0 := ⟨rfl, by decide⟩

/-! ## 4. Printed C++: a statement tree with a C meaning -/

def St.toCS : St → CS
  | .set e => .assign .x e.toC
  | .ensure p err => .guard p.toC (.lit err)

def lowerC : List St → CS
  | [] => .skip
  | s :: ss => .seq s.toCS (lowerC ss)

/-- what the printed function returns: `Res{1, x}` on fall-through, `Res{0, err}` on `return` -/
def Out.res : Out → Except UInt64 UInt64
  | .ok env => .ok (env .x)
  | .ret v => .error v

/-- the printed statements compute the early-return program, so (by `lower_correct`) the chain -/
theorem printed_lrun (k : UInt64) :
    ∀ (ss : List St) (env : Slot → UInt64), env .k = k →
      ((lowerC ss).exec [] env).map Out.res = some (lrun k ss (env .x))
  | [], env, _ => rfl
  | .set e :: ss, env, hk => by
    have he := E.toC_eval env k (env .x) rfl hk e
    have hk' : upd env .x (e.eval k (env .x)) .k = k := by rw [upd_other _ _ (by decide)]; exact hk
    simp only [lowerC, St.toCS, CS.exec, he, Option.map_some', lrun]
    rw [printed_lrun k ss _ hk', upd_same]
  | .ensure p err :: ss, env, hk => by
    have hp := P.toC_eval env k (env .x) rfl hk p
    simp only [lowerC, St.toCS, CS.exec, hp, lrun]
    by_cases h : p.eval k (env .x)
    · simp only [h, if_true]; exact printed_lrun k ss env hk
    · simp [h, CE.eval, Out.res]

theorem printed_chain (c : Chain) (k x : UInt64) (env : Slot → UInt64) (hx : env .x = x) (hk : env .k = k) :
    ((lowerC c.flat).exec [] env).map Out.res = some (c.run k x) := by
  rw [printed_lrun k _ env hk, hx, lower_correct]

/-- C++ `Res name(std::uint64_t x, std::uint64_t k)`: the statements of `lowerC`, then `return Res{1, x};` -/
def Chain.toCpp (c : Chain) (name : String) : String :=
  String.intercalate "\n" ([s!"__attribute__((noinline)) static Res {name}(std::uint64_t x, std::uint64_t k) \{"] ++
    ((lowerC c.flat).print wordNm (fun v => s!"Res\{0, {v}}")).map ("  " ++ ·) ++
    ["  return Res{1, x};", "}"])

/-! ## A worked chain: validate and normalise a reading

`check` keeps readings below 10^12 (else error 1), scales by 10 and adds the offset `k`, rejects values
that are 6 mod 7 (error 2), mixes in a constant, and rejects values that end in 96 mod 97 (error 3). It is
written nested on purpose; `checkChain_gen` says the printed straight-line code computes it anyway. -/

def check : Chain :=
  .then (.then (.st (.ensure (.lt .x (.lit 1000000000000)) 1)) (.st (.set (.add (.mul .x (.lit 10)) .k))))
    (.then (.st (.ensure (.lt (.mod .x (.lit 7)) (.lit 6)) 2))
      (.then (.st (.set (.xor .x (.lit 0x5bd1e995)))) (.st (.ensure (.lt (.mod .x (.lit 97)) (.lit 96)) 3))))

theorem checkChain_gen (k x : UInt64) (env : Slot → UInt64) (hx : env .x = x) (hk : env .k = k) :
    ((lowerC check.flat).exec [] env).map Out.res = some (check.run k x) :=
  printed_chain check k x env hx hk

end Iter.Res
