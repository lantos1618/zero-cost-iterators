import Iter.Basic
/-!
# Cost model: fused loop vs staged passes

A small IR with explicit costs. `pulls` counts item reads (source or buffer), `calls` counts user
callbacks (`map f`, `filter p`, terminal step), `allocs` counts cells written to an intermediate
collection. The only allocating construct is `Prog.buffer`.

* `Chain.staged` is the independent eager reference: every adapter is its own pass that writes a
  new list.
* `lower` turns a chain into ONE loop whose body is the adapters nested in order.

Proved for every chain of `map`/`filter` and every terminal:
* `lower_result`: same answer as the staged program;
* `lower_allocs`: zero intermediate allocations;
* `lower_pulls_le`: at most one read per source item;
* `lower_calls`, `lower_pulls` (terminals that never stop early, e.g. `foldl`): exactly as many
  callback calls as the staged program, and exactly one read per source item;
* `lower_eq_hand`: the lowering is literally the loop one writes by hand.
Result-preserving cost mutants at the end are rejected by exact cost values.
Not modelled: `take`/`enumerate` counters, `groupFold`'s table, and how Lean compiles `Iter`.
-/
namespace Iter.Cost

structure Cost where
  pulls : Nat
  calls : Nat
  allocs : Nat
deriving DecidableEq, Repr

def Cost.zero : Cost := ⟨0, 0, 0⟩
instance : Add Cost := ⟨fun a b => ⟨a.pulls + b.pulls, a.calls + b.calls, a.allocs + b.allocs⟩⟩
@[simp] theorem add_pulls (a b : Cost) : (a + b).pulls = a.pulls + b.pulls := rfl
@[simp] theorem add_calls (a b : Cost) : (a + b).calls = a.calls + b.calls := rfl
@[simp] theorem add_allocs (a b : Cost) : (a + b).allocs = a.allocs + b.allocs := rfl

/-- account for one more item read and `n` more callback calls -/
def Cost.tick {S : Type} (n : Nat) (r : S × Cost) : S × Cost := (r.1, ⟨r.2.pulls + 1, r.2.calls + n, r.2.allocs⟩)
@[simp] theorem Cost.tick_pulls {S : Type} (n : Nat) (r : S × Cost) : (Cost.tick n r).2.pulls = r.2.pulls + 1 := rfl
@[simp] theorem Cost.tick_calls {S : Type} (n : Nat) (r : S × Cost) : (Cost.tick n r).2.calls = r.2.calls + n := rfl

/-- pipeline syntax -/
inductive Chain : Type → Type → Type 1
  | src {σ : Type} : Chain σ σ
  | map {σ α β : Type} (c : Chain σ α) (f : α → β) : Chain σ β
  | filter {σ α : Type} (c : Chain σ α) (p : α → Bool) : Chain σ α

/-- per-item loop body -/
inductive Body : Type → Type → Type 1
  | emit {α : Type} : Body α α
  | call {α β γ : Type} (f : α → β) (k : Body β γ) : Body α γ
  | test {α γ : Type} (p : α → Bool) (k : Body α γ) : Body α γ

/-- loop programs; `buffer b rest` writes every output of `b` to a new list, then runs `rest` on it -/
inductive Prog : Type → Type → Type 1
  | loop {σ γ : Type} (b : Body σ γ) : Prog σ γ
  | buffer {σ α γ : Type} (b : Body σ α) (rest : Prog α γ) : Prog σ γ

/-- terminal with early exit -/
structure Term (γ ρ : Type) : Type 1 where
  S : Type
  init : S
  step : S → γ → ForInStep S
  out : S → ρ

/-- the terminal never stops early (e.g. `foldl`) -/
def Term.NonStop {γ ρ : Type} (t : Term γ ρ) : Prop := ∀ s y, ∃ s', t.step s y = .yield s'

def foldT {γ β : Type} (init : β) (step : β → γ → β) : Term γ β := ⟨β, init, fun s y => .yield (step s y), id⟩
def findT {γ : Type} (p : γ → Bool) : Term γ (Option γ) :=
  ⟨Option γ, none, fun _ y => if p y then .done (some y) else .yield none, id⟩

theorem foldT_nonStop {γ β : Type} (init : β) (step : β → γ → β) : (foldT init step).NonStop :=
  fun s y => ⟨step s y, rfl⟩

/-- run a body on one item: emitted value (if any) and callbacks invoked -/
def Body.run : {α γ : Type} → Body α γ → α → Option γ × Nat
  | _, _, .emit, a => (some a, 0)
  | _, _, .call f k, a => ((k.run (f a)).1, (k.run (f a)).2 + 1)
  | _, _, .test p k, a => if p a then ((k.run a).1, (k.run a).2 + 1) else (none, 1)

variable {σ α γ ρ : Type}

def runLoop (b : Body σ γ) (t : Term γ ρ) : t.S → List σ → t.S × Cost
  | s, [] => (s, Cost.zero)
  | s, x :: xs =>
    match (b.run x).1 with
    | none => Cost.tick (b.run x).2 (runLoop b t s xs)
    | some y =>
      match t.step s y with
      | .done s' => (s', ⟨1, (b.run x).2 + 1, 0⟩)
      | .yield s' => Cost.tick ((b.run x).2 + 1) (runLoop b t s' xs)

/-- materializing pass: one read per item, one cell per output -/
def collect (b : Body σ α) : List σ → List α × Cost
  | [] => ([], Cost.zero)
  | x :: xs =>
    match (b.run x).1 with
    | none => ((collect b xs).1, (collect b xs).2 + ⟨1, (b.run x).2, 0⟩)
    | some y => (y :: (collect b xs).1, (collect b xs).2 + ⟨1, (b.run x).2, 1⟩)

def Prog.run : {σ γ : Type} → Prog σ γ → (t : Term γ ρ) → List σ → t.S × Cost
  | _, _, .loop b, t, xs => runLoop b t t.init xs
  | _, _, .buffer b rest, t, xs => ((rest.run t (collect b xs).1).1, (collect b xs).2 + (rest.run t (collect b xs).1).2)

/-! ## Lowering and the staged reference -/

def Chain.body : {α : Type} → Chain σ α → Body α γ → Body σ γ
  | _, .src, k => k
  | _, .map c f, k => c.body (.call f k)
  | _, .filter c p, k => c.body (.test p k)

def lower (c : Chain σ α) : Prog σ α := .loop (c.body .emit)

/-- eager reference: each adapter reads its whole input and writes a new list -/
def Chain.staged : {α : Type} → Chain σ α → List σ → List α × Cost
  | _, .src, xs => (xs, Cost.zero)
  | _, .map c f, xs =>
    let r := c.staged xs
    (r.1.map f, r.2 + ⟨r.1.length, r.1.length, r.1.length⟩)
  | _, .filter c p, xs =>
    let r := c.staged xs
    (r.1.filter p, r.2 + ⟨r.1.length, r.1.length, (r.1.filter p).length⟩)

def stagedRun (c : Chain σ α) (t : Term α ρ) (xs : List σ) : t.S × Cost :=
  ((runLoop .emit t t.init (c.staged xs).1).1, (c.staged xs).2 + (runLoop .emit t t.init (c.staged xs).1).2)

/-! ## Result -/

theorem loop_call {β : Type} (f : α → β) (k : Body β γ) (t : Term γ ρ) :
    ∀ (ys : List α) s, (runLoop (.call f k) t s ys).1 = (runLoop k t s (ys.map f)).1
  | [], _ => rfl
  | y :: ys, s => by
    simp only [runLoop, Body.run, List.map_cons]
    cases (k.run (f y)).1 with
    | none => exact loop_call f k t ys s
    | some z =>
      dsimp only
      cases t.step s z with
      | done _ => rfl
      | yield s' => exact loop_call f k t ys s'

theorem loop_test (p : α → Bool) (k : Body α γ) (t : Term γ ρ) :
    ∀ (ys : List α) s, (runLoop (.test p k) t s ys).1 = (runLoop k t s (ys.filter p)).1
  | [], _ => rfl
  | y :: ys, s => by
    by_cases hp : p y = true
    · simp only [runLoop, Body.run, hp, ↓reduceIte, List.filter_cons_of_pos hp]
      cases (k.run y).1 with
      | none => exact loop_test p k t ys s
      | some z =>
        dsimp only
        cases t.step s z with
        | done _ => rfl
        | yield s' => exact loop_test p k t ys s'
    · simp only [runLoop, Body.run, hp, ↓reduceIte, List.filter_cons_of_neg hp, Bool.false_eq_true]
      exact loop_test p k t ys s

theorem body_result (t : Term γ ρ) : ∀ {α : Type} (c : Chain σ α) (k : Body α γ) (xs : List σ) s,
    (runLoop (c.body k) t s xs).1 = (runLoop k t s (c.staged xs).1).1
  | _, .src, _, _, _ => rfl
  | _, .map c f, k, xs, s => by
    simp only [Chain.body, Chain.staged]; rw [body_result t c, loop_call]
  | _, .filter c p, k, xs, s => by
    simp only [Chain.body, Chain.staged]; rw [body_result t c, loop_test]

/-- the fused loop computes the staged answer, for every terminal including early exit -/
theorem lower_result (c : Chain σ α) (t : Term α ρ) (xs : List σ) :
    ((lower c).run t xs).1 = (stagedRun c t xs).1 :=
  body_result t c .emit xs t.init

/-! ## Cost -/

theorem loop_allocs (b : Body σ γ) (t : Term γ ρ) : ∀ (xs : List σ) s, (runLoop b t s xs).2.allocs = 0
  | [], _ => rfl
  | x :: xs, s => by
    simp only [runLoop]
    cases (b.run x).1 with
    | none => exact loop_allocs b t xs s
    | some y =>
      dsimp only
      cases t.step s y with
      | done _ => rfl
      | yield s' => exact loop_allocs b t xs s'

theorem loop_pulls_le (b : Body σ γ) (t : Term γ ρ) : ∀ (xs : List σ) s, (runLoop b t s xs).2.pulls ≤ xs.length
  | [], _ => Nat.le_refl _
  | x :: xs, s => by
    simp only [runLoop, List.length_cons]
    cases (b.run x).1 with
    | none => have := loop_pulls_le b t xs s; simp only [Cost.tick_pulls]; omega
    | some y =>
      dsimp only
      cases t.step s y with
      | done _ => simp only []; omega
      | yield s' => have := loop_pulls_le b t xs s'; simp only [Cost.tick_pulls]; omega

/-- callbacks one item costs: body calls plus the terminal step if a value reaches it -/
def Body.calls (b : Body σ γ) (x : σ) : Nat := (b.run x).2 + if (b.run x).1.isSome then 1 else 0

theorem loop_nonstop (b : Body σ γ) (t : Term γ ρ) (h : t.NonStop) : ∀ (xs : List σ) s,
    (runLoop b t s xs).2.pulls = xs.length ∧ (runLoop b t s xs).2.calls = (xs.map b.calls).sum
  | [], _ => ⟨rfl, rfl⟩
  | x :: xs, s => by
    simp only [runLoop, List.length_cons, List.map_cons, List.sum_cons, Body.calls]
    cases hb : (b.run x).1 with
    | none =>
      have := loop_nonstop b t h xs s
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Cost.tick_pulls, Cost.tick_calls]
      constructor <;> omega
    | some y =>
      obtain ⟨s', hs⟩ := h s y
      have := loop_nonstop b t h xs s'
      simp only [hs, Option.isSome_some, ↓reduceIte, Cost.tick_pulls, Cost.tick_calls]; constructor <;> omega

theorem calls_call {β : Type} (f : α → β) (k : Body β γ) (y : α) :
    (Body.call f k).calls y = 1 + k.calls (f y) := by
  simp only [Body.calls, Body.run]; omega

theorem calls_test (p : α → Bool) (k : Body α γ) (y : α) :
    (Body.test p k).calls y = 1 + if p y then k.calls y else 0 := by
  by_cases hp : p y = true <;> simp only [Body.calls, Body.run, hp, ↓reduceIte, Option.isSome_none,
    Bool.false_eq_true] <;> omega

theorem sum_call {β : Type} (f : α → β) (k : Body β γ) : ∀ ys : List α,
    (ys.map (Body.call f k).calls).sum = ys.length + ((ys.map f).map k.calls).sum
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, List.sum_cons, calls_call, sum_call f k ys, List.length_cons]; omega

theorem sum_test (p : α → Bool) (k : Body α γ) : ∀ ys : List α,
    (ys.map (Body.test p k).calls).sum = ys.length + ((ys.filter p).map k.calls).sum
  | [] => rfl
  | y :: ys => by
    have ih := sum_test p k ys
    by_cases hp : p y = true
    · simp only [List.map_cons, List.sum_cons, calls_test, hp, ↓reduceIte, List.filter_cons_of_pos hp,
        List.length_cons]; omega
    · simp only [List.map_cons, List.sum_cons, calls_test, hp, ↓reduceIte, List.filter_cons_of_neg hp,
        List.length_cons, Bool.false_eq_true]; omega

theorem body_calls : ∀ {α : Type} (c : Chain σ α) (k : Body α γ) (xs : List σ),
    (xs.map (c.body k).calls).sum = (c.staged xs).2.calls + ((c.staged xs).1.map k.calls).sum
  | _, .src, _, _ => by simp [Chain.body, Chain.staged, Cost.zero]
  | _, .map c f, k, xs => by
    simp only [Chain.body, Chain.staged, add_calls]; rw [body_calls c, sum_call]; omega
  | _, .filter c p, k, xs => by
    simp only [Chain.body, Chain.staged, add_calls]; rw [body_calls c, sum_test]; omega

theorem sum_emit : ∀ ys : List α, (ys.map (Body.emit (α := α)).calls).sum = ys.length
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, List.sum_cons, sum_emit ys, List.length_cons]; simp [Body.calls, Body.run]; omega

/-- zero intermediate allocation, for every chain and terminal -/
theorem lower_allocs (c : Chain σ α) (t : Term α ρ) (xs : List σ) : ((lower c).run t xs).2.allocs = 0 :=
  loop_allocs _ t xs t.init

/-- each source item is read at most once (early-exit terminals read fewer) -/
theorem lower_pulls_le (c : Chain σ α) (t : Term α ρ) (xs : List σ) : ((lower c).run t xs).2.pulls ≤ xs.length :=
  loop_pulls_le _ t xs t.init

/-- with a terminal that never stops early: exactly one read per source item -/
theorem lower_pulls (c : Chain σ α) (t : Term α ρ) (h : t.NonStop) (xs : List σ) :
    ((lower c).run t xs).2.pulls = xs.length :=
  (loop_nonstop _ t h xs t.init).1

/-- with a terminal that never stops early: exactly the staged program's callback calls -/
theorem lower_calls (c : Chain σ α) (t : Term α ρ) (h : t.NonStop) (xs : List σ) :
    ((lower c).run t xs).2.calls = (stagedRun c t xs).2.calls := by
  show (runLoop (c.body .emit) t t.init xs).2.calls = _
  simp only [stagedRun, add_calls]
  rw [(loop_nonstop _ t h xs t.init).2, (loop_nonstop .emit t h _ t.init).2, body_calls, sum_emit]

/-- the staged program allocates one cell per intermediate item -/
theorem staged_allocs (c : Chain σ α) (t : Term α ρ) (xs : List σ) :
    (stagedRun c t xs).2.allocs = (c.staged xs).2.allocs := by
  simp only [stagedRun, add_allocs, loop_allocs]; rfl

/-- the lowering of `filter p |>.map f` is the hand-written loop body, so it has the same cost -/
theorem lower_eq_hand {β : Type} (p : σ → Bool) (f : σ → β) :
    lower ((Chain.src.filter p).map f) = .loop (.test p (.call f .emit)) := rfl

/-! ## Link to the `Iter` API: the same chain on a real iterator has the staged meaning -/

def Chain.toIter : {α : Type} → Chain σ α → Iter σ → Iter α
  | _, .src, it => it
  | _, .map c f, it => (c.toIter it).map f
  | _, .filter c p, it => (c.toIter it).filter p

theorem toIter_denotes {it : Iter σ} {xs : List σ} (h : it.Denotes xs) :
    ∀ {α : Type} (c : Chain σ α), (c.toIter it).Denotes (c.staged xs).1
  | _, .src => h
  | _, .map c f => (toIter_denotes h c).map f
  | _, .filter c p => (toIter_denotes h c).filter p

/-! ## Cost mutants: same answers, rejected by cost -/

/-- every adapter as its own materializing pass -/
def Prog.thenBuf : {σ α β : Type} → Prog σ α → Body α β → Prog σ β
  | _, _, _, .loop l, b => .buffer l (.loop b)
  | _, _, _, .buffer l r, b => .buffer l (r.thenBuf b)

def lowerStaged : {α : Type} → Chain σ α → Prog σ α
  | _, .src => .loop .emit
  | _, .map c f => (lowerStaged c).thenBuf (.call f .emit)
  | _, .filter c p => (lowerStaged c).thenBuf (.test p .emit)

/-- tests every filter predicate twice -/
def Chain.bodyDup : {α : Type} → Chain σ α → Body α γ → Body σ γ
  | _, .src, k => k
  | _, .map c f, k => c.bodyDup (.call f k)
  | _, .filter c p, k => c.bodyDup (.test p (.test p k))

/-- find that keeps reading after the hit -/
def findAllT {γ : Type} (p : γ → Bool) : Term γ (Option γ) :=
  ⟨Option γ, none, fun s y => .yield (match s with | some a => some a | none => if p y then some y else none), id⟩

def exChain : Chain Nat Nat := (Chain.src.filter (fun n => n % 2 == 0)).map (· * 10)
def exXs : List Nat := [1, 2, 3, 4, 5, 6]
def sumT : Term Nat Nat := foldT 0 (· + ·)
def bigT : Term Nat (Option Nat) := findT (· > 20)

def R {γ ρ : Type} (p : Prog Nat γ) (t : Term γ ρ) : ρ × Cost := (t.out (p.run t exXs).1, (p.run t exXs).2)
/-- fused `foldl`: 6 reads, 12 calls, 0 cells; staged: 12 reads, 12 calls, 6 cells -/
theorem ex_fold : R (lower exChain) sumT = (120, ⟨6, 12, 0⟩) ∧ (stagedRun exChain sumT exXs).2 = ⟨12, 12, 6⟩ :=
  ⟨rfl, rfl⟩
/-- fused `find`: stops after the 4th source item -/
theorem ex_find : R (lower exChain) bigT = (some 40, ⟨4, 8, 0⟩) ∧ (stagedRun exChain bigT exXs).2 = ⟨11, 11, 6⟩ :=
  ⟨rfl, rfl⟩
/-- mutant 1 (materialize each stage): same answer, 9 cells -/
theorem mut_staged : R (lowerStaged exChain) sumT = (120, ⟨15, 12, 9⟩) := rfl
/-- mutant 2 (duplicate filter test): same answer, 15 calls instead of 12 -/
theorem mut_dup : R (.loop (exChain.bodyDup .emit)) sumT = (120, ⟨6, 15, 0⟩) := rfl
/-- mutant 3 (find without early exit): same answer, 6 reads instead of 4 -/
theorem mut_noexit : R (lower exChain) (findAllT (· > 20)) = (some 40, ⟨6, 12, 0⟩) := rfl

end Iter.Cost
