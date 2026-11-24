import Iter.Rewrite
/-!
# A proved optimiser for word pipelines, with a C++ printer

`Pipe` is a tiny language for `filter keep → map f → sum` over 64-bit words, with expressions over the
item `x` and one runtime parameter `k`. `opt` turns a pipeline into a `Loop`: a branch-free masked body
summed over independent lanes, with a constant factor of `f` moved after the sum. `opt_correct` proves the
loop computes the `Iter` chain for every input. `Loop.toCpp` prints the loop as a C++ function; the printer
is the one unproved step (it is 30 lines, below). Lean's `x % 0 = x`, which is undefined behaviour in
C++, is printed as a guarded `%` unless the divisor is a nonzero literal.
-/
namespace Iter.Gen
open Iter.Rewrite

/-- 64-bit word expressions over the item `x` and the parameter `k`; arithmetic wraps, like C++ `uint64_t` -/
inductive E where
  | x
  | k
  | lit (n : UInt64)
  | add (a b : E)
  | mul (a b : E)
  | xor (a b : E)
  | mod (a b : E)

def E.eval (e : E) (k x : UInt64) : UInt64 :=
  match e with
  | .x => x
  | .k => k
  | .lit n => n
  | .add a b => a.eval k x + b.eval k x
  | .mul a b => a.eval k x * b.eval k x
  | .xor a b => a.eval k x ^^^ b.eval k x
  | .mod a b => a.eval k x % b.eval k x

/-- comparisons, combined without short-circuit -/
inductive P where
  | eq (a b : E)
  | lt (a b : E)
  | and (p q : P)

def P.eval (p : P) (k x : UInt64) : Bool :=
  match p with
  | .eq a b => a.eval k x == b.eval k x
  | .lt a b => decide (a.eval k x < b.eval k x)
  | .and p q => p.eval k x && q.eval k x

/-- `filter keep → map f → sum` -/
structure Pipe where
  keep : P
  f : E

/-- the `Iter` chain a pipeline stands for -/
def Pipe.run (q : Pipe) (k : UInt64) (xs : Array UInt64) : UInt64 :=
  (xs.iter.filter (fun x => q.keep.eval k x) |>.map (fun x => q.f.eval k x)).foldl 0 (· + ·)

/-- an optimised loop: `lanes` accumulators, `acc += body & -keep`, total times `scale` -/
structure Loop where
  lanes : Nat
  keep : P
  body : E
  scale : E

def sel (b : Bool) (v : UInt64) : UInt64 := v &&& (0 - if b then 1 else 0)

/-- what the printed C++ computes: item `j` goes to lane `j % lanes` (`rot`), lanes summed, then scaled -/
def Loop.run (L : Loop) (k : UInt64) (xs : Array UInt64) : UInt64 :=
  sumL ((xs.toList.map fun x => sel (L.keep.eval k x) (L.body.eval k x)).foldl rot (List.replicate L.lanes 0))
    * L.scale.eval k 0

/-- `e` does not read the item -/
def E.noX : E → Bool
  | .x => false
  | .k | .lit _ => true
  | .add a b | .mul a b | .xor a b | .mod a b => a.noX && b.noX

theorem E.eval_noX : ∀ (e : E), e.noX = true → ∀ k x y, e.eval k x = e.eval k y
  | .x, h, _, _, _ => by simp [E.noX] at h
  | .k, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .add a b, h, p, u, v | .mul a b, h, p, u, v | .xor a b, h, p, u, v | .mod a b, h, p, u, v => by
    simp only [E.noX, Bool.and_eq_true] at h
    simp only [E.eval, a.eval_noX h.1 p u v, b.eval_noX h.2 p u v]

/-- split `f = body * scale` when the right factor does not read the item -/
def split : E → E × E
  | .mul a c => if c.noX then (a, c) else (.mul a c, .lit 1)
  | e => (e, .lit 1)

def opt (lanes : Nat) (q : Pipe) : Loop := ⟨lanes, q.keep, (split q.f).1, (split q.f).2⟩

theorem u64_mul_one (a : UInt64) : a * 1 = a :=
  UInt64.toBitVec_inj.1 (by show a.toBitVec * 1#64 = a.toBitVec; exact BitVec.mul_one _)

theorem split_ok (k x : UInt64) : ∀ e : E, (split e).1.eval k x * (split e).2.eval k 0 = e.eval k x
  | .mul a c => by
    by_cases h : c.noX = true
    · simp only [split, h, ↓reduceIte, E.eval, c.eval_noX h k 0 x]
    · simp only [split, h, Bool.false_eq_true, ↓reduceIte, E.eval, u64_mul_one]
  | .x | .k | .lit _ | .add _ _ | .xor _ _ | .mod _ _ => u64_mul_one _

theorem sum_map_mul {σ : Type} (g : σ → UInt64) (c : UInt64) :
    ∀ l : List σ, sumL (l.map fun x => g x * c) = sumL (l.map g) * c
  | [] => (u64_zero_mul c).symm
  | x :: xs => by
    rw [List.map_cons, List.map_cons, sumL_cons u64Laws, sumL_cons u64Laws, sum_map_mul g c xs, u64_add_mul]

/-- the optimised loop computes the pipeline's `Iter` chain, for every pipeline, lane count and input -/
theorem opt_correct (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q).run k xs = q.run k xs := by
  let b := fun x => (split q.f).1.eval k x
  let c := (split q.f).2.eval k 0
  have hf : (fun x => q.f.eval k x) = fun x => b x * c := funext fun x => (split_ok k x q.f).symm
  rw [Pipe.run, (((denotes_array xs).filter _).map _).foldl]
  show _ = sumL ((xs.toList.filter (fun x => q.keep.eval k x)).map (fun x => q.f.eval k x))
  rw [hf, sum_map_mul, sum_select u64Laws, ← sum_lanes u64Laws lanes]
  simp only [Loop.run, opt, sel, select_mask]

/-! ## C++ printer (trusted) -/

def E.toCpp : E → String
  | .x => "x"
  | .k => "k"
  | .lit n => s!"{n}ULL"
  | .add a b => s!"({a.toCpp} + {b.toCpp})"
  | .mul a b => s!"({a.toCpp} * {b.toCpp})"
  | .xor a b => s!"({a.toCpp} ^ {b.toCpp})"
  | .mod a (.lit n) => if n == 0 then a.toCpp else s!"({a.toCpp} % {n}ULL)"
  | .mod a b => s!"(({b.toCpp}) == 0 ? {a.toCpp} : {a.toCpp} % {b.toCpp})"

def P.toCpp : P → String
  | .eq a b => s!"({a.toCpp} == {b.toCpp})"
  | .lt a b => s!"({a.toCpp} < {b.toCpp})"
  | .and p q => s!"({p.toCpp} & {q.toCpp})"

/-- one C++ function `name(xs, k)`; 0 lanes is printed as 1 (same sum, and no zero-length array or
zero-step loop) -/
def Loop.toCpp (L : Loop) (name : String) : String :=
  let n := max L.lanes 1
  let add := fun (lane : String) => s!"acc[{lane}] += {L.body.toCpp} & (0 - (std::uint64_t){L.keep.toCpp});"
  String.intercalate "\n" [
    s!"__attribute__((noinline)) static std::uint64_t {name}(const std::vector<std::uint64_t>& xs, std::uint64_t k) \{",
    "  (void)k;",
    s!"  std::uint64_t acc[{n}] = \{};",
    "  std::size_t n = xs.size(), i = 0;",
    s!"  for (; i + {n} <= n; i += {n})",
    s!"    for (std::size_t j = 0; j < {n}; ++j) \{ std::uint64_t x = xs[i + j]; {add "j"} }",
    s!"  for (; i < n; ++i) \{ std::uint64_t x = xs[i]; {add s!"i % {n}"} }",
    "  std::uint64_t total = 0;",
    "  for (std::uint64_t a : acc) total += a;",
    s!"  return total * {L.scale.toCpp};",
    "}"]

/-! ## The benchmark's word pipeline -/

/-- `filter ((x ^ k) % 3 == 0) → map (x * 2) → sum`, as in `Bench.lean` and `bench.cpp` -/
def wordPipe : Pipe := ⟨.eq (.mod (.xor .x .k) (.lit 3)) (.lit 0), .mul .x (.lit 2)⟩

theorem wordPipe_chain (k : UInt64) (xs : Array UInt64) :
    wordPipe.run k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2)).foldl 0 (· + ·) := rfl

/-- the generated loop for the benchmark equals its `Iter` chain -/
theorem wordPipe_gen (k : UInt64) (xs : Array UInt64) :
    (opt 8 wordPipe).run k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2)).foldl 0 (· + ·) :=
  (opt_correct 8 wordPipe k xs).trans (wordPipe_chain k xs)

/-! ## Record summaries -/

/-- expressions over a row's word fields and the call's word parameters -/
inductive X where
  | fld (i : Nat)
  | prm (i : Nat)
  | lit (n : UInt64)
  | add (a b : X)
  | mul (a b : X)
  | div (a b : X)

def X.eval (e : X) (ps r : List UInt64) : UInt64 :=
  match e with
  | .fld i => r.getD i 0
  | .prm i => ps.getD i 0
  | .lit n => n
  | .add a b => a.eval ps r + b.eval ps r
  | .mul a b => a.eval ps r * b.eval ps r
  | .div a b => a.eval ps r / b.eval ps r

inductive Q where
  | ne0 (a : X)
  | ge (a b : X)
  | and (p q : Q)

def Q.eval (q : Q) (ps r : List UInt64) : Bool :=
  match q with
  | .ne0 a => a.eval ps r != 0
  | .ge a b => decide (a.eval ps r ≥ b.eval ps r)
  | .and p q => p.eval ps r && q.eval ps r

structure Row (ν : Type) where
  label : ν
  f : List UInt64

/-- `filter keep → map (label, pay) → running (count, total, first, last)` -/
structure SPipe where
  keep : Q
  pay : X

variable {ν : Type}

def SPipe.run (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) : Summary ν UInt64 :=
  (rows.iter.filter (fun r => q.keep.eval ps r.f) |>.map (fun r => (r.label, q.pay.eval ps r.f))).foldl
    ⟨0, 0, none, none⟩ step

/-! ### one pass, branch-free

The loop `SPipe.toCpp` prints: one pass, the kept test as a mask for count and total, and first / last as
pointer selects (`fp = (k & !fp) ? &e : fp`), so no branch depends on the data. `Row` here is the C++ row
pointer and `none` is `nullptr`. -/

def SPipe.step1 (q : SPipe) (ps : List UInt64) (s : Summary (Row ν) UInt64) (r : Row ν) :
    Summary (Row ν) UInt64 :=
  let k := q.keep.eval ps r.f
  ⟨s.count + (if k then 1 else 0), s.total + sel k (q.pay.eval ps r.f),
   if k && s.first.isNone then some r else s.first, if k then some r else s.last⟩

def SPipe.fast1 (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) : Summary ν UInt64 :=
  let s := rows.toList.foldl (q.step1 ps) ⟨0, 0, none, none⟩
  ⟨s.count, s.total, s.first.map (·.label), s.last.map (·.label)⟩

/-- the one-pass step skips dropped rows and is the summary step on kept ones -/
theorem step1_filter (q : SPipe) (ps : List UInt64) : ∀ (l : List (Row ν)) (s : Summary (Row ν) UInt64),
    l.foldl (q.step1 ps) s =
      ((l.filter fun r => q.keep.eval ps r.f).map fun r => (r, q.pay.eval ps r.f)).foldl step s
  | [], _ => rfl
  | r :: rs, s => by
    have h0 : ∀ v, sel false v = 0 := fun v => by rw [sel, select_mask]; rfl
    have h1 : ∀ v, sel true v = v := fun v => by rw [sel, select_mask]; rfl
    cases hk : q.keep.eval ps r.f
    · simp only [List.foldl_cons, List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
      rw [← step1_filter q ps rs]; congr 1
      cases s; simp [SPipe.step1, hk, h0, add_zero u64Laws]
    · simp only [List.foldl_cons, List.filter_cons, hk, ↓reduceIte, List.map_cons]
      rw [step1_filter q ps rs]; congr 1
      cases s with
      | mk c t f l => cases f <;> simp [SPipe.step1, step, hk, h1]

/-- the one-pass branch-free loop computes the running summary, for every pipeline and input -/
theorem fast1_correct (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast1 ps rows = q.run ps rows := by
  rw [SPipe.run, (((denotes_array rows).filter _).map _).foldl, summary_split u64Laws, SPipe.fast1,
    step1_filter]
  simp only [summary_split u64Laws, List.length_map, List.map_map, Function.comp_def, List.head?_map,
    List.getLast?_map, Option.map_map]

/-! ### printer (trusted) -/

/-- `fields[i]` / `params[i]` are the C++ for field / parameter `i`; a missing one is `0`, as in `X.eval` -/
def X.toCpp (fields params : List String) : X → String
  | .fld i => fields.getD i "0ULL"
  | .prm i => params.getD i "0ULL"
  | .lit n => s!"{n}ULL"
  | .add a b => s!"({a.toCpp fields params} + {b.toCpp fields params})"
  | .mul a b => s!"({a.toCpp fields params} * {b.toCpp fields params})"
  | .div a (.lit n) => if n == 0 then "0ULL" else s!"({a.toCpp fields params} / {n}ULL)"
  | .div a b => s!"(({b.toCpp fields params}) == 0 ? 0ULL : {a.toCpp fields params} / {b.toCpp fields params})"

def Q.toCpp (fields params : List String) : Q → String
  | .ne0 a => s!"({a.toCpp fields params} != 0)"
  | .ge a b => s!"({a.toCpp fields params} >= {b.toCpp fields params})"
  | .and p q => s!"({p.toCpp fields params} & {q.toCpp fields params})"

/-- C++ `name(rows, p0, p1, ...)` computing `SPipe.fast1`; `fields[i]` is the C++ expression for word field
`i` of row `e`, and the includer defines the row type with a `name` member and `Summ` with `count`, `total`,
`first`, `last` -/
def SPipe.toCpp (q : SPipe) (nParams : Nat) (name rowType : String) (fields : List String) : String :=
  let ps := (List.range nParams).map (s!"p{·}")
  let params := String.join (ps.map (s!", std::uint64_t {·}"))
  String.intercalate "\n" [
    s!"__attribute__((noinline)) static Summ {name}(const std::vector<{rowType}>& es{params}) \{",
    "  std::uint64_t cnt = 0, tot = 0;",
    s!"  const {rowType}* fp = nullptr;",
    s!"  const {rowType}* lp = nullptr;",
    s!"  for (const {rowType}& e : es) \{",
    s!"    bool k = {q.keep.toCpp fields ps};",
    "    std::uint64_t m = 0 - (std::uint64_t)k;",
    s!"    cnt += 1 & m; tot += {q.pay.toCpp fields ps} & m;",
    "    fp = (k & (fp == nullptr)) ? &e : fp;",
    "    lp = k ? &e : lp;",
    "  }",
    "  Summ s; s.count = cnt; s.total = tot;",
    "  if (fp) s.first = fp->name;",
    "  if (lp) s.last = lp->name;",
    "  return s;",
    "}"]

/-- the benchmark's record pipeline: keep `active != 0 & salary >= p0`, pay `salary * p1 / 100` -/
def recPipe : SPipe := ⟨.and (.ne0 (.fld 1)) (.ge (.fld 0) (.prm 0)), .div (.mul (.fld 0) (.prm 1)) (.lit 100)⟩

theorem recPipe_gen (ps : List UInt64) (rows : Array (Row ν)) : recPipe.fast1 ps rows = recPipe.run ps rows :=
  fast1_correct recPipe ps rows

end Iter.Gen
