import Iter.Rewrite
import Iter.More
import Iter.CExpr
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

open Iter.C in
def E.toC : E → CE
  | .x => .var .x
  | .k => .var .k
  | .lit n => .lit n
  | .add a b => .bin .add a.toC b.toC
  | .mul a b => .bin .mul a.toC b.toC
  | .xor a b => .bin .xor a.toC b.toC
  | .mod a (.lit n) => if n = 0 then a.toC else .bin .mod a.toC (.lit n)
  | .mod a b => .cond (.bin .eq b.toC (.lit 0)) a.toC (.bin .mod a.toC b.toC)

open Iter.C in
def P.toC : P → CE
  | .eq a b => .bin .eq a.toC b.toC
  | .lt a b => .bin .lt a.toC b.toC
  | .and p q => .bin .band p.toC q.toC

open Iter.C in
def wordNm : Slot → String
  | .x => "x" | .k => "k" | .b => "b" | _ => "0ULL"

def E.toCpp (e : E) : String := e.toC.print wordNm
def P.toCpp (p : P) : String := p.toC.print wordNm

/-- the lane loop over `xs`: `step lane` runs with item `x`; full rounds of `n` items, then the tail -/
def laneLoop (n : Nat) (step : String → String) : List String := [
  "  std::size_t n = xs.size(), i = 0;",
  s!"  for (; i + {n} <= n; i += {n})",
  s!"    for (std::size_t j = 0; j < {n}; ++j) \{ std::uint64_t x = xs[i + j]; {step "j"} }",
  s!"  for (; i < n; ++i) \{ std::uint64_t x = xs[i]; {step s!"i % {n}"} }"]

def header (ret name : String) : String :=
  s!"__attribute__((noinline)) static {ret} {name}(const std::vector<std::uint64_t>& xs, std::uint64_t k) \{"

/-- one C++ function `name(xs, k)`; its loops are modelled line for line by `Loop.cRun` in `Iter/CLoop.lean`
(`cRun_eq`). With `br` the step is printed as `if (keep) acc[l] += body`, the same `acc[l] += sel keep body`
written as a branch (GCC may or may not if-convert it; speed only). 0 lanes is printed as 1 (same sum, and no zero-length array or
zero-step loop) -/
def Loop.toCpp (L : Loop) (name : String) (br : Bool := false) : String :=
  let n := max L.lanes 1
  String.intercalate "\n" ([header "std::uint64_t" name, "  (void)k;", s!"  std::uint64_t acc[{n}] = \{};"] ++
    laneLoop n (fun lane => if br then s!"if ({L.keep.toCpp}) acc[{lane}] += {L.body.toCpp};"
      else s!"acc[{lane}] += {(C.maskC L.body.toC (.cast L.keep.toC)).print wordNm};") ++ [
    "  std::uint64_t total = 0;",
    "  for (std::uint64_t a : acc) total += a;",
    s!"  return total * {L.scale.toCpp};",
    "}"])

/-- one accumulator over a range-for; modelled by `Loop.cRunR` (`cRunR_eq`). `br` as in `Loop.toCpp` -/
def Loop.toCppRange (L : Loop) (name : String) (br : Bool := true) : String :=
  String.intercalate "\n" [header "std::uint64_t" name, "  (void)k;", "  std::uint64_t acc = 0;",
    if br then s!"  for (std::uint64_t x : xs) if ({L.keep.toCpp}) acc += {L.body.toCpp};"
    else s!"  for (std::uint64_t x : xs) acc += {(C.maskC L.body.toC (.cast L.keep.toC)).print wordNm};",
    s!"  return acc * {L.scale.toCpp};", "}"]

/-! ## The benchmark's word pipeline -/

/-- `filter ((x ^ k) % 3 == 0) → map (x * 2) → sum`, as in `Bench.lean` and `bench.cpp` -/
def wordPipe : Pipe := ⟨.eq (.mod (.xor .x .k) (.lit 3)) (.lit 0), .mul .x (.lit 2)⟩

theorem wordPipe_chain (k : UInt64) (xs : Array UInt64) :
    wordPipe.run k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2)).foldl 0 (· + ·) := rfl

/-- the generated loop for the benchmark equals its `Iter` chain -/
theorem wordPipe_gen (k : UInt64) (xs : Array UInt64) :
    (opt 8 wordPipe).run k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2)).foldl 0 (· + ·) :=
  (opt_correct 8 wordPipe k xs).trans (wordPipe_chain k xs)

/-! ## `count`, `min?` and `max?` over word pipelines

`count` is a sum of 1 per kept item, so it reuses the sum loop (`count_correct`). `min?` and `max?` use the
same lanes with `min`/`max` as the `+` (`OpW` below), a masked body that turns dropped items into the
identity (`~0` for `min`, `0` for `max`), and one `seen` flag for the empty case (`red_correct`). -/

theorem u64_ofNat_succ (n : Nat) : (n + 1).toUInt64 = n.toUInt64 + 1 :=
  UInt64.toNat_inj.1 (by
    rw [UInt64.toNat_add]
    show (n + 1) % 2 ^ 64 = (n % 2 ^ 64 + 1) % 2 ^ 64
    rw [Nat.add_mod n 1, show 1 % 2 ^ 64 = 1 from rfl])

theorem sum_ones {σ : Type} : ∀ l : List σ, sumL (l.map fun _ => (1 : UInt64)) = l.length.toUInt64
  | [] => rfl
  | _ :: xs => by
    rw [List.map_cons, sumL_cons u64Laws, sum_ones xs, List.length_cons, u64_ofNat_succ, u64Laws.comm]

def Pipe.count (q : Pipe) (k : UInt64) (xs : Array UInt64) : Nat :=
  (xs.iter.filter fun x => q.keep.eval k x).count

/-- `count` as a word pipeline: `filter keep → map 1 → sum` -/
def Pipe.countPipe (q : Pipe) : Pipe := ⟨q.keep, .lit 1⟩

/-- the optimised sum loop of `countPipe` is `count`, as a 64-bit word -/
theorem count_correct (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q.countPipe).run k xs = (q.count k xs).toUInt64 := by
  rw [opt_correct, Pipe.run, (((denotes_array xs).filter _).map _).foldl, Pipe.count,
    ((denotes_array xs).filter _).count]
  exact sum_ones _

/-- `UInt64` with `o` as its `+` and `e` as its `0` -/
structure OpW (o : UInt64 → UInt64 → UInt64) (e : UInt64) where
  v : UInt64

instance {o e} : Add (OpW o e) := ⟨fun a b => ⟨o a.v b.v⟩⟩
instance {o e} : OfNat (OpW o e) 0 := ⟨⟨e⟩⟩

theorem opLaws {o : UInt64 → UInt64 → UInt64} {e : UInt64} (ha : ∀ a b c, o (o a b) c = o a (o b c))
    (hc : ∀ a b, o a b = o b a) (he : ∀ a, o e a = a) : AddLaws (OpW o e) :=
  ⟨fun a b c => congrArg OpW.mk (ha a.v b.v c.v), fun a b => congrArg OpW.mk (hc a.v b.v),
   fun ⟨a⟩ => congrArg OpW.mk (he a)⟩

theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = _
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem minLaws : AddLaws (OpW min (0 - 1)) :=
  opLaws (fun a b c => UInt64.toNat_inj.1 (by simp only [toNat_min]; omega))
    (fun a b => UInt64.toNat_inj.1 (by simp only [toNat_min]; omega))
    (fun a => UInt64.toNat_inj.1 (by
      have := a.toNat_lt_size
      rw [toNat_min, show (0 - 1 : UInt64).toNat = 2 ^ 64 - 1 from rfl]
      simp only [UInt64.size] at this; omega))

theorem maxLaws : AddLaws (OpW max 0) :=
  opLaws (fun a b c => UInt64.toNat_inj.1 (by simp only [toNat_max]; omega))
    (fun a b => UInt64.toNat_inj.1 (by simp only [toNat_max]; omega))
    (fun a => UInt64.toNat_inj.1 (by rw [toNat_max, show (0 : UInt64).toNat = 0 from rfl]; omega))

/-- `v | (b - 1)`: `v` if `b`, else all ones (the identity of `min`) -/
def selMin (b : Bool) (v : UInt64) : UInt64 := v ||| ((if b then 1 else 0) - 1)

theorem selMin_eq (b : Bool) (v : UInt64) : selMin b v = if b then v else 0 - 1 := by
  cases b
  · exact UInt64.toBitVec_inj.1 (by
      show v.toBitVec ||| (0 - 1 : UInt64).toBitVec = (0 - 1 : UInt64).toBitVec
      rw [show (0 - 1 : UInt64).toBitVec = BitVec.allOnes 64 by decide]; exact BitVec.or_allOnes)
  · exact UInt64.toBitVec_inj.1 (by
      show v.toBitVec ||| (1 - 1 : UInt64).toBitVec = v.toBitVec
      rw [show (1 - 1 : UInt64).toBitVec = 0#64 by decide]; exact BitVec.or_zero)

/-- reductions with an identity, printed as lanes -/
inductive Red where
  | min
  | max

def Red.op : Red → UInt64 → UInt64 → UInt64
  | .min => Min.min
  | .max => Max.max

def Red.id : Red → UInt64
  | .min => 0 - 1
  | .max => 0

/-- the masked body: the item if kept, else the identity -/
def Red.mask : Red → Bool → UInt64 → UInt64
  | .min => selMin
  | .max => sel

theorem Red.laws : (r : Red) → AddLaws (OpW r.op r.id)
  | .min => minLaws
  | .max => maxLaws

theorem Red.mask_eq : (r : Red) → ∀ b v, r.mask b v = if b then v else r.id
  | .min => selMin_eq
  | .max => fun b v => select_mask b v

/-- the `Iter` chain: `filter keep → map f → min?` (or `max?`) -/
def Pipe.red (r : Red) (q : Pipe) (k : UInt64) (xs : Array UInt64) : Option UInt64 :=
  match r with
  | .min => (xs.iter.filter (fun x => q.keep.eval k x) |>.map (fun x => q.f.eval k x)).min?
  | .max => (xs.iter.filter (fun x => q.keep.eval k x) |>.map (fun x => q.f.eval k x)).max?

/-- what the printed C++ computes: `seen |= keep`, item `j` folded into lane `j % lanes` with `op`, lanes
folded together -/
def Pipe.redRun (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) : Option UInt64 :=
  let acc := (xs.toList.map fun x => (⟨r.mask (q.keep.eval k x) (q.f.eval k x)⟩ : OpW r.op r.id)).foldl rot
    (List.replicate lanes 0)
  if xs.toList.foldl (fun s x => s || q.keep.eval k x) false then some (sumL acc).v else none

theorem foldl_or {σ : Type} (p : σ → Bool) : ∀ (l : List σ) (s : Bool),
    l.foldl (fun s x => s || p x) s = (s || l.any p)
  | [], s => by simp
  | x :: xs, s => by rw [List.foldl_cons, foldl_or p xs, List.any_cons, Bool.or_assoc]

theorem any_filter {σ : Type} (p : σ → Bool) (g : σ → UInt64) : ∀ l : List σ,
    l.any p = !((l.filter p).map g).isEmpty
  | [] => rfl
  | x :: xs => by
    by_cases hp : p x = true
    · simp [List.filter_cons, hp]
    · simp only [List.any_cons, hp, List.filter_cons, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      exact any_filter p g xs

theorem foldl_opW {o : UInt64 → UInt64 → UInt64} {e : UInt64} : ∀ (l : List UInt64) (a : UInt64),
    (l.map (OpW.mk (o := o) (e := e))).foldl (· + ·) ⟨a⟩ = ⟨l.foldl o a⟩
  | [], _ => rfl
  | x :: xs, a => foldl_opW xs (o a x)

/-- `min?`/`max?` written with the operation: `none` for no items, else a fold from the first -/
def optOf (o : UInt64 → UInt64 → UInt64) : List UInt64 → Option UInt64
  | [] => none
  | x :: xs => some (xs.foldl o x)

/-- the lane loop equals `min?` / `max?` of the chain, for every pipeline, lane count and input -/
theorem red_correct (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    q.redRun r lanes k xs = q.red r k xs := by
  let p := fun x => q.keep.eval k x
  let g := fun x => q.f.eval k x
  have hm : (fun x => (⟨r.mask (p x) (g x)⟩ : OpW r.op r.id)) = fun x => if p x then ⟨g x⟩ else 0 :=
    funext fun x => by rw [r.mask_eq]; cases p x <;> rfl
  have hl : ((xs.toList.filter p).map g).min? = optOf min ((xs.toList.filter p).map g) ∧
      ((xs.toList.filter p).map g).max? = optOf max ((xs.toList.filter p).map g) := by
    constructor <;> cases (xs.toList.filter p).map g <;> rfl
  have hr : q.red r k xs = optOf r.op ((xs.toList.filter p).map g) := by
    cases r
    · exact (((denotes_array xs).filter p).map g).min?.trans hl.1
    · exact (((denotes_array xs).filter p).map g).max?.trans hl.2
  rw [hr, Pipe.redRun]
  show (if xs.toList.foldl (fun s x => s || p x) false then
    some (sumL ((xs.toList.map fun x => (⟨r.mask (p x) (g x)⟩ : OpW r.op r.id)).foldl rot
      (List.replicate lanes 0))).v else none) = _
  rw [foldl_or, Bool.false_or, any_filter p g, sum_lanes r.laws, hm, ← sum_select r.laws,
    show (xs.toList.filter p).map (fun x => (⟨g x⟩ : OpW r.op r.id)) = ((xs.toList.filter p).map g).map OpW.mk
      by rw [List.map_map]; rfl]
  generalize (xs.toList.filter p).map g = L
  cases L with
  | nil => rfl
  | cons x rest =>
    simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte, sumL, optOf]
    rw [show (0 : OpW r.op r.id) = ⟨r.id⟩ from rfl, foldl_opW, List.foldl_cons,
      show r.op r.id x = x from congrArg OpW.v (r.laws.zero_add ⟨x⟩)]

/-- prints `Pipe.redRun r lanes q`, with `b` the kept flag as a word; 0 lanes is printed as 1. Its loops are
modelled line for line by `Pipe.cRed` in `Iter/CLoop.lean` (`cRed_eq`). -/
def Pipe.toCppRed (r : Red) (lanes : Nat) (q : Pipe) (name : String) : String :=
  let n := max lanes 1
  let (op, id, body) := match r with
    | .min => ("std::min<std::uint64_t>", "~0ULL", (C.minC q.f.toC (.var .b)).print wordNm)
    | .max => ("std::max<std::uint64_t>", "0ULL", (C.maskC q.f.toC (.var .b)).print wordNm)
  String.intercalate "\n" ([header "std::optional<std::uint64_t>" name, "  (void)k;",
    s!"  std::uint64_t acc[{n}], seen = 0;", s!"  for (std::uint64_t& a : acc) a = {id};"] ++
    laneLoop n (fun lane => s!"std::uint64_t b = {(C.CE.cast q.keep.toC).print wordNm}; seen |= b; acc[{lane}] = {op}(acc[{lane}], {body});") ++ [
    s!"  std::uint64_t m = {id};",
    s!"  for (std::uint64_t a : acc) m = {op}(m, a);",
    "  if (seen) return m;",
    "  return std::nullopt;",
    "}"])

/-- the benchmark's `filter → map → max?` and `filter → count`, as generated -/
theorem wordPipe_max (k : UInt64) (xs : Array UInt64) :
    wordPipe.redRun .max 4 k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2)).max? :=
  red_correct .max 4 wordPipe k xs

theorem wordPipe_count (k : UInt64) (xs : Array UInt64) :
    (opt 8 wordPipe.countPipe).run k xs = (xs.iter.filter (fun x => (x ^^^ k) % 3 == 0)).count.toUInt64 :=
  count_correct 8 wordPipe k xs

/-! ### Divide-free divisibility test

For `1 < d` with `d * c = 1` (mod 2^64), `y % d == 0` iff `y * c < (2^64 - 1) / d + 1`. There is no
64-bit vector divide, so this rewrite lets a compiler vectorise a `% d == 0` filter. -/

theorem mod_zero_iff_mul (y d c M : Nat) (hy : y < M) (hc : d * c % M = 1) :
    y % d = 0 ↔ y * c % M ≤ (M - 1) / d := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; rw [Nat.zero_mul, Nat.zero_mod] at hc; exact absurd hc (by decide)
    · exact h
  have hM : 1 < M := by
    rcases Nat.lt_or_ge 1 M with h | h
    · exact h
    · have : d * c % M < M := Nat.mod_lt _ (by omega)
      omega
  have back : ∀ t, (d * t) % M = (d * (t % M)) % M := fun t => by rw [Nat.mul_mod, Nat.mul_mod d (t % M), Nat.mod_mod]
  constructor
  · intro h
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have hq : d * q * c % M = q % M := by
      rw [Nat.mul_assoc, Nat.mul_comm q c, ← Nat.mul_assoc, Nat.mul_mod, hc, Nat.one_mul, Nat.mod_mod]
    have hqM : q < M := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left q hd) hy
    rw [hq, Nat.mod_eq_of_lt hqM, Nat.le_div_iff_mul_le hd, Nat.mul_comm]
    omega
  · intro h
    have h1 : y * c % M * d ≤ M - 1 := (Nat.le_div_iff_mul_le hd).1 h
    have h2 : d * (y * c % M) % M = y := by
      rw [← back, ← Nat.mul_assoc, Nat.mul_comm d y, Nat.mul_assoc, Nat.mul_mod, hc, Nat.mul_one,
        Nat.mod_mod, Nat.mod_eq_of_lt hy]
    rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; omega)] at h2
    rw [← h2, Nat.mul_mod_right]

theorem nodiv_ok (y d c : UInt64) (hd : 1 < d) (hc : d * c = 1) :
    (y % d == 0) = decide (y * c < 0xFFFFFFFFFFFFFFFF / d + 1) := by
  have hdN : 1 < d.toNat := UInt64.lt_iff_toNat_lt.1 hd
  have hcN : d.toNat * c.toNat % 2 ^ 64 = 1 := by rw [← UInt64.toNat_mul, hc]; rfl
  have key := mod_zero_iff_mul y.toNat d.toNat c.toNat (2 ^ 64) y.toNat_lt_size hcN
  have hlt : (2 ^ 64 - 1) / d.toNat < 2 ^ 64 - 1 := Nat.div_lt_self (by decide) hdN
  have h1 : (y % d == 0) = true ↔ y.toNat % d.toNat = 0 := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]; rfl
  have h2 : decide (y * c < 0xFFFFFFFFFFFFFFFF / d + 1) = true ↔
      y.toNat * c.toNat % 2 ^ 64 ≤ (2 ^ 64 - 1) / d.toNat := by
    rw [decide_eq_true_iff, UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_div]
    show _ < ((2 ^ 64 - 1) / d.toNat + 1) % 2 ^ 64 ↔ _
    rw [Nat.mod_eq_of_lt (a := (2 ^ 64 - 1) / d.toNat + 1) (by omega)]
    exact Nat.lt_succ_iff
  rw [Bool.eq_iff_iff, h1, h2]
  exact key

/-- the inverse of odd `d` mod 2^64: Newton steps, each doubling the correct low bits -/
def inv64 (d : UInt64) : UInt64 :=
  let step := fun (y : UInt64) => y * (2 - d * y)
  step (step (step (step (step d))))

/-- `a % d == z` with `z = 0` and odd `d > 1` becomes `a * inverse(d) < (2^64 - 1) / d + 1` -/
def nodivEq (a b : E) : P :=
  match a, b with
  | .mod a (.lit d), .lit z =>
    if z = 0 ∧ 1 < d ∧ d * inv64 d = 1 then .lt (.mul a (.lit (inv64 d))) (.lit (0xFFFFFFFFFFFFFFFF / d + 1))
    else .eq (.mod a (.lit d)) (.lit z)
  | a, b => .eq a b

def P.nodiv : P → P
  | .eq a b => nodivEq a b
  | .lt a b => .lt a b
  | .and p q => .and p.nodiv q.nodiv

theorem nodivEq_eval (k x : UInt64) (a b : E) : (nodivEq a b).eval k x = (P.eq a b).eval k x := by
  unfold nodivEq
  split
  · split
    · rename_i h
      obtain ⟨rfl, hd, hc⟩ := h
      simp only [P.eval, E.eval]
      exact (nodiv_ok _ _ _ hd hc).symm
    · rfl
  · rfl

theorem P.nodiv_eval (k x : UInt64) : ∀ p : P, p.nodiv.eval k x = p.eval k x
  | .eq a b => nodivEq_eval k x a b
  | .lt _ _ => rfl
  | .and p q => by simp only [P.nodiv, P.eval, P.nodiv_eval k x p, P.nodiv_eval k x q]

def Pipe.nodiv (q : Pipe) : Pipe := ⟨q.keep.nodiv, q.f⟩

theorem nodiv_run (q : Pipe) (k : UInt64) (xs : Array UInt64) : q.nodiv.run k xs = q.run k xs := by
  simp only [Pipe.run, Pipe.nodiv, P.nodiv_eval]

theorem nodiv_red (r : Red) (q : Pipe) (k : UInt64) (xs : Array UInt64) : q.nodiv.red r k xs = q.red r k xs := by
  cases r <;> simp only [Pipe.red, Pipe.nodiv, P.nodiv_eval]

theorem nodiv_count (q : Pipe) (k : UInt64) (xs : Array UInt64) : q.nodiv.count k xs = q.count k xs := by
  simp only [Pipe.count, Pipe.nodiv, P.nodiv_eval]

/-- the divide-free candidates, as generated -/
theorem wordPipe_nodiv (lanes : Nat) (k : UInt64) (xs : Array UInt64) :
    (opt lanes wordPipe.nodiv).run k xs = wordPipe.run k xs := by
  rw [opt_correct, nodiv_run]

theorem wordPipe_nodiv_count (lanes : Nat) (k : UInt64) (xs : Array UInt64) :
    (opt lanes wordPipe.nodiv.countPipe).run k xs = (wordPipe.count k xs).toUInt64 := by
  rw [count_correct, nodiv_count]

theorem wordPipe_nodiv_max (lanes : Nat) (k : UInt64) (xs : Array UInt64) :
    wordPipe.nodiv.redRun .max lanes k xs = wordPipe.red .max k xs := by
  rw [red_correct, nodiv_red]

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

/-! ### search for the first kept row, then one pass

`fast2` skips the dropped prefix with an ordinary search, takes the first kept row as `first`, and runs the
one-pass loop over the rest without tracking `first` (`step2`). -/

def SPipe.step2 (q : SPipe) (ps : List UInt64) (s : Summary (Row ν) UInt64) (r : Row ν) :
    Summary (Row ν) UInt64 :=
  let k := q.keep.eval ps r.f
  ⟨s.count + (if k then 1 else 0), s.total + sel k (q.pay.eval ps r.f), s.first, if k then some r else s.last⟩

def SPipe.fast2 (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) : Summary ν UInt64 :=
  match rows.toList.dropWhile (fun r => !q.keep.eval ps r.f) with
  | [] => ⟨0, 0, none, none⟩
  | r :: rest =>
    let s := rest.foldl (q.step2 ps) ⟨1, q.pay.eval ps r.f, some r, some r⟩
    ⟨s.count, s.total, s.first.map (·.label), s.last.map (·.label)⟩

theorem step1_drop (q : SPipe) (ps : List UInt64) (s : Summary (Row ν) UInt64) (r : Row ν)
    (h : q.keep.eval ps r.f = false) : q.step1 ps s r = s := by
  have h0 : ∀ v, sel false v = 0 := fun v => by rw [sel, select_mask]; rfl
  cases s; simp [SPipe.step1, h, h0, add_zero u64Laws]

/-- dropped rows before the first kept one change nothing -/
theorem step1_dropWhile (q : SPipe) (ps : List UInt64) : ∀ (l : List (Row ν)) (s : Summary (Row ν) UInt64),
    l.foldl (q.step1 ps) s = (l.dropWhile fun r => !q.keep.eval ps r.f).foldl (q.step1 ps) s
  | [], _ => rfl
  | r :: rs, s => by
    cases hk : q.keep.eval ps r.f
    · simp only [List.foldl_cons, List.dropWhile_cons, hk, Bool.not_false, ↓reduceIte, step1_drop q ps s r hk]
      exact step1_dropWhile q ps rs s
    · simp [List.dropWhile_cons, hk]

/-- once `first` is set, `step1` is `step2` -/
theorem step1_step2 (q : SPipe) (ps : List UInt64) (f : Row ν) : ∀ (l : List (Row ν)) (s : Summary (Row ν) UInt64),
    s.first = some f → l.foldl (q.step1 ps) s = l.foldl (q.step2 ps) s
  | [], _, _ => rfl
  | r :: rs, s, h => by
    have e : q.step1 ps s r = q.step2 ps s r := by
      cases s; simp only at h; subst h; simp [SPipe.step1, SPipe.step2]
    rw [List.foldl_cons, List.foldl_cons, e]
    exact step1_step2 q ps f rs _ (by simp [SPipe.step2, h])

theorem dropWhile_head {α : Type} {p : α → Bool} :
    ∀ {l : List α} {r : α} {rest : List α}, l.dropWhile p = r :: rest → p r = false
  | [], _, _, h => by simp at h
  | x :: xs, r, rest, h => by
    by_cases hx : p x
    · simp only [List.dropWhile_cons, hx, ↓reduceIte] at h; exact dropWhile_head h
    · simp only [List.dropWhile_cons, hx, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h; simpa using hx

theorem fast2_correct (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast2 ps rows = q.run ps rows := by
  rw [← fast1_correct, SPipe.fast1, step1_dropWhile, SPipe.fast2]
  have h1 : ∀ v, sel true v = v := fun v => by rw [sel, select_mask]; rfl
  generalize hd : rows.toList.dropWhile (fun r => !q.keep.eval ps r.f) = d
  cases d with
  | nil => rfl
  | cons r rest =>
    have hk : q.keep.eval ps r.f = true := by simpa using dropWhile_head hd
    simp only [List.foldl_cons]
    rw [step1_step2 q ps r rest _ (by simp [SPipe.step1, hk])]
    simp [SPipe.step1, hk, h1, u64Laws.zero_add]

/-! ### switching between masked and branchy blocks

`fast3 mode` is `fast2` with each row after the first kept one handled by either the masked body
(`step2`) or the branchy body (`stepB`): row `i` uses the masked one when `mode i`. The printed loop picks
the body per block from the data; whatever it picks is some `mode`, so `fast3_correct` covers it. -/

def SPipe.stepB (q : SPipe) (ps : List UInt64) (s : Summary (Row ν) UInt64) (r : Row ν) :
    Summary (Row ν) UInt64 :=
  if q.keep.eval ps r.f then ⟨s.count + 1, s.total + q.pay.eval ps r.f, s.first, some r⟩ else s

theorem stepB_step2 (q : SPipe) (ps : List UInt64) : q.stepB ps = (q.step2 ps : Summary (Row ν) UInt64 → _) := by
  have h0 : ∀ v, sel false v = 0 := fun v => by rw [sel, select_mask]; rfl
  have h1 : ∀ v, sel true v = v := fun v => by rw [sel, select_mask]; rfl
  funext s r
  cases hk : q.keep.eval ps r.f <;> cases s <;> simp [SPipe.stepB, SPipe.step2, hk, h0, h1, add_zero u64Laws]

/-- a fold that picks its step per position from `mode` equals the plain fold when every choice is `f` -/
theorem foldl_mix {α β : Type} (f : β → α → β) (g : Bool → β → α → β) (hg : ∀ b, g b = f)
    (mode : Nat → Bool) : ∀ (l : List α) (s : β) (i : Nat),
    (l.foldl (fun (p : β × Nat) x => (g (mode p.2) p.1 x, p.2 + 1)) (s, i)).1 = l.foldl f s
  | [], _, _ => rfl
  | x :: xs, s, i => by rw [List.foldl_cons, List.foldl_cons, foldl_mix f g hg mode xs, hg]

def SPipe.fast3 (mode : Nat → Bool) (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) : Summary ν UInt64 :=
  match rows.toList.dropWhile (fun r => !q.keep.eval ps r.f) with
  | [] => ⟨0, 0, none, none⟩
  | r :: rest =>
    let s := (rest.foldl (fun (p : Summary (Row ν) UInt64 × Nat) x =>
      ((if mode p.2 then q.step2 ps else q.stepB ps) p.1 x, p.2 + 1)) (⟨1, q.pay.eval ps r.f, some r, some r⟩, 0)).1
    ⟨s.count, s.total, s.first.map (·.label), s.last.map (·.label)⟩

/-- every choice of masked or branchy body per row computes the running summary -/
theorem fast3_correct (mode : Nat → Bool) (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast3 mode ps rows = q.run ps rows := by
  rw [← fast2_correct, SPipe.fast3, SPipe.fast2]
  generalize rows.toList.dropWhile (fun r => !q.keep.eval ps r.f) = d
  cases d with
  | nil => rfl
  | cons r rest =>
    simp only
    rw [foldl_mix (q.step2 ps) (fun b => if b then q.step2 ps else q.stepB ps)
      (fun b => by cases b <;> simp [stepB_step2]) mode rest]

/-! ### printer (trusted) -/

open Iter.C in
def X.toC : X → CE
  | .fld i => .var (.fld i)
  | .prm i => .var (.prm i)
  | .lit n => .lit n
  | .add a b => .bin .add a.toC b.toC
  | .mul a b => .bin .mul a.toC b.toC
  | .div a (.lit n) => if n = 0 then .lit 0 else .bin .div a.toC (.lit n)
  | .div a b => .cond (.bin .eq b.toC (.lit 0)) (.lit 0) (.bin .div a.toC b.toC)

open Iter.C in
def Q.toC : Q → CE
  | .ne0 a => .bin .ne a.toC (.lit 0)
  | .ge a b => .bin .ge a.toC b.toC
  | .and p q => .bin .band p.toC q.toC

open Iter.C in
/-- `fields[i]` / `params[i]` are the C++ for field / parameter `i`; a missing one is `0`, as in `X.eval` -/
def recNm (fields params : List String) : Slot → String
  | .fld i => fields.getD i "0ULL" | .prm i => params.getD i "0ULL" | .b => "kb" | _ => "0ULL"

def X.toCpp (fields params : List String) (e : X) : String := e.toC.print (recNm fields params)
def Q.toCpp (fields params : List String) (q : Q) : String := q.toC.print (recNm fields params)

/-- C++ `name(rows, p0, p1, ...)` computing `SPipe.fast2`; `fields[i]` is the C++ expression for word field
`i` of row `e`, and the includer defines the row type with a `name` member and `Summ` with `count`, `total`,
`first`, `last`. Its two loops are modelled by `SPipe.cRun` in `Iter/CLoop.lean` (`cRunS_eq`). -/
def SPipe.toCpp (q : SPipe) (nParams : Nat) (name rowType : String) (fields : List String) : String :=
  let ps := (List.range nParams).map (s!"p{·}")
  let params := String.join (ps.map (s!", std::uint64_t {·}"))
  String.intercalate "\n" [
    s!"__attribute__((noinline)) static Summ {name}(const std::vector<{rowType}>& es{params}) \{",
    "  std::size_t i = 0, n = es.size();",
    s!"  for (; i < n; ++i) \{ const {rowType}& e = es[i]; if ({q.keep.toCpp fields ps}) break; }",
    "  Summ s;",
    "  if (i == n) return s;",
    s!"  const {rowType}* fp = &es[i];",
    s!"  const {rowType}* lp = fp;",
    "  std::uint64_t cnt = 1, tot;",
    s!"  \{ const {rowType}& e = *fp; tot = {q.pay.toCpp fields ps}; }",
    "  for (++i; i < n; ++i) {",
    s!"    const {rowType}& e = es[i];",
    s!"    std::uint64_t kb = {(C.CE.cast q.keep.toC).print (recNm fields ps)};",
    s!"    cnt += kb; tot += {(C.maskC q.pay.toC (.var .b)).print (recNm fields ps)};",
    "    lp = kb ? &e : lp;",
    "  }",
    "  s.count = cnt; s.total = tot; s.first = fp->name; s.last = lp->name;",
    "  return s;",
    "}"]

/-- C++ `name(rows, p0, ...)` computing `SPipe.fast3`: after the first kept row, blocks of `blk` rows, each
run masked or branchy. A masked block counts kept-run starts over its first `win` rows, a branchy block on its
kept rows; the next block is masked iff `starts * den > rows measured`. The choice changes speed only
(`fast3_correct` holds for every `mode`). `optimize("no-tree-loop-if-convert")` stops GCC -O3 turning the
branchy block back into selects. -/
def SPipe.toCppAdapt (q : SPipe) (nParams : Nat) (name rowType : String) (fields : List String)
    (blk win den : Nat) : String :=
  let ps := (List.range nParams).map (s!"p{·}")
  let params := String.join (ps.map (s!", std::uint64_t {·}"))
  let keep := q.keep.toCpp fields ps
  let pay := q.pay.toCpp fields ps
  let masked := s!"const {rowType}& e = es[i]; std::uint64_t k = {keep}; std::uint64_t m = 0 - k; "
  String.intercalate "\n" [
    s!"__attribute__((noinline, optimize(\"no-tree-loop-if-convert\"))) static Summ {name}(const std::vector<{rowType}>& es{params}) \{",
    "  std::size_t i = 0, n = es.size();",
    s!"  for (; i < n; ++i) \{ const {rowType}& e = es[i]; if ({keep}) break; }",
    "  Summ s;",
    "  if (i == n) return s;",
    s!"  const {rowType}* fp = &es[i];",
    s!"  const {rowType}* lp = fp;",
    "  std::uint64_t cnt = 1, tot;",
    s!"  \{ const {rowType}& e = *fp; tot = {pay}; }",
    "  bool masked = true;",
    "  for (++i; i < n;) {",
    s!"    std::size_t end = n - i > {max blk 1} ? i + {max blk 1} : n;",
    "    std::uint64_t starts = 0, w;",
    "    if (masked) {",
    s!"      std::size_t pe = end - i > {win} ? i + {win} : end;",
    "      w = pe - i;",
    "      std::uint64_t prev = lp + 1 == &es[i];",
    s!"      for (; i < pe; ++i) \{ {masked}starts += k & ~prev; prev = k; cnt += 1 & m; tot += {pay} & m; lp = k ? &e : lp; }",
    s!"      for (; i < end; ++i) \{ {masked}cnt += 1 & m; tot += {pay} & m; lp = k ? &e : lp; }",
    "    } else {",
    "      w = end - i;",
    s!"      for (; i < end; ++i) \{ const {rowType}& e = es[i]; if ({keep}) \{ starts += lp + 1 != &e; cnt += 1; tot += {pay}; lp = &e; } }",
    "    }",
    s!"    masked = starts * {den} > w;",
    "  }",
    "  s.count = cnt; s.total = tot; s.first = fp->name; s.last = lp->name;",
    "  return s;",
    "}"]

/-- the benchmark's record pipeline: keep `active != 0 & salary >= p0`, pay `salary * p1 / 100` -/
def recPipe : SPipe := ⟨.and (.ne0 (.fld 1)) (.ge (.fld 0) (.prm 0)), .div (.mul (.fld 0) (.prm 1)) (.lit 100)⟩

theorem recPipe_gen (ps : List UInt64) (rows : Array (Row ν)) : recPipe.fast2 ps rows = recPipe.run ps rows :=
  fast2_correct recPipe ps rows

theorem recPipe_adapt (mode : Nat → Bool) (ps : List UInt64) (rows : Array (Row ν)) :
    recPipe.fast3 mode ps rows = recPipe.run ps rows :=
  fast3_correct mode recPipe ps rows

end Iter.Gen
