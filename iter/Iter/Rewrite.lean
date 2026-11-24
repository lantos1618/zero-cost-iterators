import Iter.Basic
/-!
# Proved loop rewrites, for use outside Lean

Rewrites a compiler may not make on its own, each proved equal to the plain chain, so the faster loop can be
written in C++ (see `bench.cpp`, `proved*`) with the same meaning:

* `sum_select`: a filtered sum is a sum of selects (`p x ? f x : 0`), so the loop body has no branch;
  `select_mask` turns the select into a bit mask, which GCC keeps branch-free;
* `sum_lanes`: with `+` associative and commutative with `0`, item `j` may go to accumulator `j % k`, for any
  `k`, and the lanes are added at the end; independent lanes remove the loop-carried dependency;
* `summary_split`: a running summary (count, total, first, last) splits into a count, a sum, a forward
  search and a backward search, each of which can run on its own;
* `chain_lanes`: the `Iter` chain `filter → map → foldl (+)` equals the select + lanes loop.
Holds for `UInt64` (wrapping, like C++ `uint64_t`) and `Nat`.
-/
namespace Iter.Rewrite

/-- what a lane split needs from `+` -/
structure AddLaws (α : Type) [Add α] [OfNat α 0] : Prop where
  assoc : ∀ a b c : α, a + b + c = a + (b + c)
  comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, 0 + a = a

theorem natLaws : AddLaws Nat := ⟨Nat.add_assoc, Nat.add_comm, Nat.zero_add⟩

theorem u64Laws : AddLaws UInt64 :=
  ⟨fun _ _ _ => UInt64.toBitVec_inj.1 (BitVec.add_assoc _ _ _),
   fun _ _ => UInt64.toBitVec_inj.1 (BitVec.add_comm _ _),
   fun _ => UInt64.toBitVec_inj.1 (BitVec.zero_add _)⟩

variable {α ν : Type} [Add α] [OfNat α 0]

def sumL (l : List α) : α := l.foldl (· + ·) 0

theorem foldl_add (h : AddLaws α) : ∀ (l : List α) (a : α), l.foldl (· + ·) a = a + sumL l
  | [], a => by rw [sumL, List.foldl_nil, List.foldl_nil, h.comm, h.zero_add]
  | x :: xs, a => by
    simp only [sumL, List.foldl_cons]
    rw [foldl_add h xs, foldl_add h xs (0 + x), h.zero_add, h.assoc]

theorem sumL_cons (h : AddLaws α) (x : α) (l : List α) : sumL (x :: l) = x + sumL l := by
  rw [sumL, List.foldl_cons, h.zero_add, foldl_add h]

theorem add_zero (h : AddLaws α) (a : α) : a + 0 = a := by rw [h.comm, h.zero_add]

/-! ## Branch-free select -/

theorem sum_select {σ : Type} (h : AddLaws α) (p : σ → Bool) (f : σ → α) :
    ∀ l : List σ, sumL ((l.filter p).map f) = sumL (l.map fun x => if p x then f x else 0)
  | [] => rfl
  | x :: xs => by
    by_cases hp : p x = true
    · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, sumL_cons h, sum_select h p f xs]
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, sumL_cons h,
        h.zero_add, sum_select h p f xs]

/-- the select as a bit mask, as `bench.cpp` writes it: `v & -(b ? 1 : 0)` is `b ? v : 0` on 64-bit words -/
theorem select_mask (b : Bool) (v : UInt64) : (v &&& (0 - if b then 1 else 0)) = if b then v else 0 := by
  cases b
  · exact UInt64.toBitVec_inj.1 (by
      show v.toBitVec &&& (0 - 0 : UInt64).toBitVec = 0#64
      rw [show (0 - 0 : UInt64).toBitVec = 0#64 by decide]; exact BitVec.and_zero)
  · exact UInt64.toBitVec_inj.1 (by
      show v.toBitVec &&& (0 - 1 : UInt64).toBitVec = v.toBitVec
      rw [show (0 - 1 : UInt64).toBitVec = BitVec.allOnes 64 by decide]; exact BitVec.and_allOnes)

/-! ## Independent accumulators -/

/-- add `x` to the first lane, then move that lane to the back: item `j` lands in lane `j % k` -/
def rot : List α → α → List α
  | [], x => [x]
  | a :: as, x => as ++ [a + x]

theorem sumL_append (h : AddLaws α) (l r : List α) : sumL (l ++ r) = sumL l + sumL r := by
  rw [sumL, List.foldl_append, foldl_add h]; rfl

theorem sumL_rot (h : AddLaws α) : ∀ (accs : List α) (x : α), sumL (rot accs x) = sumL accs + x
  | [], _ => rfl
  | a :: as, x => by
    rw [rot, sumL_append h, sumL_cons h, sumL_cons h, show sumL ([] : List α) = 0 from rfl, add_zero h,
      ← h.assoc, h.comm (sumL as) a]

theorem sum_lanes_from (h : AddLaws α) : ∀ (xs accs : List α), sumL (xs.foldl rot accs) = sumL accs + sumL xs
  | [], accs => by rw [List.foldl_nil, show sumL ([] : List α) = 0 from rfl, add_zero h]
  | x :: xs, accs => by
    rw [List.foldl_cons, sum_lanes_from h xs, sumL_rot h, sumL_cons h, h.assoc]

theorem sumL_zeros (h : AddLaws α) : ∀ k : Nat, sumL (List.replicate k (0 : α)) = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, sumL_cons h, sumL_zeros h k, h.zero_add]

/-- `k` accumulators, any `k` -/
theorem sum_lanes (h : AddLaws α) (k : Nat) (xs : List α) :
    sumL (xs.foldl rot (List.replicate k 0)) = sumL xs := by
  rw [sum_lanes_from h, sumL_zeros h, h.zero_add]

/-- the `Iter` chain equals the branch-free `k`-lane loop -/
theorem chain_lanes {σ : Type} (h : AddLaws α) (xs : Array σ) (p : σ → Bool) (f : σ → α) (k : Nat) :
    (xs.iter.filter p |>.map f).foldl 0 (· + ·)
      = sumL ((xs.toList.map fun x => if p x then f x else 0).foldl rot (List.replicate k 0)) := by
  rw [(((denotes_array xs).filter p).map f).foldl, sum_lanes h, ← sum_select h]; rfl

/-! ## Splitting a running summary -/

structure Summary (ν α : Type) where
  count : Nat
  total : α
  first : Option ν
  last : Option ν

/-- the step a hand loop would write -/
def step (s : Summary ν α) (r : ν × α) : Summary ν α :=
  ⟨s.count + 1, s.total + r.2, s.first.or (some r.1), some r.1⟩

theorem fold_step (h : AddLaws α) : ∀ (rows : List (ν × α)) (s : Summary ν α),
    rows.foldl step s = ⟨s.count + rows.length, s.total + sumL (rows.map Prod.snd),
      s.first.or (rows.head?.map Prod.fst), (rows.getLast?.map Prod.fst).or s.last⟩
  | [], s => by cases s; simp [sumL, add_zero h]
  | r :: rest, s => by
    rw [List.foldl_cons, fold_step h rest]
    simp only [step, List.length_cons, List.map_cons, sumL_cons h, List.head?_cons, Option.map_some']
    congr 1
    · omega
    · rw [h.assoc]
    · cases s.first <;> rfl
    · cases rest with
      | nil => rfl
      | cons y ys =>
        obtain ⟨z, hz⟩ : ∃ z, (y :: ys).getLast? = some z :=
          ⟨_, List.getLast?_eq_getLast _ (List.cons_ne_nil _ _)⟩
        rw [List.getLast?_cons_cons, hz]; rfl

/-- the summary is a count, a sum, the first row and the last row, each computable on its own -/
theorem summary_split (h : AddLaws α) (rows : List (ν × α)) :
    rows.foldl step ⟨0, 0, none, none⟩ =
      ⟨rows.length, sumL (rows.map Prod.snd), rows.head?.map Prod.fst, rows.getLast?.map Prod.fst⟩ := by
  rw [fold_step h]; simp [h.zero_add]

/-- the first kept row is a forward search -/
theorem head_filter {σ : Type} (p : σ → Bool) : ∀ l : List σ, (l.filter p).head? = l.find? p
  | [] => rfl
  | x :: xs => by cases hp : p x <;> simp [List.filter_cons, List.find?_cons, hp, head_filter p xs]

/-- the last kept row is a backward search -/
theorem getLast_filter {σ : Type} (p : σ → Bool) : ∀ l : List σ, (l.filter p).getLast? = l.reverse.find? p
  | [] => rfl
  | x :: xs => by
    rw [List.reverse_cons, List.find?_append, ← getLast_filter p xs]
    cases hp : p x
    · simp [List.filter_cons, hp, List.find?_cons]
    · rw [List.filter_cons, hp, if_pos rfl, show x :: xs.filter p = [x] ++ xs.filter p from rfl, List.getLast?_append]
      simp [List.find?_cons, hp]

end Iter.Rewrite
