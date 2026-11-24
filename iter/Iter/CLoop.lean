import Iter.Gen

/-! # The lane loop exactly as the printed C++ runs it

`Loop.run` (proved equal to the `Iter` chain by `opt_correct`) sends item `j` to lane `j % lanes` by
rotating a list. The printed C++ does something else: full rounds of `n` items with an inner `j` loop,
then a tail loop using `i % n`, then a sum over the lane array. `Loop.cRun` models that control flow one
C++ loop per Lean function, and `cRun_eq` proves it computes `Loop.run`. What stays trusted after this is
the 1:1 text of each line (`Loop.toCpp`), the per-constructor `E.toCpp`/`P.toCpp`, and GCC. -/

namespace Iter.Gen
open Iter Iter.Rewrite

/-- `acc[l] += v` -/
def bump : List UInt64 → Nat → UInt64 → List UInt64
  | [], _, _ => []
  | a :: as, 0, v => (a + v) :: as
  | a :: as, l + 1, v => a :: bump as l v

theorem bump_length : ∀ (acc : List UInt64) (l : Nat) (v : UInt64), (bump acc l v).length = acc.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, l + 1, v => by simp [bump, bump_length as l v]

theorem bump_sum : ∀ (acc : List UInt64) (l : Nat) (v : UInt64), l < acc.length →
    sumL (bump acc l v) = sumL acc + v
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: as, 0, v, _ => by
    rw [bump, sumL_cons u64Laws, sumL_cons u64Laws, u64Laws.assoc, u64Laws.assoc, u64Laws.comm v]
  | a :: as, l + 1, v, h => by
    rw [bump, sumL_cons u64Laws, sumL_cons u64Laws, bump_sum as l v (by simp at h; omega), u64Laws.assoc]

/-- `g` summed over indices `i, i+1, …, i+c-1` -/
def rs (g : Nat → UInt64) (i c : Nat) : UInt64 := sumL ((List.range' i c).map g)

theorem rs_zero (g : Nat → UInt64) (i : Nat) : rs g i 0 = 0 := rfl

theorem rs_succ (g : Nat → UInt64) (i c : Nat) : rs g i (c + 1) = g i + rs g (i + 1) c := by
  rw [rs, List.range'_succ, List.map_cons, sumL_cons u64Laws]; rfl

theorem rs_add (g : Nat → UInt64) : ∀ (a i b : Nat), rs g i (a + b) = rs g i a + rs g (i + a) b
  | 0, i, b => by rw [Nat.zero_add, rs_zero, u64Laws.zero_add, Nat.add_zero]
  | a + 1, i, b => by
    rw [Nat.add_right_comm, rs_succ, rs_succ, rs_add g a (i + 1) b, u64Laws.assoc,
      show i + 1 + a = i + (a + 1) by omega]

section
variable (n size : Nat) (g : Nat → UInt64)

/-- `for (std::size_t j = 0; j < n; ++j) acc[j] += g(i + j);` -/
def inner (i j : Nat) (acc : List UInt64) : List UInt64 :=
  if j < n then inner i (j + 1) (bump acc j (g (i + j))) else acc
termination_by n - j

/-- `for (; i < size; ++i) acc[i % n] += g(i);` -/
def tail (i : Nat) (acc : List UInt64) : List UInt64 :=
  if i < size then tail (i + 1) (bump acc (i % n) (g i)) else acc
termination_by size - i

/-- `for (; i + n <= size; i += n) { inner }` then `tail`; the printer only uses `n ≥ 1` -/
def rounds (i : Nat) (acc : List UInt64) : List UInt64 :=
  if _ : 0 < n ∧ i + n ≤ size then rounds (i + n) (inner n g i 0 acc) else tail n size g i acc
termination_by size - i
decreasing_by omega

theorem inner_spec (i : Nat) : ∀ (d j : Nat) (acc : List UInt64), n - j = d → acc.length = n →
    (inner n g i j acc).length = n ∧ sumL (inner n g i j acc) = sumL acc + rs g (i + j) (n - j)
  | 0, j, acc, hd, hl => by
    unfold inner; rw [if_neg (by omega), hd, rs_zero, add_zero u64Laws]; exact ⟨hl, rfl⟩
  | d + 1, j, acc, hd, hl => by
    unfold inner; rw [if_pos (by omega)]
    have ⟨h1, h2⟩ := inner_spec i d (j + 1) (bump acc j (g (i + j))) (by omega) (by rw [bump_length, hl])
    refine ⟨h1, ?_⟩
    rw [h2, bump_sum _ _ _ (by omega), show n - j = (n - (j + 1)) + 1 by omega, rs_succ, u64Laws.assoc,
      show i + j + 1 = i + (j + 1) by omega]

theorem tail_spec (hn : 0 < n) : ∀ (d i : Nat) (acc : List UInt64), size - i = d → acc.length = n →
    sumL (tail n size g i acc) = sumL acc + rs g i (size - i)
  | 0, i, acc, hd, _ => by unfold tail; rw [if_neg (by omega), hd, rs_zero, add_zero u64Laws]
  | d + 1, i, acc, hd, hl => by
    unfold tail; rw [if_pos (by omega)]
    rw [tail_spec hn d (i + 1) _ (by omega) (by rw [bump_length, hl]),
      bump_sum _ _ _ (by rw [hl]; exact Nat.mod_lt _ hn),
      show size - i = (size - (i + 1)) + 1 by omega, rs_succ, u64Laws.assoc]

theorem rounds_spec (hn : 0 < n) : ∀ (d i : Nat) (acc : List UInt64), size - i = d → acc.length = n →
    sumL (rounds n size g i acc) = sumL acc + rs g i (size - i) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro i acc hd hl
    unfold rounds
    by_cases h : 0 < n ∧ i + n ≤ size
    · rw [dif_pos h]
      have ⟨h1, h2⟩ := inner_spec n g i (n - 0) 0 acc rfl hl
      rw [ih (size - (i + n)) (by omega) (i + n) _ rfl h1, h2, Nat.sub_zero, Nat.add_zero, u64Laws.assoc,
        ← rs_add, show n + (size - (i + n)) = size - i by omega]
    · rw [dif_neg h]; exact tail_spec n size g hn _ i acc rfl hl
end

/-- what the printed `Loop.toCpp` function computes, loop by loop: `n = max lanes 1` lanes, item value
`body & (0 - keep)` read as `x = xs[t]`, then `total = Σ acc`, then `total * scale` -/
def Loop.cRun (L : Loop) (k : UInt64) (xs : Array UInt64) : UInt64 :=
  let n := max L.lanes 1
  let g := fun t => let x := xs.getD t 0; sel (L.keep.eval k x) (L.body.eval k x)
  sumL (rounds n xs.size g 0 (List.replicate n 0)) * L.scale.eval k 0

theorem range_getD_map (f : UInt64 → UInt64) (xs : Array UInt64) :
    (List.range' 0 xs.size).map (fun t => f (xs.getD t 0)) = xs.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp at h1
    simp [List.getElem_range', Array.getD, h1]

/-- the C++ loop structure computes the proved loop -/
theorem cRun_eq (L : Loop) (k : UInt64) (xs : Array UInt64) : L.cRun k xs = L.run k xs := by
  rw [Loop.cRun, Loop.run, sum_lanes u64Laws]
  simp only
  rw [rounds_spec _ _ _ (by omega) _ 0 _ rfl (by simp), sumL_zeros u64Laws, u64Laws.zero_add, rs,
    Nat.sub_zero, range_getD_map (fun x => sel (L.keep.eval k x) (L.body.eval k x))]

/-- the printed loop structure computes the `Iter` chain, for every pipeline, lane count and input -/
theorem printed_correct (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q).cRun k xs = q.run k xs :=
  (cRun_eq _ k xs).trans (opt_correct lanes q k xs)

/-- the same for the generated `count` -/
theorem printed_count (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q.countPipe).cRun k xs = (q.count k xs).toUInt64 :=
  (cRun_eq _ k xs).trans (count_correct lanes q k xs)

end Iter.Gen
