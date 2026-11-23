import Vw.Controls
import Pipe.Chains
/-! APL array operations as small independent reference models behind `.view()`.
APL reduction `f/` folds RIGHT to left; aligned extents are checked (LENGTH ERROR), never truncated. -/
namespace Apl
open Vw

/-- `+/` : right fold with identity 0 -/
def plusRed (xs : List Int) : Int := xs.foldr (· + ·) 0
/-- `f/` for a general f on a nonempty vector: x1 f (x2 f (... f xn)) -/
def redR (f : Int → Int → Int) : List Int → Option Int
  | [] => none
  | [x] => some x
  | x :: xs => (redR f xs).map (f x)
/-- `M/Y` Boolean compress, aligned extents -/
def compress {α} (m : List Bool) (y : List α) : Except String (List α) :=
  if m.length = y.length then .ok ((m.zip y).filterMap fun q => if q.1 then some q.2 else none) else .error "LENGTH ERROR"
/-- `+\` : item i is `+/` of the first i+1 items (quadratic definition) -/
def scanPlus (xs : List Int) : List Int := (List.range xs.length).map fun i => plusRed (xs.take (i + 1))
/-- `∧/ p¨ X` -/
def andRed {α} (p : α → Bool) (xs : List α) : Bool := xs.foldr (fun x acc => p x && acc) true
/-- `A × B` elementwise, aligned extents -/
def times : List Int → List Int → List Int
  | a :: as, b :: bs => a * b :: times as bs
  | _, _ => []
/-- vector inner product `A +.× B` = `+/ A × B` -/
def ipVec (a b : List Int) : Except String Int :=
  if a.length = b.length then .ok (plusRed (times a b)) else .error "LENGTH ERROR"
/-- matrix inner product shape rule: contract the LEFT LAST axis with the RIGHT FIRST axis (model only) -/
def ipShape (sa sb : List Nat) : Except String (List Nat) :=
  match sa.getLast?, sb.head? with
  | some n, some m => if n = m then .ok (sa.dropLast ++ sb.tail) else .error "LENGTH ERROR"
  | _, _ => .ok (sa.dropLast ++ sb.drop 1)

/-- exact-extent zip view: refuses instead of truncating -/
def viewZip {α β} (a : List α) (b : List β) : Except String (View (α × β)) :=
  if a.length = b.length then .ok (List.zip a b).view else .error "LENGTH ERROR"

theorem plusRed_eq (xs : List Int) : plusRed xs = xs.foldl (· + ·) 0 := (foldl_eq_foldr intAdd xs).symm

theorem filter_map_eq {α} : ∀ l : List (Bool × α),
    (l.filter (·.1)).map (·.2) = l.filterMap fun q => if q.1 then some q.2 else none
  | [] => rfl
  | (b, x) :: l => by cases b <;> simp [List.filter_cons, filter_map_eq l]

theorem compress_sum (m : List Bool) (y : List Int) :
    ((viewZip m y).bind fun v => (v.filter (·.1) |>.map (·.2) |>.fuse).accumulate 0) = (compress m y).map plusRed := by
  unfold viewZip compress; split
  · simp only [Except.bind, Except.map]
    rw [View.accumulate_ok _ _ (by simp [View.fuse, View.map, View.filter, View.st, List.view])]
    simp only [den, List.view, View.map, View.filter, View.st, View.fuse, Vw.map, Vw.filter, Int.zero_add]
    rw [filter_map_eq, plusRed_eq]
  · rfl

theorem scan_plus (xs : List Int) : (xs.view.scan 0 (· + ·) |>.fuse).items = scanPlus xs := by
  rw [View.items_eq]; simp only [den, List.view, View.scan, View.st, View.fuse, Vw.scan, prefixFolds, scanPlus]
  apply List.map_congr_left; intro i _; rw [plusRed_eq]

theorem and_all {α} (p : α → Bool) (xs : List α) : (xs.view.fuse).all p = .ok (andRed p xs) := by
  rw [View.all_ok _ _ rfl]; simp only [den, List.view, View.fuse]
  congr 1; induction xs <;> simp_all [andRed]

theorem times_eq : ∀ a b : List Int, times a b = (List.zip a b).map fun q => q.1 * q.2
  | a :: as, b :: bs => by simp [times, times_eq as bs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem ip_view (a b : List Int) :
    ((viewZip a b).bind fun v => (v.map (fun q => q.1 * q.2) |>.fuse).accumulate 0) = ipVec a b := by
  unfold viewZip ipVec; split
  · simp only [Except.bind]
    rw [View.accumulate_ok _ _ (by simp [View.fuse, View.map, View.st, List.view])]
    simp only [den, List.view, View.map, View.st, View.fuse, Vw.map]
    rw [plusRed_eq, times_eq]
  · rfl

/-- the dot-product connection: APL `A +.× B` equals the existing fluent `dot` chain's meaning and
the one-loop IR result (`Pipe.fusion`), on every aligned pair of integer vectors -/
theorem ip_dot (a b : List Int) (r : Int) (h : ipVec a b = .ok r) :
    r = Chains.dot.den a b ∧ r = (IR.run (Pipe.lower Chains.dot) a b).acc := by
  unfold ipVec at h; split at h
  · cases h; rw [Pipe.fusion]
    simp [Pipe.Reduced.den, Pipe.Elems.den, Pipe.RedFn.den, Pipe.ZipFn.den, Chains.dot, Pipe.BytePairs,
      Pipe.Pairs.loop, Pipe.Elems.loop, Pipe.LoopStage.step, Pipe.multiply, plusRed_eq, times_eq]
  · cases h

/-! checked examples and counterexamples -/
theorem minus_red_counter : redR (· - ·) [10, 3, 2] = some 9 ∧ ([3, 2] : List Int).foldl (· - ·) 10 = 5 := by decide
theorem plus_red_ex : plusRed [1, 2, 3, 4] = 10 ∧ scanPlus [1, 2, 3, 4] = [1, 3, 6, 10] := by decide
theorem compress_ex : (compress [true, false, true] ([5, 6, 7] : List Int)).toOption = some [5, 7] := by decide
theorem compress_len : (compress [true, false] ([5, 6, 7] : List Int)).toOption = none := by decide
/-- a truncating zip is not an APL shape check -/
theorem zip_truncates : (List.zip ([1, 2, 3] : List Int) [1, 2]).length = 2 ∧ (ipVec [1, 2, 3] [1, 2]).toOption = none := by decide
theorem ip_ex : (ipVec [1, 2, 3] [4, 5, 6]).toOption = some 32 := by decide
theorem shape_ok : (ipShape [2, 3] [3, 4]).toOption = some [2, 4] ∧ (ipShape [2, 3] [4, 3]).toOption = none := by decide
/-- mask mutant: dropping a selected element changes the sum -/
theorem compress_drop_mutant : plusRed [5, 7] = 12 ∧ plusRed [7] ≠ 12 := by decide
end Apl
