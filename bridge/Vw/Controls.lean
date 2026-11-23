import Vw.Par
/-! Concrete positives and counterexamples, checked by kernel `decide`. -/
namespace Vw.Ctl
open Vw

def okv {β} : Except String β → Option β | .ok b => some b | .error _ => none

def src5 : List Int := [1, 2, 3, 4, 5]
def even (x : Int) : Bool := x % 2 == 0

/-! take/drop, zero and short inputs; exact pull counts (no over-pull) -/
theorem take2_pulls : (src5.view.take 2 |>.fuse).pulls = 2 := by decide
theorem take0_pulls : (src5.view.take 0 |>.fuse).pulls = 0 := by decide
theorem take_short : (([7] : List Int).view.take 3 |>.fuse).items = [7] ∧ (([7] : List Int).view.take 3).pulls = 1 := by decide
theorem drop_short : (([7] : List Int).view.drop 3 |>.fuse).items = [] ∧ (src5.view.drop 0).items = src5 := by decide
theorem filter_take_pulls : (src5.view.filter even |>.take 1 |>.fuse).pulls = 2 := by decide
/-- over-pull mutant: same output, but a take that never reports `done` pulls the whole source -/
def takeNoStop (n : Nat) : M Int Int := { takeM n with done := fun _ => false }
theorem overpull_mutant : (takeNoStop 2).pull (takeNoStop 2).init src5 = ([1, 2], 5) ∧ (takeM 2).pull (takeM (σ := Int) 2).init src5 = ([1, 2], 2) := by decide

/-! enumerate (0-based) -/
theorem enum_ex : (([5, 6] : List Int).view.enumerate |>.fuse).items = [(0, 5), (1, 6)] := by decide

/-! find / any / all: earliest match and exact prefix -/
theorem find_ex : okv ((src5.view.map (· * 10) |>.fuse).find (· > 15)) = some (some 20) := by decide
theorem find_pulls : (src5.view.map (· * 10) |>.fuse).findPulls (· > 15) = 2 := by decide
theorem find_none_pulls : (src5.view.fuse).findPulls (· > 9) = 5 := by decide
theorem any_pulls : (src5.view.fuse).findPulls (fun x => x == 1) = 1 := by decide
theorem all_ex : okv ((src5.view.fuse).all (· > 0)) = some true ∧ okv ((src5.view.fuse).all (· < 3)) = some false := by decide
/-- wrong-short-circuit mutant: reporting the LAST match differs from the earliest -/
theorem findlast_mutant : (src5.filter (· > 2)).getLast? = some 5 ∧ src5.find? (· > 2) = some 3 := by decide

/-! scan: inclusive, seed not emitted -/
theorem scan_ex : (([1, 2, 3, 4] : List Int).view.scan 0 (· + ·) |>.fuse).items = [1, 3, 6, 10] := by decide
/-- dependent scan: restarting the scan per chunk is wrong -/
theorem scan_chunk_mutant :
    ((blocks 2 ([1, 2, 3, 4] : List Int)).flatMap (prefixFolds (· + ·) 0)) = [1, 3, 3, 7] := by decide

/-! flatMap: inner order -/
theorem flatMap_ex : (([1, 2] : List Int).view.flatMap (fun x => [x, x * 10]) |>.fuse).items = [1, 10, 2, 20] := by decide

/-! chunk / window: size, stride, incomplete tail dropped -/
theorem chunk_ex : (src5.view.chunk 2 |>.fuse).items = [[1, 2], [3, 4]] := by decide
theorem window_ex : (src5.view.window 3 |>.fuse).items = [[1, 2, 3], [2, 3, 4], [3, 4, 5]] := by decide
theorem window_short : (([1, 2] : List Int).view.window 3 |>.fuse).items = [] := by decide
/-- bad tails: a tail-keeping chunk emits [5]; trailing partial windows are not windows -/
theorem chunk_tail_mutant : blocks 2 src5 = [[1, 2], [3, 4], [5]] ∧ blocks 2 src5 ≠ chunkRef 2 src5 := by decide
/-- windows computed per chunk miss the window that crosses the chunk boundary -/
theorem window_cross_mutant : ((chunkRef 2 src5).flatMap (windowRef 2)) = [[1, 2], [3, 4]] ∧
    windowRef 2 src5 = [[1, 2], [2, 3], [3, 4], [4, 5]] := by decide

/-! filter/take ordering: swapping the stages changes the result -/
theorem filter_take_reorder : (src5.view.filter even |>.take 1).items = [2] ∧ (src5.view.take 1 |>.filter even).items = [] := by decide

/-! global distinct: retained seen-set; an adjacent-only (1-item state) dedup is wrong -/
theorem distinct_ex : (distinctM.feed [] ([1, 2, 1, 3, 2] : List Int)).2 = [1, 2, 3] := by decide
def adjDedupM : M Int Int := ⟨Option Int, none, fun last x => if last = some x then (last, []) else (some x, [x]), fun _ => false⟩
theorem distinct_adjacent_mutant : (adjDedupM.feed none [1, 2, 1, 3, 2]).2 = [1, 2, 1, 3, 2] := by decide

/-! barriers are retained by `.fuse`: two segments -/
theorem sort_segments : (src5.view.map (· * 2) |>.sortBy (· ≤ ·) |>.take 1 |>.fuse).segments = 2 := by decide
theorem stage_segments : (src5.view.map (· * 2) |>.filter even |>.take 1 |>.fuse).segments = 1 := by decide

/-! parallelize: legality decided by the terminal -/
def isErr {β} : Except String β → Bool | .error _ => true | .ok _ => false
theorem sub_par_refused : isErr (([10, 3, 2] : List Int).view.parallelize 2 |>.foldl 0 (· - ·)) = true := by decide
/-- why: chunking subtraction changes the answer (ordered -15 vs chunked 15) -/
theorem sub_chunk_mutant : ([10, 3, 2] : List Int).foldl (· - ·) 0 = -15 ∧
    ((blocks 2 ([10, 3, 2] : List Int)).map (·.foldl (· - ·) 0)).foldl (· - ·) 0 = 15 := by decide
theorem add_par_ok : okv (src5.view.parallelize 2 |>.accumulate 0) = some 15 := by decide
theorem app_par_ordered : okv (([[1], [2], [3]] : List (List Nat)).view.parallelize 2 |>.reduce listApp) = some [1, 2, 3] := by decide
theorem app_unordered_refused : isErr (([[1], [2]] : List (List Nat)).view.parallelize 1 |>.reduceUnordered listApp) = true := by decide
/-- why: an unordered combine of concatenation reorders the sequence -/
theorem app_reorder_mutant : parReduceAny listApp 1 [[1], [2]] = [2, 1] := by decide
theorem add_unordered_ok : okv (src5.view.parallelize 2 |>.reduceUnordered intAdd) = some 15 := by decide
theorem find_par_refused : isErr ((src5.view.parallelize 2).find (· > 2)) = true := by decide

/-! effects: callback order is observable. Staged runs all f then all g; fused interleaves. The view
accepts only pure Lean functions, so this boundary is never crossed silently. -/
def traceStaged (xs : List Int) : List (String × Int) := xs.map (fun x => ("f", x)) ++ xs.map (fun x => ("g", x + 1))
def traceFused (xs : List Int) : List (String × Int) := xs.flatMap (fun x => [("f", x), ("g", x + 1)])
theorem effect_order_differs : traceStaged [1, 2] ≠ traceFused [1, 2] := by decide
end Vw.Ctl
