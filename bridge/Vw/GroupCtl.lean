import Vw.Group
import Vw.Controls
/-! groupFold fixtures and negative controls (String keys, String-bearing records). Each `theorem` is
checked by the Lean kernel; mutants are shown to DIFFER from the reference on a concrete input. -/
namespace Vw.GroupCtl
open Vw

structure Ev where
  key : String
  label : String
  n : Nat
  deriving DecidableEq, Repr

/-- repeated keys separated by other keys: a b a c b a -/
def evs : List Ev := [⟨"a", "1", 1⟩, ⟨"b", "2", 0⟩, ⟨"a", "3", 3⟩, ⟨"c", "4", 4⟩, ⟨"b", "5", 5⟩, ⟨"a", "6", 6⟩]

/-- order-sensitive, non-associative user step (the explicit witness) -/
def br (acc : String) (e : Ev) : String := "[" ++ acc ++ "|" ++ e.label ++ "]"
/-- separator join: admits a lawful chunk merge (`++`), used to contrast with `br` -/
def sep (acc : String) (e : Ev) : String := acc ++ "," ++ e.label

def ok? {ε τ} : Except ε τ → Option τ | .ok x => some x | .error _ => none

theorem gf_interleaved :
    ok? (evs.view.fuse.groupFold (·.key) "" br) =
      some [("a", "[[[|1]|3]|6]"), ("b", "[[|2]|5]"), ("c", "[|4]")] := by decide
theorem gf_unfused_same :
    ok? (evs.view.groupFold (·.key) "" br) = ok? (evs.view.fuse.groupFold (·.key) "" br) := by decide
/-- predicate and value transform fuse into the same traversal; label rewritten by map -/
theorem gf_filter_map :
    ok? (evs.view.filter (·.n ≠ 0) |>.map (fun e => { e with label := e.label ++ "!" }) |>.fuse
      |>.groupFold (·.key) "" br) = some [("a", "[[[|1!]|3!]|6!]"), ("c", "[|4!]"), ("b", "[|5!]")] := by decide
theorem gf_empty : ok? (([] : List Ev).view.fuse.groupFold (·.key) "" br) = some [] := by decide
theorem gf_all_filtered : ok? (evs.view.filter (fun _ => false) |>.fuse |>.groupFold (·.key) "" br) = some [] := by decide
theorem gf_ref : groupRef (·.key) "" br evs = [("a", "[[[|1]|3]|6]"), ("b", "[[|2]|5]"), ("c", "[|4]")] := by
  simp only [← groupFold_correct]; decide

/-! ### broken implementations -/
/-- MUTANT: resets the key's state on every hit -/
def gInsReset {α β κ} [DecidableEq κ] (key : α → κ) (init : β) (step : β → α → β) : List (κ × β) → α → List (κ × β)
  | [], x => [(key x, step init x)]
  | (k, b) :: t, x => if k = key x then (k, step init x) :: t else (k, b) :: gInsReset key init step t x
/-- MUTANT: new keys go to the FRONT (order changes) -/
def gInsFront {α β κ} [DecidableEq κ] (key : α → κ) (init : β) (step : β → α → β) (t : List (κ × β)) (x : α) : List (κ × β) :=
  if t.any (·.1 = key x) then gIns key init step t x else (key x, step init x) :: t
/-- MUTANT: adjacent grouping (List.splitBy) then fold: repeats separated by other keys split -/
def adjGroupFold (xs : List Ev) : List (String × String) :=
  (xs.splitBy (fun a b => a.key = b.key)).filterMap fun g => g.head?.map fun h => (h.key, g.foldl br "")

theorem reset_differs : evs.foldl (gInsReset (·.key) "" br) [] ≠ groupRef (·.key) "" br evs := by
  simp only [← groupFold_correct]; decide
theorem front_differs : evs.foldl (gInsFront (·.key) "" br) [] ≠ groupRef (·.key) "" br evs := by
  simp only [← groupFold_correct]; decide
theorem adjacent_differs : adjGroupFold evs ≠ groupRef (·.key) "" br evs := by
  simp only [← groupFold_correct]; decide
theorem reversed_source_differs : groupRef (·.key) "" br evs.reverse ≠ groupRef (·.key) "" br evs := by
  simp only [← groupFold_correct]; decide

/-! ### chunked plans: a lawful merge exists for `sep`, not for `br`; the view refuses both -/
def mergeT (t u : List (String × String)) : List (String × String) :=
  (t.map fun (k, a) => (k, a ++ ((u.find? (·.1 = k)).map (·.2)).getD "")) ++ u.filter (fun (k, _) => !(t.any (·.1 = k)))
def chunked (step : String → Ev → String) : List (String × String) :=
  mergeT ((evs.take 3).foldl (gIns (·.key) "" step) []) ((evs.drop 3).foldl (gIns (·.key) "" step) [])

theorem chunk_sep_lawful : chunked sep = groupRef (·.key) "" sep evs := by
  simp only [← groupFold_correct]; decide
theorem chunk_br_wrong : chunked br ≠ groupRef (·.key) "" br evs := by
  simp only [← groupFold_correct]; decide
theorem gf_par_refused : ok? (evs.view.fuse.parallelize 2 |>.groupFold (·.key) "" br) = none := by decide
theorem foldl_par_refused : ok? (evs.view.fuse.parallelize 2 |>.foldl "" br) = none := by decide
/-- ordered non-associative foldl over records: the fused result is the left fold, and the
right-nested alternative differs -/
theorem br_foldl : ok? (evs.view.fuse.foldl "" br) = some "[[[[[[|1]|2]|3]|4]|5]|6]" := by decide

end Vw.GroupCtl
