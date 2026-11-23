import Vw
open Vw Vw.GroupCtl
/-! POSITIVE: the generic theorems instantiate at arbitrary types, and a String-record pipeline evaluates -/
example {σ α β : Type} (c : Chain σ α) (k : β → α → β) (xs : List σ) (b : β) :
    xs.foldl (c.push k) b = (c.ref xs).foldl k b := Chain.push_fold c k xs b
example {α β κ : Type} [DecidableEq κ] (key : α → κ) (init : β) (step : β → α → β) (xs : List α) :
    xs.foldl (gIns key init step) [] = groupRef key init step xs := groupFold_correct key init step xs
example : ok? (evs.view.filter (fun e => e.n != 0) |>.map (fun e => e.label) |>.fuse
    |>.foldl "" (fun acc s => "[" ++ acc ++ "|" ++ s ++ "]")) = some "[[[[[|1]|3]|4]|5]|6]" := by decide
