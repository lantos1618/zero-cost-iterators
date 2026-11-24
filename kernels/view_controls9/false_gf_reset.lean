import Vw
open Vw Vw.GroupCtl
-- FALSE: the reset mutant forgets retained per-key state
example : evs.foldl (gInsReset (·.key) "" br) [] = evs.foldl (gIns (·.key) "" br) [] := by decide
