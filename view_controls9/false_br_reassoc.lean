import Vw
open Vw Vw.GroupCtl
-- FALSE: the ordered fold of the bracket step is not its right fold (no associativity is assumed)
example : evs.foldl br "" = evs.foldr (fun e acc => br acc e) "" := by decide
