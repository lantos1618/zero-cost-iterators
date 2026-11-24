import Vw
open Vw Vw.GroupCtl
-- FALSE: new keys at the front changes the deterministic first-seen key order
example : evs.foldl (gInsFront (·.key) "" br) [] = evs.foldl (gIns (·.key) "" br) [] := by decide
