import Vw
open Vw Vw.GroupCtl
-- FALSE: adjacent grouping splits a key repeated after other keys; it is not groupFold
example : adjGroupFold evs = evs.foldl (gIns (·.key) "" br) [] := by decide
