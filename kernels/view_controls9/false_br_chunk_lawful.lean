import Vw
open Vw Vw.GroupCtl
-- FALSE: naive chunk concatenation is not lawful for the order-sensitive bracket step
example : chunked br = evs.foldl (gIns (·.key) "" br) [] := by decide
