import Vw
open Vw Vw.GroupCtl
-- FALSE: parallelize + groupFold is refused (no lawful per-key chunk summary), not accepted
example : (ok? (evs.view.fuse.parallelize 2 |>.groupFold (·.key) "" br)).isSome = true := by decide
