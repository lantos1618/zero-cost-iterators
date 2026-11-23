import Vw
open Vw Vw.GroupCtl
-- FALSE: swapping map and filter (filter now reads the mapped label) changes the result
example : ok? (evs.view.filter (fun e => e.n != 0) |>.map (fun e => e.label) |>.fuse |>.foldl "" (· ++ ·))
        = ok? (evs.view.map (fun e => e.label) |>.filter (fun s => s != "1") |>.fuse |>.foldl "" (· ++ ·)) := by decide
