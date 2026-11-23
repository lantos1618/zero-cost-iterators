import Vw
open Pipe in
-- the certified C entry point accepts only the closed stage descriptions, not callbacks
example := (BytePairs.view.map (fun (x : Int) => x) |>.fuse |>.accumulate 0)
