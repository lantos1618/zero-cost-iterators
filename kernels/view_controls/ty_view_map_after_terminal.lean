import Vw
open Pipe in
-- a terminal result (Except String Reduced) has no view adapters
example := (BytePairs.view.map multiply |>.fuse |>.accumulate 0).map abs
