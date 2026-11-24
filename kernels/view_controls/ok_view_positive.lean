import Vw
open Pipe in
example : (BytePairs.view.map multiply |>.fuse |>.accumulate 0) = .ok Chains.dot := rfl
example : (Apl.ipVec [1, 2, 3] [4, 5, 6]).toOption = some 32 := by decide
