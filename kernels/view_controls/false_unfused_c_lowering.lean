import Vw
open Pipe in
-- false: without .fuse() the C lowering request is refused, so it is not .ok dot
example : (BytePairs.view.map multiply |>.accumulate 0) = .ok Chains.dot := rfl
