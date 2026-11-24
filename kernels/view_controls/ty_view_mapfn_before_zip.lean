import Vw
open Pipe in
-- the first adapter on a byte-pair view must be a pair-combining ZipFn
example := (BytePairs.view.map abs |>.fuse |>.accumulate 0)
