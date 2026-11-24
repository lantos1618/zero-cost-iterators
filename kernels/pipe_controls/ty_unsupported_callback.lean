import Pipe.Chains
open Pipe
def c : Reduced := BytePairs.loop subtract |>.loop (fun (v : Int) => v + 1) |>.loop sum
