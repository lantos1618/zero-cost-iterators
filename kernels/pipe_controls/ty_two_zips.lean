import Pipe.Chains
open Pipe
def c : Reduced := BytePairs.loop subtract |>.loop multiply |>.loop sum
