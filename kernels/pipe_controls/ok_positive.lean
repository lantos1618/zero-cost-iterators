import Pipe.Chains
open Pipe
def c : Reduced := BytePairs.loop subtract |>.loop abs |>.loop sum
