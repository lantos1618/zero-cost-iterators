import Pipe.Chains
open Pipe
def c : Reduced := BytePairs.loop abs |>.loop sum
