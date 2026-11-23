import Pipe.Core
/-! The five user-facing source chains (plus one renamed, name-blind example). -/
open Pipe

namespace Chains

def dot : Reduced := BytePairs.loop multiply |>.loop sum
def l1  : Reduced := BytePairs.loop subtract |>.loop abs |>.loop sum
def l2  : Reduced := BytePairs.loop subtract |>.loop square |>.loop sum
def ham : Reduced := BytePairs.loop subtract |>.loop nonzero |>.loop sum
def osl : Reduced := BytePairs.loop subtract |>.loop clampNeg |>.loop sum

/-- name-blind: unrelated name and stage aliases; lowers to the same loop as `l1` -/
def minus := subtract
def magnitude := Pipe.abs
def qz7 : Reduced := BytePairs.loop minus |>.loop magnitude |>.loop sum

/-! well-typed edits whose lowered program or meaning changes (controls) -/
def l1_drop_abs    : Reduced := BytePairs.loop subtract |>.loop sum
def l1_abs_to_sq   : Reduced := BytePairs.loop subtract |>.loop square |>.loop sum
def l1_extra_sq    : Reduced := BytePairs.loop subtract |>.loop abs |>.loop square |>.loop sum
def dot_to_sub     : Reduced := BytePairs.loop subtract |>.loop sum
def dot_extra_abs  : Reduced := BytePairs.loop multiply |>.loop abs |>.loop sum
def ham_swap_order : Reduced := BytePairs.loop subtract |>.loop abs |>.loop nonzero |>.loop sum
def ham_mul_zip    : Reduced := BytePairs.loop multiply |>.loop nonzero |>.loop sum
def osl_to_abs     : Reduced := BytePairs.loop subtract |>.loop abs |>.loop sum
def osl_twice      : Reduced := BytePairs.loop subtract |>.loop clampNeg |>.loop clampNeg |>.loop sum
def l2_to_mul      : Reduced := BytePairs.loop multiply |>.loop square |>.loop sum

end Chains
