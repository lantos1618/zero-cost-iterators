import Pipe.Chains
import Pipe.Emit
/-! Per-chain facts, all by kernel `decide` or `rfl`. -/
open IR Check Pipe Chains Proofs

namespace Facts
/-- lowering the five chains yields exactly the certified one-loop programs -/
theorem lower_dot : lower dot = posIR := rfl
theorem lower_l1 : lower l1 = l1IR := rfl
theorem lower_l2 : lower l2 = l2IR := rfl
theorem lower_ham : lower ham = hamIR := rfl
theorem lower_osl : lower osl = oslIR := rfl
theorem lower_qz7 : lower qz7 = lower l1 := rfl
/-- the stage-effect guard equals the checker's proved tight bound for each lowered program -/
theorem guard_dot : dot.guard = bound (lower dot) := by decide
theorem guard_l1 : l1.guard = bound (lower l1) := by decide
theorem guard_l2 : l2.guard = bound (lower l2) := by decide
theorem guard_ham : ham.guard = bound (lower ham) := by decide
theorem guard_osl : osl.guard = bound (lower osl) := by decide
/-- chain meaning = independent references, for all integer lists (via fusion + shared induction) -/
theorem den_dot (xs ys : List Int) : dot.den xs ys = refDot xs ys := by
  rw [← fusion, lower_dot, ir_exact_run posIR (by decide)]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]
theorem den_l1 (xs ys : List Int) : l1.den xs ys = refL1 xs ys := by
  rw [← fusion, lower_l1, ir_exact_run l1IR (by decide)]; simp [refOf]
theorem den_l2 (xs ys : List Int) : l2.den xs ys = refL2 xs ys := by
  rw [← fusion, lower_l2, ir_exact_run l2IR (by decide)]; simp [refOf, l1IR, l2IR]
theorem den_ham (xs ys : List Int) : ham.den xs ys = refHam xs ys := by
  rw [← fusion, lower_ham, ir_exact_run hamIR (by decide)]; simp [refOf, l1IR, l2IR, hamIR]
theorem den_osl (xs ys : List Int) : osl.den xs ys = refOsl xs ys := by
  rw [← fusion, lower_osl, ir_exact_run oslIR (by decide)]; simp [refOf, l1IR, l2IR, hamIR, oslIR]
/-- a different valid chain is a different meaning, not a corruption of the same one -/
theorem l1_abs_to_sq_differs : l1_abs_to_sq.den [0] [2] ≠ l1.den [0] [2] := by decide
theorem osl_to_abs_differs : osl_to_abs.den [0] [2] ≠ osl.den [0] [2] := by decide
theorem l1_drop_abs_differs : l1_drop_abs.den [0] [2] ≠ l1.den [0] [2] := by decide
/-- semantically equal to `ham`, but a different (uncertified) lowered program -/
theorem ham_swap_same_meaning (xs ys : List Int) : ham_swap_order.den xs ys = ham.den xs ys := by
  simp only [Reduced.den, den_pointwise, Elems.pt]; congr 2; funext p
  simp [ham_swap_order, ham, Pipe.abs, nonzero, subtract, LoopStage.step, Elems.loop, Pairs.loop, MapFn.den, ZipFn.den]
  split <;> omega
theorem ham_swap_lowers_differently : lower ham_swap_order ≠ lower ham := by decide
end Facts
