import Bridge
import Pipe.Chains
import Pipe.BendGen
/-! Actual pipegen-emitted prog.bend files (translated by the trusted bend2lean.py) → chain meaning. -/
open IR Check Pipe Chains Link

namespace GenLink

/-- any Bend program whose decoded term is `lower r` computes the chain's staged meaning -/
theorem bend_chain (q : BK.Stmts) (r : Reduced) (hq : stmtsv q = lower r) (xs ys : BK.Zs) :
    zv (BK.acc_of (BK.run q xs ys)) = r.den (zsv xs) (zsv ys) := by
  rw [acc_of_v, run_v, hq, fusion]

theorem bend_chain_ints (q : BK.Stmts) (r : Reduced) (hq : stmtsv q = lower r) (a b : List Int) :
    zv (BK.acc_of (BK.run q (encs a) (encs b))) = r.den a b := by
  rw [bend_chain q r hq, zsv_encs, zsv_encs]

/-- ... and executes no buffer operation -/
theorem chain_run_nobuf (r : Reduced) (xs ys : List Int) : (IR.run (lower r) xs ys).mats = 0 := by
  simp only [lower, IR.run, runProg, start, IR.init]
  exact ir_loop_mats _ (lower_fused r).2.2.2.1 _ _ _ _

theorem bend_chain_nobuf (q : BK.Stmts) (r : Reduced) (hq : stmtsv q = lower r) (xs ys : BK.Zs) :
    BK.mats_of (BK.run q xs ys) = 0 := by
  rw [mats_of_v, run_v, hq, chain_run_nobuf]

/-- each generated prog.bend decodes to its chain's lowering -/
theorem gen_dot_term : stmtsv BK.P_gdot.prog = lower dot := rfl
theorem gen_l1_term : stmtsv BK.P_gl1.prog = lower l1 := rfl
theorem gen_l2_term : stmtsv BK.P_gl2.prog = lower l2 := rfl
theorem gen_ham_term : stmtsv BK.P_gham.prog = lower ham := rfl
theorem gen_osl_term : stmtsv BK.P_gosl.prog = lower osl := rfl
theorem gen_qz7_term : stmtsv BK.P_gqz7.prog = lower qz7 := rfl
/-- the generated Bend terms are the i8red6 terms (same Bend term; only the provenance comment differs) -/
theorem gen_same_terms : BK.P_gdot.prog = BK.P_pos.prog ∧ BK.P_gl1.prog = BK.P_l1.prog ∧
    BK.P_gl2.prog = BK.P_l2.prog ∧ BK.P_gham.prog = BK.P_ham.prog ∧ BK.P_gosl.prog = BK.P_osl.prog ∧
    BK.P_gqz7.prog = BK.P_l1.prog := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- per-file instances: the actual generated Bend program computes the chain meaning, for all int lists -/
theorem gen_dot_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gdot.prog (encs a) (encs b))) = dot.den a b :=
  bend_chain_ints _ _ gen_dot_term a b
theorem gen_l1_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gl1.prog (encs a) (encs b))) = l1.den a b :=
  bend_chain_ints _ _ gen_l1_term a b
theorem gen_l2_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gl2.prog (encs a) (encs b))) = l2.den a b :=
  bend_chain_ints _ _ gen_l2_term a b
theorem gen_ham_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gham.prog (encs a) (encs b))) = ham.den a b :=
  bend_chain_ints _ _ gen_ham_term a b
theorem gen_osl_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gosl.prog (encs a) (encs b))) = osl.den a b :=
  bend_chain_ints _ _ gen_osl_term a b
theorem gen_qz7_den (a b : List Int) : zv (BK.acc_of (BK.run BK.P_gqz7.prog (encs a) (encs b))) = qz7.den a b :=
  bend_chain_ints _ _ gen_qz7_term a b

end GenLink
