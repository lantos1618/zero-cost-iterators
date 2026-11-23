import Pipe.Chains
import Vw.Apl
/-! The REAL C entry point for `.view()` over byte pairs: a typed lazy view head on the existing
`Pipe` front end. `BytePairs.view.map multiply |>.fuse |>.accumulate 0` builds the same `Reduced`
chain that `.loop()` builds, so it reuses `lower`, the emitter, the exact gate and `chain_gate_sound`.
Without `.fuse()` the view still evaluates (staged, aligned extents) but C lowering is refused. -/
namespace Pipe

structure PView where
  fused : Bool := false
  deriving DecidableEq, Repr
structure PElems where
  e : Elems
  fused : Bool
  deriving DecidableEq, Repr

def Pairs.view (_ : Pairs) : PView := {}
def PView.fuse (v : PView) : PView := { v with fused := true }
def PView.map (v : PView) (z : ZipFn) : PElems := ⟨⟨z, []⟩, v.fused⟩
def PElems.map (p : PElems) (m : MapFn) : PElems := ⟨⟨p.e.z, p.e.ms ++ [m]⟩, p.fused⟩
def PElems.fuse (p : PElems) : PElems := { p with fused := true }

/-- terminal `accumulate(seed)` = ordered `foldl(seed, add)`; legality of the requested C lowering
is checked HERE: it needs `.fuse()` and the certified emitter's seed 0 -/
def PElems.accumulate (p : PElems) (seed : Int) : Except String Reduced :=
  if !p.fused then .error "refused: C lowering needs an explicit .fuse()"
  else if seed ≠ 0 then .error "refused: certified emitter supports accumulate(0) only"
  else .ok ⟨p.e, .sum⟩

/-- plain (unfused) staged evaluation; aligned extents are checked, never truncated -/
def PElems.eval (p : PElems) (seed : Int) (xs ys : List Int) : Except String Int :=
  if xs.length = ys.length then .ok ((p.e.den xs ys).foldl (· + ·) seed) else .error "LENGTH ERROR"

open Chains in
theorem view_chains :
    (BytePairs.view.map multiply |>.fuse |>.accumulate 0) = .ok dot ∧
    (BytePairs.view.map subtract |>.map abs |>.fuse |>.accumulate 0) = .ok l1 ∧
    (BytePairs.view.map subtract |>.map square |>.fuse |>.accumulate 0) = .ok l2 ∧
    (BytePairs.view.map subtract |>.map nonzero |>.fuse |>.accumulate 0) = .ok ham ∧
    (BytePairs.view.map subtract |>.map clampNeg |>.fuse |>.accumulate 0) = .ok osl := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem view_nofuse_refused : (BytePairs.view.map multiply |>.accumulate 0).toOption = none := by decide
theorem view_seed_refused : (BytePairs.view.map multiply |>.fuse |>.accumulate 5).toOption = none := by decide
/-- `.fuse()` may be placed on the head or after the adapters -/
theorem fuse_position : (BytePairs.view.fuse.map multiply |>.accumulate 0) = (BytePairs.view.map multiply |>.fuse |>.accumulate 0) := rfl

/-- plain view use (no transformation requested) is APL `A +.× B` on every aligned or misaligned pair -/
theorem view_eval_ip (a b : List Int) : (BytePairs.view.map multiply).eval 0 a b = Apl.ipVec a b := by
  unfold PElems.eval Apl.ipVec; split
  · simp [Elems.den, PView.map, Pairs.view, ZipFn.den, multiply, Apl.plusRed_eq, Apl.times_eq]
  · rfl

open Check C Proofs in
/-- END-TO-END: if the dot view's fused lowering passes the exact gate on files cs/bs, then the C
returns APL `A +.× B` of the first n admitted elements (and -1 on the oversize guard) -/
theorem view_dot_gate {cs bs : String} (r : Reduced)
    (hv : (BytePairs.view.map multiply |>.fuse |>.accumulate 0) = .ok r)
    (h : gate cs bs true = .pass (lower r)) :
    ∃ f, C.parseFile cs = .ok f ∧ ∀ env out0, Admitted env → cRun f env out0 =
      if bound (lower r) < env.n then .ret (-1) out0
      else .ret 0 (some ((Apl.ipVec (env.a.take env.n) (env.b.take env.n)).toOption.getD 0)) := by
  have hr : r = Chains.dot := by have := view_chains.1; rw [this] at hv; cases hv; rfl
  subst hr
  obtain ⟨f, hf, _, hrun⟩ := chain_gate_sound _ h
  refine ⟨f, hf, fun env out0 hA => ?_⟩
  rw [hrun env out0 hA]; split
  · rfl
  · have hl : (env.a.take env.n).length = (env.b.take env.n).length := by
      have := hA; simp only [Admitted] at this; simp [List.length_take]; omega
    have e := Apl.ip_dot (env.a.take env.n) (env.b.take env.n)
    unfold Apl.ipVec at e ⊢; rw [if_pos hl] at e ⊢
    rw [(e _ rfl).1]; rfl
end Pipe
