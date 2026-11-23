import Bridge.Proofs
/-! Fluent staged front door: `BytePairs.loop zip |>.loop map* |>.loop reduce`.
The supported "functions" are this closed set of stage descriptions (not arbitrary callbacks). -/
open IR

namespace Pipe

/-- pair-combining stage: (signed byte, signed byte) → element -/
inductive ZipFn | multiply | subtract deriving DecidableEq, Repr
/-- element → element stage -/
inductive MapFn | abs | square | nonzero | clampNeg deriving DecidableEq, Repr
/-- terminal reduction -/
inductive RedFn | sum deriving DecidableEq, Repr

/-- the source: n readable signed-byte pairs (a[i], b[i]) -/
structure Pairs where
  deriving Repr
/-- after the zip stage and zero or more map stages, in application order -/
structure Elems where
  z : ZipFn
  ms : List MapFn
  deriving DecidableEq, Repr
/-- a terminated chain; it has no `.loop`, so nothing may follow the reduction -/
structure Reduced where
  e : Elems
  r : RedFn
  deriving DecidableEq, Repr

def BytePairs : Pairs := {}
def multiply : ZipFn := .multiply
def subtract : ZipFn := .subtract
def abs : MapFn := .abs
def square : MapFn := .square
def nonzero : MapFn := .nonzero
def clampNeg : MapFn := .clampNeg
def sum : RedFn := .sum

/-- the typing of stage composition: which stage kind may follow which chain kind -/
class LoopStage (σ τ : Type) (ρ : outParam Type) where
  step : σ → τ → ρ
instance : LoopStage Pairs ZipFn Elems := ⟨fun _ z => ⟨z, []⟩⟩
instance : LoopStage Elems MapFn Elems := ⟨fun e m => ⟨e.z, e.ms ++ [m]⟩⟩
instance : LoopStage Elems RedFn Reduced := ⟨fun e r => ⟨e, r⟩⟩

def Pairs.loop {τ ρ : Type} [LoopStage Pairs τ ρ] (p : Pairs) (s : τ) : ρ := LoopStage.step p s
def Elems.loop {τ ρ : Type} [LoopStage Elems τ ρ] (e : Elems) (s : τ) : ρ := LoopStage.step e s

/-! ## Source denotation: ordered zip, then each map as a whole-list pass, then a left fold. -/
def ZipFn.den : ZipFn → Int → Int → Int
  | .multiply, x, y => x * y
  | .subtract, x, y => x - y
def MapFn.den : MapFn → Int → Int
  | .abs, v => (v.natAbs : Int)
  | .square, v => v * v
  | .nonzero, v => if v = 0 then 0 else 1
  | .clampNeg, v => max v 0
def RedFn.den : RedFn → List Int → Int
  | .sum, l => l.foldl (· + ·) 0
def Elems.den (e : Elems) (xs ys : List Int) : List Int :=
  e.ms.foldl (fun l m => l.map m.den) ((List.zip xs ys).map fun p => e.z.den p.1 p.2)
def Reduced.den (r : Reduced) (xs ys : List Int) : Int := r.r.den (r.e.den xs ys)

/-! ## Lowering: traverse the supplied stages, in order, into one loop body. -/
def ZipFn.op : ZipFn → Op | .multiply => .Mul | .subtract => .Sub
def MapFn.op : MapFn → Op | .abs => .AbsT | .square => .Sq | .nonzero => .Ne0 | .clampNeg => .Pos
def RedFn.op : RedFn → Op | .sum => .Acc
def Reduced.body (r : Reduced) : List Op := [.LdA, .LdB, r.e.z.op] ++ r.e.ms.map MapFn.op ++ [r.r.op]
def lower (r : Reduced) : Prog := [.Loop r.body]

/-! ## Guard derivation from bounded stage effects (interval analysis over int8 inputs).
Not trusted for safety: the gate re-checks the emitted guard against the proved `Check.bound`. -/
structure Iv where
  lo : Int
  hi : Int
  deriving Repr
def ZipFn.iv : ZipFn → Iv
  | .multiply => let c := [(-128) * (-128), (-128) * 127, 127 * (-128), 127 * 127]
                 ⟨c.foldl min 0, c.foldl max 0⟩
  | .subtract => ⟨-128 - 127, 127 - (-128)⟩
def MapFn.iv : MapFn → Iv → Iv
  | .abs, ⟨l, h⟩ => ⟨if 0 ≤ l then l else if h ≤ 0 then -h else 0, max (l.natAbs : Int) (h.natAbs : Int)⟩
  | .square, ⟨l, h⟩ => ⟨if 0 ≤ l then l * l else if h ≤ 0 then h * h else 0, max (l * l) (h * h)⟩
  | .nonzero, ⟨l, h⟩ => ⟨if 0 < l ∨ h < 0 then 1 else 0, if l = 0 ∧ h = 0 then 0 else 1⟩
  | .clampNeg, ⟨l, h⟩ => ⟨max l 0, max h 0⟩
def Elems.iv (e : Elems) : Iv := e.ms.foldl (fun i m => m.iv i) e.z.iv
/-- largest n with n · max|element| ≤ INT32_MAX -/
def Reduced.guard (r : Reduced) : Nat :=
  let i := r.e.iv
  let m := max i.lo.natAbs i.hi.natAbs
  if m = 0 then 2147483647 else 2147483647 / m

/-! ## Proofs: chain denotation = fused IR execution (all Int inputs, no bounds needed) -/
def Elems.pt (e : Elems) (x y : Int) : Int := e.ms.foldl (fun v m => m.den v) (e.z.den x y)

theorem ir_execBody_append (x y t : Int) : ∀ (l1 l2 : List Op) (s : St),
    execBody (l1 ++ l2) x y t s = execBody l2 x y t (execBody l1 x y t s)
  | [], _, _ => rfl
  | o :: r, l2, s => ir_execBody_append x y t r l2 (exec o x y t s)

theorem map_exec (m : MapFn) (x y t : Int) (s : St) :
    exec m.op x y t s = { s with r0 := m.den s.r0 } := by
  cases m <;> simp only [MapFn.op, MapFn.den, exec]
  · congr 1; split <;> omega
  · congr 1; rw [Int.max_def]; split <;> split <;> omega

theorem maps_exec (x y t : Int) : ∀ (ms : List MapFn) (s : St),
    execBody (ms.map MapFn.op) x y t s = { s with r0 := ms.foldl (fun v m => m.den v) s.r0 }
  | [], s => rfl
  | m :: ms, s => by
    simp only [List.map_cons, execBody, map_exec, maps_exec x y t ms, List.foldl_cons]

theorem body_exec (r : Reduced) (x y t : Int) (s : St) :
    execBody r.body x y t s = { s with r0 := r.e.pt x y, r1 := y, acc := s.acc + r.e.pt x y } := by
  obtain ⟨⟨z, ms⟩, red⟩ := r
  cases red
  simp only [Reduced.body, ir_execBody_append, maps_exec]
  cases z <;> simp [execBody, exec, ZipFn.op, RedFn.op, Elems.pt, ZipFn.den]

theorem loop_acc (r : Reduced) : ∀ (xs ys tin : List Int) (s : St),
    (runLoop r.body xs ys tin s).acc = ((List.zip xs ys).map fun p => r.e.pt p.1 p.2).foldl (· + ·) s.acc
  | [], _, _, _ => by simp [runLoop]
  | _ :: _, [], _, _ => by simp [runLoop]
  | x :: xs, y :: ys, tin, s => by
    simp only [runLoop, List.zip_cons_cons, List.map_cons, List.foldl_cons]
    rw [loop_acc r xs ys (tl tin), body_exec]

theorem maps_pointwise (L : List (Int × Int)) : ∀ (ms : List MapFn) (f : Int × Int → Int),
    ms.foldl (fun l m => l.map m.den) (L.map f) = L.map (fun p => ms.foldl (fun v m => m.den v) (f p))
  | [], f => rfl
  | m :: ms, f => by
    simp only [List.foldl_cons, List.map_map]
    exact maps_pointwise L ms (m.den ∘ f)

theorem den_pointwise (e : Elems) (xs ys : List Int) :
    e.den xs ys = (List.zip xs ys).map fun p => e.pt p.1 p.2 := maps_pointwise _ e.ms _

/-- FUSION: the staged zip/map/reduce denotation equals the one-loop IR result, same left-to-right order -/
theorem fusion (r : Reduced) (xs ys : List Int) : (IR.run (lower r) xs ys).acc = r.den xs ys := by
  obtain ⟨e, red⟩ := r
  cases red
  simp only [lower, IR.run, runProg, start, IR.init]
  rw [loop_acc]
  simp [Reduced.den, RedFn.den, den_pointwise]

/-- lowering adds no buffer, allocation, wrap or adapter: one loop over the supported op set -/
def fusedOps : List Op := [.LdA, .LdB, .Mul, .Sub, .AbsT, .Sq, .Ne0, .Pos, .Acc]

theorem lower_fused (r : Reduced) :
    lower r = [.Loop r.body] ∧ (∀ o ∈ r.body, o ∈ fusedOps) ∧
    PS.Alloc ∉ lower r ∧ Op.StT ∉ r.body ∧ Op.LdT ∉ r.body ∧ Op.Wrap ∉ r.body := by
  obtain ⟨⟨z, ms⟩, red⟩ := r
  have hm : ∀ m : MapFn, m.op ∈ fusedOps := by intro m; cases m <;> decide
  have hz : ∀ z : ZipFn, z.op ∈ fusedOps := by intro z; cases z <;> decide
  have hr : ∀ r : RedFn, r.op ∈ fusedOps := by intro r; cases r; decide
  have hall : ∀ o ∈ (Reduced.body ⟨⟨z, ms⟩, red⟩), o ∈ fusedOps := by
    intro o ho
    simp only [Reduced.body, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil] at ho
    rcases ho with ((h | h | h | h) | ⟨m, _, rfl⟩) | h | h
    all_goals first | (subst h; first | decide | exact hz _ | exact hr _) | exact hm _ | exact absurd h id
  refine ⟨rfl, hall, by simp [lower], ?_, ?_, ?_⟩ <;> intro h <;>
    have := hall _ h <;> revert this <;> decide

/-! ## End-to-end: a PASS of the exact gate on files whose term is `lower r` gives the chain's meaning -/
open Check C Proofs in
theorem chain_gate_sound (r : Reduced) {cs bs : String} (h : gate cs bs true = .pass (lower r)) :
    ∃ f, C.parseFile cs = .ok f ∧ BendP.parseBend bs = .ok (lower r) ∧
      ∀ env out0, Admitted env → cRun f env out0 = if bound (lower r) < env.n then .ret (-1) out0
        else .ret 0 (some (r.den (env.a.take env.n) (env.b.take env.n))) := by
  obtain ⟨f, hf, hb, hc, H⟩ := exact_gate_sound h
  have he : exactCert (lower r) = true := by
    rcases hc with h | h | h | h | h <;> rw [h] <;> decide
  refine ⟨f, hf, hb, fun env out0 ha => ?_⟩
  rw [H env out0 ha, ← ir_exact_run _ he, fusion]

end Pipe
