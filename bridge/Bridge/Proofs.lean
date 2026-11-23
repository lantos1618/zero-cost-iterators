import Bridge.Check
import Bridge.CSem
/-! Bridge theorems. Premise: the executable checker (`Check.gate`, called by `i8check`) accepts the
actual file text. Conclusion: the recovered C program, run in the independent C-subset semantics
(`C.cRun`), agrees with the IR program parsed from prog.bend, run in the IR model (`IR.run`). -/
open C IR Check

namespace Proofs

def R (out : Option Int) (st : CSt) (s : IR.St) : Prop :=
  st.acc = some s.acc ∧ st.r0 = some s.r0 ∧ st.r1 = some s.r1 ∧ st.out = out
/-- "C faults, or C agrees with IR" -/
def Ag (out : Option Int) (o : Option CSt) (s : IR.St) : Prop := o = none ∨ ∃ st, o = some st ∧ R out st s

theorem Ag.bind {out : Option Int} {o : Option CSt} {s s' : IR.St} {g : CSt → Option CSt}
    (h : Ag out o s) (hg : ∀ st, R out st s → Ag out (g st) s') : Ag out (o.bind g) s' := by
  rcases h with rfl | ⟨st, rfl, hr⟩
  · left; rfl
  · exact hg st hr

theorem execBody_append (env : Env) (i : Option Nat) :
    ∀ (l1 l2 : List S) (st : CSt), C.execBody env i (l1 ++ l2) st = (C.execBody env i l1 st).bind (C.execBody env i l2)
  | [], l2, st => by simp [C.execBody]
  | s :: r, l2, st => by
    simp only [List.cons_append, C.execBody]
    cases execS env i st s <;> simp [execBody_append env i r l2]

theorem mask_eq (z : Int) : ((z % 4294967296).toNat &&& 255) = (z % 256).toNat := by
  have : (255 : Nat) = 2^8 - 1 := rfl
  rw [this, Nat.and_pow_two_sub_one_eq_mod]
  omega

theorem op_sim {env : Env} {i : Nat} {x y t : Int} {out : Option Int} {st : CSt} {s : IR.St}
    (op : Op) (ss : List S) (hop : opS op = some ss) (hr : R out st s)
    (hx : env.a[i]? = some x) (hy : env.b[i]? = some y)
    (hx8 : -128 ≤ x ∧ x ≤ 127) (hy8 : -128 ≤ y ∧ y ≤ 127) :
    Ag out (C.execBody env (some i) ss st) (IR.exec op x y t s) := by
  obtain ⟨ha, h0, h1, ho⟩ := hr
  cases op <;> simp only [opS, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  · right; refine ⟨st.set .r0 x, ?_, ?_⟩
    · simp [C.execBody, execS, assign, evalE, CSt.get, Env.arr, h0, hx, hx8]
    · simp [R, CSt.set, IR.exec, ha, h1, ho]
  · right; refine ⟨st.set .r1 y, ?_, ?_⟩
    · simp [C.execBody, execS, assign, evalE, CSt.get, Env.arr, h1, hy, hy8]
    · simp [R, CSt.set, IR.exec, ha, h0, ho]
  · by_cases hm : inI32 (s.r0 * s.r1)
    · right; refine ⟨st.set .r0 (s.r0 * s.r1), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, h1, hm]
      · simp [R, CSt.set, IR.exec, ha, h1, ho]
    · left; simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, h1, hm]
  · by_cases hm : inI32 (s.acc + s.r0)
    · right; refine ⟨st.set .acc (s.acc + s.r0), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, ha, h0, hm]
      · simp [R, CSt.set, IR.exec, h0, h1, ho]
    · left; simp [C.execBody, execS, assign, evalE, i32op, CSt.get, ha, h0, hm]
  · right
    have hv : ((s.acc % 4294967296).toNat &&& 255) = (s.acc % 256).toNat := mask_eq s.acc
    have hle : (((s.acc % 256).toNat : Nat) : Int) = s.acc % 256 := by omega
    have hb : (s.acc % 256).toNat ≤ 2147483647 := by omega
    by_cases hg : 127 < s.acc % 256
    · have hs : -2147483648 ≤ s.acc % 256 - 256 ∧ s.acc % 256 - 256 ≤ 2147483647 := by omega
      refine ⟨st.set .acc (s.acc % 256 - 256), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, CSt.set, ha, hv, hle, hb, hg, hs, inI32]
      · simp only [R, CSt.set, IR.exec, IR.wrap8, h0, h1, ho, and_true, Option.some.injEq]; omega
    · refine ⟨st.set .acc (s.acc % 256), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, CSt.set, ha, hv, hle, hb, hg, inI32]
      · simp only [R, CSt.set, IR.exec, IR.wrap8, h0, h1, ho, and_true, Option.some.injEq]; omega

  · by_cases hm : inI32 (s.r0 - s.r1)
    · right; refine ⟨st.set .r0 (s.r0 - s.r1), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, h1, hm]
      · simp [R, CSt.set, IR.exec, ha, h1, ho]
    · left; simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, h1, hm]
  · by_cases hn : s.r0 < 0
    · by_cases hm : inI32 (-s.r0)
      · right; refine ⟨st.set .r0 (-s.r0), ?_, ?_⟩
        · simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, hm]
        · simp [R, CSt.set, IR.exec, ha, h1, ho, hn]
      · left; simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, hm]
    · right; refine ⟨st, ?_, ?_⟩
      · simp [C.execBody, execS, CSt.get, h0, hn]
      · simp [R, IR.exec, ha, h0, h1, ho, hn]
  · by_cases hm : inI32 (s.r0 * s.r0)
    · right; refine ⟨st.set .r0 (s.r0 * s.r0), ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, hm]
      · simp [R, CSt.set, IR.exec, ha, h1, ho]
    · left; simp [C.execBody, execS, assign, evalE, i32op, CSt.get, h0, hm]
  · by_cases hn : s.r0 < 0
    · right; refine ⟨st.set .r0 0, ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, inI32]
      · simp [R, CSt.set, IR.exec, ha, h1, ho, hn]
    · right; refine ⟨st, ?_, ?_⟩
      · simp [C.execBody, execS, CSt.get, h0, hn]
      · simp [R, IR.exec, ha, h0, h1, ho, hn]
  · by_cases hn : 0 < s.r0
    · right; refine ⟨st.set .r0 1, ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, inI32]
      · simp [R, CSt.set, IR.exec, ha, h1, ho, hn]
    · right; refine ⟨st, ?_, ?_⟩
      · simp [C.execBody, execS, CSt.get, h0, hn]
      · simp [R, IR.exec, ha, h0, h1, ho, hn]
  · by_cases hn : s.r0 < 0
    · by_cases hm : inI32 (-s.r0)
      · right; refine ⟨st.set .r0 (-s.r0), ?_, ?_⟩
        · simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, hm]
        · simp [R, CSt.set, IR.exec, ha, h1, ho, hn]
      · left; simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, hm]
    · right; refine ⟨st.set .r0 s.r0, ?_, ?_⟩
      · simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn]
      · simp [R, CSt.set, IR.exec, ha, h1, ho, hn]
  · right; refine ⟨st.set .r0 (if s.r0 = 0 then 0 else 1), ?_, ?_⟩
    · by_cases hn : s.r0 = 0 <;> simp [C.execBody, execS, assign, evalE, CSt.get, h0, hn, inI32]
    · simp [R, CSt.set, IR.exec, ha, h1, ho]

theorem body_sim {env : Env} {i : Nat} {x y t : Int} {out : Option Int}
    (hx : env.a[i]? = some x) (hy : env.b[i]? = some y)
    (hx8 : -128 ≤ x ∧ x ≤ 127) (hy8 : -128 ≤ y ∧ y ≤ 127) :
    ∀ (ops : List Op) (ss : List S) (st : CSt) (s : IR.St),
    renderOps ops = some ss → R out st s →
    Ag out (C.execBody env (some i) ss st) (IR.execBody ops x y t s)
  | [], ss, st, s, h, hr => by
    simp [renderOps] at h; subst h; right; exact ⟨st, rfl, hr⟩
  | o :: r, ss, st, s, h, hr => by
    simp only [renderOps] at h
    cases ho : opS o with
    | none => simp [ho] at h
    | some a =>
      cases hrr : renderOps r with
      | none => simp [ho, hrr] at h
      | some b =>
        simp [ho, hrr] at h; subst h
        rw [execBody_append]
        exact Ag.bind (op_sim o a ho hr hx hy hx8 hy8) (fun st' hr' => body_sim hx hy hx8 hy8 r b st' _ hrr hr')

theorem drop_take_len (l : List Int) (n : Nat) : (l.take n).drop n = [] :=
  List.drop_eq_nil_of_le (by simp; exact Nat.min_le_left _ _)

theorem loop_sim {env : Env} {out : Option Int} (ha : Admitted env) (ops : List Op) (ss : List S)
    (hro : renderOps ops = some ss) :
    ∀ (k i : Nat) (st : CSt) (s : IR.St) (tin : List Int), i + k = env.n → R out st s →
    Ag out (loopK env ss k i st) (IR.runLoop ops ((env.a.take env.n).drop i) ((env.b.take env.n).drop i) tin s)
  | 0, i, st, s, tin, hk, hrs => by
    have : i = env.n := by omega
    subst this
    right; refine ⟨st, by simp [loopK], ?_⟩
    rw [drop_take_len]; simp only [IR.runLoop]; exact hrs
  | k + 1, i, st, s, tin, hk, hrs => by
    have hi : i < env.n := by omega
    have hia : i < env.a.length := by have := ha.2.2.1; omega
    have hib : i < env.b.length := by have := ha.2.2.2.1; omega
    have hta : i < (env.a.take env.n).length := by simp; omega
    have htb : i < (env.b.take env.n).length := by simp; omega
    rw [List.drop_eq_getElem_cons hta, List.drop_eq_getElem_cons htb]
    simp only [loopK, hi, if_true, IR.runLoop, List.getElem_take]
    exact Ag.bind (body_sim (List.getElem?_eq_getElem hia) (List.getElem?_eq_getElem hib)
        (ha.1 _ (List.getElem_mem hia)) (ha.2.1 _ (List.getElem_mem hib)) ops ss st s hro hrs)
      (fun st' h' => loop_sim ha ops ss hro k (i + 1) st' _ _ (by omega) h')

theorem prog_sim {env : Env} {out : Option Int} {dirs : List Dir} (ha : Admitted env) :
    ∀ (p : Prog) (ls : List T) (st : CSt) (s : IR.St), mapO renderPS p = some ls → R out st s →
    execT env dirs (ls ++ epilogue) st = .fault ∨
    execT env dirs (ls ++ epilogue) st = .ret 0 (some (IR.runProg p (env.a.take env.n) (env.b.take env.n) s).acc)
  | [], ls, st, s, h, hrs => by
    simp [mapO] at h; subst h
    right; simp [epilogue, execT, CSt.get, hrs.1, IR.runProg]
  | ps :: r, ls, st, s, h, hrs => by
    simp only [mapO] at h
    cases hp : renderPS ps with
    | none => simp [hp] at h
    | some t =>
      cases hr : mapO renderPS r with
      | none => simp [hp, hr] at h
      | some ls' =>
        simp [hp, hr] at h; subst h
        match ps, hp with
        | .Alloc, hp => simp [renderPS] at hp
        | .Loop [], hp => simp [renderPS] at hp
        | .Loop (o :: os), hp =>
          simp only [renderPS] at hp
          cases hro : renderOps (o :: os) with
          | none => simp [hro] at hp
          | some ss =>
            simp [hro] at hp; subst hp
            have hl := loop_sim ha (o :: os) ss hro env.n 0 st { s with tout := [] } s.tout (by omega) hrs
            simp only [List.drop_zero] at hl
            simp only [List.cons_append, execT, runFor]
            rcases hl with h0 | ⟨st', h1, h2⟩
            · left; rw [h0]
            · rw [h1]; simp only [IR.runProg, IR.start]; exact prog_sim ha r ls' st' _ hr h2

/-- generic bridge: for ANY IR program the file is a rendering of, on every admitted input the C
semantics either faults or produces exactly the IR result; the guard path never faults. -/
theorem sound_render (p : Prog) (f : CFile) (hr : render p = some f) (env : Env) (out0 : Option Int)
    (ha : Admitted env) :
    (bound p < env.n → cRun f env out0 = .ret (-1) out0) ∧
    (env.n ≤ bound p → cRun f env out0 = .fault ∨
       cRun f env out0 = .ret 0 (some (IR.run p (env.a.take env.n) (env.b.take env.n)).acc)) := by
  cases p with
  | nil => simp [render] at hr
  | cons ps r =>
    cases hm : mapO renderPS (ps :: r) with
    | none => simp [render, hm] at hr
    | some ls =>
      simp [render, hm] at hr; subst hr
      constructor
      · intro hn; simp [cRun, prologue, execT, lookupDef, dirsFor, hn]
      · intro hn
        have hnn : ¬ bound (ps :: r) < env.n := by omega
        have := prog_sim (out := out0) (dirs := dirsFor (bound (ps :: r))) ha (ps :: r) ls ⟨some 0, some 0, some 0, out0⟩ IR.init hm ⟨rfl, rfl, rfl, rfl⟩
        simpa [cRun, prologue, execT, lookupDef, dirsFor, hnn, CSt.get, CSt.set, inI32, IR.run] using this

theorem exactCert_cases {p : Prog} (h : exactCert p = true) :
    p = posIR ∨ p = l1IR ∨ p = l2IR ∨ p = hamIR ∨ p = oslIR := by
  simp only [exactCert, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> simp [h]
theorem certified_cases {p : Prog} (h : certified p = true) :
    p = posIR ∨ p = wrapIR ∨ p = l1IR ∨ p = l2IR ∨ p = hamIR ∨ p = oslIR := by
  simp only [certified, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;> simp [h]
theorem exactCert_certified {p : Prog} (h : exactCert p = true) : certified p = true := by
  rcases exactCert_cases h with h | h | h | h | h <;> subst h <;> decide

/-- the executable gate's PASS verdict recovers: the parsed file, its IR, the identical prog.bend IR,
certification, and the exact-gate restriction -/
theorem gate_pass {cs bs : String} {ex : Bool} {p : Prog} (h : gate cs bs ex = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ validate f = .ok p ∧ BendP.parseBend bs = .ok p ∧
      render p = some f ∧ certified p = true ∧ (ex = true → exactCert p = true) := by
  unfold gate at h
  split at h
  · cases h
  · rename_i f hf
    split at h
    · cases h
    · rename_i q hv
      have hr : render q = some f := by
        unfold validate at hv
        split at hv
        · split at hv
          · cases hv; assumption
          · cases hv
        · cases hv
      split at h
      · cases h
      · rename_i q' hb
        by_cases hne : q = q'
        · subst hne
          cases ex
          · simp only [ne_eq, not_true_eq_false, if_false, Bool.false_eq_true] at h
            split at h
            · cases h; exact ⟨f, hf, hv, hb, hr, ‹_›, by simp⟩
            · cases h
          · simp only [ne_eq, not_true_eq_false, if_false, if_true] at h
            split at h
            · rename_i hq
              cases h; exact ⟨f, hf, hv, hb, hr, exactCert_certified hq, fun _ => hq⟩
            · cases h
        · simp [hne] at h

theorem mapO_shape : ∀ (p : Prog) (ls : List T), mapO renderPS p = some ls →
    ls.length = p.length ∧ ∀ t ∈ ls, ∃ ss, t = .forN ss ∧ ss ≠ []
  | [], ls, h => by simp [mapO] at h; subst h; simp
  | ps :: r, ls, h => by
    simp only [mapO] at h
    cases hp : renderPS ps with
    | none => simp [hp] at h
    | some t =>
      cases hr : mapO renderPS r with
      | none => simp [hp, hr] at h
      | some ls' =>
        simp [hp, hr] at h; subst h
        obtain ⟨hl, ht⟩ := mapO_shape r ls' hr
        refine ⟨by simp [hl], ?_⟩
        intro t' ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · match ps, hp with
          | .Alloc, hp => simp [renderPS] at hp
          | .Loop [], hp => simp [renderPS] at hp
          | .Loop (o :: os), hp =>
            simp only [renderPS] at hp
            cases hro : renderOps (o :: os) with
            | none => simp [hro] at hp
            | some ss =>
              simp [hro] at hp; subst hp
              refine ⟨ss, rfl, ?_⟩
              intro hss; subst hss
              simp only [renderOps] at hro
              cases ho : opS o with
              | none => simp [ho] at hro
              | some a =>
                cases hr2 : renderOps os with
                | none => simp [ho, hr2] at hro
                | some b =>
                  simp [ho, hr2] at hro
                  cases o <;> simp [opS] at ho <;> subst ho <;> simp at hro
        · exact ht t' ht'

/-- recovered program: every accepted file is the fixed directives, guard, three declarations,
≥ 1 non-empty `for` loops, then `*out = acc; return 0;` - nothing else, in exactly this order -/
theorem recovered_shape {cs bs : String} {ex : Bool} {p : Prog} (h : gate cs bs ex = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ f.dirs = dirsFor (bound p) ∧ ∃ ls, ls ≠ [] ∧
      f.body = [.guard "I8DOT_MAX_N" (-1), .decl .acc 0, .decl .r0 0, .decl .r1 0] ++ ls ++ [.store .acc, .ret 0] ∧
      ∀ t ∈ ls, ∃ ss, t = .forN ss ∧ ss ≠ [] := by
  obtain ⟨f, hf, -, -, hr, -, -⟩ := gate_pass h
  refine ⟨f, hf, ?_⟩
  cases p with
  | nil => simp [render] at hr
  | cons ps r =>
    cases hm : mapO renderPS (ps :: r) with
    | none => simp [render, hm] at hr
    | some ls =>
      simp [render, hm] at hr; subst hr
      obtain ⟨hl, ht⟩ := mapO_shape _ ls hm
      refine ⟨rfl, ls, ?_, rfl, ht⟩
      intro h0; subst h0; simp at hl

/-- internal, conditional simulation restated on PASS: agrees with the IR or faults (the public total
guarantee is `gate_total`) -/
theorem gate_pass_conditional_sim {cs bs : String} {ex : Bool} {p : Prog} (h : gate cs bs ex = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ BendP.parseBend bs = .ok p ∧ ∀ env out0, Admitted env →
      (bound p < env.n → cRun f env out0 = .ret (-1) out0) ∧
      (env.n ≤ bound p → cRun f env out0 = .fault ∨
        cRun f env out0 = .ret 0 (some (IR.run p (env.a.take env.n) (env.b.take env.n)).acc)) := by
  obtain ⟨f, hf, -, hb, hr, -, -⟩ := gate_pass h
  exact ⟨f, hf, hb, fun env out0 ha => sound_render p f hr env out0 ha⟩

theorem prod_bound (x y : Int) (hx : -128 ≤ x ∧ x ≤ 127) (hy : -128 ≤ y ∧ y ≤ 127) :
    -16256 ≤ x * y ∧ x * y ≤ 16384 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rcases Int.le_total 0 x with h0x | hx0 <;> rcases Int.le_total 0 y with h0y | hy0
  · have h1 : x * y ≤ 127 * 127 := Int.mul_le_mul hx2 hy2 h0y (by decide)
    have h2 : 0 ≤ x * y := Int.mul_nonneg h0x h0y
    omega
  · have h1 : x * (-y) ≤ 127 * 128 := Int.mul_le_mul hx2 (by omega) (by omega) (by decide)
    have h2 : 0 ≤ x * (-y) := Int.mul_nonneg h0x (by omega)
    rw [Int.mul_neg] at h1 h2
    omega
  · have h1 : (-x) * y ≤ 128 * 127 := Int.mul_le_mul (by omega) hy2 h0y (by decide)
    have h2 : 0 ≤ (-x) * y := Int.mul_nonneg (by omega) h0y
    rw [Int.neg_mul] at h1 h2
    omega
  · have h1 : (-x) * (-y) ≤ 128 * 128 := Int.mul_le_mul (by omega) (by omega) (by omega) (by decide)
    have h2 : 0 ≤ (-x) * (-y) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.neg_mul_neg] at h1 h2
    omega

def posBody : List S := [.assign .r0 (.ld .a), .assign .r1 (.ld .b),
  .assign .r0 (.mul (.var .r0) (.var .r1)), .assign .acc (.add (.var .acc) (.var .r0))]
def wrapTail : List S := [.assign .acc (.toI32 (.andU (.toU32 (.var .acc)) 255)),
  .ifGt .acc 127 .acc (.sub (.var .acc) (.lit 256))]
def posFile : CFile := ⟨stdDirs, prologue ++ [.forN posBody] ++ epilogue⟩
def wrapFile : CFile := ⟨stdDirs, prologue ++ [.forN (posBody ++ wrapTail)] ++ epilogue⟩
theorem render_pos : render posIR = some posFile := rfl
theorem render_wrap : render wrapIR = some wrapFile := rfl

/-- C-level totality of the positive loop: with n ≤ 131071 every product and prefix sum is in int32 -/
theorem pos_loop_total {env : Env} (ha : Admitted env) (hn : env.n ≤ 131071) :
    ∀ (k i : Nat) (z u v : Int) (o : Option Int), i + k = env.n →
    -16256 * (i : Int) ≤ z → z ≤ 16384 * (i : Int) →
    ∃ z' u' v', loopK env posBody k i ⟨some z, some u, some v, o⟩ = some ⟨some z', some u', some v', o⟩
  | 0, i, z, u, v, o, hk, _, _ => by
    have : ¬ i < env.n := by omega
    exact ⟨z, u, v, by simp [loopK, this]⟩
  | k + 1, i, z, u, v, o, hk, h1, h2 => by
    have hi : i < env.n := by omega
    have hia : i < env.a.length := by have := ha.2.2.1; omega
    have hib : i < env.b.length := by have := ha.2.2.2.1; omega
    have hx8 := ha.1 _ (List.getElem_mem hia)
    have hy8 := ha.2.1 _ (List.getElem_mem hib)
    have hp := prod_bound _ _ hx8 hy8
    have hm : inI32 (env.a[i] * env.b[i]) := by unfold inI32; omega
    have hs : inI32 (z + env.a[i] * env.b[i]) := by unfold inI32; omega
    obtain ⟨z', u', v', h'⟩ := pos_loop_total ha hn k (i + 1) (z + env.a[i] * env.b[i])
      (env.a[i] * env.b[i]) env.b[i] o (by omega) (by push_cast; omega) (by push_cast; omega)
    refine ⟨z', u', v', ?_⟩
    simp [loopK, hi, posBody, C.execBody, execS, assign, evalE, i32op, CSt.get, CSt.set, Env.arr,
      List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib, hx8, hy8, hm, hs]
    exact h'

/-- C-level totality of the wrap loop: the accumulator stays in [-128, 127] -/
theorem wrap_loop_total {env : Env} (ha : Admitted env) :
    ∀ (k i : Nat) (z u v : Int) (o : Option Int), i + k = env.n → -128 ≤ z → z ≤ 127 →
    ∃ z' u' v', loopK env (posBody ++ wrapTail) k i ⟨some z, some u, some v, o⟩ = some ⟨some z', some u', some v', o⟩
  | 0, i, z, u, v, o, hk, _, _ => by
    have : ¬ i < env.n := by omega
    exact ⟨z, u, v, by simp [loopK, this]⟩
  | k + 1, i, z, u, v, o, hk, h1, h2 => by
    have hi : i < env.n := by omega
    have hia : i < env.a.length := by have := ha.2.2.1; omega
    have hib : i < env.b.length := by have := ha.2.2.2.1; omega
    have hx8 := ha.1 _ (List.getElem_mem hia)
    have hy8 := ha.2.1 _ (List.getElem_mem hib)
    have hp := prod_bound _ _ hx8 hy8
    have hm : inI32 (env.a[i] * env.b[i]) := by unfold inI32; omega
    have hs : inI32 (z + env.a[i] * env.b[i]) := by unfold inI32; omega
    have hv := mask_eq (z + env.a[i] * env.b[i])
    have hle : (((z + env.a[i] * env.b[i]) % 256).toNat : Int) = (z + env.a[i] * env.b[i]) % 256 := by omega
    have hb : ((z + env.a[i] * env.b[i]) % 256).toNat ≤ 2147483647 := by omega
    by_cases hg : 127 < (z + env.a[i] * env.b[i]) % 256
    · have hs2 : inI32 ((z + env.a[i] * env.b[i]) % 256 - 256) := by unfold inI32; omega
      obtain ⟨z', u', v', h'⟩ := wrap_loop_total ha k (i + 1) ((z + env.a[i] * env.b[i]) % 256 - 256)
        (env.a[i] * env.b[i]) env.b[i] o (by omega) (by omega) (by omega)
      refine ⟨z', u', v', ?_⟩
      simp only [inI32] at hm hs hs2
      simp [loopK, hi, posBody, wrapTail, C.execBody, execS, assign, evalE, i32op, CSt.get, CSt.set, Env.arr,
        List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib, hx8, hy8, hm, hs, hv, hle, hb, hg, hs2, inI32]
      exact h'
    · obtain ⟨z', u', v', h'⟩ := wrap_loop_total ha k (i + 1) ((z + env.a[i] * env.b[i]) % 256)
        (env.a[i] * env.b[i]) env.b[i] o (by omega) (by omega) (by omega)
      refine ⟨z', u', v', ?_⟩
      simp only [inI32] at hm hs
      simp [loopK, hi, posBody, wrapTail, C.execBody, execS, assign, evalE, i32op, CSt.get, CSt.set, Env.arr,
        List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib, hx8, hy8, hm, hs, hv, hle, hb, hg, inI32]
      exact h'

theorem ir_pos_loop : ∀ (xs ys tin : List Int) (s : IR.St),
    (IR.runLoop [.LdA, .LdB, .Mul, .Acc] xs ys tin s).acc = s.acc + refDot xs ys
  | [], _, _, s => by simp [IR.runLoop, refDot]
  | _ :: _, [], _, s => by simp [IR.runLoop, refDot]
  | x :: xs, y :: ys, tin, s => by
    simp [IR.runLoop, IR.execBody, IR.exec, refDot, ir_pos_loop xs ys, Int.add_assoc]

/-- IR-model exactness (Lean mirror of the Bend `exact` law) -/
theorem ir_pos_exact (xs ys : List Int) : (IR.run posIR xs ys).acc = refDot xs ys := by
  simp [IR.run, posIR, IR.runProg, IR.start, ir_pos_loop, IR.init]

theorem cRun_pos (env : Env) (out0 : Option Int) (ha : Admitted env) :
    cRun posFile env out0 = if 131071 < env.n then .ret (-1) out0
      else .ret 0 (some (refDot (env.a.take env.n) (env.b.take env.n))) := by
  have hs := sound_render posIR posFile rfl env out0 ha
  rw [show bound posIR = 131071 by decide] at hs
  by_cases hn : 131071 < env.n
  · simp [hn, hs.1 hn]
  · simp only [hn, if_false]
    have hnf : cRun posFile env out0 ≠ .fault := by
      obtain ⟨z', u', v', h'⟩ := pos_loop_total ha (by omega) env.n 0 0 0 0 out0 (by omega) (by simp) (by simp)
      simp [cRun, posFile, prologue, epilogue, execT, lookupDef, stdDirs, dirsFor, hn, CSt.get, CSt.set, inI32, runFor, h']
    rcases hs.2 (by omega) with h | h
    · exact absurd h hnf
    · rw [h, ir_pos_exact]

theorem cRun_wrap (env : Env) (out0 : Option Int) (ha : Admitted env) :
    cRun wrapFile env out0 = if 131071 < env.n then .ret (-1) out0
      else .ret 0 (some (IR.run wrapIR (env.a.take env.n) (env.b.take env.n)).acc) := by
  have hs := sound_render wrapIR wrapFile rfl env out0 ha
  rw [show bound wrapIR = 131071 by decide] at hs
  by_cases hn : 131071 < env.n
  · simp [hn, hs.1 hn]
  · simp only [hn, if_false]
    have hnf : cRun wrapFile env out0 ≠ .fault := by
      obtain ⟨z', u', v', h'⟩ := wrap_loop_total ha env.n 0 0 0 0 out0 (by omega) (by decide) (by decide)
      simp [cRun, wrapFile, prologue, epilogue, execT, lookupDef, stdDirs, dirsFor, hn, CSt.get, CSt.set, inI32, runFor, h']
    rcases hs.2 (by omega) with h | h
    · exact absurd h hnf
    · exact h


/-! ## Shared certificate (i8red): ONE induction for every certified exact reduction -/

/-- ops allowed in exact (non-wrapping, unbuffered) loop bodies -/
def exactOp : Op → Bool | .Wrap => false | .StT => false | .LdT => false | _ => true

def RegsOK (s : IR.St) : Prop := inI32 s.r0 ∧ inI32 s.r1 ∧ inI32 s.acc

/-- every op is an exact op and every intermediate IR state has int32 registers -/
def BodyOK : List Op → Int → Int → Int → IR.St → Prop
  | [], _, _, _, _ => True
  | o :: r, x, y, t, s => exactOp o = true ∧ RegsOK (IR.exec o x y t s) ∧ BodyOK r x y t (IR.exec o x y t s)

theorem op_total {env : Env} {i : Nat} {x y t : Int} {out : Option Int} {st : CSt} {s : IR.St}
    (op : Op) (ss : List S) (hop : opS op = some ss) (hr : R out st s)
    (hx : env.a[i]? = some x) (hy : env.b[i]? = some y)
    (hx8 : -128 ≤ x ∧ x ≤ 127) (hy8 : -128 ≤ y ∧ y ≤ 127)
    (hex : exactOp op = true) (hok : RegsOK (IR.exec op x y t s)) :
    ∃ st', C.execBody env (some i) ss st = some st' ∧ R out st' (IR.exec op x y t s) := by
  rcases op_sim op ss hop hr hx hy hx8 hy8 with h | h
  · exfalso
    obtain ⟨ha, h0, h1, ho⟩ := hr
    obtain ⟨k0, k1, k2⟩ := hok
    cases op <;> simp only [opS, Option.some.injEq, reduceCtorEq] at hop <;> subst hop <;>
      simp only [exactOp, reduceCtorEq, Bool.false_eq_true] at hex <;> simp only [IR.exec] at k0 k1 k2
    all_goals (first
      | (by_cases hn : s.r0 < 0 <;> simp_all [C.execBody, execS, assign, evalE, i32op, CSt.get, Env.arr]) <;> done
      | (by_cases hn : s.r0 < 0 <;> simp_all [C.execBody, execS, assign, evalE, i32op, CSt.get, Env.arr, inI32]) <;> done
      | (by_cases hn : 0 < s.r0 <;> simp_all [C.execBody, execS, assign, evalE, i32op, CSt.get, Env.arr, inI32]) <;> done
      | (by_cases hn : s.r0 = 0 <;> simp_all [C.execBody, execS, assign, evalE, i32op, CSt.get, Env.arr, inI32]) <;> done)
  · obtain ⟨st', h1, h2⟩ := h; exact ⟨st', h1, h2⟩

theorem body_total {env : Env} {i : Nat} {x y t : Int} {out : Option Int}
    (hx : env.a[i]? = some x) (hy : env.b[i]? = some y)
    (hx8 : -128 ≤ x ∧ x ≤ 127) (hy8 : -128 ≤ y ∧ y ≤ 127) :
    ∀ (ops : List Op) (ss : List S) (st : CSt) (s : IR.St),
    renderOps ops = some ss → R out st s → BodyOK ops x y t s →
    ∃ st', C.execBody env (some i) ss st = some st' ∧ R out st' (IR.execBody ops x y t s)
  | [], ss, st, s, h, hr, _ => by
    simp [renderOps] at h; subst h; exact ⟨st, by simp [C.execBody], hr⟩
  | o :: r, ss, st, s, h, hr, hok => by
    simp only [renderOps] at h
    cases ho : opS o with
    | none => simp [ho] at h
    | some a =>
      cases hrr : renderOps r with
      | none => simp [ho, hrr] at h
      | some b =>
        simp [ho, hrr] at h; subst h
        rw [execBody_append]
        obtain ⟨st1, e1, r1⟩ := op_total o a ho hr hx hy hx8 hy8 hok.1 hok.2.1
        simp only [e1, Option.some_bind]
        exact body_total hx hy hx8 hy8 r b st1 _ hrr r1 hok.2.2

/-- a certificate: loop body, length guard N, element bound M with N*M ≤ INT32_MAX, the element
function f, and the per-element step facts (primitive expression semantics + bounds) -/
structure Cert where
  ops : List Op
  N : Nat
  M : Int
  f : Int → Int → Int
  hne : ops ≠ []
  hN : (N : Int) * M ≤ 2147483647
  hM : 0 ≤ M
  hacc : ∀ x y t (s : IR.St), (IR.execBody ops x y t s).acc = s.acc + f x y
  step : ∀ (x y t : Int) (s : IR.St), -128 ≤ x ∧ x ≤ 127 → -128 ≤ y ∧ y ≤ 127 → inI32 s.r1 →
    -2147483648 ≤ s.acc - M → s.acc + M ≤ 2147483647 →
    BodyOK ops x y t s ∧ inI32 (IR.execBody ops x y t s).r1 ∧ -M ≤ f x y ∧ f x y ≤ M

/-- the shared induction: for n ≤ N the C loop never faults and tracks the IR state; the accumulator
after i iterations lies in [-i*M, i*M] -/
theorem cert_loop (c : Cert) {env : Env} {out : Option Int} (ha : Admitted env) (hn : env.n ≤ c.N)
    (ss : List S) (hro : renderOps c.ops = some ss) :
    ∀ (k i : Nat) (st : CSt) (s : IR.St) (tin : List Int), i + k = env.n → R out st s → inI32 s.r1 →
    -((i : Int) * c.M) ≤ s.acc → s.acc ≤ (i : Int) * c.M →
    ∃ st', loopK env ss k i st = some st' ∧
      R out st' (IR.runLoop c.ops ((env.a.take env.n).drop i) ((env.b.take env.n).drop i) tin s)
  | 0, i, st, s, tin, hk, hrs, _, _, _ => by
    have : i = env.n := by omega
    subst this
    refine ⟨st, by simp [loopK], ?_⟩
    rw [drop_take_len]; simp only [IR.runLoop]; exact hrs
  | k + 1, i, st, s, tin, hk, hrs, hr1, hl, hu => by
    have hi : i < env.n := by omega
    have hia : i < env.a.length := by have := ha.2.2.1; omega
    have hib : i < env.b.length := by have := ha.2.2.2.1; omega
    have hta : i < (env.a.take env.n).length := by simp; omega
    have htb : i < (env.b.take env.n).length := by simp; omega
    have hx8 := ha.1 _ (List.getElem_mem hia)
    have hy8 := ha.2.1 _ (List.getElem_mem hib)
    have e1 : ((i : Int) + 1) * c.M = (i : Int) * c.M + c.M := by rw [Int.add_mul, Int.one_mul]
    have e2 : ((i : Int) + 1) * c.M ≤ (c.N : Int) * c.M := Int.mul_le_mul_of_nonneg_right (by omega) c.hM
    have hN := c.hN
    have hM := c.hM
    obtain ⟨hb, hr1', hf1, hf2⟩ := c.step env.a[i] env.b[i] (IR.hd tin) s hx8 hy8 hr1 (by omega) (by omega)
    have hacc := c.hacc env.a[i] env.b[i] (IR.hd tin) s
    rw [List.drop_eq_getElem_cons hta, List.drop_eq_getElem_cons htb]
    simp only [loopK, hi, if_true, IR.runLoop, List.getElem_take]
    obtain ⟨st1, e3, r3⟩ := body_total (List.getElem?_eq_getElem hia) (List.getElem?_eq_getElem hib)
      hx8 hy8 c.ops ss st s hro hrs hb
    simp only [e3, Option.some_bind]
    exact cert_loop c ha hn ss hro k (i + 1) st1 _ _ (by omega) r3 hr1' (by push_cast; omega) (by push_cast; omega)

/-- independent generic reduction reference: Σ f(a_i, b_i) over the shorter list -/
def refRed (g : Int → Int → Int) : List Int → List Int → Int
  | x :: xs, y :: ys => g x y + refRed g xs ys
  | _, _ => 0

theorem cert_loop_acc (c : Cert) : ∀ (xs ys tin : List Int) (s : IR.St),
    (IR.runLoop c.ops xs ys tin s).acc = s.acc + refRed c.f xs ys
  | [], _, _, s => by simp [IR.runLoop, refRed]
  | _ :: _, [], _, s => by simp [IR.runLoop, refRed]
  | x :: xs, y :: ys, tin, s => by
    simp only [IR.runLoop, refRed, cert_loop_acc c xs ys, c.hacc]; omega

theorem cert_run (c : Cert) (xs ys : List Int) : (IR.run [.Loop c.ops] xs ys).acc = refRed c.f xs ys := by
  simp [IR.run, IR.runProg, IR.start, cert_loop_acc, IR.init]

/-- shared totality + exactness for any certificate whose guard is the rendered `#define` -/
theorem cert_total (c : Cert) (f : CFile) (hr : render [.Loop c.ops] = some f)
    (hb : bound [.Loop c.ops] = c.N) (env : Env) (out0 : Option Int) (ha : Admitted env) :
    cRun f env out0 = if c.N < env.n then .ret (-1) out0
      else .ret 0 (some (refRed c.f (env.a.take env.n) (env.b.take env.n))) := by
  have hs := sound_render _ f hr env out0 ha
  rw [hb] at hs
  by_cases hn : c.N < env.n
  · simp [hn, hs.1 hn]
  · simp only [hn, if_false]
    obtain ⟨o, os, he⟩ : ∃ o os, c.ops = o :: os := by
      cases h : c.ops with
      | nil => exact absurd h c.hne
      | cons o os => exact ⟨o, os, rfl⟩
    cases hro : renderOps c.ops with
    | none =>
      rw [he] at hr hro; simp [render, mapO, renderPS, hro] at hr
    | some ss =>
      have hro' := hro
      rw [he] at hr hro' hb
      simp only [render, mapO, renderPS, hro', Option.bind_eq_bind, Option.some_bind, Option.map_eq_map,
        Functor.map, Option.map_some', pure, Option.some.injEq] at hr
      obtain ⟨st', h', hR⟩ := cert_loop c (out := out0) ha (by omega) ss hro env.n 0
        ⟨some 0, some 0, some 0, out0⟩ IR.init [] (by omega) ⟨rfl, rfl, rfl, rfl⟩ (by decide) (by simp [IR.init]) (by simp [IR.init])
      have hnf : cRun f env out0 ≠ .fault := by
        subst hr
        simp [cRun, prologue, epilogue, execT, lookupDef, dirsFor, hb, hn, CSt.get, CSt.set, inI32, runFor, h', hR.1]
      rcases hs.2 (by omega) with h | h
      · exact absurd h hnf
      · rw [h, cert_run]

/-- C + IR in one statement for a certified program `p = [.Loop c.ops]` -/
theorem cert_gate (c : Cert) (p : Prog) (hp : p = [.Loop c.ops]) (hb : bound p = c.N) {f : CFile}
    (hr : render p = some f) (env : Env) (out0 : Option Int) (ha : Admitted env) :
    cRun f env out0 = if bound p < env.n then .ret (-1) out0
      else .ret 0 (some (IR.run p (env.a.take env.n) (env.b.take env.n)).acc) := by
  subst hp; rw [cert_total c f hr hb env out0 ha, hb, cert_run]

theorem sq_bound (d : Int) (h : -255 ≤ d ∧ d ≤ 255) : 0 ≤ d * d ∧ d * d ≤ 65025 := by
  obtain ⟨h1, h2⟩ := h
  rcases Int.le_total 0 d with h0 | h0
  · exact ⟨Int.mul_nonneg h0 h0, by have := Int.mul_le_mul h2 h2 h0 (by decide); omega⟩
  · have h4 := Int.mul_le_mul (show -d ≤ 255 by omega) (show -d ≤ 255 by omega) (by omega) (by decide)
    have h3 := Int.mul_nonneg (show 0 ≤ -d by omega) (show 0 ≤ -d by omega)
    rw [Int.neg_mul_neg] at h4 h3; exact ⟨h3, by omega⟩

/-! ### the five certificates (only primitive expression semantics + bounds per kernel) -/

def certDot : Cert where
  ops := [.LdA, .LdB, .Mul, .Acc]
  N := 131071
  M := 16384
  f := fun x y => x * y
  hne := by simp
  hN := by omega
  hM := by omega
  hacc := by intro x y t s; simp [IR.execBody, IR.exec]
  step := by
    intro x y t s hx hy hr1 h1 h2
    have := prod_bound x y hx hy
    simp [BodyOK, RegsOK, IR.execBody, IR.exec, exactOp, inI32] at hr1 ⊢; omega

def certL1 : Cert where
  ops := [.LdA, .LdB, .Sub, .AbsT, .Acc]
  N := 8421504
  M := 255
  f := fun x y => if x - y < 0 then -(x - y) else x - y
  hne := by simp
  hN := by omega
  hM := by omega
  hacc := by intro x y t s; simp [IR.execBody, IR.exec]
  step := by
    intro x y t s hx hy hr1 h1 h2
    simp only [inI32] at hr1
    by_cases hd : x - y < 0 <;> simp [BodyOK, RegsOK, IR.execBody, IR.exec, exactOp, inI32, hd] <;> omega

def certL2 : Cert where
  ops := [.LdA, .LdB, .Sub, .Sq, .Acc]
  N := 33025
  M := 65025
  f := fun x y => (x - y) * (x - y)
  hne := by simp
  hN := by omega
  hM := by omega
  hacc := by intro x y t s; simp [IR.execBody, IR.exec]
  step := by
    intro x y t s hx hy hr1 h1 h2
    have := sq_bound (x - y) (by omega)
    simp [BodyOK, RegsOK, IR.execBody, IR.exec, exactOp, inI32] at hr1 ⊢; omega

/-- AbsT (C ternary) has the same IR meaning as Abs (C if-statement) on every state; the two C spellings stay distinct ops -/
theorem absT_eq_abs (x y t : Int) (s : IR.St) : IR.exec .AbsT x y t s = IR.exec .Abs x y t s := by
  simp [IR.exec]

/-- Ne0 (C `r0 != 0`) equals Abs followed by Bit on every state ... -/
theorem ne0_eq_bit_abs (x y t : Int) (s : IR.St) : IR.exec .Ne0 x y t s = IR.exec .Bit x y t (IR.exec .Abs x y t s) := by
  simp only [IR.exec]; congr 1; (repeat' split) <;> omega

/-- ... but Ne0 is NOT Bit alone: on a negative nonzero register Bit keeps r0, Ne0 yields 1 -/
theorem ne0_ne_bit : IR.exec .Ne0 0 0 0 ⟨-1, 0, 0, 0, []⟩ ≠ IR.exec .Bit 0 0 0 ⟨-1, 0, 0, 0, []⟩ := by
  simp [IR.exec]

def certHam : Cert where
  ops := [.LdA, .LdB, .Sub, .Ne0, .Acc]
  N := 2147483647
  M := 1
  f := fun x y => if x - y = 0 then 0 else 1
  hne := by simp
  hN := by omega
  hM := by omega
  hacc := by intro x y t s; simp [IR.execBody, IR.exec]
  step := by
    intro x y t s hx hy hr1 h1 h2
    simp only [inI32] at hr1
    by_cases hd : x - y = 0 <;> simp [BodyOK, RegsOK, IR.execBody, IR.exec, exactOp, inI32, hd] <;> omega

def certOsl : Cert where
  ops := [.LdA, .LdB, .Sub, .Pos, .Acc]
  N := 8421504
  M := 255
  f := fun x y => if x - y < 0 then 0 else x - y
  hne := by simp
  hN := by omega
  hM := by omega
  hacc := by intro x y t s; simp [IR.execBody, IR.exec]
  step := by
    intro x y t s hx hy hr1 h1 h2
    simp only [inI32] at hr1
    by_cases hd : x - y < 0 <;> simp [BodyOK, RegsOK, IR.execBody, IR.exec, exactOp, inI32, hd] <;> omega

/-- the guards are the largest n with n*M ≤ INT32_MAX for each element bound M -/
theorem guard_tight :
    (131071 : Int) * 16384 ≤ 2147483647 ∧ (131072 : Int) * 16384 > 2147483647 ∧
    (8421504 : Int) * 255 ≤ 2147483647 ∧ (8421505 : Int) * 255 > 2147483647 ∧
    (33025 : Int) * 65025 ≤ 2147483647 ∧ (33026 : Int) * 65025 > 2147483647 ∧
    (2147483647 : Int) * 1 ≤ 2147483647 ∧ (2147483648 : Int) * 1 > 2147483647 := by decide

/-- the element bounds are attained by admitted signed bytes -/
theorem elem_bound_attained :
    (-128 : Int) * -128 = 16384 ∧ (127 : Int) - -128 = 255 ∧ ((127 : Int) - -128) * (127 - -128) = 65025 ∧
    (if (127 : Int) = -128 then (0 : Int) else 1) = 1 ∧
    (if (127 : Int) - -128 < 0 then (0 : Int) else 127 - -128) = 255 := by decide

theorem bound_values : bound posIR = 131071 ∧ bound wrapIR = 131071 ∧ bound l1IR = 8421504 ∧
    bound l2IR = 33025 ∧ bound hamIR = 2147483647 ∧ bound oslIR = 8421504 := by decide

theorem refRed_dot : ∀ xs ys, refRed (fun x y => x * y) xs ys = refDot xs ys
  | x :: xs, y :: ys => by simp only [refRed, refDot, refRed_dot xs ys]
  | [], _ => by simp [refRed, refDot]
  | _ :: _, [] => by simp [refRed, refDot]
theorem refRed_l1 : ∀ xs ys, refRed (fun x y => if x - y < 0 then -(x - y) else x - y) xs ys = refL1 xs ys
  | x :: xs, y :: ys => by simp only [refRed, refL1, refRed_l1 xs ys]
  | [], _ => by simp [refRed, refL1]
  | _ :: _, [] => by simp [refRed, refL1]
theorem refRed_l2 : ∀ xs ys, refRed (fun x y => (x - y) * (x - y)) xs ys = refL2 xs ys
  | x :: xs, y :: ys => by simp only [refRed, refL2, refRed_l2 xs ys]
  | [], _ => by simp [refRed, refL2]
  | _ :: _, [] => by simp [refRed, refL2]

theorem refRed_ham : ∀ xs ys, refRed (fun x y => if x - y = 0 then 0 else 1) xs ys = refHam xs ys
  | x :: xs, y :: ys => by
    simp only [refRed, refHam, refRed_ham xs ys]; congr 1; (repeat' split) <;> omega
  | [], _ => by simp [refRed, refHam]
  | _ :: _, [] => by simp [refRed, refHam]
theorem refRed_osl : ∀ xs ys, refRed (fun x y => if x - y < 0 then 0 else x - y) xs ys = refOsl xs ys
  | x :: xs, y :: ys => by
    simp only [refRed, refOsl, refRed_osl xs ys]; congr 1; by_cases hd : x - y < 0 <;> simp only [hd, ↓reduceIte] <;> (repeat' split) <;> omega
  | [], _ => by simp [refRed, refOsl]
  | _ :: _, [] => by simp [refRed, refOsl]

/-- the independent exact reference selected by the exact program -/
def refOf (p : Prog) : List Int → List Int → Int :=
  if p = l1IR then refL1 else if p = l2IR then refL2 else if p = hamIR then refHam
  else if p = oslIR then refOsl else refDot

theorem ir_exact_run (p : Prog) (hp : exactCert p = true) (xs ys : List Int) :
    (IR.run p xs ys).acc = refOf p xs ys := by
  rcases exactCert_cases hp with rfl | rfl | rfl | rfl | rfl
  · have e : (IR.run posIR xs ys).acc = refDot xs ys := (cert_run certDot xs ys).trans (refRed_dot xs ys)
    rw [e]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]
  · have e : (IR.run l1IR xs ys).acc = refL1 xs ys := (cert_run certL1 xs ys).trans (refRed_l1 xs ys)
    rw [e]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]
  · have e : (IR.run l2IR xs ys).acc = refL2 xs ys := (cert_run certL2 xs ys).trans (refRed_l2 xs ys)
    rw [e]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]
  · have e : (IR.run hamIR xs ys).acc = refHam xs ys := (cert_run certHam xs ys).trans (refRed_ham xs ys)
    rw [e]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]
  · have e : (IR.run oslIR xs ys).acc = refOsl xs ys := (cert_run certOsl xs ys).trans (refRed_osl xs ys)
    rw [e]; simp [refOf, posIR, l1IR, l2IR, hamIR, oslIR]

/-- MATCH GATE for the wrap mutant: acceptance against a prog.bend whose term is `wrapIR` ⇒ the C text
is `wrapFile` and its C semantics equals the IR semantics of wrapIR on every admitted input (total) -/
theorem wrap_match_sound {cs bs : String} {ex : Bool} {p : Prog} (h : gate cs bs ex = .pass p)
    (hw : BendP.parseBend bs = .ok wrapIR) :
    C.parseFile cs = .ok wrapFile ∧ ∀ env out0, Admitted env →
      cRun wrapFile env out0 = if 131071 < env.n then .ret (-1) out0
        else .ret 0 (some (IR.run wrapIR (env.a.take env.n) (env.b.take env.n)).acc) := by
  obtain ⟨f, hf, -, hb, hr, -, -⟩ := gate_pass h
  rw [hw] at hb; cases hb
  rw [render_wrap] at hr; cases hr
  exact ⟨hf, cRun_wrap⟩

theorem wrapIR_ne_posIR : wrapIR ≠ posIR := by decide

/-- IR-model values at the Bend witnesses (compare: Bend REFUTE/demo give Z{0,124}, Z{7,26}, mats=2) -/
theorem ir_witness_wrap : (IR.run wrapIR [12] [11]).acc = -124 := by decide
theorem ir_witness_pos : (IR.run posIR [3, -5, 7] [-2, 4, 1]).acc = -19 := by decide
theorem ir_witness_buf_mats : (IR.run bufIR [1] [1]).mats = 2 := by decide
theorem ir_witness_buf_acc : (IR.run bufIR [3, -5, 7] [-2, 4, 1]).acc = -19 := by decide

/-- PUBLIC GUARANTEE (one theorem for both gates): if the executable gate used by `i8check` returns PASS
on the actual C text `cs` and prog.bend text `bs`, then the C text parses to `f`, prog.bend's term is
`p` (certified: posIR, wrapIR, l1IR, l2IR, hamIR, oslIR; exact gate: all but wrapIR), and on EVERY admitted
input the C-subset semantics of `f` does not fault: it returns -1 with `*out` unchanged when
n > bound p, and otherwise returns 0 with `*out` = the IR result of `p` on the first n elements. -/
theorem gate_total {cs bs : String} {ex : Bool} {p : Prog} (h : gate cs bs ex = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ BendP.parseBend bs = .ok p ∧ certified p = true ∧
      (ex = true → exactCert p = true) ∧
      ∀ env out0, Admitted env → cRun f env out0 = if bound p < env.n then .ret (-1) out0
        else .ret 0 (some (IR.run p (env.a.take env.n) (env.b.take env.n)).acc) := by
  obtain ⟨f, hf, -, hb, hr, hc, hx⟩ := gate_pass h
  refine ⟨f, hf, hb, hc, hx, fun env out0 ha => ?_⟩
  rcases certified_cases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_gate certDot posIR rfl (by decide) hr env out0 ha
  · rw [render_wrap] at hr; cases hr; rw [show bound wrapIR = 131071 by decide]; exact cRun_wrap env out0 ha
  · exact cert_gate certL1 l1IR rfl (by decide) hr env out0 ha
  · exact cert_gate certL2 l2IR rfl (by decide) hr env out0 ha
  · exact cert_gate certHam hamIR rfl (by decide) hr env out0 ha
  · exact cert_gate certOsl oslIR rfl (by decide) hr env out0 ha

/-- the exact gate never passes against a prog.bend term outside {posIR, l1IR, l2IR, hamIR, oslIR} (e.g. wrapIR) -/
theorem exact_gate_requires_exact {cs bs : String} {p q : Prog} (hb : BendP.parseBend bs = .ok q)
    (hq : exactCert q = false) : gate cs bs true ≠ .pass p := by
  intro h
  obtain ⟨-, -, -, hb', -, -, hp⟩ := gate_pass h
  rw [hb] at hb'; cases hb'
  rw [hp rfl] at hq; cases hq

theorem exactCert_wrap : exactCert wrapIR = false := by decide

/-- EXACT GATE (main theorem, i8red): if `i8check exact` accepts the actual C text `cs` against the
actual prog.bend text `bs`, then prog.bend is one of the five exact reductions (dot, L1, squared L2,
Hamming, one-sided L1),
and on every admitted input the C semantics never faults: it returns -1 leaving *out untouched when
n > bound p (131071 / 8421504 / 33025 / 2147483647 / 8421504), and otherwise returns 0 with *out = the independent exact
reference (refDot / refL1 / refL2 / refHam / refOsl) of the first n elements. -/
theorem exact_gate_sound {cs bs : String} {p : Prog} (h : gate cs bs true = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ BendP.parseBend bs = .ok p ∧
      (p = posIR ∨ p = l1IR ∨ p = l2IR ∨ p = hamIR ∨ p = oslIR) ∧
      ∀ env out0, Admitted env → cRun f env out0 = if bound p < env.n then .ret (-1) out0
        else .ret 0 (some (refOf p (env.a.take env.n) (env.b.take env.n))) := by
  obtain ⟨f, hf, hb, hc, hx, H⟩ := gate_total h
  have he := hx rfl
  refine ⟨f, hf, hb, exactCert_cases he, fun env out0 ha => ?_⟩
  rw [H env out0 ha, ir_exact_run p he]

/-- n = 0 corollary: an accepted exact kernel returns 0 with *out = 0 -/
theorem exact_gate_zero {cs bs : String} {p : Prog} (h : gate cs bs true = .pass p) :
    ∃ f, C.parseFile cs = .ok f ∧ ∀ (a b : List Int) out0, Admitted ⟨a, b, 0⟩ →
      cRun f ⟨a, b, 0⟩ out0 = .ret 0 (some 0) := by
  obtain ⟨f, hf, -, hp, H⟩ := exact_gate_sound h
  refine ⟨f, hf, fun a b out0 ha => ?_⟩
  rw [H _ out0 ha]
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [refOf, refDot, refL1, refL2, refHam, refOsl, posIR, l1IR, l2IR, hamIR, oslIR]

/-- the match gate never passes an uncertified prog.bend term -/
theorem gate_requires_certified {cs bs : String} {ex : Bool} {p q : Prog}
    (hb : BendP.parseBend bs = .ok q) (hq : certified q = false) : gate cs bs ex ≠ .pass p := by
  intro h
  obtain ⟨-, -, -, hb', -, hc, -⟩ := gate_pass h
  rw [hb] at hb'; cases hb'
  rw [hq] at hc; cases hc

theorem overflowIR_not_certified : certified overflowIR = false := by decide

/-- why certification is needed: the overflow program renders to valid C, and on an admitted in-range
input (n = 4) its C-subset semantics faults (signed overflow), so no total guarantee can hold for it -/
theorem overflow_faults :
    ∃ f, render overflowIR = some f ∧ Admitted ⟨[-128, 127, -128, 127], [-128, -128, 127, 127], 4⟩ ∧
      cRun f ⟨[-128, 127, -128, 127], [-128, -128, 127, 127], 4⟩ none = .fault :=
  ⟨_, rfl, by unfold Admitted; decide, by decide⟩

theorem zadd_val (a b : Nat × Nat) : zval (zadd a b) = zval a + zval b := by
  simp only [zval, zadd, Int.natCast_add]; omega

theorem zmul_val (a b : Nat × Nat) : zval (zmul a b) = zval a * zval b := by
  simp only [zval, zmul, Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]; omega

end Proofs
