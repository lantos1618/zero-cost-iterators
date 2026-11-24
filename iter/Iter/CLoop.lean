import Iter.Gen

/-! # The lane loop exactly as the printed C++ runs it

`Loop.run` (proved equal to the `Iter` chain by `opt_correct`) sends item `j` to lane `j % lanes` by
rotating a list. The printed C++ does something else: full rounds of `n` items with an inner `j` loop,
then a tail loop using `i % n`, then a sum over the lane array. `Loop.cRun` models that control flow one
C++ loop per Lean function, and `cRun_eq` proves it computes `Loop.run`. What stays trusted after this is
the 1:1 text of each line (`Loop.toCpp`), the per-constructor `E.toCpp`/`P.toCpp`, and GCC. -/

namespace Iter.Gen
open Iter Iter.Rewrite

section
variable {α : Type} [Add α]

/-- `acc[l] += v` (or `acc[l] = op(acc[l], v)` with `op` as `+`) -/
def bump : List α → Nat → α → List α
  | [], _, _ => []
  | a :: as, 0, v => (a + v) :: as
  | a :: as, l + 1, v => a :: bump as l v

theorem bump_length : ∀ (acc : List α) (l : Nat) (v : α), (bump acc l v).length = acc.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, l + 1, v => by simp [bump, bump_length as l v]

theorem bump_sum [OfNat α 0] (h : AddLaws α) : ∀ (acc : List α) (l : Nat) (v : α), l < acc.length →
    sumL (bump acc l v) = sumL acc + v
  | [], _, _, hl => absurd hl (Nat.not_lt_zero _)
  | a :: as, 0, v, _ => by
    rw [bump, sumL_cons h, sumL_cons h, h.assoc, h.assoc, h.comm v]
  | a :: as, l + 1, v, hl => by
    rw [bump, sumL_cons h, sumL_cons h, bump_sum h as l v (by simp at hl; omega), h.assoc]
end

section
variable {β : Type} [Add β] [OfNat β 0]

/-- `G` summed over indices `i, i+1, …, i+c-1` -/
def rs (G : Nat → β) (i c : Nat) : β := sumL ((List.range' i c).map G)

theorem rs_zero (G : Nat → β) (i : Nat) : rs G i 0 = 0 := rfl

theorem rs_succ (h : AddLaws β) (G : Nat → β) (i c : Nat) : rs G i (c + 1) = G i + rs G (i + 1) c := by
  rw [rs, List.range'_succ, List.map_cons, sumL_cons h]; rfl

theorem rs_add (h : AddLaws β) (G : Nat → β) : ∀ (a i b : Nat), rs G i (a + b) = rs G i a + rs G (i + a) b
  | 0, i, b => by rw [Nat.zero_add, rs_zero, h.zero_add, Nat.add_zero]
  | a + 1, i, b => by
    rw [Nat.add_right_comm, rs_succ h, rs_succ h, rs_add h G a (i + 1) b, h.assoc,
      show i + 1 + a = i + (a + 1) by omega]
end

/-! The three C++ loops of every printed lane loop. The loop state `σ` is whatever the body updates
(the lane array, plus `seen` for `min?`/`max?`); `st s lane t` is one body run on item `t`. -/

section
variable {σ : Type} (n size : Nat) (st : σ → Nat → Nat → σ)

/-- `for (std::size_t j = 0; j < n; ++j) { x = xs[i + j]; body(lane j) }` -/
def inner (i j : Nat) (s : σ) : σ :=
  if j < n then inner i (j + 1) (st s j (i + j)) else s
termination_by n - j

/-- `for (; i < size; ++i) { x = xs[i]; body(lane i % n) }` -/
def tail (i : Nat) (s : σ) : σ :=
  if i < size then tail (i + 1) (st s (i % n) i) else s
termination_by size - i

/-- `for (; i + n <= size; i += n) { inner }` then `tail`; the printers only use `n ≥ 1` -/
def rounds (i : Nat) (s : σ) : σ :=
  if _ : 0 < n ∧ i + n ≤ size then rounds (i + n) (inner n st i 0 s) else tail n size st i s
termination_by size - i
decreasing_by omega
end

/-- if one body run adds `G t` to a measure `F` of the state (for every lane `< n`, keeping `ok`), the
three loops add `G` over every index: lane order and loop shape do not matter -/
theorem rounds_spec {σ β : Type} [Add β] [OfNat β 0] (h : AddLaws β) (n size : Nat) (st : σ → Nat → Nat → σ)
    (ok : σ → Prop) (F : σ → β) (G : Nat → β)
    (hst : ∀ s l t, ok s → l < n → ok (st s l t) ∧ F (st s l t) = F s + G t) (hn : 0 < n) :
    ∀ (i : Nat) (s : σ), ok s → F (rounds n size st i s) = F s + rs G i (size - i) := by
  have hin : ∀ i d j s, n - j = d → ok s →
      ok (inner n st i j s) ∧ F (inner n st i j s) = F s + rs G (i + j) (n - j) := by
    intro i d
    induction d with
    | zero => intro j s hd hs; unfold inner; rw [if_neg (by omega), hd, rs_zero, add_zero h]; exact ⟨hs, rfl⟩
    | succ d ih =>
      intro j s hd hs
      unfold inner; rw [if_pos (by omega)]
      have ⟨o1, f1⟩ := hst s j (i + j) hs (by omega)
      have ⟨o2, f2⟩ := ih (j + 1) _ (by omega) o1
      refine ⟨o2, ?_⟩
      rw [f2, f1, show n - j = (n - (j + 1)) + 1 by omega, rs_succ h, h.assoc, show i + j + 1 = i + (j + 1) by omega]
  have htl : ∀ d i s, size - i = d → ok s → F (tail n size st i s) = F s + rs G i (size - i) := by
    intro d
    induction d with
    | zero => intro i s hd _; unfold tail; rw [if_neg (by omega), hd, rs_zero, add_zero h]
    | succ d ih =>
      intro i s hd hs
      unfold tail; rw [if_pos (by omega)]
      have ⟨o1, f1⟩ := hst s (i % n) i hs (Nat.mod_lt _ hn)
      rw [ih (i + 1) _ (by omega) o1, f1, show size - i = (size - (i + 1)) + 1 by omega, rs_succ h, h.assoc]
  have key : ∀ d i s, size - i = d → ok s → F (rounds n size st i s) = F s + rs G i (size - i) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro i s hd hs
      unfold rounds
      by_cases hc : 0 < n ∧ i + n ≤ size
      · rw [dif_pos hc]
        have ⟨o1, f1⟩ := hin i (n - 0) 0 s rfl hs
        rw [ih (size - (i + n)) (by omega) (i + n) _ rfl o1, f1, Nat.sub_zero, Nat.add_zero, h.assoc,
          ← rs_add h, show n + (size - (i + n)) = size - i by omega]
      · rw [dif_neg hc]; exact htl _ i s rfl hs
  exact fun i s hs => key _ i s rfl hs

/-- what the printed `Loop.toCpp` function computes, loop by loop: `n = max lanes 1` lanes, item value
`body & (0 - keep)` read as `x = xs[t]`, then `total = Σ acc`, then `total * scale` -/
def Loop.cRun (L : Loop) (k : UInt64) (xs : Array UInt64) : UInt64 :=
  let n := max L.lanes 1
  let g := fun t => let x := xs.getD t 0; sel (L.keep.eval k x) (L.body.eval k x)
  sumL (rounds n xs.size (fun acc l t => bump acc l (g t)) 0 (List.replicate n 0)) * L.scale.eval k 0

theorem range_getD_map {γ : Type} (f : UInt64 → γ) (xs : Array UInt64) :
    (List.range' 0 xs.size).map (fun t => f (xs.getD t 0)) = xs.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp at h1
    simp [List.getElem_range', Array.getD, h1]

/-- the C++ loop structure computes the proved loop -/
theorem cRun_eq (L : Loop) (k : UInt64) (xs : Array UInt64) : L.cRun k xs = L.run k xs := by
  rw [Loop.cRun, Loop.run, sum_lanes u64Laws]
  simp only
  rw [rounds_spec u64Laws _ _ (fun acc l t => bump acc l (sel (L.keep.eval k (xs.getD t 0)) (L.body.eval k (xs.getD t 0))))
      (fun s => s.length = max L.lanes 1) sumL (fun t => sel (L.keep.eval k (xs.getD t 0)) (L.body.eval k (xs.getD t 0)))
      (fun s l t hs hl => by simp only at hs ⊢; exact ⟨by rw [bump_length, hs], bump_sum u64Laws _ _ _ (by omega)⟩) (by omega) 0 _ (by simp),
    sumL_zeros u64Laws, u64Laws.zero_add, rs,
    Nat.sub_zero, range_getD_map (fun x => sel (L.keep.eval k x) (L.body.eval k x))]

/-- the printed loop structure computes the `Iter` chain, for every pipeline, lane count and input -/
theorem printed_correct (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q).cRun k xs = q.run k xs :=
  (cRun_eq _ k xs).trans (opt_correct lanes q k xs)

/-- the same for the generated `count` -/
theorem printed_count (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q.countPipe).cRun k xs = (q.count k xs).toUInt64 :=
  (cRun_eq _ k xs).trans (count_correct lanes q k xs)

/-! ## `min?` / `max?`: the lane array plus a `seen` word -/

def bor (a b : UInt64) : UInt64 := a ||| b

theorem orLaws : AddLaws (OpW bor 0) :=
  opLaws (fun a b c => UInt64.toBitVec_inj.1 (by simp [bor, BitVec.or_assoc]))
    (fun a b => UInt64.toBitVec_inj.1 (by simp [bor, BitVec.or_comm]))
    (fun a => UInt64.toBitVec_inj.1 (by simp [bor]))

/-- one body run of the printed `Pipe.toCppRed`:
`std::uint64_t b = keep; seen |= b; acc[lane] = op(acc[lane], body);` -/
def Pipe.cRedStep (r : Red) (q : Pipe) (k : UInt64) (xs : Array UInt64)
    (s : List (OpW r.op r.id) × UInt64) (l t : Nat) : List (OpW r.op r.id) × UInt64 :=
  let x := xs.getD t 0
  (bump s.1 l ⟨r.mask (q.keep.eval k x) (q.f.eval k x)⟩, s.2 ||| (if q.keep.eval k x then 1 else 0))

/-- lanes and `seen` after the three loops, from `acc[i] = id`, `seen = 0` -/
def Pipe.cRedState (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    List (OpW r.op r.id) × UInt64 :=
  rounds (max lanes 1) xs.size (q.cRedStep r k xs) 0 (List.replicate (max lanes 1) 0, 0)

/-- what the printed `Pipe.toCppRed` returns: `m = id; for (a : acc) m = op(m, a);`, then
`seen ? m : nullopt` -/
def Pipe.cRed (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) : Option UInt64 :=
  let s := q.cRedState r lanes k xs
  if s.2 != 0 then some (sumL s.1).v else none

theorem or_ones (p : UInt64 → Bool) : ∀ l : List UInt64,
    (sumL (l.map fun x => (⟨if p x then 1 else 0⟩ : OpW bor 0))).v = if l.any p then 1 else 0
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, sumL_cons orLaws]
    show bor _ (sumL (xs.map fun x => (⟨if p x then 1 else 0⟩ : OpW bor 0))).v = _
    rw [or_ones p xs, List.any_cons]
    cases p x <;> cases xs.any p <;> decide

theorem cRed_eq (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    q.cRed r lanes k xs = q.redRun r lanes k xs := by
  have hok : ∀ (s : List (OpW r.op r.id) × UInt64) l t, s.1.length = max lanes 1 →
      (q.cRedStep r k xs s l t).1.length = max lanes 1 := fun s l t hs => by
    simp only [Pipe.cRedStep]; rw [bump_length, hs]
  have h1 : sumL (q.cRedState r lanes k xs).1 =
      sumL (xs.toList.map fun x => (⟨r.mask (q.keep.eval k x) (q.f.eval k x)⟩ : OpW r.op r.id)) := by
    rw [Pipe.cRedState, rounds_spec r.laws _ _ _ (fun s => s.1.length = max lanes 1) (fun s => sumL s.1)
      (fun t => (⟨r.mask (q.keep.eval k (xs.getD t 0)) (q.f.eval k (xs.getD t 0))⟩ : OpW r.op r.id))
      (fun s l t hs hl => ⟨hok s l t hs, bump_sum r.laws _ _ _ (by rw [hs]; exact hl)⟩) (by omega) 0 _ (by simp),
      rs, Nat.sub_zero, range_getD_map (fun x => (⟨r.mask (q.keep.eval k x) (q.f.eval k x)⟩ : OpW r.op r.id))]
    show sumL (List.replicate _ 0) + _ = _
    rw [sumL_zeros r.laws, r.laws.zero_add]
  have h2 : (⟨(q.cRedState r lanes k xs).2⟩ : OpW bor 0) =
      sumL (xs.toList.map fun x => (⟨if q.keep.eval k x then 1 else 0⟩ : OpW bor 0)) := by
    rw [Pipe.cRedState, rounds_spec orLaws _ _ _ (fun s => s.1.length = max lanes 1)
      (fun s => (⟨s.2⟩ : OpW bor 0)) (fun t => (⟨if q.keep.eval k (xs.getD t 0) then 1 else 0⟩ : OpW bor 0))
      (fun s l t hs _ => ⟨hok s l t hs, rfl⟩) (by omega) 0 _ (by simp), rs, Nat.sub_zero,
      range_getD_map (fun x => (⟨if q.keep.eval k x then 1 else 0⟩ : OpW bor 0))]
    exact orLaws.zero_add _
  have hs : ((q.cRedState r lanes k xs).2 != 0) = xs.toList.foldl (fun s x => s || q.keep.eval k x) false := by
    rw [show (q.cRedState r lanes k xs).2 = _ from congrArg OpW.v h2, or_ones, foldl_or, Bool.false_or]
    cases xs.toList.any _ <;> decide
  simp only [Pipe.cRed, Pipe.redRun, hs, h1, sum_lanes r.laws]

/-- the printed `min?`/`max?` loop structure computes the `Iter` chain -/
theorem printed_red (r : Red) (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    q.cRed r lanes k xs = q.red r k xs :=
  (cRed_eq r lanes q k xs).trans (red_correct r lanes q k xs)

/-! ## Record summary: the printed `SPipe.toCpp` index loops -/

section
variable {ν : Type} (q : SPipe) (ps : List UInt64) (rows : Array (Row ν))

/-- `for (; i < n; ++i) { if (keep(es[i])) break; }`: the index it stops at -/
def SPipe.cFind (i : Nat) : Nat :=
  if h : i < rows.size then (if q.keep.eval ps rows[i].f then i else SPipe.cFind (i + 1)) else rows.size
termination_by rows.size - i

/-- `for (++i; i < n; ++i) { body(es[i]) }` with the masked body `step2` -/
def SPipe.cFold (i : Nat) (s : Summary (Row ν) UInt64) : Summary (Row ν) UInt64 :=
  if h : i < rows.size then SPipe.cFold (i + 1) (q.step2 ps s rows[i]) else s
termination_by rows.size - i

/-- what the printed `SPipe.toCpp` returns: empty `Summ` if the search reaches `n`, else the first kept row
seeds `cnt = 1, tot = pay, fp = lp = &row` and the masked loop runs over the rest -/
def SPipe.cRun : Summary ν UInt64 :=
  let i := q.cFind ps rows 0
  if h : i < rows.size then
    let s := q.cFold ps rows (i + 1) ⟨1, q.pay.eval ps rows[i].f, some rows[i], some rows[i]⟩
    ⟨s.count, s.total, s.first.map (·.label), s.last.map (·.label)⟩
  else ⟨0, 0, none, none⟩

theorem cFold_eq : ∀ d i s, rows.size - i = d → q.cFold ps rows i s = (rows.toList.drop i).foldl (q.step2 ps) s := by
  intro d
  induction d with
  | zero =>
    intro i s hd
    unfold SPipe.cFold
    rw [dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ d ih =>
    intro i s hd
    have hi : i < rows.size := by omega
    unfold SPipe.cFold
    rw [dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi), List.foldl_cons, Array.getElem_toList]
    exact ih (i + 1) _ (by omega)

theorem cFind_spec : ∀ d i, rows.size - i = d →
    (rows.toList.drop i).dropWhile (fun r => !q.keep.eval ps r.f) = rows.toList.drop (q.cFind ps rows i) := by
  intro d
  induction d with
  | zero =>
    intro i hd
    unfold SPipe.cFind
    rw [dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by simp)]; rfl
  | succ d ih =>
    intro i hd
    have hi : i < rows.size := by omega
    unfold SPipe.cFind
    rw [dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi), List.dropWhile_cons, Array.getElem_toList]
    by_cases hk : q.keep.eval ps rows[i].f
    · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (by simpa using (List.drop_eq_getElem_cons (l := rows.toList) (n := i) (by simpa using hi)).symm)
    · simp only [hk, Bool.not_false, ↓reduceIte]
      exact ih (i + 1) (by omega)

/-- the printed record loop structure computes the proved one-pass loop -/
theorem cRunS_eq : q.cRun ps rows = q.fast2 ps rows := by
  rw [SPipe.cRun, SPipe.fast2, ← List.drop_zero (l := rows.toList), cFind_spec q ps rows _ 0 rfl]
  simp only
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (by simpa using h), Array.getElem_toList, cFold_eq q ps rows _ _ _ rfl]
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simp; omega)]

/-- the printed record loop structure computes the `Iter` chain -/
theorem printed_summary : q.cRun ps rows = q.run ps rows :=
  (cRunS_eq q ps rows).trans (fast2_correct q ps rows)
end

/-- `Loop.toCppRange`: one accumulator over a range-for, either step form -/
def Loop.cRunR (L : Loop) (k : UInt64) (xs : Array UInt64) : UInt64 :=
  xs.toList.foldl (fun a x => a + sel (L.keep.eval k x) (L.body.eval k x)) 0 * L.scale.eval k 0

theorem cRunR_eq (L : Loop) (k : UInt64) (xs : Array UInt64) : L.cRunR k xs = L.run k xs := by
  rw [Loop.cRunR, Loop.run, sum_lanes u64Laws, sumL, List.foldl_map]

theorem printed_range (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q).cRunR k xs = q.run k xs :=
  (cRunR_eq _ k xs).trans (opt_correct lanes q k xs)

theorem printed_range_count (lanes : Nat) (q : Pipe) (k : UInt64) (xs : Array UInt64) :
    (opt lanes q.countPipe).cRunR k xs = (q.count k xs).toUInt64 :=
  (cRunR_eq _ k xs).trans ((cRun_eq _ k xs).symm.trans (printed_count lanes q k xs))


/-! ### printed expressions: each tree the printer emits means the proved value, and is never undefined -/

theorem u64_mod_zero (a : UInt64) : a % 0 = a := by
  cases a with | mk v => exact congrArg UInt64.mk BitVec.umod_zero

theorem u64_div_zero (a : UInt64) : a / 0 = 0 := by
  cases a with | mk v => exact congrArg UInt64.mk (BitVec.udiv_zero (x := v))

theorem band01 (a b : Bool) :
    ((if a = true then (1 : UInt64) else 0) &&& if b = true then 1 else 0) = if (a && b) = true then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-! ## Switching record summary: the printed `SPipe.toCppAdapt` loops

State: `(summary, index of lp, starts, prev)`. Each printed inner loop is one `cLoop` with its body. -/

abbrev AState (ν : Type) := Summary (Row ν) UInt64 × Nat × UInt64 × UInt64

section
variable {ν : Type} (q : SPipe) (ps : List UInt64) (rows : Array (Row ν))

/-- `for (; i < e; ++i) { body(i, es[i]) }` -/
def cLoop {σ : Type} (e : Nat) (f : Nat → Row ν → σ → σ) (i : Nat) (st : σ) : σ :=
  if h : i < e ∧ i < rows.size then cLoop e f (i + 1) (f i rows[i] st) else st
termination_by e - i

theorem cLoop_lt {σ : Type} (e : Nat) (f : Nat → Row ν → σ → σ) (i : Nat) (st : σ)
    (h1 : i < e) (h2 : i < rows.size) : cLoop rows e f i st = cLoop rows e f (i + 1) (f i rows[i] st) := by
  rw [cLoop, dif_pos ⟨h1, h2⟩]

theorem cLoop_ge {σ : Type} (e : Nat) (f : Nat → Row ν → σ → σ) (i : Nat) (st : σ)
    (h : ¬(i < e ∧ i < rows.size)) : cLoop rows e f i st = st := by
  rw [cLoop, dif_neg h]

/-- a loop whose body acts on a projection as `g` acts there -/
theorem cLoop_map {σ τ : Type} (p : σ → τ) (f : Nat → Row ν → σ → σ) (g : Nat → Row ν → τ → τ)
    (hf : ∀ i r st, p (f i r st) = g i r (p st)) (e : Nat) :
    ∀ d i st, e - i = d → p (cLoop rows e f i st) = cLoop rows e g i (p st) := by
  intro d
  induction d with
  | zero => intro i st hd; rw [cLoop_ge rows e f i st (by omega), cLoop_ge rows e g i _ (by omega)]
  | succ d ih =>
    intro i st hd
    by_cases h : i < rows.size
    · rw [cLoop_lt rows e f i st (by omega) h, cLoop_lt rows e g i _ (by omega) h, ← hf]
      exact ih (i + 1) _ (by omega)
    · rw [cLoop_ge rows e f i st (by omega), cLoop_ge rows e g i _ (by omega)]

/-- `for (; i < pe; ...)` then `for (; i < e; ...)` with the same body is one loop to `e` -/
theorem cLoop_trans {σ : Type} (g : Nat → Row ν → σ → σ) (pe e : Nat) (hpe : pe ≤ e) :
    ∀ d i st, pe - i = d → i ≤ pe → cLoop rows e g pe (cLoop rows pe g i st) = cLoop rows e g i st := by
  intro d
  induction d with
  | zero => intro i st hd hi; rw [cLoop_ge rows pe g i st (by omega), show pe = i by omega]
  | succ d ih =>
    intro i st hd hi
    by_cases h : i < rows.size
    · rw [cLoop_lt rows pe g i st (by omega) h, cLoop_lt rows e g i st (by omega) h]
      exact ih (i + 1) _ (by omega) (by omega)
    · rw [cLoop_ge rows pe g i st (by omega), cLoop_ge rows e g i st (by omega),
        cLoop_ge rows e g pe st (by omega)]

/-- masked body with the flip count: `k = keep; starts += k & ~prev; prev = k; cnt += 1 & m;
tot += pay & m; lp = k ? &e : lp` -/
def SPipe.aMaskC (i : Nat) (r : Row ν) (st : AState ν) : AState ν :=
  let k : UInt64 := if q.keep.eval ps r.f then 1 else 0
  (q.step2 ps st.1 r, if q.keep.eval ps r.f then i else st.2.1, st.2.2.1 + (k &&& ~~~st.2.2.2), k)

/-- masked body: `cnt += 1 & m; tot += pay & m; lp = k ? &e : lp` -/
def SPipe.aMask (i : Nat) (r : Row ν) (st : AState ν) : AState ν :=
  (q.step2 ps st.1 r, if q.keep.eval ps r.f then i else st.2.1, st.2.2)

/-- branchy body: `if (keep) { starts += lp + 1 != &e; cnt += 1; tot += pay; lp = &e; }` -/
def SPipe.aBr (i : Nat) (r : Row ν) (st : AState ν) : AState ν :=
  if q.keep.eval ps r.f then (q.stepB ps st.1 r, i, st.2.2.1 + (if st.2.1 + 1 ≠ i then 1 else 0), st.2.2.2)
  else st

/-- the block loop: `end = n - i > blk ? i + blk : n`; a masked block counts over its first `win` rows
then runs uncounted, a branchy block counts on kept rows; next block masked iff `starts * den > w` -/
def SPipe.aBlocks (blk win den : Nat) (i : Nat) (st : AState ν) (masked : Bool) : AState ν :=
  if h : i < rows.size then
    let e := if rows.size - i > max blk 1 then i + max blk 1 else rows.size
    let pe := if e - i > win then i + win else e
    let r : AState ν × Nat :=
      if masked then
        (cLoop rows e (q.aMask ps) pe
          (cLoop rows pe (q.aMaskC ps) i (st.1, st.2.1, 0, if st.2.1 + 1 = i then 1 else 0)), pe - i)
      else (cLoop rows e (q.aBr ps) i (st.1, st.2.1, 0, st.2.2.2), e - i)
    SPipe.aBlocks blk win den e r.1 (decide (r.1.2.2.1 * den.toUInt64 > r.2.toUInt64))
  else st
termination_by rows.size - i
decreasing_by split <;> omega

/-- what the printed `SPipe.toCppAdapt` returns -/
def SPipe.cAdapt (blk win den : Nat) : Summary ν UInt64 :=
  let i := q.cFind ps rows 0
  if h : i < rows.size then
    let st := q.aBlocks ps rows blk win den (i + 1)
      (⟨1, q.pay.eval ps rows[i].f, some rows[i], some rows[i]⟩, i, 0, 0) true
    ⟨st.1.count, st.1.total, st.1.first.map (·.label), st.1.last.map (·.label)⟩
  else ⟨0, 0, none, none⟩

theorem cFold_loop : ∀ d i s, rows.size - i = d →
    q.cFold ps rows i s = cLoop rows rows.size (fun _ r s => q.step2 ps s r) i s := by
  intro d
  induction d with
  | zero => intro i s hd; unfold SPipe.cFold; rw [dif_neg (by omega), cLoop_ge rows _ _ i s (by omega)]
  | succ d ih =>
    intro i s hd
    unfold SPipe.cFold
    rw [dif_pos (by omega), cLoop_lt rows _ _ i s (by omega) (by omega)]
    exact ih (i + 1) _ (by omega)

/-- whatever bodies the blocks pick, the summary part is the masked loop to the end -/
theorem aBlocks_fst (blk win den : Nat) : ∀ d i st m, rows.size - i = d →
    (q.aBlocks ps rows blk win den i st m).1 = cLoop rows rows.size (fun _ r s => q.step2 ps s r) i st.1 := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i st m hd
    by_cases h : i < rows.size
    · rw [SPipe.aBlocks, dif_pos h]
      simp only
      have he : i < (if rows.size - i > max blk 1 then i + max blk 1 else rows.size) ∧
          (if rows.size - i > max blk 1 then i + max blk 1 else rows.size) ≤ rows.size := by
        split <;> omega
      generalize (if rows.size - i > max blk 1 then i + max blk 1 else rows.size) = e at he ⊢
      have hp : i ≤ (if e - i > win then i + win else e) ∧ (if e - i > win then i + win else e) ≤ e := by
        split <;> omega
      generalize (if e - i > win then i + win else e) = pe at hp ⊢
      rw [ih (rows.size - e) (by omega) e _ _ rfl]
      cases m
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [cLoop_map rows Prod.fst (q.aBr ps) (fun _ r s => q.step2 ps s r)
          (fun i r st => by
            simp only [SPipe.aBr]; split
            · simp [stepB_step2]
            · rename_i hk; rw [← stepB_step2]; simp [SPipe.stepB, hk]) e _ i _ rfl]
        exact cLoop_trans rows _ e rows.size he.2 _ i _ rfl (by omega)
      · simp only [↓reduceIte]
        rw [cLoop_map rows Prod.fst (q.aMask ps) (fun _ r s => q.step2 ps s r) (fun _ _ _ => rfl) e _ pe _ rfl,
          cLoop_map rows Prod.fst (q.aMaskC ps) (fun _ r s => q.step2 ps s r) (fun _ _ _ => rfl) pe _ i _ rfl,
          cLoop_trans rows _ pe e hp.2 _ i _ rfl hp.1]
        exact cLoop_trans rows _ e rows.size he.2 _ i _ rfl (by omega)
    · rw [SPipe.aBlocks, dif_neg h, cLoop_ge rows _ _ i _ (by omega)]

/-- the printed switching loop structure computes the printed one-pass loop, for every block size, window
and threshold -/
theorem cAdapt_eq (blk win den : Nat) : q.cAdapt ps rows blk win den = q.cRun ps rows := by
  rw [SPipe.cAdapt, SPipe.cRun]
  simp only
  split
  · rw [aBlocks_fst q ps rows blk win den _ _ _ _ rfl, cFold_loop q ps rows _ _ _ rfl]
  · rfl

/-- the printed switching loop structure computes the `Iter` chain -/
theorem printed_adapt (blk win den : Nat) : q.cAdapt ps rows blk win den = q.run ps rows :=
  (cAdapt_eq q ps rows blk win den).trans (printed_summary q ps rows)
end

section exprs
open Iter.C
variable (env : Slot → UInt64)

theorem E.toC_eval (k x : UInt64) (hx : env .x = x) (hk : env .k = k) :
    ∀ e : E, e.toC.eval env = some (e.eval k x)
  | .x => by simp [E.toC, CE.eval, E.eval, hx]
  | .k => by simp [E.toC, CE.eval, E.eval, hk]
  | .lit n => by simp [E.toC, CE.eval, E.eval]
  | .add a b => by simp [E.toC, CE.eval, E.eval, Op.eval, E.toC_eval k x hx hk a, E.toC_eval k x hx hk b]
  | .mul a b => by simp [E.toC, CE.eval, E.eval, Op.eval, E.toC_eval k x hx hk a, E.toC_eval k x hx hk b]
  | .xor a b => by simp [E.toC, CE.eval, E.eval, Op.eval, E.toC_eval k x hx hk a, E.toC_eval k x hx hk b]
  | .mod a (.lit n) => by
    by_cases h : n = 0
    · subst h; simp [E.toC, E.eval, E.toC_eval k x hx hk a, u64_mod_zero]
    · simp [E.toC, CE.eval, E.eval, Op.eval, h, E.toC_eval k x hx hk a]
  | .mod a b => by
    have hb := E.toC_eval k x hx hk b
    have ha := E.toC_eval k x hx hk a
    by_cases h : b.eval k x = 0 <;> cases b <;>
      simp_all [E.toC, CE.eval, E.eval, Op.eval, u64_mod_zero]

theorem P.toC_eval (k x : UInt64) (hx : env .x = x) (hk : env .k = k) :
    ∀ p : P, p.toC.eval env = some (if p.eval k x then 1 else 0)
  | .eq a b => by
    simp [P.toC, CE.eval, P.eval, Op.eval, E.toC_eval env k x hx hk a, E.toC_eval env k x hx hk b]
  | .lt a b => by
    simp [P.toC, CE.eval, P.eval, Op.eval, E.toC_eval env k x hx hk a, E.toC_eval env k x hx hk b]
  | .and p q => by
    simp only [P.toC, CE.eval, P.eval, Op.eval, P.toC_eval k x hx hk p, P.toC_eval k x hx hk q]
    rw [band01]

theorem X.toC_eval (ps r : List UInt64) (hf : ∀ i, env (.fld i) = r.getD i 0)
    (hp : ∀ i, env (.prm i) = ps.getD i 0) : ∀ e : X, e.toC.eval env = some (e.eval ps r)
  | .fld i => by simp [X.toC, CE.eval, X.eval, hf]
  | .prm i => by simp [X.toC, CE.eval, X.eval, hp]
  | .lit n => by simp [X.toC, CE.eval, X.eval]
  | .add a b => by simp [X.toC, CE.eval, X.eval, Op.eval, X.toC_eval ps r hf hp a, X.toC_eval ps r hf hp b]
  | .mul a b => by simp [X.toC, CE.eval, X.eval, Op.eval, X.toC_eval ps r hf hp a, X.toC_eval ps r hf hp b]
  | .div a (.lit n) => by
    by_cases h : n = 0
    · subst h; simp [X.toC, CE.eval, X.eval, u64_div_zero]
    · simp [X.toC, CE.eval, X.eval, Op.eval, h, X.toC_eval ps r hf hp a]
  | .div a b => by
    have hb := X.toC_eval ps r hf hp b
    have ha := X.toC_eval ps r hf hp a
    by_cases h : b.eval ps r = 0 <;> cases b <;>
      simp_all [X.toC, CE.eval, X.eval, Op.eval, u64_div_zero]

theorem Q.toC_eval (ps r : List UInt64) (hf : ∀ i, env (.fld i) = r.getD i 0)
    (hp : ∀ i, env (.prm i) = ps.getD i 0) : ∀ q : Q, q.toC.eval env = some (if q.eval ps r then 1 else 0)
  | .ne0 a => by
    simp [Q.toC, CE.eval, Q.eval, Op.eval, X.toC_eval env ps r hf hp a]
  | .ge a b => by
    simp [Q.toC, CE.eval, Q.eval, Op.eval, X.toC_eval env ps r hf hp a, X.toC_eval env ps r hf hp b]
  | .and p q => by
    simp only [Q.toC, CE.eval, Q.eval, Op.eval, Q.toC_eval ps r hf hp p, Q.toC_eval ps r hf hp q]
    rw [band01]

/-- the printed word step `acc[l] += body & (0 - (uint64_t)keep)` adds `sel keep body` -/
theorem word_step (L : Loop) (k x : UInt64) (hx : env .x = x) (hk : env .k = k) :
    (maskC L.body.toC (.cast L.keep.toC)).eval env = some (sel (L.keep.eval k x) (L.body.eval k x)) := by
  simp [maskC, CE.eval, Op.eval, E.toC_eval env k x hx hk, P.toC_eval env k x hx hk, sel]

/-- the printed reduction steps, with `b = (uint64_t)keep` -/
theorem red_step (r : Red) (q : Pipe) (k x : UInt64) (hx : env .x = x) (hk : env .k = k)
    (hb : env .b = if q.keep.eval k x then 1 else 0) :
    (match r with | .min => minC q.f.toC (.var .b) | .max => maskC q.f.toC (.var .b)).eval env =
      some (r.mask (q.keep.eval k x) (q.f.eval k x)) := by
  cases r <;> simp [minC, maskC, CE.eval, Op.eval, E.toC_eval env k x hx hk, hb, Red.mask, selMin, sel]

/-- the printed record step: `kb = (uint64_t)keep` and `tot += pay & (0 - kb)` add `sel keep pay` -/
theorem rec_step (q : SPipe) (ps r : List UInt64) (hf : ∀ i, env (.fld i) = r.getD i 0)
    (hp : ∀ i, env (.prm i) = ps.getD i 0) (hb : env .b = if q.keep.eval ps r then 1 else 0) :
    (CE.cast q.keep.toC).eval env = some (if q.keep.eval ps r then 1 else 0) ∧
    (maskC q.pay.toC (.var .b)).eval env = some (sel (q.keep.eval ps r) (q.pay.eval ps r)) := by
  refine ⟨by simp [CE.eval, Q.toC_eval env ps r hf hp], ?_⟩
  simp [maskC, CE.eval, Op.eval, X.toC_eval env ps r hf hp, hb, sel]

end exprs

end Iter.Gen
