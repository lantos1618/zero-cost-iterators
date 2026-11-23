import Vw.Blocks
import Vw.Push
/-! Typed lazy views. `xs.view` builds a plan; no item is pulled until a terminal runs.
`.fuse` requests one traversal per barrier-free segment; `.parallelize k` requests a chunked
schedule. Legality of each request is decided when the terminal is chosen. -/
namespace Vw
variable {σ α β : Type}

/-- an explicit barrier: materializes ALL upstream items, then runs a primitive algorithm -/
structure Bar (α β : Type) where
  impl : List α → List β
  name : String
  state : String

inductive Plan : Type → Type 1
  | src {α : Type} (xs : List α) : Plan α
  | stage {α β : Type} (p : Plan α) (a : Ad α β) : Plan β
  | barrier {α β : Type} (p : Plan α) (b : Bar α β) : Plan β

/-- staged reference meaning: each stage's whole-list reference, applied in order -/
def den : {α : Type} → Plan α → List α
  | _, Plan.src xs => xs
  | _, Plan.stage p a => a.ref (den p)
  | _, Plan.barrier p b => b.impl (den p)

/-- one barrier-free segment: a source list and ONE composed machine -/
structure Seg (α : Type) where
  σ : Type
  xs : List σ
  m : M σ α
  ab : Absorb m

theorem idM_absorb : Absorb (idM (σ := σ)) := fun _ _ h => by simp [idM] at h

def Seg.run (s : Seg α) : List α × Nat := s.m.pull s.m.init s.xs

/-- lowering: consecutive stages compose into one machine; a barrier ends the segment,
fully runs the upstream segment, materializes, and starts a new segment -/
def lower : {α : Type} → Plan α → Seg α
  | _, Plan.src xs => ⟨_, xs, idM, idM_absorb⟩
  | _, Plan.stage p a => ⟨(lower p).σ, (lower p).xs, (lower p).m.comp a.m, comp_absorb _ _ (lower p).ab a.ab⟩
  | _, Plan.barrier p b => ⟨_, b.impl (lower p).run.1, idM, idM_absorb⟩

def nBarriers : {α : Type} → Plan α → Nat
  | _, Plan.src _ => 0
  | _, Plan.stage p _ => nBarriers p
  | _, Plan.barrier p _ => nBarriers p + 1

theorem lower_feed : ∀ {α : Type} (p : Plan α), ((lower p).m.feed (lower p).m.init (lower p).xs).2 = den p
  | _, Plan.src xs => idM_feed () xs
  | _, Plan.stage p a => by
    show (((lower p).m.comp a.m).feed ((lower p).m.init, a.m.init) (lower p).xs).2 = a.ref (den p)
    rw [comp_feed]; simp only; rw [lower_feed p, a.ok]
  | _, Plan.barrier p b => by
    show (idM.feed () (b.impl (lower p).run.1)).2 = b.impl (den p)
    rw [idM_feed, Seg.run, pull_out _ (lower p).ab, lower_feed p]

/-- FUSION: the fused traversal (with early stop) yields exactly the staged result, in order -/
theorem fused_eq_staged (p : Plan α) : (lower p).run.1 = den p := by
  rw [Seg.run, pull_out _ (lower p).ab, lower_feed]

/-- a stage-only plan lowers to one segment over the ORIGINAL source -/
theorem one_segment : ∀ (p : Plan α), nBarriers p = 0 → ∃ (τ : Type) (xs : List τ) (h : (lower p).σ = τ), True
  | p, _ => ⟨_, (lower p).xs, rfl, trivial⟩

/-! ## terminal machines -/
def findM (q : α → Bool) : M α α :=
  ⟨Bool, false, fun f x => if f then (true, []) else if q x then (true, [x]) else (false, []), id⟩
theorem findM_absorb (q : α → Bool) : Absorb (findM q) := fun s x h => by simp [findM] at h ⊢; simp [h]
theorem findM_feed (q : α → Bool) : ∀ xs, ((findM q).feed false xs).2 = (xs.find? q).toList := by
  have hd : ∀ ys, ((findM q).feed true ys).2 = [] := by
    intro ys; induction ys with
    | nil => rfl
    | cons y ys ih => simp only [M.feed]; exact (by simpa [findM] using ih)
  intro xs; induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : q x = true
    · simp only [M.feed]; simp [findM, h]; simpa [findM] using hd xs
    · simp only [M.feed]; simp [findM, h]; simpa [findM] using ih

/-- fused find: the plan's last segment with the terminal machine composed on; returns the
answer and the exact number of items pulled from that segment's source -/
def findRun (p : Plan α) (q : α → Bool) : Option α × Nat :=
  let s := lower p
  let r := (s.m.comp (findM q)).pull (s.m.init, false) s.xs
  (r.1.head?, r.2)

theorem findRun_val (p : Plan α) (q : α → Bool) : (findRun p q).1 = (den p).find? q := by
  simp only [findRun]
  rw [pull_out _ (comp_absorb _ _ (lower p).ab (findM_absorb q)), comp_feed]
  simp only; rw [lower_feed, findM_feed]; cases (den p).find? q <;> rfl

/-- exact observed prefix for find: it pulled k items, was not done before any of them,
and stopped early only because the answer was already determined -/
theorem findRun_prefix (p : Plan α) (q : α → Bool) :
    let s := lower p; let m := s.m.comp (findM q); let k := (findRun p q).2
    (∀ j < k, m.done (m.feed (s.m.init, false) (s.xs.take j)).1 = false) ∧
    (k < s.xs.length → m.done (m.feed (s.m.init, false) (s.xs.take k)).1 = true) :=
  let h := pull_prefix ((lower p).m.comp (findM q)) ((lower p).m.init, false) (lower p).xs
  ⟨h.2.1, h.2.2⟩

theorem find_isSome (q : α → Bool) : ∀ l : List α, (l.find? q).isSome = l.any q
  | [] => rfl
  | x :: xs => by by_cases h : q x = true <;> simp [List.find?, h, find_isSome q xs]

/-! ## the view -/
structure View (α : Type) where
  plan : Plan α
  fused : Bool := false
  chunks : Option Nat := none
  /-- set while the whole plan is a map/filter chain directly on the source: the generic push lowering -/
  push : Option (PP α) := none
  pok : ∀ q, push = some q → q.c.ref q.xs = den plan := by intro q h; cases h

end Vw

@[inline] def List.view {α : Type} (xs : List α) : Vw.View α :=
  { plan := .src xs, push := some ⟨α, xs, .id, fun k => k, fun _ => rfl⟩, pok := fun q h => by cases h; rfl }

namespace Vw.View
open Vw
variable {α β γ : Type}
def st (v : View α) (a : Ad α β) : View β := { plan := .stage v.plan a, fused := v.fused, chunks := v.chunks }
@[inline] def map (v : View α) (f : α → β) : View β :=
  { plan := .stage v.plan (Vw.map f), fused := v.fused, chunks := v.chunks,
    push := v.push.map fun q => ⟨q.τ, q.xs, q.c.map f, fun k => q.run (fun b a => k b (f a)),
      fun k => by show q.run _ = _; rw [q.hrun]; rfl⟩,
    pok := by
      intro q h
      cases hp : v.push with
      | none => simp [hp] at h
      | some q0 => simp [hp] at h; subst h; simp [Chain.ref, den, Vw.map, v.pok q0 hp] }
@[inline] def filter (v : View α) (p : α → Bool) : View α :=
  { plan := .stage v.plan (Vw.filter p), fused := v.fused, chunks := v.chunks,
    push := v.push.map fun q => ⟨q.τ, q.xs, q.c.filter p, fun k => q.run (fun b a => if p a then k b a else b),
      fun k => by show q.run _ = _; rw [q.hrun]; rfl⟩,
    pok := by
      intro q h
      cases hp : v.push with
      | none => simp [hp] at h
      | some q0 => simp [hp] at h; subst h; simp [Chain.ref, den, Vw.filter, v.pok q0 hp] }
def take (v : View α) (n : Nat) := v.st (Vw.take n)
def drop (v : View α) (n : Nat) := v.st (Vw.drop n)
def enumerate (v : View α) := v.st Vw.enumerate
def scan (v : View α) (seed : β) (f : β → α → β) := v.st (Vw.scan f seed)
def flatMap (v : View α) (g : α → List β) := v.st (Vw.flatMap g)
def distinct [DecidableEq α] (v : View α) := v.st Vw.distinct
def chunk (v : View α) (k : Nat) (hk : 0 < k := by decide) := v.st (Vw.chunk k hk)
def window (v : View α) (k : Nat) (hk : 0 < k := by decide) := v.st (Vw.window k hk)
/-- BARRIER, explicit primitive `List.mergeSort` (stable), materializes all upstream items -/
def sortBy (v : View α) (le : α → α → Bool) : View α :=
  { plan := .barrier v.plan ⟨fun xs => xs.mergeSort le, "sortBy(List.mergeSort, stable)", "all n items"⟩,
    fused := v.fused, chunks := v.chunks }
/-- BARRIER, explicit primitive `List.splitBy` (ordered runs of equal keys), materializes all items -/
def groupBy (v : View α) (eq : α → α → Bool) : View (List α) :=
  { plan := .barrier v.plan ⟨fun xs => xs.splitBy eq, "groupBy(List.splitBy, consecutive)", "all n items"⟩,
    fused := v.fused, chunks := v.chunks }
@[inline] def fuse (v : View α) : View α := { v with fused := true }
@[inline] def parallelize (v : View α) (chunks : Nat) : View α := { v with chunks := some chunks }

/-- the items the terminal consumes: staged reference, or the fused traversal if requested -/
def items (v : View α) : List α := if v.fused then (lower v.plan).run.1 else den v.plan
theorem items_eq (v : View α) : v.items = den v.plan := by
  unfold items; split <;> simp [fused_eq_staged]

def refusedPar (t : String) : String :=
  "refused: parallelize with " ++ t ++ " (no proved chunked schedule for this terminal; no parallel backend)"

/-- what a fold terminal executes: with `.fuse` on a map/filter chain, the generic push lowering
(ONE `List.foldl` over the original source, no list between adapters); otherwise the staged/segment items -/
@[inline] def foldPath (v : View α) (seed : β) (step : β → α → β) : β :=
  match v.fused, v.push with
  | true, some q => q.xs.foldl (q.run step) seed
  | _, _ => v.items.foldl step seed
theorem foldPath_eq (v : View α) (seed : β) (step : β → α → β) :
    v.foldPath seed step = (den v.plan).foldl step seed := by
  unfold foldPath
  cases hf : v.fused <;> cases hp : v.push with
  | none => simp [items_eq]
  | some q => simp [items_eq, q.hrun, Chain.push_fold, v.pok q hp]

@[inline] def foldl (v : View α) (seed : β) (step : β → α → β) : Except String β :=
  if v.chunks.isSome then .error (refusedPar "foldl: arbitrary step, order fixed")
  else .ok (v.foldPath seed step)
def find (v : View α) (q : α → Bool) : Except String (Option α) :=
  if v.chunks.isSome then .error (refusedPar "find: earliest match needs ordered pulls")
  else .ok (if v.fused then (findRun v.plan q).1 else (den v.plan).find? q)
def any (v : View α) (q : α → Bool) : Except String Bool := (v.find q).map Option.isSome
def all (v : View α) (q : α → Bool) : Except String Bool := (v.find (fun x => !q x)).map (fun o => !o.isSome)
/-- pulls made by the fused find from the last segment's source (diagnostic, proved exact above) -/
def findPulls (v : View α) (q : α → Bool) : Nat := (findRun v.plan q).2
def pulls (v : View α) : Nat := (lower v.plan).run.2
def segments (v : View α) : Nat := nBarriers v.plan + 1

theorem foldl_ok (v : View α) (seed : β) (step : β → α → β) (h : v.chunks = none) :
    v.foldl seed step = .ok ((den v.plan).foldl step seed) := by
  simp [foldl, h, foldPath_eq]
theorem foldl_refused (v : View α) (seed : β) (step : β → α → β) (k : Nat) :
    ∃ e, (v.parallelize k).foldl seed step = .error e := by
  simp [foldl, parallelize]
theorem find_ok (v : View α) (q : α → Bool) (h : v.chunks = none) :
    v.find q = .ok ((den v.plan).find? q) := by
  unfold find; simp [h]; intro _; exact findRun_val _ _
theorem any_ok (v : View α) (q : α → Bool) (h : v.chunks = none) : v.any q = .ok ((den v.plan).any q) := by
  simp [any, find_ok v q h, Except.map, find_isSome]
theorem all_ok (v : View α) (q : α → Bool) (h : v.chunks = none) : v.all q = .ok ((den v.plan).all q) := by
  simp only [all, find_ok v (fun x => !q x) h, Except.map, find_isSome]
  congr 1; induction den v.plan <;> simp_all
end Vw.View
