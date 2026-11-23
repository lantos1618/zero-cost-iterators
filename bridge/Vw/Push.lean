/-! Generic push (CPS) lowering of an ordered map/filter chain.
Source type `σ`, element type `α`, accumulator type `β` are ARBITRARY Lean types (strings, records, ...).
Callbacks are arbitrary pure total Lean functions; a closure's captured values are immutable by
construction. `Chain.ref` is the independent staged meaning (whole-list `List.map`/`List.filter`,
one intermediate list per adapter). `Chain.push` is the fused lowering: it only composes step
functions, so the fused fold is ONE `List.foldl` over the original source with no list built
between adapters. No associativity, commutativity or identity law is assumed for `step`. -/
namespace Vw

inductive Chain : Type → Type → Type 1
  | id {σ : Type} : Chain σ σ
  | map {σ α β : Type} (c : Chain σ α) (f : α → β) : Chain σ β
  | filter {σ α : Type} (c : Chain σ α) (p : α → Bool) : Chain σ α

namespace Chain
variable {σ α β γ : Type}

/-- staged reference: each adapter materializes its whole output list -/
def ref : {α : Type} → Chain σ α → List σ → List α
  | _, .id, xs => xs
  | _, .map c f, xs => (c.ref xs).map f
  | _, .filter c p, xs => (c.ref xs).filter p

/-- fused lowering: transform the terminal's step into a step over SOURCE items -/
def push : {α : Type} → Chain σ α → (β → α → β) → (β → σ → β)
  | _, .id, k => k
  | _, .map c f, k => c.push (fun b a => k b (f a))
  | _, .filter c p, k => c.push (fun b a => if p a then k b a else b)

theorem foldl_filter (p : α → Bool) (k : β → α → β) : ∀ (xs : List α) (b : β),
    xs.foldl (fun b a => if p a then k b a else b) b = (xs.filter p).foldl k b
  | [], _ => rfl
  | x :: xs, b => by by_cases h : p x = true <;> simp [List.filter_cons, h, foldl_filter p k xs]

/-- FUSION, generic: for every chain, every source list, every accumulator type, seed and step,
the single fused traversal equals the staged fold. -/
theorem push_fold : ∀ {α : Type} (c : Chain σ α) (k : β → α → β) (xs : List σ) (b : β),
    xs.foldl (c.push k) b = (c.ref xs).foldl k b
  | _, .id, _, _, _ => rfl
  | _, .map c f, k, xs, b => by simp only [push, ref, push_fold c, List.foldl_map]
  | _, .filter c p, k, xs, b => by simp only [push, ref, push_fold c, foldl_filter]

/-- callback-order witness: logging every step call in a list accumulator shows the terminal
step sees exactly the staged items, in staged order, once each -/
theorem push_trace (c : Chain σ α) (xs : List σ) :
    (xs.foldl (c.push (fun (l : List α) a => l ++ [a])) []) = c.ref xs := by
  rw [push_fold]
  suffices h : ∀ (ys acc : List α), ys.foldl (fun l a => l ++ [a]) acc = acc ++ ys by simpa using h _ []
  intro ys; induction ys with
  | nil => simp
  | cons y ys ih => intro acc; simp [ih]

/-- fused step on one source item: `step` is called at most once (map/filter emit ≤ 1 item) -/
def emits : {α : Type} → Chain σ α → σ → Option α
  | _, .id, x => some x
  | _, .map c f, x => (c.emits x).map f
  | _, .filter c p, x => (c.emits x).bind fun a => if p a then some a else none

theorem push_one : ∀ {α : Type} (c : Chain σ α) (k : β → α → β) (b : β) (x : σ),
    c.push k b x = match c.emits x with | some a => k b a | none => b
  | _, .id, _, _, _ => rfl
  | _, .map c f, k, b, x => by
    simp only [push, emits, push_one c]; cases c.emits x <;> rfl
  | _, .filter c p, k, b, x => by
    simp only [push, emits, push_one c]; cases c.emits x with
    | none => rfl
    | some a => by_cases h : p a = true <;> simp [h]

/-- a capture is just a closure argument: the theorem is the same for `f κ` and `p κ` with any
captured immutable value `κ` -/
theorem push_fold_capture {κ : Type} (cap : κ) (f : κ → σ → α) (p : κ → α → Bool) (k : β → α → β)
    (xs : List σ) (b : β) :
    xs.foldl (((Chain.id : Chain σ σ).map (f cap) |>.filter (p cap)).push k) b = ((xs.map (f cap)).filter (p cap)).foldl k b :=
  push_fold _ k xs b

end Chain

/-- a fusible map/filter prefix sitting directly on a source -/
structure PP (α : Type) where
  τ : Type
  xs : List τ
  c : Chain τ α
  /-- the same lowering as an inlineable closure, composed when the view is built; proved equal to
  `c.push`. At a call site whose adapters are inlined, the compiler sees concrete lambdas here -/
  run : {β : Type} → (β → α → β) → (β → τ → β)
  hrun : ∀ {β : Type} (k : β → α → β), run k = c.push k

end Vw
