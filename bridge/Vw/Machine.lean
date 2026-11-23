/-! Pull machines: the executable lowering of view adapters.
`feed` = push every input (no early stop); `pull` = the fused traversal, which checks `done`
BEFORE pulling the next source item and counts pulls. -/
namespace Vw

structure M (σ α : Type) where
  S : Type
  init : S
  step : S → σ → S × List α
  done : S → Bool

variable {σ α β : Type}

def M.feed (m : M σ α) : m.S → List σ → m.S × List α
  | s, [] => (s, [])
  | s, x :: xs => ((m.feed (m.step s x).1 xs).1, (m.step s x).2 ++ (m.feed (m.step s x).1 xs).2)

def M.pull (m : M σ α) : m.S → List σ → List α × Nat
  | _, [] => ([], 0)
  | s, x :: xs => if m.done s then ([], 0) else
      ((m.step s x).2 ++ (m.pull (m.step s x).1 xs).1, (m.pull (m.step s x).1 xs).2 + 1)

/-- once done, a machine emits nothing more and stays done -/
def Absorb (m : M σ α) : Prop := ∀ s x, m.done s = true → (m.step s x).2 = [] ∧ m.done (m.step s x).1 = true

theorem feed_done (m : M σ α) (h : Absorb m) : ∀ s xs, m.done s = true →
    (m.feed s xs).2 = [] ∧ m.done (m.feed s xs).1 = true
  | s, [], hs => ⟨rfl, hs⟩
  | s, x :: xs, hs => by
    obtain ⟨h1, h2⟩ := h s x hs
    obtain ⟨h3, h4⟩ := feed_done m h _ xs h2
    simp only [M.feed, h1, h3, h4, List.append_nil, and_self]

theorem feed_append (m : M σ α) : ∀ s l1 l2, m.feed s (l1 ++ l2) =
    ((m.feed (m.feed s l1).1 l2).1, (m.feed s l1).2 ++ (m.feed (m.feed s l1).1 l2).2)
  | s, [], l2 => by simp [M.feed]
  | s, x :: xs, l2 => by simp [M.feed, feed_append m _ xs l2, List.append_assoc]

/-- stopping early is unobservable in the output -/
theorem pull_out (m : M σ α) (h : Absorb m) : ∀ s xs, (m.pull s xs).1 = (m.feed s xs).2
  | _, [] => rfl
  | s, x :: xs => by
    by_cases hs : m.done s = true
    · simp [M.pull, hs, (feed_done m h s (x :: xs) hs).1]
    · simp [M.pull, hs, M.feed, pull_out m h _ xs]

/-- exact observed prefix: the fused run pulled exactly `k` items, its output is the feed of that prefix,
the machine was not done before any of those pulls, and it is done if it stopped early -/
theorem pull_prefix (m : M σ α) : ∀ s xs, let r := m.pull s xs;
    r.1 = (m.feed s (xs.take r.2)).2 ∧ (∀ j < r.2, m.done (m.feed s (xs.take j)).1 = false) ∧
    (r.2 < xs.length → m.done (m.feed s (xs.take r.2)).1 = true)
  | s, [] => by simp [M.pull, M.feed]
  | s, x :: xs => by
    by_cases hs : m.done s = true
    · simp [M.pull, hs, M.feed]
    · have ih := pull_prefix m (m.step s x).1 xs
      simp only [M.pull, hs, Bool.false_eq_true, if_false] at ih ⊢
      refine ⟨by simp [List.take_succ_cons, M.feed, ih.1], fun j hj => ?_, fun hl => ?_⟩
      · cases j with
        | zero => simpa [M.feed] using hs
        | succ j => simpa [List.take_succ_cons, M.feed] using ih.2.1 j (by omega)
      · simpa [List.take_succ_cons, M.feed] using ih.2.2 (by simp at hl; omega)

def M.comp (m1 : M σ α) (m2 : M α β) : M σ β where
  S := m1.S × m2.S
  init := (m1.init, m2.init)
  step := fun s x => (((m1.step s.1 x).1, (m2.feed s.2 (m1.step s.1 x).2).1), (m2.feed s.2 (m1.step s.1 x).2).2)
  done := fun s => m1.done s.1 || m2.done s.2

theorem comp_feed (m1 : M σ α) (m2 : M α β) : ∀ (s : m1.S × m2.S) xs,
    (m1.comp m2).feed s xs = (((m1.feed s.1 xs).1, (m2.feed s.2 (m1.feed s.1 xs).2).1), (m2.feed s.2 (m1.feed s.1 xs).2).2)
  | s, [] => by simp [M.feed]
  | s, x :: xs => by
    simp only [M.feed, comp_feed m1 m2 _ xs, feed_append]
    rfl

theorem comp_absorb (m1 : M σ α) (m2 : M α β) (h1 : Absorb m1) (h2 : Absorb m2) : Absorb (m1.comp m2) := by
  intro s x hs
  simp only [M.comp, Bool.or_eq_true] at hs ⊢
  rcases hs with hs | hs
  · obtain ⟨e, d⟩ := h1 s.1 x hs
    simp [e, M.feed, d]
  · obtain ⟨e, d⟩ := feed_done m2 h2 s.2 (m1.step s.1 x).2 hs
    simp [e, d]

end Vw
