/-!
# Zero-cost iterators: core

An `Iter α` is a polymorphic internal iterator: it is its own `for` loop. Adapters (`map`, `filter`,
`take`, `enumerate`) only wrap the loop body, so a whole chain is one loop over the source with no
intermediate collection. Callbacks run in any monad, so effects (state, `throw`) are allowed and are
sequenced exactly as in the staged list program.

`Denotes it l` says: running `it` with any body in any lawful monad is the same as running that body
over the list `l`, left to right, stopping at the first `.done`. Every source and adapter preserves
`Denotes`, so every chain gets its staged-list meaning by composition.
-/

structure Iter (α : Type) where
  fold : {m : Type → Type} → [Monad m] → {β : Type} → (β → α → m (ForInStep β)) → β → m β

namespace Iter

/-- reference semantics: run the body over list items left to right, stopping at the first `.done` -/
@[specialize] def lfold {m : Type → Type} [Monad m] {α β : Type} (k : β → α → m (ForInStep β)) :
    β → List α → m β
  | b, [] => pure b
  | b, x :: xs => do
    match ← k b x with
    | .done b => pure b
    | .yield b => lfold k b xs

/-- `it` behaves exactly like the list `l`, for every body, accumulator type and lawful monad -/
def Denotes {α : Type} (it : Iter α) (l : List α) : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] (β : Type) (k : β → α → m (ForInStep β)) (b : β),
    it.fold k b = lfold k b l

theorem lfold_forIn {m : Type → Type} [Monad m] {α δ : Type} (f : α → δ → m (ForInStep δ)) :
    ∀ (l : List α) (b : δ), lfold (fun b a => f a b) b l = forIn l b f
  | [], b => by simp [lfold]
  | x :: xs, b => by
    rw [List.forIn_cons]; simp only [lfold]
    refine congrArg (f x b >>= ·) (funext fun r => ?_)
    cases r with
    | done _ => rfl
    | yield b' => exact lfold_forIn f xs b'

/-! ## Sources -/

@[specialize] def arrLoop {m : Type → Type} [Monad m] {α β : Type} (a : Array α)
    (k : β → α → m (ForInStep β)) (i : Nat) (b : β) : m β :=
  if h : i < a.size then
    let j := i + 1
    do
    match ← k b a[i] with
    | .done b => pure b
    | .yield b => arrLoop a k j b
  else pure b
termination_by a.size - i

theorem arrLoop_eq {m : Type → Type} [Monad m] {α β : Type} (a : Array α) (k : β → α → m (ForInStep β)) :
    ∀ n i b, a.size - i = n → arrLoop a k i b = lfold k b (a.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i b h
    have hi : ¬ i < a.size := by omega
    unfold arrLoop
    rw [dif_neg hi, List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i b h
    have hi : i < a.size := by omega
    unfold arrLoop
    rw [dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [lfold, Array.getElem_toList]
    refine congrArg (k b a[i] >>= ·) (funext fun r => ?_)
    cases r with
    | done b' => rfl
    | yield b' => exact ih (i + 1) b' (by omega)

end Iter

@[inline] def List.iter {α : Type} (l : List α) : Iter α := ⟨fun k b => Iter.lfold k b l⟩
@[inline] def Array.iter {α : Type} (a : Array α) : Iter α := ⟨fun k b => Iter.arrLoop a k 0 b⟩

namespace Iter

theorem denotes_list {α : Type} (l : List α) : l.iter.Denotes l := fun _ _ _ _ _ _ => rfl

theorem denotes_array {α : Type} (a : Array α) : a.iter.Denotes a.toList := by
  intro m _ _ β k b
  show arrLoop a k 0 b = _
  rw [arrLoop_eq a k _ 0 b rfl, List.drop_zero]

/-! ## Adapters -/

@[inline] def map {α β : Type} (it : Iter α) (f : α → β) : Iter β :=
  ⟨fun k b => it.fold (fun b a => k b (f a)) b⟩

@[inline] def filter {α : Type} (it : Iter α) (p : α → Bool) : Iter α :=
  ⟨fun k b => it.fold (fun b a => if p a then k b a else pure (.yield b)) b⟩

@[macro_inline] def takeStep {m : Type → Type} [Monad m] {α δ : Type} (k : δ → α → m (ForInStep δ)) (n : Nat)
    (s : δ × Nat) (a : α) : m (ForInStep (δ × Nat)) := do
  match ← k s.1 a with
  | .done b => pure (.done (b, s.2))
  | .yield b => pure (if s.2 + 1 < n then .yield (b, s.2 + 1) else .done (b, s.2 + 1))

/-- first `n` items; stops pulling the source as soon as the `n`-th item is handled -/
@[inline] def take {α : Type} (it : Iter α) (n : Nat) : Iter α :=
  ⟨fun k b => if n = 0 then pure b else Prod.fst <$> it.fold (takeStep k n) (b, 0)⟩

@[macro_inline] def enumStep {m : Type → Type} [Monad m] {α δ : Type} (k : δ → Nat × α → m (ForInStep δ))
    (s : δ × Nat) (a : α) : m (ForInStep (δ × Nat)) :=
  match s with
  | (b, i) => do
    match ← k b (i, a) with
    | .done b => pure (.done (b, i + 1))
    | .yield b => pure (.yield (b, i + 1))

/-- pair each item with its 0-based position in this iterator -/
@[inline] def enumerate {α : Type} (it : Iter α) : Iter (Nat × α) :=
  ⟨fun k b => Prod.fst <$> it.fold (enumStep k) (b, 0)⟩

theorem lfold_map {m : Type → Type} [Monad m] {α β δ : Type} (k : δ → β → m (ForInStep δ)) (f : α → β) :
    ∀ (l : List α) b, lfold k b (l.map f) = lfold (fun b a => k b (f a)) b l
  | [], _ => rfl
  | x :: xs, b => by simp only [List.map_cons, lfold, lfold_map k f xs]

theorem lfold_filter {m : Type → Type} [Monad m] [LawfulMonad m] {α δ : Type} (k : δ → α → m (ForInStep δ))
    (p : α → Bool) : ∀ (l : List α) b,
    lfold k b (l.filter p) = lfold (fun b a => if p a then k b a else pure (.yield b)) b l
  | [], _ => rfl
  | x :: xs, b => by
    by_cases hp : p x <;> simp [List.filter_cons, hp, lfold, lfold_filter k p xs]

theorem lfold_take {m : Type → Type} [Monad m] [LawfulMonad m] {α δ : Type} (k : δ → α → m (ForInStep δ))
    (n : Nat) : ∀ (l : List α) (b : δ) (i : Nat), i < n →
    Prod.fst <$> lfold (takeStep k n) (b, i) l = lfold k b (l.take (n - i))
  | [], b, i, _ => by simp [lfold]
  | x :: xs, b, i, hi => by
    have e : n - i = (n - i - 1) + 1 := by omega
    rw [e, List.take_succ_cons]
    simp only [lfold, takeStep, bind_assoc, map_bind]
    refine congrArg (k b x >>= ·) (funext fun r => ?_)
    cases r with
    | done b' => simp
    | yield b' =>
      by_cases h : i + 1 < n
      · simp only [h, if_true, pure_bind]
        rw [lfold_take k n xs b' (i + 1) h, show n - (i + 1) = n - i - 1 by omega]
      · have h0 : n - i - 1 = 0 := by omega
        simp [h, h0, lfold]

theorem lfold_enum {m : Type → Type} [Monad m] [LawfulMonad m] {α δ : Type} (k : δ → Nat × α → m (ForInStep δ)) :
    ∀ (l : List α) (b : δ) (i : Nat), Prod.fst <$> lfold (enumStep k) (b, i) l = lfold k b (l.enumFrom i)
  | [], b, i => by simp [lfold]
  | x :: xs, b, i => by
    rw [List.enumFrom_cons]
    simp only [lfold, enumStep, bind_assoc, map_bind]
    refine congrArg (k b (i, x) >>= ·) (funext fun r => ?_)
    cases r <;> simp [lfold_enum k xs]

variable {α β : Type} {it : Iter α} {l : List α}

theorem Denotes.map (h : it.Denotes l) (f : α → β) : (it.map f).Denotes (l.map f) := by
  intro m _ _ δ k b
  show it.fold _ b = _
  rw [h, lfold_map]

theorem Denotes.filter (h : it.Denotes l) (p : α → Bool) : (it.filter p).Denotes (l.filter p) := by
  intro m _ _ δ k b
  show it.fold _ b = _
  rw [h, lfold_filter]

theorem Denotes.take (h : it.Denotes l) (n : Nat) : (it.take n).Denotes (l.take n) := by
  intro m _ _ δ k b
  show (if n = 0 then pure b else Prod.fst <$> it.fold (takeStep k n) (b, 0)) = _
  by_cases hn : n = 0
  · subst hn; simp [lfold]
  · rw [if_neg hn, h, lfold_take k n l b 0 (by omega), Nat.sub_zero]

theorem Denotes.enumerate (h : it.Denotes l) : it.enumerate.Denotes l.enum := by
  intro m _ _ δ k b
  show Prod.fst <$> it.fold (enumStep k) (b, 0) = _
  rw [h, lfold_enum]
  rfl

/-! ## Terminals (plain values; no `Except`, no flags) -/

@[inline] def foldl {δ : Type} (it : Iter α) (init : δ) (step : δ → α → δ) : δ :=
  Id.run (it.fold (m := Id) (fun b a => pure (.yield (step b a))) init)

/-- first item satisfying `p`; stops pulling at that item -/
@[inline] def find? (it : Iter α) (p : α → Bool) : Option α :=
  Id.run (it.fold (m := Id) (fun _ a => pure (if p a then .done (some a) else .yield none)) none)

instance {m : Type → Type} : ForIn m (Iter α) α where
  forIn it b f := it.fold (fun b a => f a b) b

theorem lfold_foldl {δ : Type} (step : δ → α → δ) : ∀ (l : List α) (b : δ),
    Id.run (lfold (m := Id) (fun b a => pure (.yield (step b a))) b l) = l.foldl step b
  | [], _ => rfl
  | x :: xs, b => lfold_foldl step xs (step b x)

theorem lfold_find (p : α → Bool) : ∀ (l : List α),
    Id.run (lfold (m := Id) (fun (_ : Option α) a => pure (if p a then .done (some a) else .yield none)) none l)
      = l.find? p
  | [] => rfl
  | x :: xs => by
    cases hp : p x
    · simp only [lfold, hp, List.find?_cons]; exact lfold_find p xs
    · simp only [lfold, hp, List.find?_cons]; rfl

theorem Denotes.foldl {δ : Type} (h : it.Denotes l) (init : δ) (step : δ → α → δ) :
    it.foldl init step = l.foldl step init := by
  unfold Iter.foldl; rw [h Id]; exact lfold_foldl step l init

theorem Denotes.find? (h : it.Denotes l) (p : α → Bool) : it.find? p = l.find? p := by
  unfold Iter.find?; rw [h Id]; exact lfold_find p l

/-- `for x in it do body` is `for x in l do body`, for any lawful monad (state, exceptions, IO-like) -/
theorem Denotes.forIn {m : Type → Type} [Monad m] [LawfulMonad m] {δ : Type} (h : it.Denotes l) (b : δ)
    (f : α → δ → m (ForInStep δ)) : ForIn.forIn it b f = ForIn.forIn l b f := by
  show it.fold _ b = _
  rw [h, lfold_forIn]

end Iter
