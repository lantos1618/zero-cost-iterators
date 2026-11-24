import Iter.Basic

/-!
# More adapters and terminals

`takeWhile`, `drop`, `dropWhile`, `zip` with an array, and the terminals `count`, `any`, `all`, `contains`, `min?`, `max?`.
Each adapter keeps at most a counter or a flag next to the accumulator, so a chain stays one loop with no
intermediate collection; each has a `Denotes` theorem giving its `List` meaning, effects and early exit
included. `any`, `all`, `contains` and `takeWhile` stop pulling the source as soon as the answer is known.
-/

namespace Iter

/-- items while `p` holds; stops pulling at the first item that fails `p` -/
@[inline] def takeWhile {α : Type} (it : Iter α) (p : α → Bool) : Iter α :=
  ⟨fun k b => it.fold (fun b a => if p a then k b a else pure (.done b)) b⟩

@[macro_inline] def dropStep {m : Type → Type} [Monad m] {α δ : Type} (k : δ → α → m (ForInStep δ)) (n : Nat)
    (s : δ × Nat) (a : α) : m (ForInStep (δ × Nat)) :=
  match s with
  | (b, i) =>
    if i < n then pure (.yield (b, i + 1)) else do
      match ← k b a with
      | .done b => pure (.done (b, i))
      | .yield b => pure (.yield (b, i))

/-- all but the first `n` items -/
@[inline] def drop {α : Type} (it : Iter α) (n : Nat) : Iter α :=
  ⟨fun k b => Prod.fst <$> it.fold (dropStep k n) (b, 0)⟩

@[macro_inline] def dropWhileStep {m : Type → Type} [Monad m] {α δ : Type} (k : δ → α → m (ForInStep δ))
    (p : α → Bool) (s : δ × Bool) (a : α) : m (ForInStep (δ × Bool)) :=
  match s with
  | (b, d) =>
    if d && p a then pure (.yield (b, true)) else do
      match ← k b a with
      | .done b => pure (.done (b, false))
      | .yield b => pure (.yield (b, false))

/-- items from the first one that fails `p` on -/
@[inline] def dropWhile {α : Type} (it : Iter α) (p : α → Bool) : Iter α :=
  ⟨fun k b => Prod.fst <$> it.fold (dropWhileStep k p) (b, true)⟩

section
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α δ : Type} (k : δ → α → m (ForInStep δ))

theorem lfold_takeWhile (p : α → Bool) : ∀ (l : List α) (b : δ),
    lfold (fun b a => if p a then k b a else pure (.done b)) b l = lfold k b (l.takeWhile p)
  | [], _ => rfl
  | x :: xs, b => by
    by_cases hp : p x
    · simp only [lfold, hp, ↓reduceIte, List.takeWhile_cons]
      refine congrArg (k b x >>= ·) (funext fun r => ?_)
      cases r with
      | done _ => rfl
      | yield b' => exact lfold_takeWhile p xs b'
    · simp [lfold, hp, List.takeWhile_cons]

theorem lfold_drop_ge (n : Nat) : ∀ (l : List α) (b : δ) (i : Nat), n ≤ i →
    Prod.fst <$> lfold (dropStep k n) (b, i) l = lfold k b l
  | [], b, i, _ => by simp [lfold]
  | x :: xs, b, i, hi => by
    simp only [lfold, dropStep, if_neg (Nat.not_lt.mpr hi), bind_assoc, map_bind]
    refine congrArg (k b x >>= ·) (funext fun r => ?_)
    cases r with
    | done b' => simp
    | yield b' => simp only [pure_bind]; exact lfold_drop_ge n xs b' i hi

theorem lfold_drop (n : Nat) : ∀ (l : List α) (b : δ) (i : Nat),
    Prod.fst <$> lfold (dropStep k n) (b, i) l = lfold k b (l.drop (n - i))
  | [], b, i => by simp [lfold]
  | x :: xs, b, i => by
    by_cases h : i < n
    · have e : n - i = (n - i - 1) + 1 := by omega
      rw [e, List.drop_succ_cons]
      simp only [lfold, dropStep, h, ↓reduceIte, pure_bind]
      rw [lfold_drop n xs b (i + 1), show n - (i + 1) = n - i - 1 by omega]
    · rw [show n - i = 0 by omega, List.drop_zero]
      exact lfold_drop_ge k n (x :: xs) b i (by omega)

theorem lfold_dropWhile_false (p : α → Bool) : ∀ (l : List α) (b : δ),
    Prod.fst <$> lfold (dropWhileStep k p) (b, false) l = lfold k b l
  | [], b => by simp [lfold]
  | x :: xs, b => by
    simp only [lfold, dropWhileStep, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, map_bind]
    refine congrArg (k b x >>= ·) (funext fun r => ?_)
    cases r with
    | done b' => simp
    | yield b' => simp only [pure_bind]; exact lfold_dropWhile_false p xs b'

theorem lfold_dropWhile (p : α → Bool) : ∀ (l : List α) (b : δ),
    Prod.fst <$> lfold (dropWhileStep k p) (b, true) l = lfold k b (l.dropWhile p)
  | [], b => by simp [lfold]
  | x :: xs, b => by
    by_cases hp : p x
    · simp only [lfold, dropWhileStep, Bool.true_and, hp, ↓reduceIte, pure_bind, List.dropWhile_cons]
      exact lfold_dropWhile p xs b
    · rw [List.dropWhile_cons, if_neg hp, ← lfold_dropWhile_false k p (x :: xs) b]
      simp [lfold, dropWhileStep, hp]
end

variable {α : Type} {it : Iter α} {l : List α}

theorem Denotes.takeWhile (h : it.Denotes l) (p : α → Bool) : (it.takeWhile p).Denotes (l.takeWhile p) := by
  intro m _ _ δ k b
  show it.fold _ b = _
  rw [h, lfold_takeWhile]

theorem Denotes.drop (h : it.Denotes l) (n : Nat) : (it.drop n).Denotes (l.drop n) := by
  intro m _ _ δ k b
  show Prod.fst <$> it.fold (dropStep k n) (b, 0) = _
  rw [h, lfold_drop, Nat.sub_zero]

theorem Denotes.dropWhile (h : it.Denotes l) (p : α → Bool) : (it.dropWhile p).Denotes (l.dropWhile p) := by
  intro m _ _ δ k b
  show Prod.fst <$> it.fold (dropWhileStep k p) (b, true) = _
  rw [h, lfold_dropWhile]

/-! ## zip with an array

An `Iter` runs its own loop, so two of them cannot be stepped in lockstep; `zip` pairs each item with the
array element at the same position, by index, and stops when either side runs out. -/

@[macro_inline] def zipStep {m : Type → Type} [Monad m] {α β δ : Type} (k : δ → α × β → m (ForInStep δ))
    (bs : Array β) (s : δ × Nat) (a : α) : m (ForInStep (δ × Nat)) :=
  match s with
  | (b, i) =>
    if h : i < bs.size then do
      match ← k b (a, bs[i]) with
      | .done b => pure (.done (b, i + 1))
      | .yield b => pure (.yield (b, i + 1))
    else pure (.done (b, i))

@[inline] def zip {β : Type} (it : Iter α) (bs : Array β) : Iter (α × β) :=
  ⟨fun k b => Prod.fst <$> it.fold (zipStep k bs) (b, 0)⟩

theorem lfold_zip {m : Type → Type} [Monad m] [LawfulMonad m] {β δ : Type} (k : δ → α × β → m (ForInStep δ))
    (bs : Array β) : ∀ (l : List α) (b : δ) (i : Nat),
    Prod.fst <$> lfold (zipStep k bs) (b, i) l = lfold k b (l.zip (bs.toList.drop i))
  | [], b, i => by simp [lfold]
  | x :: xs, b, i => by
    by_cases h : i < bs.size
    · rw [List.drop_eq_getElem_cons (by simpa using h), List.zip_cons_cons]
      simp only [lfold, zipStep, dif_pos h, bind_assoc, map_bind, Array.getElem_toList]
      refine congrArg (k b (x, bs[i]) >>= ·) (funext fun r => ?_)
      cases r with
      | done b' => simp
      | yield b' => simp only [pure_bind]; exact lfold_zip k bs xs b' (i + 1)
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.zip_nil_right]
      simp [lfold, zipStep, h]

theorem Denotes.zip {β : Type} (h : it.Denotes l) (bs : Array β) : (it.zip bs).Denotes (l.zip bs.toList) := by
  intro m _ _ δ k b
  show Prod.fst <$> it.fold (zipStep k bs) (b, 0) = _
  rw [h, lfold_zip, List.drop_zero]

/-! ## Terminals -/

@[inline] def count (it : Iter α) : Nat := it.foldl 0 fun n _ => n + 1

/-- is some item `p`? stops pulling at the first one -/
@[inline] def any (it : Iter α) (p : α → Bool) : Bool :=
  Id.run (it.fold (m := Id) (fun _ a => pure (if p a then .done true else .yield false)) false)

/-- is every item `p`? stops pulling at the first one that is not -/
@[inline] def all (it : Iter α) (p : α → Bool) : Bool :=
  Id.run (it.fold (m := Id) (fun _ a => pure (if p a then .yield true else .done false)) true)

@[inline] def contains [BEq α] (it : Iter α) (a : α) : Bool := it.any (· == a)

@[inline] def min? [Min α] (it : Iter α) : Option α :=
  it.foldl none fun o a => some (match o with | none => a | some b => min b a)

@[inline] def max? [Max α] (it : Iter α) : Option α :=
  it.foldl none fun o a => some (match o with | none => a | some b => max b a)

theorem foldl_count : ∀ (l : List α) (n : Nat), l.foldl (fun n _ => n + 1) n = n + l.length
  | [], _ => rfl
  | _ :: xs, n => by rw [List.foldl_cons, foldl_count xs, List.length_cons]; omega

theorem lfold_any (p : α → Bool) : ∀ l : List α,
    Id.run (lfold (m := Id) (fun (_ : Bool) a => pure (if p a then .done true else .yield false)) false l) = l.any p
  | [] => rfl
  | x :: xs => by
    cases hp : p x
    · simp only [lfold, hp, List.any_cons, Bool.false_or]; exact lfold_any p xs
    · simp only [lfold, hp, List.any_cons, Bool.true_or]; rfl

theorem lfold_all (p : α → Bool) : ∀ l : List α,
    Id.run (lfold (m := Id) (fun (_ : Bool) a => pure (if p a then .yield true else .done false)) true l) = l.all p
  | [] => rfl
  | x :: xs => by
    cases hp : p x
    · simp only [lfold, hp, List.all_cons, Bool.false_and]; rfl
    · simp only [lfold, hp, List.all_cons, Bool.true_and]; exact lfold_all p xs

theorem foldl_opt (f : α → α → α) : ∀ (l : List α) (b : α),
    l.foldl (fun o a => some (match o with | none => a | some b => f b a)) (some b) = some (l.foldl f b)
  | [], _ => rfl
  | x :: xs, b => foldl_opt f xs (f b x)

theorem Denotes.count (h : it.Denotes l) : it.count = l.length := by
  rw [Iter.count, h.foldl, foldl_count, Nat.zero_add]

theorem Denotes.any (h : it.Denotes l) (p : α → Bool) : it.any p = l.any p := by
  unfold Iter.any; rw [h Id]; exact lfold_any p l

theorem Denotes.all (h : it.Denotes l) (p : α → Bool) : it.all p = l.all p := by
  unfold Iter.all; rw [h Id]; exact lfold_all p l

theorem Denotes.contains [BEq α] (h : it.Denotes l) (a : α) : it.contains a = l.any (· == a) :=
  h.any _

theorem Denotes.min? [Min α] (h : it.Denotes l) : it.min? = l.min? := by
  rw [Iter.min?, h.foldl]
  cases l with
  | nil => rfl
  | cons x xs => exact foldl_opt min xs x

theorem Denotes.max? [Max α] (h : it.Denotes l) : it.max? = l.max? := by
  rw [Iter.max?, h.foldl]
  cases l with
  | nil => rfl
  | cons x xs => exact foldl_opt max xs x

end Iter
