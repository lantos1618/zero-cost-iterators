import Vw.Adapters
/-! Fixed-size blocks. Both drop an incomplete tail (stated policy). Buffered state: at most k-1 items. -/
namespace Vw
variable {σ : Type}

/-- chunk k: disjoint blocks, size k, stride k; reference by index arithmetic -/
def chunkRef (k : Nat) (xs : List σ) : List (List σ) :=
  (List.range (xs.length / k)).map fun i => (xs.drop (i * k)).take k
def chunkM (k : Nat) : M σ (List σ) :=
  ⟨List σ, [], fun buf x => if buf.length + 1 = k then ([], [buf ++ [x]]) else (buf ++ [x], []), fun _ => false⟩
theorem chunkM_step (k : Nat) (buf : List σ) x : (chunkM k).step buf x =
    if buf.length + 1 = k then ([], [buf ++ [x]]) else (buf ++ [x], []) := rfl

theorem chunkRef_short (k : Nat) (buf : List σ) (h : buf.length < k) : chunkRef k buf = [] := by
  simp [chunkRef, Nat.div_eq_of_lt h]
theorem chunkRef_block (k : Nat) (c ys : List σ) (hk : 0 < k) (hc : c.length = k) :
    chunkRef k (c ++ ys) = c :: chunkRef k ys := by
  have hl : (c ++ ys).length / k = ys.length / k + 1 := by
    simp only [List.length_append, hc]; rw [Nat.add_comm, Nat.add_div_right _ hk]
  rw [chunkRef, hl, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero, chunkRef]
  congr 1
  · simp [← hc]
  · apply List.map_congr_left; intro i _
    simp only [Function.comp_apply, Nat.succ_mul]
    rw [Nat.add_comm, ← List.drop_drop, List.drop_left' hc]

theorem chunkM_feed (k : Nat) (hk : 0 < k) : ∀ (buf xs : List σ), buf.length < k →
    ((chunkM k).feed buf xs).2 = chunkRef k (buf ++ xs) := by
  intro buf xs; induction xs generalizing buf with
  | nil => intro h; simp [M.feed, chunkRef_short k buf h]
  | cons x xs ih =>
    intro h
    by_cases he : buf.length + 1 = k
    · have e1 := ih [] (by simp; omega)
      simp only [M.feed, chunkM_step, he, if_true]
      rw [e1, List.nil_append, show buf ++ x :: xs = (buf ++ [x]) ++ xs by simp,
          chunkRef_block k _ _ hk (by simp [he])]
      rfl
    · simp only [M.feed, chunkM_step, he, if_false, List.nil_append]
      rw [ih _ (by simp; omega)]; simp

def chunk (k : Nat) (hk : 0 < k := by decide) : Ad σ (List σ) :=
  ⟨chunkM k, chunkRef k, fun xs => by simpa using chunkM_feed k hk [] xs (by simpa using hk),
   fun _ _ h => by simp [chunkM] at h, "chunk", "buffer of < k items"⟩

/-- window k: sliding, size k, stride 1; windows start at 0 .. len-k -/
def windowRef (k : Nat) (xs : List σ) : List (List σ) :=
  (List.range (xs.length + 1 - k)).map fun i => (xs.drop i).take k
def windowM (k : Nat) : M σ (List σ) :=
  ⟨List σ, [], fun buf x => if (buf ++ [x]).length = k then ((buf ++ [x]).tail, [buf ++ [x]]) else (buf ++ [x], []),
   fun _ => false⟩
theorem windowM_step (k : Nat) (buf : List σ) x : (windowM k).step buf x =
    if (buf ++ [x]).length = k then ((buf ++ [x]).tail, [buf ++ [x]]) else (buf ++ [x], []) := rfl

theorem windowRef_short (k : Nat) (buf : List σ) (h : buf.length < k) : windowRef k buf = [] := by
  have : buf.length + 1 - k = 0 := by omega
  simp [windowRef, this]
theorem windowRef_block (k : Nat) (a : σ) (c ys : List σ) (hc : c.length + 1 = k) :
    windowRef k ((a :: c) ++ ys) = (a :: c) :: windowRef k (c ++ ys) := by
  have hl : ((a :: c) ++ ys).length + 1 - k = (c ++ ys).length + 1 - k + 1 := by simp; omega
  rw [windowRef, hl, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.drop_zero, windowRef]
  congr 1
  · subst hc; simp
  all_goals (try (apply List.map_congr_left; intro i _; simp))

theorem windowM_feed (k : Nat) (hk : 0 < k) : ∀ (buf xs : List σ), buf.length < k →
    ((windowM k).feed buf xs).2 = windowRef k (buf ++ xs) := by
  intro buf xs; induction xs generalizing buf with
  | nil => intro h; simp [M.feed, windowRef_short k buf h]
  | cons x xs ih =>
    intro h
    by_cases he : (buf ++ [x]).length = k
    · simp only [M.feed, windowM_step, he, if_true]
      cases hb : buf ++ [x] with
      | nil => simp at hb
      | cons a c =>
        have hc : c.length + 1 = k := by rw [← he, hb]; simp
        simp only [List.tail_cons]
        rw [ih c (by omega), show buf ++ x :: xs = (a :: c) ++ xs by rw [← hb]; simp, windowRef_block k a c xs hc]
        simp
    · simp only [M.feed, windowM_step, he, if_false, List.nil_append]
      rw [ih _ (by simp at he ⊢; omega)]; simp

def window (k : Nat) (hk : 0 < k := by decide) : Ad σ (List σ) :=
  ⟨windowM k, windowRef k, fun xs => by simpa using windowM_feed k hk [] xs (by simpa using hk),
   fun _ _ h => by simp [windowM] at h, "window", "buffer of < k items (last k-1)"⟩
end Vw
