/-! Native exactness contract for the emitted C kernel (int32_t acc, r0, r1; int is 32-bit).
Every value the loop computes is an exact Int if inputs are int8 and n ≤ 131071:
each product x*y ∈ [-16256, 16384] and every prefix sum of `acc := acc + x*y` ∈ [-2^31, 2^31-1]. -/

def I8 (x : Int) : Prop := -128 ≤ x ∧ x ≤ 127

theorem prod_bound (x y : Int) (hx : I8 x) (hy : I8 y) : -16256 ≤ x * y ∧ x * y ≤ 16384 := by
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

/-- accumulator value after each iteration of `acc := acc + a[i]*b[i]` -/
def prefixes (acc : Int) : List Int → List Int → List Int
  | x :: xs, y :: ys => (acc + x * y) :: prefixes (acc + x * y) xs ys
  | _, _ => []

theorem prefixes_bound : ∀ (xs ys : List Int) (acc : Int) (k : Nat),
    (∀ x ∈ xs, I8 x) → (∀ y ∈ ys, I8 y) →
    -16256 * (k : Int) ≤ acc → acc ≤ 16384 * (k : Int) →
    ∀ s ∈ prefixes acc xs ys,
      -16256 * ((k + xs.length : Nat) : Int) ≤ s ∧ s ≤ 16384 * ((k + xs.length : Nat) : Int) := by
  intro xs
  induction xs with
  | nil => intro ys acc k _ _ _ _ s hs; simp [prefixes] at hs
  | cons x xs ih =>
    intro ys acc k hx hy hlo hhi s hs
    cases ys with
    | nil => simp [prefixes] at hs
    | cons y ys =>
      have hp := prod_bound x y (hx x (by simp)) (hy y (by simp))
      simp only [prefixes, List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp only [List.length_cons]; omega
      · have := ih ys (acc + x * y) (k + 1) (fun z hz => hx z (by simp [hz]))
          (fun z hz => hy z (by simp [hz])) (by push_cast; omega) (by push_cast; omega) s hs
        simp only [List.length_cons]
        have e : k + (xs.length + 1) = k + 1 + xs.length := by omega
        rw [e]; exact this

theorem int32_prefix_safe (xs ys : List Int) (hx : ∀ x ∈ xs, I8 x) (hy : ∀ y ∈ ys, I8 y)
    (hn : xs.length ≤ 131071) :
    ∀ s ∈ prefixes 0 xs ys, -2147483648 ≤ s ∧ s ≤ 2147483647 := by
  intro s hs
  have := prefixes_bound xs ys 0 0 hx hy (by decide) (by decide) s hs
  simp only [Nat.zero_add] at this
  omega

theorem int32_product_safe (x y : Int) (hx : I8 x) (hy : I8 y) :
    -2147483648 ≤ x * y ∧ x * y ≤ 2147483647 := by
  have := prod_bound x y hx hy; omega

/-- the length bound is the largest one this argument allows -/
theorem bound_tight : 131071 * 16384 ≤ (2147483647 : Int) ∧ 131072 * 16384 > (2147483647 : Int) := by decide

#print axioms prod_bound
#print axioms prefixes_bound
#print axioms int32_prefix_safe
#print axioms int32_product_safe
#print axioms bound_tight
