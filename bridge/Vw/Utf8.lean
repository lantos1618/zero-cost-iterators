import Vw.Plan
/-! Bytes vs Unicode scalars. Policy: INVALID INPUT IS REJECTED (`none`), never replaced.
Rejected: stray continuation bytes, C0/C1 and F5..FF leads, overlong forms, surrogates
U+D800..DFFF, values above U+10FFFF, and truncated sequences. -/
namespace Utf8

def cont (b : Nat) : Bool := 0x80 ≤ b && b < 0xC0

/-- decode ONE scalar from the front: returns it and the remaining bytes -/
def dec1 : List Nat → Option (Nat × List Nat)
  | [] => none
  | b0 :: rest =>
    if b0 < 0x80 then some (b0, rest)
    else if 0xC2 ≤ b0 ∧ b0 < 0xE0 then
      match rest with
      | b1 :: r => if cont b1 then some ((b0 - 0xC0) * 64 + (b1 - 0x80), r) else none
      | _ => none
    else if 0xE0 ≤ b0 ∧ b0 < 0xF0 then
      match rest with
      | b1 :: b2 :: r =>
        if cont b1 && cont b2 && 0x800 ≤ (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) &&
          !(0xD800 ≤ (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) &&
            (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) < 0xE000)
        then some ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80), r) else none
      | _ => none
    else if 0xF0 ≤ b0 ∧ b0 < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: r =>
        if cont b1 && cont b2 && cont b3 &&
          0x10000 ≤ (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80) &&
          (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80) < 0x110000
        then some ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80), r) else none
      | _ => none
    else none

/-- direct iteration, left to right; fuel = byte count (each step consumes >= 1 byte) -/
def decF : Nat → List Nat → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, b :: bs => match dec1 (b :: bs) with
    | some (v, r) => (decF n r).map (v :: ·)
    | none => none
def dec (bs : List Nat) : Option (List Nat) := decF bs.length bs

/-- independent reference encoder, arithmetic (div/mod) form -/
def enc1 (v : Nat) : List Nat :=
  if v < 0x80 then [v]
  else if v < 0x800 then [0xC0 + v / 64, 0x80 + v % 64]
  else if v < 0x10000 then [0xE0 + v / 4096, 0x80 + v / 64 % 64, 0x80 + v % 64]
  else [0xF0 + v / 262144, 0x80 + v / 4096 % 64, 0x80 + v / 64 % 64, 0x80 + v % 64]

def scalar (v : Nat) : Prop := v < 0x110000 ∧ ¬(0xD800 ≤ v ∧ v < 0xE000)

set_option maxRecDepth 8000 in
theorem dec1_enc1 (v : Nat) (h : scalar v) (r : List Nat) : dec1 (enc1 v ++ r) = some (v, r) := by
  unfold scalar at h
  unfold enc1
  by_cases h1 : v < 0x80
  · rw [if_pos h1]; simp only [List.cons_append, List.nil_append, dec1]; rw [if_pos h1]
  by_cases h2 : v < 0x800
  · rw [if_neg h1, if_pos h2]; simp only [List.cons_append, List.nil_append, dec1, cont]
    rw [if_neg (by omega), if_pos (by omega), if_pos (by simp; omega)]
    congr 2; omega
  by_cases h3 : v < 0x10000
  · rw [if_neg h1, if_neg h2, if_pos h3]; simp only [List.cons_append, List.nil_append, dec1, cont]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by simp; omega)]
    congr 2; omega
  · rw [if_neg h1, if_neg h2, if_neg h3]; simp only [List.cons_append, List.nil_append, dec1, cont]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by simp; omega)]
    congr 2; omega

theorem enc1_len (v : Nat) : 1 ≤ (enc1 v).length := by unfold enc1; split <;> (try split) <;> (try split) <;> simp

theorem decF_step (m : Nat) (bs r : List Nat) (v : Nat) (h : dec1 bs = some (v, r)) :
    decF (m + 1) bs = (decF m r).map (v :: ·) := by
  cases bs with
  | nil => simp [dec1] at h
  | cons b bs => simp [decF, h]

theorem decF_encode : ∀ (cps : List Nat) (n : Nat), (∀ v ∈ cps, scalar v) → (cps.flatMap enc1).length ≤ n →
    decF n (cps.flatMap enc1) = some cps
  | [], n, _, _ => by cases n <;> rfl
  | v :: vs, n, h, hl => by
    have e := enc1_len v
    simp only [List.flatMap_cons, List.length_append] at hl ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [decF_step m _ _ v (dec1_enc1 v (h v (by simp)) _),
      decF_encode vs m (fun w hw => h w (by simp [hw])) (by omega)]; rfl

/-- for EVERY list of Unicode scalar values, decoding the reference encoding gives it back -/
theorem dec_encode (cps : List Nat) (h : ∀ v ∈ cps, scalar v) : dec (cps.flatMap enc1) = some cps :=
  decF_encode cps _ h (Nat.le_refl _)

/-- every Lean `Char` is a scalar value, so this covers the scalars of every Lean `String` -/
theorem char_scalar (c : Char) : scalar c.toNat := by
  have := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at this
  unfold scalar; simp only [Char.toNat]; omega
theorem dec_string (s : String) :
    dec (s.toList.flatMap (enc1 ∘ Char.toNat)) = some (s.toList.map Char.toNat) := by
  have := dec_encode (s.toList.map Char.toNat) (by simp; intro c _; exact char_scalar c)
  rw [List.flatMap_map] at this; simpa [Function.comp_def] using this

/-! invalid-input policy, checked -/
theorem rej_stray : dec [0x80] = none := by decide
theorem rej_overlong2 : dec [0xC0, 0x80] = none ∧ dec [0xC1, 0xBF] = none := by decide
theorem rej_overlong3 : dec [0xE0, 0x80, 0x80] = none := by decide
theorem rej_surrogate : dec [0xED, 0xA0, 0x80] = none := by decide
theorem rej_too_big : dec [0xF4, 0x90, 0x80, 0x80] = none ∧ dec [0xF5, 0x80, 0x80, 0x80] = none := by decide
theorem rej_trunc : dec [0xE2, 0x82] = none := by decide
theorem acc_ex : dec [0x61, 0xC3, 0xA9, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80] = some [0x61, 0xE9, 0x20AC, 0x1F600] := by decide

/-! byte vs scalar boundary: "é" is 2 bytes but 1 scalar; taking 1 BYTE splits the scalar -/
theorem boundary_count : (enc1 0xE9).length = 2 := by decide
theorem byte_take_splits : dec ((enc1 0xE9).take 1) = none ∧ dec (enc1 0xE9) = some [0xE9] := by decide
end Utf8
