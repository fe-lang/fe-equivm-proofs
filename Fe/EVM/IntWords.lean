import Fe.EVM.Int
import Reasoning.EVMWord

/-!
# Integers as words

Fe's signed integer types are held as 256-bit two's-complement words.  `I n` is the word of an
integer `n`.  The lemmas state each operation of `IntTy` on such words as one on integers:
`IntTy.addW (.i b) (I x) (I y) = I ((x + y).bmod 2 ^ b)` and so on, for any width.
-/

open Ethereum Reasoning.Theory

namespace Fe.EVM

/-- The 256-bit two's-complement word of an integer. -/
def I (n : ℤ) : UInt256 := UInt256.ofNat (n % 2 ^ 256).toNat

theorem I_toNat (n : ℤ) : (I n).toNat = (n % 2 ^ 256).toNat := by
  unfold I
  have h1 := Int.emod_nonneg n (show (2 : ℤ) ^ 256 ≠ 0 by norm_num)
  have h2 := Int.emod_lt_of_pos n (show (0 : ℤ) < 2 ^ 256 by norm_num)
  rw [ulit_toNat' _ (by unfold UInt256.size; omega)]

theorem I_toNat_cast (n : ℤ) : ((I n).toNat : ℤ) = n % 2 ^ 256 := by
  rw [I_toNat]
  exact Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))

/-- A signed reading of a word in range. -/
theorem val_i_I (b : ℕ) {n : ℤ} (h1 : -2 ^ 255 ≤ n) (h2 : n < 2 ^ 255) :
    IntTy.val (.i b) (I n) = n := by
  simp only [IntTy.val]
  have := I_toNat_cast n
  split <;> omega

/-- An unsigned reading of a word in range. -/
theorem val_u_I (b : ℕ) {n : ℤ} (h1 : 0 ≤ n) (h2 : n < 2 ^ 256) :
    IntTy.val (.u b) (I n) = n := by
  simp only [IntTy.val]
  have := I_toNat_cast n
  omega

theorem wrap_i (b : ℕ) (hb : 0 < b) (n : ℤ) : IntTy.wrap (.i b) n = I (n.bmod (2 ^ b)) := by
  simp only [IntTy.wrap, Int.bmod]
  have h2 : (((2 ^ b : ℕ) : ℤ) + 1) / 2 = 2 ^ (b - 1) := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    push_cast
    simp only [pow_succ]; omega
  rw [h2]
  push_cast
  rfl

theorem wrap_u (b : ℕ) (n : ℤ) (hb : b ≤ 256) : IntTy.wrap (.u b) n = I (n % 2 ^ b) := by
  simp only [IntTy.wrap, I]
  congr 2
  have h1 := Int.emod_nonneg n (show (2 : ℤ) ^ b ≠ 0 by positivity)
  have h2 := Int.emod_lt_of_pos n (show (0 : ℤ) < 2 ^ b by positivity)
  have : (2 : ℤ) ^ b ≤ 2 ^ 256 := pow_le_pow_right₀ (by norm_num) hb
  rw [Int.emod_eq_of_lt h1 (by omega)]

/-! ## Arithmetic -/

section
variable {x y : ℤ}

theorem addW_i (b : ℕ) (hb : 0 < b) (hx1 : -2 ^ 255 ≤ x) (hx2 : x < 2 ^ 255) (hy1 : -2 ^ 255 ≤ y)
    (hy2 : y < 2 ^ 255) : IntTy.addW (.i b) (I x) (I y) = I ((x + y).bmod (2 ^ b)) := by
  simp only [IntTy.addW, val_i_I b hx1 hx2, val_i_I b hy1 hy2, wrap_i b hb]

theorem subW_i (b : ℕ) (hb : 0 < b) (hx1 : -2 ^ 255 ≤ x) (hx2 : x < 2 ^ 255) (hy1 : -2 ^ 255 ≤ y)
    (hy2 : y < 2 ^ 255) : IntTy.subW (.i b) (I x) (I y) = I ((x - y).bmod (2 ^ b)) := by
  simp only [IntTy.subW, val_i_I b hx1 hx2, val_i_I b hy1 hy2, wrap_i b hb]

theorem mulW_i (b : ℕ) (hb : 0 < b) (hx1 : -2 ^ 255 ≤ x) (hx2 : x < 2 ^ 255) (hy1 : -2 ^ 255 ≤ y)
    (hy2 : y < 2 ^ 255) : IntTy.mulW (.i b) (I x) (I y) = I ((x * y).bmod (2 ^ b)) := by
  simp only [IntTy.mulW, val_i_I b hx1 hx2, val_i_I b hy1 hy2, wrap_i b hb]

/-- An arithmetic right shift is a floor division. -/
theorem shr_i (b : ℕ) (hb : 0 < b) (hx1 : -2 ^ 255 ≤ x) (hx2 : x < 2 ^ 255) {k : ℕ}
    (hk : k < 256) : IntTy.shr (.i b) (I x) (UInt256.ofNat k) = I ((x / 2 ^ k).bmod (2 ^ b)) := by
  simp only [IntTy.shr, ulit_toNat' _ (show k < 2 ^ 256 by omega), val_i_I b hx1 hx2,
    wrap_i b hb, show ¬ 256 ≤ k by omega, if_false]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]

end

/-- The signed comparison with zero. -/
theorem sltBool_I_zero {x : ℤ} (hx1 : -2 ^ 255 ≤ x) (hx2 : x < 2 ^ 255) :
    UInt256.sltBool (I x) (UInt256.ofNat 0) = decide (x < 0) := by
  have := I_toNat_cast x
  unfold UInt256.sltBool
  rw [ulit_toNat' _ (by decide)]
  by_cases h : x < 0
  · rw [if_pos (by omega), if_neg (by omega)]; simp [h]
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [h, decide_false]
    change decide ((I x).toNat < 0) = false
    simp

end Fe.EVM
