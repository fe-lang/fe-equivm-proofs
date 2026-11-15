import FeProofs.Precompiles.Field.Words
import Fe.EVM.IntWords

/-!
# Precompiles: signed words

The inversion in `inversion.fe` computes with `i64` and `i128` values, which the exporter keeps
as 256-bit two's-complement words, and with `u64` values as words below `2 ^ 64`.  `I n`, the
word of an integer `n`, and the lemmas stating `IntTy`'s operations on such words as operations
on integers are in `Fe/EVM/IntWords.lean`.  This file adds the facts about `I` the inversion
uses, the `u64` operations, the truncations, and `u64` words as limbs.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

theorem I_inj {x y : ℤ} (h : x % 2 ^ 256 = y % 2 ^ 256) : I x = I y := by
  unfold I; rw [h]

/-- A natural number's word is its integer's. -/
theorem ofNat_eq_I {k : ℕ} (hk : k < 2 ^ 256) : UInt256.ofNat k = I k := by
  unfold I
  congr 1
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

/-- Every word is the word of its natural number. -/
theorem eq_I (w : UInt256) : w = I w.toNat := by
  rw [← ofNat_eq_I (show w.toNat < 2 ^ 256 from w.val.isLt), ofNat_toNat]

/-! ## Unsigned 64-bit words -/

section
variable {x y : ℕ}

theorem addW_u64 (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    IntTy.addW (.u 64) (UInt256.ofNat x) (UInt256.ofNat y) = UInt256.ofNat ((x + y) % 2 ^ 64) := by
  simp only [IntTy.addW, IntTy.val, IntTy.wrap, toNat_lit hx, toNat_lit hy]
  congr 1

theorem mulW_u64 (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    IntTy.mulW (.u 64) (UInt256.ofNat x) (UInt256.ofNat y) = UInt256.ofNat (x * y % 2 ^ 64) := by
  simp only [IntTy.mulW, IntTy.val, IntTy.wrap, toNat_lit hx, toNat_lit hy]
  congr 1

theorem subW_u64 (hx : x < 2 ^ 256) (hy : y < 2 ^ 64) :
    IntTy.subW (.u 64) (UInt256.ofNat x) (UInt256.ofNat y) =
      UInt256.ofNat ((x + 2 ^ 64 - y) % 2 ^ 64) := by
  simp only [IntTy.subW, IntTy.val, IntTy.wrap, toNat_lit hx, toNat_lit (show y < 2 ^ 256 by omega)]
  congr 1; omega

theorem shl_u64 (hx : x < 2 ^ 256) {k : ℕ} (hk : k < 256) :
    IntTy.shl (.u 64) (UInt256.ofNat x) (UInt256.ofNat k) = UInt256.ofNat (x * 2 ^ k % 2 ^ 64) := by
  simp only [IntTy.shl, IntTy.val, IntTy.wrap, toNat_lit hx, toNat_lit (show k < 2 ^ 256 by omega),
    show ¬ 256 ≤ k by omega, ite_false]
  congr 1

theorem ushr_eq (hx : x < 2 ^ 256) {k : ℕ} (hk : k < 256) :
    UInt256.ofNat x >>> UInt256.ofNat k = UInt256.ofNat (x / 2 ^ k) := by
  apply word_eq_of_toNat
  rw [shiftRight_toNat _ hk, toNat_lit hx, toNat_lit (lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem land_eq (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    UInt256.ofNat x &&& UInt256.ofNat y = UInt256.ofNat (x &&& y) := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, toNat_lit hx, toNat_lit hy,
    toNat_lit (lt_of_le_of_lt Nat.and_le_left hx)]

theorem lor_eq (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    UInt256.ofNat x ||| UInt256.ofNat y = UInt256.ofNat (x ||| y) := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, toNat_lit hx, toNat_lit hy,
    toNat_lit (Nat.or_lt_two_pow (n := 256) hx hy)]

end

/-- The low 62 bits of a signed word, as `& M62_SIGNED` takes them. -/
theorem I_land_M62 (x : ℤ) : I x &&& UInt256.ofNat 4611686018427387903 = I (x % 2 ^ 62) := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, toNat_lit (by decide), show (4611686018427387903 : ℕ) = 2 ^ 62 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, I_toNat, I_toNat]
  have h1 := Int.emod_nonneg x (show (2 : ℤ) ^ 256 ≠ 0 by norm_num)
  have h2 := Int.emod_nonneg x (show (2 : ℤ) ^ 62 ≠ 0 by norm_num)
  have h3 := Int.emod_lt_of_pos x (show (0 : ℤ) < 2 ^ 62 by norm_num)
  have h4 : x % 2 ^ 256 % 2 ^ 62 = x % 2 ^ 62 :=
    Int.emod_emod_of_dvd x (by norm_num)
  rw [Int.emod_eq_of_lt h2 (by omega)]
  omega

/-! ## Truncations -/

open Precompiles.Exported.Shared

theorem sign_extend_mod (v : UInt256) :
    ∃ w, Lib.sign_extend v
        (UInt256.ofNat 18446744073709551615) (UInt256.ofNat 9223372036854775808) = pure w ∧
      w.toNat % 2 ^ 64 = v.toNat % 2 ^ 64 := by
  unfold Lib.sign_extend
  simp only [Lib.U256_MASK, pure_bind]
  split
  · refine ⟨_, rfl, ?_⟩
    change (UInt256.lor _ _).toNat % 2 ^ 64 = _
    rw [u256_lor_toNat_exact, land_mask_toNat]
    have hx : (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 ^^^
        UInt256.ofNat 18446744073709551615).toNat = 2 ^ 64 * (2 ^ 192 - 1) := by decide
    rw [hx, Nat.lor_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    omega
  · exact ⟨_, rfl, by rw [land_mask_toNat, Nat.mod_mod]⟩

/-- A truncation to `i64` keeps the low 64 bits, read as signed. -/
theorem downcast_truncate_u64_i64_eq (v : UInt256) :
    downcast_truncate_u64_i64 v = pure (I ((v.toNat : ℤ).bmod (2 ^ 64))) := by
  obtain ⟨w, hw, hm⟩ := sign_extend_mod v
  simp only [Lib.downcast_truncate_u64_i64, Lib.u64_to_word, Lib.i64_IS_SIGNED, Lib.i64_MASK,
    Lib.U64_MASK, Lib.i64_SIGN_BIT, Lib.I64_SIGN_BIT, pure_bind, ite_true]
  rw [hw]
  simp only [pure_bind, Lib.i64_from_word, IntTy.cast, IntTy.val, wrap_i 64 (by decide)]
  rw [← Int.emod_bmod, ← Int.emod_bmod (v.toNat : ℤ)]
  congr 3
  exact_mod_cast hm

theorem downcast_truncate_i128_i64_eq (v : UInt256) :
    downcast_truncate_i128_i64 v = pure (I ((v.toNat : ℤ).bmod (2 ^ 64))) := by
  obtain ⟨w, hw, hm⟩ := sign_extend_mod v
  simp only [Lib.downcast_truncate_i128_i64, Lib.i128_to_word, Lib.i64_IS_SIGNED, Lib.i64_MASK,
    Lib.U64_MASK, Lib.i64_SIGN_BIT, Lib.I64_SIGN_BIT, pure_bind, ite_true]
  rw [hw]
  simp only [pure_bind, Lib.i64_from_word, IntTy.cast, IntTy.val, wrap_i 64 (by decide)]
  rw [← Int.emod_bmod, ← Int.emod_bmod (v.toNat : ℤ)]
  congr 3
  exact_mod_cast hm

/-- A truncation to `u64` keeps the low 64 bits. -/
theorem downcast_truncate_i64_u64_eq (v : UInt256) :
    downcast_truncate_i64_u64 v = pure (UInt256.ofNat (v.toNat % 2 ^ 64)) := by
  simp only [Lib.downcast_truncate_i64_u64, Lib.i64_to_word, Lib.u64_IS_SIGNED, Lib.u64_MASK,
    Lib.U64_MASK, Lib.u64_from_word, truncate, pure_bind, Bool.false_eq_true, ite_false,
    land_mask_toNat, Nat.mod_mod]

theorem downcast_truncate_i128_u64_eq (v : UInt256) :
    downcast_truncate_i128_u64 v = pure (UInt256.ofNat (v.toNat % 2 ^ 64)) := by
  simp only [Lib.downcast_truncate_i128_u64, Lib.i128_to_word, Lib.u64_IS_SIGNED, Lib.u64_MASK,
    Lib.U64_MASK, Lib.u64_from_word, truncate, pure_bind, Bool.false_eq_true, ite_false,
    land_mask_toNat, Nat.mod_mod]

/-- The word of an integer, modulo `2 ^ 64`. -/
theorem I_toNat_mod64 (n : ℤ) : (((I n).toNat % 2 ^ 64 : ℕ) : ℤ) = n % 2 ^ 64 := by
  push_cast
  rw [I_toNat_cast, Int.emod_emod_of_dvd n (by norm_num)]

/-! ## `u64` words as limbs -/

namespace Limb

/-- The signed reading of a limb, as `i64`. -/
def sgn (x : Limb) : ℤ := (x.val : ℤ).bmod (2 ^ 64)

/-- The limb of an integer modulo `2 ^ 64`. -/
def ofInt (x : ℤ) : Limb :=
  ⟨(x % 2 ^ 64).toNat, by
    have := Int.emod_lt_of_pos x (show (0 : ℤ) < 2 ^ 64 by norm_num)
    have := Int.emod_nonneg x (show (2 : ℤ) ^ 64 ≠ 0 by norm_num)
    omega⟩

/-- `u64` shift left. -/
def shl (a : Limb) (k : ℕ) : Limb := ⟨a.val * 2 ^ k % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

/-- `u64` shift right. -/
def shr (a : Limb) (k : ℕ) : Limb := ⟨a.val / 2 ^ k, lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩

/-- The number of trailing zero bits, `64` for zero. -/
def tz (a : Limb) : Limb :=
  ⟨((List.range 64).takeWhile fun n => !a.val.testBit n).length, by
    have := (List.takeWhile_sublist (fun n => !a.val.testBit n) (l := List.range 64)).length_le
    simp only [List.length_range] at this
    omega⟩

theorem tz_le (a : Limb) : a.tz.val ≤ 64 := by
  have := (List.takeWhile_sublist (fun n => !a.val.testBit n) (l := List.range 64)).length_le
  simp only [List.length_range] at this
  exact this

end Limb

theorem addW_w (a b : Limb) : IntTy.addW (.u 64) a.w b.w = (a + b).w := by
  simp only [IntTy.addW, IntTy.val, IntTy.wrap, Limb.toNat_w]
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega), Fin.val_add]
  omega

theorem mulW_w (a b : Limb) : IntTy.mulW (.u 64) a.w b.w = (a * b).w := by
  simp only [IntTy.mulW, IntTy.val, IntTy.wrap, Limb.toNat_w]
  rw [show ((a.val : ℤ) * b.val) = ((a.val * b.val : ℕ) : ℤ) by push_cast; ring]
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega), Fin.val_mul]
  omega

theorem subW_w (a b : Limb) : IntTy.subW (.u 64) a.w b.w = (a - b).w := by
  have := a.isLt; have := b.isLt
  simp only [IntTy.subW, IntTy.val, IntTy.wrap, Limb.toNat_w]
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega), Fin.sub_def]
  simp only
  omega

theorem shl_w (a k : Limb) : IntTy.shl (.u 64) a.w k.w = (a.shl k.val).w := by
  by_cases hk : 256 ≤ k.val
  · simp only [IntTy.shl, Limb.toNat_w, hk, ite_true]
    apply word_eq_of_toNat
    rw [Limb.toNat_w, toNat_lit (by decide)]
    simp only [Limb.shl]
    obtain ⟨j, hj⟩ : ∃ j, k.val = 64 + j := ⟨k.val - 64, by omega⟩
    rw [hj, pow_add, ← Nat.mul_assoc, Nat.mul_comm a.val, Nat.mul_assoc, Nat.mul_mod_right]
  simp only [IntTy.shl, IntTy.val, IntTy.wrap, Limb.toNat_w, hk, ite_false]
  rw [show ((a.val : ℤ) * 2 ^ k.val) = ((a.val * 2 ^ k.val : ℕ) : ℤ) by push_cast; ring]
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega)]
  simp only [Limb.shl]
  omega

theorem shr_w (a k : Limb) : a.w >>> k.w = (a.shr k.val).w := by
  apply word_eq_of_toNat
  by_cases hk : k.val < 256
  · rw [show k.w = UInt256.ofNat k.val from rfl, shiftRight_toNat _ hk]
    simp [Limb.shr]
  · change (UInt256.shiftRight _ _).toNat = _
    unfold UInt256.shiftRight
    rw [ite_eq_left (by change k.w.toNat ≥ 256; rw [Limb.toNat_w]; omega), Limb.toNat_w]
    simp only [Limb.shr]
    have : a.val < 2 ^ k.val :=
      lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt this]
    rfl

theorem land_w (a b : Limb) : a.w &&& b.w = (a &&& b).w := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, Limb.toNat_w, Limb.toNat_w, Limb.toNat_w]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left a.isLt)).symm

theorem lor_w (a b : Limb) : a.w ||| b.w = (a ||| b).w := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, Limb.toNat_w, Limb.toNat_w, Limb.toNat_w]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 64) a.isLt b.isLt)).symm

theorem tz_w (a : Limb) : IntTy.trailingZeros (.u 64) a.w = a.tz.w := by
  rw [IntTy.trailingZeros, IntTy.pattern, Limb.toNat_w]
  simp only [IntTy.bits, Nat.mod_eq_of_lt a.isLt]
  rfl

theorem downcast_u64_i64_w (a : Limb) : downcast_truncate_u64_i64 a.w = pure (I a.sgn) := by
  rw [downcast_truncate_u64_i64_eq, Limb.toNat_w]
  rfl

theorem downcast_i64_u64_I (x : ℤ) : downcast_truncate_i64_u64 (I x) = pure (Limb.ofInt x).w := by
  rw [downcast_truncate_i64_u64_eq]
  congr 1
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega), I_toNat]
  simp only [Limb.ofInt]
  have h1 := Int.emod_nonneg x (show (2 : ℤ) ^ 256 ≠ 0 by norm_num)
  have h2 := Int.emod_emod_of_dvd x (show (2 : ℤ) ^ 64 ∣ 2 ^ 256 by norm_num)
  omega

theorem w_lit (n : ℕ) (h : n < 2 ^ 64) : UInt256.ofNat n = Limb.w ⟨n, h⟩ := rfl

end FeProofs.Precompiles
