import FeProofs.Precompiles.Exported.Shared
import Reasoning.EVMWord

/-!
# Precompiles: 64-bit word helpers

The Montgomery arithmetic of fevm's `montgomery.fe` works on 64-bit limbs held in 256-bit
words.  A `Limb` is a natural number below `2 ^ 64`, and `Limb.w` its word.  The exported
helpers `mul_wide`, `adc`, `sbb` and `u64_wrapping_mul` are pure on limbs: each is `pure` of
the limbs of an integer identity, whatever the limbs (`mul_wide_eq` and the rest).  Their
checked `u128` additions and multiplications cannot overflow on limbs, so no side condition is
needed; the bound travels in the type.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

/-- A 64-bit limb. -/
abbrev Limb := Fin (2 ^ 64)

/-- The word of a limb. -/
def Limb.w (x : Limb) : UInt256 := UInt256.ofNat x.val

@[simp] theorem Limb.toNat_w (x : Limb) : x.w.toNat = x.val :=
  ulit_toNat' _ (lt_trans x.isLt (by decide))

theorem Limb.w_inj {x y : Limb} : x.w = y.w ↔ x = y := by
  constructor
  · intro h
    exact Fin.ext (by simpa using congrArg UInt256.toNat h)
  · rintro rfl; rfl

/-- The limb of a natural number below `2 ^ 64`. -/
def limb (n : ℕ) (h : n < 2 ^ 64) : Limb := ⟨n, h⟩

/-! ## The pure operations -/

/-- `a * b` as (low, high) limbs. -/
def mulLo (a b : Limb) : Limb := ⟨a.val * b.val % 2 ^ 64, Nat.mod_lt _ (by decide)⟩
def mulHi (a b : Limb) : Limb :=
  ⟨a.val * b.val / 2 ^ 64, by
    have := Nat.mul_lt_mul'' a.isLt b.isLt
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    simpa using this⟩

/-- `a + b + c` as (sum, carry) limbs. -/
def adcLo (a b c : Limb) : Limb := ⟨(a.val + b.val + c.val) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩
def adcHi (a b c : Limb) : Limb :=
  ⟨(a.val + b.val + c.val) / 2 ^ 64, by
    have := a.isLt; have := b.isLt; have := c.isLt
    rw [Nat.div_lt_iff_lt_mul (by decide)]; omega⟩

/-- `a - b - c` as (difference, borrow) limbs. -/
def sbbLo (a b c : Limb) : Limb :=
  ⟨(a.val + 2 ^ 128 - b.val - c.val) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩
def sbbHi (a b c : Limb) : Limb := if a.val < b.val + c.val then 1 else 0

theorem mulLo_add_mulHi (a b : Limb) :
    (mulLo a b).val + 2 ^ 64 * (mulHi a b).val = a.val * b.val := by
  simp only [mulLo, mulHi]; omega

theorem adcLo_add_adcHi (a b c : Limb) :
    (adcLo a b c).val + 2 ^ 64 * (adcHi a b c).val = a.val + b.val + c.val := by
  simp only [adcLo, adcHi]; omega

theorem adcHi_le_two (a b c : Limb) : (adcHi a b c).val ≤ 2 := by
  have := a.isLt; have := b.isLt; have := c.isLt
  simp only [adcHi]; omega

/-- With a carry of at most one the carry out is at most one. -/
theorem adcHi_le_one {a b c : Limb} (hc : c.val ≤ 1) : (adcHi a b c).val ≤ 1 := by
  have := a.isLt; have := b.isLt
  simp only [adcHi]; omega

theorem sbbLo_sbbHi (a b c : Limb) (hc : c.val ≤ 1) :
    (sbbLo a b c).val + b.val + c.val = a.val + 2 ^ 64 * (sbbHi a b c).val := by
  have := a.isLt; have := b.isLt
  unfold sbbLo sbbHi
  split <;> simp <;> omega

/-! ## Words and limbs -/

theorem word_lt {n : ℕ} (h : n < 2 ^ 128) : n < UInt256.size :=
  lt_trans h (by decide)

theorem toNat_lit {n : ℕ} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := ulit_toNat' n h

theorem shiftRight_toNat (x : UInt256) {k : ℕ} (hk : k < 256) :
    (x >>> UInt256.ofNat k).toNat = x.toNat / 2 ^ k := by
  have hkword : (UInt256.ofNat k).toNat = k := toNat_lit (by omega)
  change (UInt256.shiftRight x (UInt256.ofNat k)).toNat = _
  unfold UInt256.shiftRight
  rw [ite_eq_right (by change ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  change (x.toNat >>> (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkword, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self x.toNat (2 ^ k)) x.val.isLt)

theorem land_mask_toNat (x : UInt256) :
    (x &&& UInt256.ofNat 18446744073709551615).toNat = x.toNat % 2 ^ 64 := by
  change (UInt256.land x _).toNat = _
  rw [uland_toNat, toNat_lit (by decide), show (18446744073709551615 : ℕ) = 2 ^ 64 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem ofNat_toNat (x : UInt256) : UInt256.ofNat x.toNat = x := by
  cases x with
  | mk v =>
    change (⟨Fin.ofNat _ v.val⟩ : UInt256) = ⟨v⟩
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt v.isLt)

theorem word_eq_of_toNat {x y : UInt256} (h : x.toNat = y.toNat) : x = y := by
  rw [← ofNat_toNat x, ← ofNat_toNat y, h]

open Precompiles.Exported.Shared

/-- Truncation of a word to 64 bits. -/
theorem downcast_truncate_u128_u64_eq (x : UInt256) :
    downcast_truncate_u128_u64 x =
      pure (UInt256.ofNat (x.toNat % 2 ^ 64)) := by
  simp only [Lib.downcast_truncate_u128_u64, Lib.u128_to_word, Lib.u64_IS_SIGNED, Lib.u64_MASK,
    Lib.U64_MASK, Lib.u64_from_word, truncate, pure_bind, bind_pure_comp, Bool.false_eq_true,
    ite_false, map_pure]
  rw [land_mask_toNat, Nat.mod_mod]

theorem downcast_truncate_u256_u64_eq (x : UInt256) :
    Lib.downcast_truncate_u256_u64 x =
      pure (UInt256.ofNat (x.toNat % 2 ^ 64)) := by
  simp only [Lib.downcast_truncate_u256_u64, Lib.u256_to_word, Lib.u64_IS_SIGNED, Lib.u64_MASK,
    Lib.U64_MASK, Lib.u64_from_word, truncate, pure_bind, bind_pure_comp, Bool.false_eq_true,
    ite_false, map_pure]
  rw [land_mask_toNat, Nat.mod_mod]

/-- A word wrapped to 128 bits, of a natural number. -/
theorem wrap128_toNat (n : ℕ) :
    (UInt256.ofNat (((n : ℤ) % 2 ^ 128).toNat)).toNat = n % 2 ^ 128 := by
  rw [toNat_lit (by omega)]; omega

/-- `mul_wide` on limbs. -/
theorem mul_wide_eq (a b : Limb) :
    mul_wide a.w b.w = pure ((mulLo a b).w, (mulHi a b).w) := by
  have hab : a.val * b.val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' a.isLt b.isLt; simpa using this
  simp only [mul_wide, IntTy.mul, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    Limb.toNat_w]
  rw [show ((a.val : ℤ) * b.val) = ((a.val * b.val : ℕ) : ℤ) by push_cast; ring,
    ite_eq_left (by constructor <;> omega)]
  simp only [pure_bind, downcast_truncate_u128_u64_eq, wrap128_toNat,
    shiftRight_toNat _ (show 64 < 256 by decide)]
  congr 2
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, mulLo]
    rw [toNat_lit] <;> omega
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, mulHi]
    rw [toNat_lit] <;> omega

/-- `adc` on limbs. -/
theorem adc_eq (a b c : Limb) :
    adc a.w b.w c.w = pure ((adcLo a b c).w, (adcHi a b c).w) := by
  have := a.isLt; have := b.isLt; have := c.isLt
  simp only [adc, IntTy.add, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap, Limb.toNat_w]
  rw [show ((a.val : ℤ) + b.val) = ((a.val + b.val : ℕ) : ℤ) by push_cast; ring,
    ite_eq_left (by constructor <;> omega)]
  simp only [pure_bind, wrap128_toNat]
  rw [show (((a.val + b.val) % 2 ^ 128 : ℕ) : ℤ) + c.val =
      (((a.val + b.val) % 2 ^ 128 + c.val : ℕ) : ℤ) by push_cast; ring,
    ite_eq_left (by constructor <;> omega)]
  simp only [pure_bind, downcast_truncate_u128_u64_eq, wrap128_toNat,
    shiftRight_toNat _ (show 64 < 256 by decide)]
  congr 2
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, adcLo]
    rw [toNat_lit] <;> omega
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, adcHi]
    rw [toNat_lit] <;> omega

/-- `sbb` on limbs, for a borrow in of at most one. -/
theorem sbb_eq (a b c : Limb) (hc : c.val ≤ 1) :
    sbb a.w b.w c.w = pure ((sbbLo a b c).w, (sbbHi a b c).w) := by
  have := a.isLt; have := b.isLt
  simp only [sbb, Lib.u128_wrapping_sub, IntTy.subW, IntTy.val, IntTy.wrap, Limb.toNat_w,
    pure_bind]
  have h1 : (UInt256.ofNat (((a.val : ℤ) - b.val) % 2 ^ 128).toNat).toNat =
      (a.val + 2 ^ 128 - b.val) % 2 ^ 128 := by
    rw [toNat_lit (by omega)]; omega
  rw [h1]
  have h2 : (UInt256.ofNat (((((a.val + 2 ^ 128 - b.val) % 2 ^ 128 : ℕ) : ℤ) - c.val) %
      2 ^ 128).toNat).toNat = (a.val + 2 ^ 128 - b.val - c.val) % 2 ^ 128 := by
    rw [toNat_lit (by omega)]; omega
  simp only [h2, downcast_truncate_u128_u64_eq, pure_bind,
    shiftRight_toNat _ (show 127 < 256 by decide)]
  congr 2
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, sbbLo]
    rw [toNat_lit] <;> omega
  · apply word_eq_of_toNat
    simp only [Limb.toNat_w, sbbHi]
    rw [toNat_lit (n := (_ % 2 ^ 128 / 2 ^ 127 % 2 ^ 64)) (by omega)]
    split <;> simp <;> omega

/-- `u64::wrapping_mul` on limbs. -/
theorem u64_wrapping_mul_eq (a b : Limb) :
    Lib.u64_wrapping_mul a.w b.w = pure (mulLo a b).w := by
  simp only [Lib.u64_wrapping_mul, IntTy.mulW, IntTy.val, IntTy.wrap, Limb.toNat_w]
  congr 1

/-! ## Constants and assembled words -/

theorem zero_w : UInt256.ofNat 0 = (0 : Limb).w := rfl

theorem sbbHi_val_le (a b c : Limb) : (sbbHi a b c).val ≤ 1 := by
  unfold sbbHi; split <;> simp

theorem zero_val_le : (0 : Limb).val ≤ 1 := by decide

theorem one_w : UInt256.ofNat 1 = (1 : Limb).w := rfl

theorem shiftLeft_toNat (x : UInt256) {k : ℕ} (hk : k < 256) (hx : x.toNat * 2 ^ k < 2 ^ 256) :
    (x <<< UInt256.ofNat k).toNat = 2 ^ k * x.toNat := by
  have hkword : (UInt256.ofNat k).toNat = k := toNat_lit (by omega)
  change (UInt256.shiftLeft x (UInt256.ofNat k)).toNat = _
  unfold UInt256.shiftLeft
  rw [ite_eq_right (by change ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  change (x.toNat <<< (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkword, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show _ < UInt256.size from hx), Nat.mul_comm]

/-- The word `value` assembles from four limbs is their sum at their weights. -/
theorem assemble_eq (x0 x1 x2 x3 : Limb) :
    x0.w ||| x1.w <<< UInt256.ofNat 64 ||| x2.w <<< UInt256.ofNat 128 |||
      x3.w <<< UInt256.ofNat 192 =
    UInt256.ofNat (x0.val + 2 ^ 64 * x1.val + 2 ^ 128 * x2.val + 2 ^ 192 * x3.val) := by
  have h0 := x0.isLt; have h1 := x1.isLt; have h2 := x2.isLt; have h3 := x3.isLt
  apply word_eq_of_toNat
  change (UInt256.lor (UInt256.lor (UInt256.lor _ _) _) _).toNat = _
  rw [u256_lor_toNat_exact, u256_lor_toNat_exact, u256_lor_toNat_exact,
    shiftLeft_toNat _ (by decide) (by simp; omega), shiftLeft_toNat _ (by decide) (by simp; omega),
    shiftLeft_toNat _ (by decide) (by simp; omega), toNat_lit (by omega)]
  simp only [Limb.toNat_w]
  have e1 : x0.val ||| 2 ^ 64 * x1.val = 2 ^ 64 * x1.val + x0.val := by
    rw [Nat.lor_comm]; exact (Nat.two_pow_add_eq_or_of_lt h0 _).symm
  have e2 : (2 ^ 64 * x1.val + x0.val) ||| 2 ^ 128 * x2.val =
      2 ^ 128 * x2.val + (2 ^ 64 * x1.val + x0.val) := by
    rw [Nat.lor_comm]; exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  have e3 : (2 ^ 128 * x2.val + (2 ^ 64 * x1.val + x0.val)) ||| 2 ^ 192 * x3.val =
      2 ^ 192 * x3.val + (2 ^ 128 * x2.val + (2 ^ 64 * x1.val + x0.val)) := by
    rw [Nat.lor_comm]; exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  rw [e1, e2, e3]
  omega

end FeProofs.Precompiles
