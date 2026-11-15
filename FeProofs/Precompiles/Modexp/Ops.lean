import FeProofs.Precompiles.Field.Words
import FeProofs.Precompiles.Exported.Modexp

/-!
# Modexp: word operations on limbs

The limb arithmetic of fevm's `modexp.fe` and `bignum.fe` is written with `#[arithmetic(unchecked)]`,
so the exported code wraps: `IntTy.mulW`, `addW`, `subW` at `u64` and `u128`, shifts, and the
truncating casts.  On limbs, and on natural numbers below `2 ^ 128`, each is the word of a
natural-number expression (`mulW64_eq` and the rest).  `mac_eq` is `mac` of `montgomery.fe`, which
the exporter prints in this contract, as `macLo` and `macHi` of `Field/Words.lean`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## Wrapping at a width -/

theorem val_u (b : ℕ) (x : UInt256) : IntTy.val (.u b) x = x.toNat := rfl

theorem wrap_u_nat (b n : ℕ) :
    IntTy.wrap (.u b) (n : ℤ) = UInt256.ofNat (n % 2 ^ b) := by
  simp only [IntTy.wrap]
  congr 1

theorem wrap_u_sub (b x y : ℕ) (hy : y ≤ 2 ^ b) :
    IntTy.wrap (.u b) ((x : ℤ) - y) = UInt256.ofNat ((x + 2 ^ b - y) % 2 ^ b) := by
  simp only [IntTy.wrap]
  congr 1
  have h : ((x + 2 ^ b - y : ℕ) : ℤ) = (x : ℤ) - y + 2 ^ b := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have : ((x : ℤ) - y) % 2 ^ b = (((x + 2 ^ b - y) % 2 ^ b : ℕ) : ℤ) := by
    rw [Int.natCast_mod, h, Nat.cast_pow, Nat.cast_ofNat, ← Int.emod_eq_add_self_emod]
  omega

theorem toNat_ofNat_lt {n : ℕ} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := toNat_lit h

/-! ## Limbs -/

theorem mulW64_eq (a b : Limb) : IntTy.mulW (.u 64) a.w b.w = (mulLo a b).w := by
  simp only [IntTy.mulW, val_u, Limb.toNat_w]
  rw [show ((a.val : ℤ) * b.val) = ((a.val * b.val : ℕ) : ℤ) by push_cast; ring,
    wrap_u_nat _ _]
  rfl

/-- The sum of two limbs, wrapped. -/
def addMod (a b : Limb) : Limb := ⟨(a.val + b.val) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

/-- The difference of two limbs, wrapped. -/
def subMod (a b : Limb) : Limb := ⟨(a.val + 2 ^ 64 - b.val) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

theorem addW64_eq (a b : Limb) : IntTy.addW (.u 64) a.w b.w = (addMod a b).w := by
  simp only [IntTy.addW, val_u, Limb.toNat_w]
  rw [show ((a.val : ℤ) + b.val) = ((a.val + b.val : ℕ) : ℤ) by push_cast; ring,
    wrap_u_nat _ _]
  rfl

theorem subW64_eq (a b : Limb) : IntTy.subW (.u 64) a.w b.w = (subMod a b).w := by
  simp only [IntTy.subW, val_u, Limb.toNat_w]
  rw [wrap_u_sub _ _ _ (le_of_lt b.isLt)]
  rfl

/-- `mac` on limbs. -/
theorem mac_eq (a b c d : Limb) :
    mac a.w b.w c.w d.w = pure ((macLo a b c d).w, (macHi a b c d).w) := by
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt a.isLt) (Nat.le_pred_of_lt b.isLt)
  have := c.isLt; have := d.isLt
  simp only [Nat.pred_eq_sub_one] at hab
  simp only [mac, IntTy.mul, IntTy.add, IntTy.checked, IntTy.Fits, val_u, Limb.toNat_w]
  rw [show ((a.val : ℤ) * b.val) = ((a.val * b.val : ℕ) : ℤ) by push_cast; ring,
    if_pos (by constructor <;> omega), wrap_u_nat _ _, pure_bind,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega),
    show ((a.val * b.val : ℕ) : ℤ) + c.val = ((a.val * b.val + c.val : ℕ) : ℤ) by push_cast; ring,
    if_pos (by constructor <;> omega), wrap_u_nat _ _, pure_bind,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega),
    show ((a.val * b.val + c.val : ℕ) : ℤ) + d.val = ((a.val * b.val + c.val + d.val : ℕ) : ℤ) by
      push_cast; ring,
    if_pos (by constructor <;> omega), wrap_u_nat _ _, pure_bind,
    Nat.mod_eq_of_lt (show a.val * b.val + c.val + d.val < 2 ^ 128 by omega),
    downcast_truncate_u128_u64_eq, pure_bind, toNat_ofNat_lt (by omega),
    downcast_truncate_u128_u64_eq, pure_bind, shiftRight_toNat _ (show 64 < 256 by decide),
    toNat_ofNat_lt (by omega)]
  congr 2
  apply word_eq_of_toNat
  simp only [Limb.toNat_w, macHi]
  rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end FeProofs.Modexp

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## Powers as numerals, for `omega` -/

theorem pow63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
theorem pow64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
theorem pow127 : (2 : ℕ) ^ 127 = 170141183460469231731687303715884105728 := by norm_num
theorem pow128 : (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
theorem pow192 : (2 : ℕ) ^ 192 =
    6277101735386680763835789423207666416102355444464034512896 := by norm_num

/-! ## Wrapping one limb at a time -/

theorem subm_ge {p d : ℕ} (hp : p < 2 ^ 64) (h : d ≤ p) : (p + 2 ^ 64 - d) % 2 ^ 64 = p - d := by
  rw [show p + 2 ^ 64 - d = (p - d) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem subm_lt {p d : ℕ} (hd : d ≤ 2 ^ 64) (h : p < d) :
    (p + 2 ^ 64 - d) % 2 ^ 64 = p + 2 ^ 64 - d := Nat.mod_eq_of_lt (by omega)

theorem addm_lt {p d : ℕ} (h : p + d < 2 ^ 64) : (p + d) % 2 ^ 64 = p + d := Nat.mod_eq_of_lt h

theorem addm_ge {p d : ℕ} (hp : p < 2 ^ 64) (hd : d < 2 ^ 64) (h : 2 ^ 64 ≤ p + d) :
    (p + d) % 2 ^ 64 = p + d - 2 ^ 64 := by
  rw [show p + d = (p + d - 2 ^ 64) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]; omega

/-! ## Double limbs -/

/-- A 128-bit value. -/
abbrev Dbl := Fin (2 ^ 128)

/-- The word of a double limb. -/
def Dbl.w (x : Dbl) : UInt256 := UInt256.ofNat x.val

@[simp] theorem Dbl.toNat_w (x : Dbl) : x.w.toNat = x.val :=
  toNat_lit (lt_trans x.isLt (by decide))

theorem Limb.lt_dbl (a : Limb) : a.val < 2 ^ 128 := lt_trans a.isLt (by decide)

theorem mul_limbs_lt (a b : Limb) : a.val * b.val < 2 ^ 128 := by
  have := Nat.mul_lt_mul'' a.isLt b.isLt; simpa using this

/-- The product of two limbs. -/
def mulD (a b : Limb) : Dbl := ⟨a.val * b.val, mul_limbs_lt a b⟩

/-- A limb shifted up a limb, and a limb below it. -/
def joinD (h l : Limb) : Dbl :=
  ⟨h.val * 2 ^ 64 + l.val, by have := h.isLt; have := l.isLt; omega⟩

def addD (x y : Dbl) : Dbl := ⟨(x.val + y.val) % 2 ^ 128, Nat.mod_lt _ (by decide)⟩
def subD (x y : Dbl) : Dbl := ⟨(x.val + 2 ^ 128 - y.val) % 2 ^ 128, Nat.mod_lt _ (by decide)⟩
def hiD (x : Dbl) : Limb :=
  ⟨x.val / 2 ^ 64, by have := x.isLt; rw [Nat.div_lt_iff_lt_mul (by decide)]; omega⟩
def loD (x : Dbl) : Limb := ⟨x.val % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

theorem Limb.w_eq_dbl (a : Limb) : a.w = Dbl.w ⟨a.val, Limb.lt_dbl a⟩ := rfl

theorem mulW128_eq (a b : Limb) : IntTy.mulW (.u 128) a.w b.w = (mulD a b).w := by
  simp only [IntTy.mulW, val_u, Limb.toNat_w]
  rw [show ((a.val : ℤ) * b.val) = ((a.val * b.val : ℕ) : ℤ) by push_cast; ring, wrap_u_nat,
    Nat.mod_eq_of_lt (mul_limbs_lt a b)]
  rfl

theorem shl128_join (h l : Limb) :
    IntTy.shl (.u 128) h.w (UInt256.ofNat 64) ||| l.w = (joinD h l).w := by
  have := h.isLt; have := l.isLt
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact]
  simp only [IntTy.shl, val_u, Limb.toNat_w, show (UInt256.ofNat 64).toNat = 64 from rfl,
    show (256 ≤ 64) = False by decide, if_false]
  rw [show ((h.val : ℤ) * 2 ^ 64) = ((h.val * 2 ^ 64 : ℕ) : ℤ) by push_cast; ring, wrap_u_nat,
    Nat.mod_eq_of_lt (by omega), toNat_lit (by omega), Dbl.toNat_w, joinD]
  simp only
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt l.isLt]

theorem addW128_eq (x y : Dbl) : IntTy.addW (.u 128) x.w y.w = (addD x y).w := by
  simp only [IntTy.addW, val_u, Dbl.toNat_w]
  rw [show ((x.val : ℤ) + y.val) = ((x.val + y.val : ℕ) : ℤ) by push_cast; ring, wrap_u_nat]
  rfl

theorem subW128_eq (x y : Dbl) : IntTy.subW (.u 128) x.w y.w = (subD x y).w := by
  simp only [IntTy.subW, val_u, Dbl.toNat_w]
  rw [wrap_u_sub _ _ _ (le_of_lt y.isLt)]
  rfl

theorem shr64_eq (x : Dbl) : x.w >>> UInt256.ofNat 64 = (hiD x).w := by
  apply word_eq_of_toNat
  rw [shiftRight_toNat _ (by decide)]
  simp [hiD]

theorem down128_eq (x : Dbl) : downcast_truncate_u128_u64 x.w = pure (loD x).w := by
  rw [downcast_truncate_u128_u64_eq, Dbl.toNat_w]; rfl

theorem down128_limb_eq (x : Limb) : downcast_truncate_u128_u64 x.w = pure x.w := by
  rw [downcast_truncate_u128_u64_eq, Limb.toNat_w, Nat.mod_eq_of_lt x.isLt]; rfl

end FeProofs.Modexp
