import FeProofs.Precompiles.Exported.Ripemd160
import FeProofs.Precompiles.Inverse.Signed
import FeProofs.Precompiles.Ripemd160.CompressSpec

/-!
# Ripemd160: 32-bit words

fevm's RIPEMD-160 computes with `u32` values, which the exporter keeps as words below `2 ^ 32`.
`lw32 x` is the word of `x : UInt32`; on such words the exported wrapping add, shifts, bitwise
operations, `rotate_left` and `f0` to `f4` are the `UInt32` ones (`addW_lw32` and the rest).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ripemd160

open FeProofs.Precompiles
open Precompiles.Exported.Ripemd160

/-- A 32-bit word as the exported code holds it. -/
def lw32 (x : UInt32) : UInt256 := UInt256.ofNat x.toNat

theorem lw32_lt (x : UInt32) : x.toNat < 2 ^ 256 := lt_trans x.toNat_lt (by decide)

@[simp] theorem lw32_toNat (x : UInt32) : (lw32 x).toNat = x.toNat := toNat_lit (lw32_lt x)

theorem addW_lw32 (x y : UInt32) : IntTy.addW (.u 32) (lw32 x) (lw32 y) = lw32 (x + y) := by
  simp only [IntTy.addW, IntTy.val, IntTy.wrap, lw32_toNat]
  unfold lw32
  congr 1

theorem addW_lit (x : UInt32) {c : ℕ} (hc : c < 2 ^ 32) :
    IntTy.addW (.u 32) (lw32 x) (UInt256.ofNat c) = lw32 (x + UInt32.ofNat c) := by
  have : UInt256.ofNat c = lw32 (UInt32.ofNat c) := by
    simp only [lw32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hc]
  rw [this, addW_lw32]

theorem xor_lw32 (x y : UInt32) : lw32 x ^^^ lw32 y = lw32 (x ^^^ y) := by
  apply word_eq_of_toNat
  change (UInt256.xor _ _).toNat = _
  rw [lw32_toNat, UInt32.toNat_xor]
  change ((x.toNat % 2 ^ 256) ^^^ (y.toNat % 2 ^ 256)) % 2 ^ 256 = _
  rw [Nat.mod_eq_of_lt (lw32_lt x), Nat.mod_eq_of_lt (lw32_lt y),
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 256) (lw32_lt x) (lw32_lt y))]

theorem or_lw32 (x y : UInt32) : lw32 x ||| lw32 y = lw32 (x ||| y) := by
  rw [lw32, lw32, lor_eq (lw32_lt x) (lw32_lt y), lw32, UInt32.toNat_or]

theorem and_lw32 (x y : UInt32) : lw32 x &&& lw32 y = lw32 (x &&& y) := by
  rw [lw32, lw32, land_eq (lw32_lt x) (lw32_lt y), lw32, UInt32.toNat_and]

theorem not_lw32 (x : UInt32) : IntTy.not (.u 32) (lw32 x) = lw32 (~~~x) := by
  have hx := x.toNat_lt
  have hz : (-(x.toNat : ℤ) - 1) % 2 ^ 32 = ((2 ^ 32 - 1 - x.toNat : ℕ) : ℤ) := by
    have e : (-(x.toNat : ℤ) - 1) = ((2 ^ 32 - 1 - x.toNat : ℕ) : ℤ) + 2 ^ 32 * (-1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by omega)]
  simp only [IntTy.not, IntTy.wrap, IntTy.val, lw32, toNat_lit (lw32_lt x), hz, Int.toNat_natCast,
    UInt32.toNat_not]
  rfl

theorem shl_lw32 (x : UInt32) {k : ℕ} (hk : k < 32) :
    IntTy.shl (.u 32) (lw32 x) (UInt256.ofNat k) = lw32 (x <<< UInt32.ofNat k) := by
  have hko : (UInt32.ofNat k).toNat = k := by rw [UInt32.toNat_ofNat']; omega
  simp only [IntTy.shl, IntTy.val, IntTy.wrap, lw32_toNat, toNat_lit (show k < 2 ^ 256 by omega),
    show ¬ 256 ≤ k by omega, ite_false]
  unfold lw32
  congr 1
  rw [UInt32.toNat_shiftLeft, hko, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq]
  have : ((x.toNat : ℤ) * 2 ^ k) = ((x.toNat * 2 ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [this]
  omega

theorem shr_lw32 (x : UInt32) {k : ℕ} (hk : k < 32) :
    lw32 x >>> UInt256.ofNat k = lw32 (x >>> UInt32.ofNat k) := by
  have hko : (UInt32.ofNat k).toNat = k := by rw [UInt32.toNat_ofNat']; omega
  rw [lw32, ushr_eq (lw32_lt x) (show k < 256 by omega), lw32, UInt32.toNat_shiftRight, hko,
    Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem sub32 {k : ℕ} (hk : k ≤ 32) :
    IntTy.sub (.u 32) (UInt256.ofNat 32) (UInt256.ofNat k) = pure (UInt256.ofNat (32 - k)) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show 32 < 2 ^ 256 by decide), toNat_lit (show k < 2 ^ 256 by omega)]
  rw [ite_eq_left (by constructor <;> omega)]
  congr 2
  omega

/-- `rotate_left`: `RIPEMD160.rol`. -/
theorem rotate_lw32 (x : UInt32) {k : ℕ} (hk0 : 0 < k) (hk : k < 32) :
    rotate_left (lw32 x) (UInt256.ofNat k) = pure (lw32 (RIPEMD160.rol x k)) := by
  simp only [rotate_left, sub32 (show k ≤ 32 by omega), pure_bind, shl_lw32 x hk,
    shr_lw32 x (show 32 - k < 32 by omega), or_lw32]
  rfl

theorem f0_lw32 (x y z : UInt32) : f0 (lw32 x) (lw32 y) (lw32 z) = pure (lw32 (F0 x y z)) := by
  simp only [f0, xor_lw32]; rfl

theorem f1_lw32 (x y z : UInt32) : f1 (lw32 x) (lw32 y) (lw32 z) = pure (lw32 (F1 x y z)) := by
  simp only [f1, and_lw32, not_lw32, or_lw32]; rfl

theorem f2_lw32 (x y z : UInt32) : f2 (lw32 x) (lw32 y) (lw32 z) = pure (lw32 (F2 x y z)) := by
  simp only [f2, not_lw32, or_lw32, xor_lw32]; rfl

theorem f3_lw32 (x y z : UInt32) : f3 (lw32 x) (lw32 y) (lw32 z) = pure (lw32 (F3 x y z)) := by
  simp only [f3, and_lw32, not_lw32, or_lw32]; rfl

theorem f4_lw32 (x y z : UInt32) : f4 (lw32 x) (lw32 y) (lw32 z) = pure (lw32 (F4 x y z)) := by
  simp only [f4, not_lw32, or_lw32, xor_lw32]; rfl

/-! ## The state and the block -/

/-- The state as the exported `[u32; 5]`. -/
def toV5 (S : RIPEMD160.State) : Vector UInt256 5 :=
  #v[lw32 S.h₀, lw32 S.h₁, lw32 S.h₂, lw32 S.h₃, lw32 S.h₄]

/-- A block of bytes as the exported `[u8; 64]`. -/
def toBlk (B : ℕ → UInt8) : Vector UInt256 64 := Vector.ofFn fun k => lw32 (B k.val).toUInt32

theorem toBlk_get (B : ℕ → UInt8) {k : ℕ} (hk : k < 64) : (toBlk B)[k]! = lw32 (B k).toUInt32 := by
  simp [toBlk, hk]

theorem toV5_get0 (S : RIPEMD160.State) : (toV5 S)[0]! = lw32 S.h₀ := rfl
theorem toV5_get1 (S : RIPEMD160.State) : (toV5 S)[1]! = lw32 S.h₁ := rfl
theorem toV5_get2 (S : RIPEMD160.State) : (toV5 S)[2]! = lw32 S.h₂ := rfl
theorem toV5_get3 (S : RIPEMD160.State) : (toV5 S)[3]! = lw32 S.h₃ := rfl
theorem toV5_get4 (S : RIPEMD160.State) : (toV5 S)[4]! = lw32 S.h₄ := rfl

theorem toV5_set0 (S : RIPEMD160.State) (x : UInt32) :
    (toV5 S).set! 0 (lw32 x) = toV5 ⟨x, S.h₁, S.h₂, S.h₃, S.h₄⟩ := rfl
theorem toV5_set1 (S : RIPEMD160.State) (x : UInt32) :
    (toV5 S).set! 1 (lw32 x) = toV5 ⟨S.h₀, x, S.h₂, S.h₃, S.h₄⟩ := rfl
theorem toV5_set2 (S : RIPEMD160.State) (x : UInt32) :
    (toV5 S).set! 2 (lw32 x) = toV5 ⟨S.h₀, S.h₁, x, S.h₃, S.h₄⟩ := rfl
theorem toV5_set3 (S : RIPEMD160.State) (x : UInt32) :
    (toV5 S).set! 3 (lw32 x) = toV5 ⟨S.h₀, S.h₁, S.h₂, x, S.h₄⟩ := rfl
theorem toV5_set4 (S : RIPEMD160.State) (x : UInt32) :
    (toV5 S).set! 4 (lw32 x) = toV5 ⟨S.h₀, S.h₁, S.h₂, S.h₃, x⟩ := rfl

theorem checkIndex_lit {k n : ℕ} (h : k < n) (hn : n < 2 ^ 256) :
    checkIndex (UInt256.ofNat k) n = pure () := by
  simp [checkIndex, toNat_lit (show k < 2 ^ 256 by omega), h]

end FeProofs.Ripemd160
