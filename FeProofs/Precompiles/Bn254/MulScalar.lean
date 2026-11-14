import FeProofs.Precompiles.Bn254.Add
import FeProofs.Precompiles.Exported.Bn254Mul
import FeProofs.Precompiles.Field.Checked
import Ethereum.BN254.Order

/-!
# Bn254Mul: the GLV decomposition

`multiply_g1` reduces the scalar modulo `r`, takes approximate quotients `c₁, c₂` from the top
128 bits and fevm's `GLV_G1`, `GLV_G2`, and splits the scalar as `k₁ = k − c₁ a₁ − c₂ a₂`,
`k₂ = c₁ b₁ − c₂ b₂` in 256-bit two's complement, read back as a magnitude and a sign
(`magnitude`).  For every scalar below `2 ^ 256`:

* no checked product overflows, and `|k₁|, |k₂| < 2 ^ 130` as fevm's comment says
  (`z1_bound`, `z2_bound`), so the two's complement words hold the integers and `magnitude`
  reads their signs (`magnitude_eq`);
* `k₁ + k₂ λ ≡ k (mod r)` (`glv_congr`), since `a₁ − b₁ λ` and `a₂ + b₂ λ` are multiples of `r`
  (EVMLean's `glv_1`, `glv_2`, here as the integer identities `glv_1'`, `glv_2'`).

All bounds are linear in the scalar with constant coefficients, which `omega` checks.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul

/-- The integers of the decomposition, for the reduced scalar `kr`. -/
def c1Of (kr : ℕ) : ℕ := kr / 2 ^ 128 * 0x2d91d232ec7e0b3d7 / 2 ^ 128
def c2Of (kr : ℕ) : ℕ := kr / 2 ^ 128 * 0x24ccef014a773d2cf7a7bd9d4391eb18d / 2 ^ 128
def z1Of (kr : ℕ) : ℤ := kr - c1Of kr * BN254.GLV_A1 - c2Of kr * BN254.GLV_A2
def z2Of (kr : ℕ) : ℤ := c1Of kr * BN254.GLV_B1 - c2Of kr * BN254.GLV_B2

theorem A1_val : BN254.GLV_A1 = 9931322734385697763 := rfl
theorem A2_val : BN254.GLV_A2 = 147946756881789319010696353538189108491 := rfl
theorem B1_val : BN254.GLV_B1 = 147946756881789319000765030803803410728 := rfl
theorem B2_val : BN254.GLV_B2 = 9931322734385697763 := rfl
theorem L_val : BN254.LAMBDA = 4407920970296243842393367215006156084916469457145843978461 := rfl
theorem r_val : BN254.r =
    21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl

/-- `a₁ − b₁ λ` is a multiple of `r`. -/
theorem glv_1' : (BN254.GLV_A1 : ℤ) - BN254.GLV_B1 * BN254.LAMBDA =
    -29793968203157093285 * BN254.r := by
  rw [A1_val, B1_val, L_val, r_val]; norm_num

/-- `a₂ + b₂ λ` is a multiple of `r`. -/
theorem glv_2' : (BN254.GLV_A2 : ℤ) + BN254.GLV_B2 * BN254.LAMBDA = 2 * BN254.r := by
  rw [A2_val, B2_val, L_val, r_val]; norm_num

/-- **The decomposition**: `k₁ + k₂ λ ≡ k (mod r)`. -/
theorem glv_congr (kr : ℕ) : z1Of kr + z2Of kr * BN254.LAMBDA ≡ kr [ZMOD BN254.r] := by
  have e : z1Of kr + z2Of kr * BN254.LAMBDA = kr - c1Of kr * ((BN254.GLV_A1 : ℤ) -
      BN254.GLV_B1 * BN254.LAMBDA) - c2Of kr * ((BN254.GLV_A2 : ℤ) + BN254.GLV_B2 * BN254.LAMBDA) := by
    unfold z1Of z2Of; ring
  rw [e, glv_1', glv_2', Int.ModEq]
  have : (kr : ℤ) - c1Of kr * (-29793968203157093285 * BN254.r) - c2Of kr * (2 * BN254.r) =
      kr + BN254.r * (c1Of kr * 29793968203157093285 - c2Of kr * 2) := by ring
  rw [this, Int.add_mul_emod_self_left]

theorem z1_bound {kr : ℕ} (hk : kr < BN254.r) : -(2 ^ 130 : ℤ) < z1Of kr ∧ z1Of kr < 2 ^ 130 := by
  unfold z1Of c1Of c2Of
  rw [A1_val, A2_val]
  rw [r_val] at hk
  omega

theorem z2_bound {kr : ℕ} (hk : kr < BN254.r) : -(2 ^ 130 : ℤ) < z2Of kr ∧ z2Of kr < 2 ^ 130 := by
  unfold z2Of c1Of c2Of
  rw [B1_val, B2_val]
  rw [r_val] at hk
  omega

theorem kr_bounds {kr : ℕ} (hk : kr < BN254.r) :
    kr / 2 ^ 128 * 0x2d91d232ec7e0b3d7 < 2 ^ 256 ∧
      kr / 2 ^ 128 * 0x24ccef014a773d2cf7a7bd9d4391eb18d < 2 ^ 256 ∧
      c1Of kr * BN254.GLV_A1 < 2 ^ 256 ∧ c2Of kr * BN254.GLV_A2 < 2 ^ 256 ∧
      c1Of kr * BN254.GLV_B1 < 2 ^ 256 ∧ c2Of kr * BN254.GLV_B2 < 2 ^ 256 := by
  unfold c1Of c2Of
  rw [A1_val, A2_val, B1_val, B2_val]
  rw [r_val] at hk
  omega

/-! ## Two's complement words -/

/-- The 256-bit two's complement word of an integer. -/
def toWord (z : ℤ) : UInt256 := UInt256.ofNat (z % 2 ^ 256).toNat

theorem toWord_toNat (z : ℤ) : (toWord z).toNat = (z % 2 ^ 256).toNat :=
  toNat_lit (by omega)

theorem toWord_ofNat {n : ℕ} (hn : n < 2 ^ 256) : toWord n = UInt256.ofNat n := by
  apply word_eq_of_toNat
  rw [toWord_toNat, toNat_lit hn]
  omega

theorem sub_toNat (a b : UInt256) :
    (a - b).toNat = (a.toNat + (2 ^ 256 - b.toNat)) % 2 ^ 256 := by
  have ha := a.val.isLt
  have hb := b.val.isLt
  change (UInt256.sub a b).toNat = _
  change a.toNat < 2 ^ 256 at ha
  change b.toNat < 2 ^ 256 at hb
  by_cases h : b.toNat ≤ a.toNat
  · rw [usub_toNat h]; omega
  · rw [usub_toNat_underflow (by omega)]; change 2 ^ 256 + _ - _ = _; omega

theorem toWord_sub (x y : ℤ) : toWord x - toWord y = toWord (x - y) := by
  apply word_eq_of_toNat
  rw [sub_toNat, toWord_toNat, toWord_toNat, toWord_toNat]
  omega

/-- `magnitude` reads an integer of magnitude below `2 ^ 255` from its word. -/
theorem magnitude_eq {z : ℤ} (h1 : -(2 ^ 255 : ℤ) < z) (h2 : z < 2 ^ 255) :
    magnitude (toWord z) = pure (UInt256.ofNat z.natAbs, decide (z < 0)) := by
  have e : toWord z >>> UInt256.ofNat 255 = UInt256.ofNat (if z < 0 then 1 else 0) := by
    apply word_eq_of_toNat
    rw [shiftRight_toNat _ (by decide), toWord_toNat]
    split_ifs with hz <;> rw [toNat_lit (by decide)] <;> omega
  simp only [magnitude, e, Lib.u256_wrapping_sub]
  by_cases hz : z < 0
  · simp only [hz, if_true, decide_true, pure_bind]
    rw [← toWord_ofNat (n := 0) (by decide), toWord_sub,
      show ((0 : ℕ) : ℤ) - z = (z.natAbs : ℤ) by omega, toWord_ofNat (by omega)]
  · simp only [hz, if_false, decide_false, pure_bind]
    have : ¬ (UInt256.ofNat 0 = UInt256.ofNat 1) := by decide
    simp only [this, decide_false, Bool.false_eq_true, if_false]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hz)
    rw [toWord_ofNat (by omega), Int.natAbs_natCast]

/-! ## The decomposition in `multiply_g1` -/

theorem r_lit : (21888242871839275222246405745257275088548364400416034343698204186575808495617 : ℕ) =
    BN254.r := rfl

theorem r_lt : BN254.r < 2 ^ 256 := by rw [r_val]; decide

/-- `multiply_g1` up to the call of its second half: the reduced scalar's approximate quotients
and the first half-scalar, read by `magnitude`. -/
theorem multiply_g1_eq (P : Point_Mont_Bn254Base) (k : UInt256) :
    multiply_g1 P k = multiply_g1_k1 P (UInt256.ofNat (c1Of (k.toNat % BN254.r)))
      (UInt256.ofNat (c2Of (k.toNat % BN254.r)))
      (UInt256.ofNat (z1Of (k.toNat % BN254.r)).natAbs, decide (z1Of (k.toNat % BN254.r) < 0))
      default default default default default default default default default default default
      default default default default default default default := by
  have hk : k.toNat % BN254.r < BN254.r := Nat.mod_lt _ (by rw [r_val]; decide)
  obtain ⟨b1, b2, b3, b4, -, -⟩ := kr_bounds hk
  have hz := z1_bound hk
  have hkr : k.toNat % BN254.r < 2 ^ 256 := lt_trans hk r_lt
  have hq : k.toNat % BN254.r / 2 ^ 128 < 2 ^ 256 := by omega
  simp only [multiply_g1, ORDER, GLV_G1, GLV_G2, GLV_A1, GLV_A2, pure_bind]
  rw [checkedRem_lit k (b := 21888242871839275222246405745257275088548364400416034343698204186575808495617)
    (by decide) (by decide), r_lit, pure_bind, ushr_eq hkr (show 128 < 256 by decide),
    checkedMul_small hq (by decide) b1, pure_bind, checkedMul_small hq (by decide) b2, pure_bind,
    ushr_eq b1 (show 128 < 256 by decide), ushr_eq b2 (show 128 < 256 by decide)]
  rw [show k.toNat % BN254.r / 2 ^ 128 * 52538187511802934231 / 2 ^ 128 = c1Of (k.toNat % BN254.r)
      from rfl,
    show k.toNat % BN254.r / 2 ^ 128 * 782660544089080853078787955015628534157 / 2 ^ 128 =
      c2Of (k.toNat % BN254.r) from rfl,
    show (9931322734385697763 : ℕ) = BN254.GLV_A1 from rfl,
    show (147946756881789319010696353538189108491 : ℕ) = BN254.GLV_A2 from rfl,
    checkedMul_small (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by rw [A1_val]; decide)) b3)
      (by rw [A1_val]; decide) b3,
    checkedMul_small (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by rw [A2_val]; decide)) b4)
      (by rw [A2_val]; decide) b4]
  simp only [Lib.u256_wrapping_sub, pure_bind]
  rw [← toWord_ofNat hkr, ← toWord_ofNat b3, ← toWord_ofNat b4, toWord_sub, toWord_sub,
    show ((k.toNat % BN254.r : ℕ) : ℤ) - ((c1Of (k.toNat % BN254.r) * BN254.GLV_A1 : ℕ) : ℤ) -
      ((c2Of (k.toNat % BN254.r) * BN254.GLV_A2 : ℕ) : ℤ) = z1Of (k.toNat % BN254.r) by
        unfold z1Of; push_cast; ring,
    magnitude_eq (by omega) (by omega), pure_bind]

end FeProofs.Bn254Mul
