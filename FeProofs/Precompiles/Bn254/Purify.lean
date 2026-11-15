import FeProofs.Precompiles.Field.MontPure
import FeProofs.Precompiles.Exported.Bn254Add

/-!
# Bn254Add: the exported Montgomery code is pure

Each exported Montgomery method of `Bn254Base`, at limbs, is `pure` of the method of
`MontPure.lean` at the constants `KBn` of the BN254 base field prime.  The exported text is
secp256k1's `Base` at other constants, and the tactics are those of `Secp256k1/Purify.lean`
over this contract's names.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add

/-- The constants of `Bn254Base`, the BN254 base field prime. -/
def KBn : Modulus where
  P0 := ⟨4332616871279656263, by decide⟩
  P1 := ⟨10917124144477883021, by decide⟩
  P2 := ⟨13281191951274694749, by decide⟩
  P3 := ⟨3486998266802970665, by decide⟩
  INV := ⟨9786893198990664585, by decide⟩
  R2 := 3096616502983703923843567936837374451735540968419076528771170197431451843209

/-- The word form of four limbs, as `Bn254Base`. -/
def toBn (a : L4) : Mont_Bn254Base := ⟨a.l0.w, a.l1.w, a.l2.w, a.l3.w⟩

theorem Bn254Base_P0_eq : Bn254Base_P0 = pure KBn.P0.w := rfl
theorem Bn254Base_P1_eq : Bn254Base_P1 = pure KBn.P1.w := rfl
theorem Bn254Base_P2_eq : Bn254Base_P2 = pure KBn.P2.w := rfl
theorem Bn254Base_P3_eq : Bn254Base_P3 = pure KBn.P3.w := rfl
theorem Bn254Base_INV_eq : Bn254Base_INV = pure KBn.INV.w := rfl

@[simp] theorem toBn_l0 (a : L4) : (toBn a).l0 = a.l0.w := rfl
@[simp] theorem toBn_l1 (a : L4) : (toBn a).l1 = a.l1.w := rfl
@[simp] theorem toBn_l2 (a : L4) : (toBn a).l2 = a.l2.w := rfl
@[simp] theorem toBn_l3 (a : L4) : (toBn a).l3 = a.l3.w := rfl

theorem mk_toBn (a b c d : Limb) : (⟨a.w, b.w, c.w, d.w⟩ : Mont_Bn254Base) = toBn ⟨a, b, c, d⟩ :=
  rfl

/-- The tactic that turns an exported Montgomery method into its pure form: unfold the method
and the helpers it calls into their pure forms, then compare. -/
macro "purify_bn" : tactic => `(tactic| (
  simp only [Mont_shift_reduced_Bn254Base, Mont_shift_reduced_Bn254Base_k1,
    Mont_shift_reduced_Bn254Base_k2, Mont_shift_reduced_Bn254Base_k3, Mont_first_row_Bn254Base,
    Mont_first_row_Bn254Base_k1, Mont_row_Bn254Base, Mont_row_Bn254Base_k1, Mont_row_Bn254Base_k2,
    Mont_row_Bn254Base_k3, Mont_reduce_Bn254Base, Bn254Base_P0_eq, Bn254Base_P1_eq,
    Bn254Base_P2_eq, Bn254Base_P3_eq, Bn254Base_INV_eq, toBn, zero_w, mul_wide_eq, adc_eq,
    sbb_eq _ _ _ (sbbHi_val_le _ _ _), sbb_eq _ _ _ zero_val_le, u64_wrapping_mul_eq,
    pure_bind, one_w, Limb.w_inj, decide_eq_true_eq]
  first
  | (split <;> rename_i h <;> simp only [Mont.reduce, Mont.sub, h, ↓reduceIte])
  | rfl))

theorem shift_reduced_Bn254Base (s0 s1 s2 s3 s4 s5 : Limb) :
    Mont_shift_reduced_Bn254Base s0.w s1.w s2.w s3.w s4.w s5.w =
      pure (toBn (Mont.shiftReduced KBn s0 s1 s2 s3 s4 s5).1,
        (Mont.shiftReduced KBn s0 s1 s2 s3 s4 s5).2.w) := by
  purify_bn

theorem first_row_Bn254Base (a : L4) (b : Limb) :
    Mont_first_row_Bn254Base (toBn a) b.w =
      pure (toBn (Mont.firstRow KBn a b).1, (Mont.firstRow KBn a b).2.w) := by
  purify_bn

theorem row_Bn254Base (a : L4) (b : Limb) (t : L4) (top : Limb) :
    Mont_row_Bn254Base (toBn a) b.w (toBn t) top.w =
      pure (toBn (Mont.row KBn a b t top).1, (Mont.row KBn a b t top).2.w) := by
  purify_bn

theorem reduce_Bn254Base (a : L4) (top : Limb) :
    Mont_reduce_Bn254Base (toBn a) top.w = pure (toBn (Mont.reduce KBn a top)) := by
  purify_bn

namespace Bn254Base
/-- The BN254 base field prime, as the exported `MODULUS`. -/
def value : ℕ := 21888242871839275222246405745257275088696311157297823662689037894645226208583
end Bn254Base

/-- The tactic for the methods built on `first_row`, `row` and `reduce`. -/
macro "purify_mont_bn" : tactic => `(tactic| (
  simp only [Mont_mul_Bn254Base, Mont_add_Bn254Base, Mont_double_Bn254Base,
    Mont_square_Bn254Base, Mont_sub_Bn254Base, Mont_sub_Bn254Base_k1, Mont_sub_Bn254Base_k2,
    Mont_zero_Bn254Base, first_row_Bn254Base, row_Bn254Base, reduce_Bn254Base, toBn_l0, toBn_l1,
    toBn_l2, toBn_l3, Bn254Base_P0_eq, Bn254Base_P1_eq, Bn254Base_P2_eq, Bn254Base_P3_eq, zero_w,
    adc_eq, sbb_eq _ _ _ (sbbHi_val_le _ _ _), sbb_eq _ _ _ zero_val_le, pure_bind, one_w,
    Limb.w_inj, decide_eq_true_eq, mk_toBn]
  first
  | (split <;> rename_i h <;> simp only [Mont.sub, Mont.zero, toBn, h, ↓reduceIte])
  | rfl))

theorem mul_Bn254Base (a b : L4) :
    Mont_mul_Bn254Base (toBn a) (toBn b) = pure (toBn (Mont.mul KBn a b)) := by
  purify_mont_bn

theorem sub_Bn254Base (a b : L4) :
    Mont_sub_Bn254Base (toBn a) (toBn b) = pure (toBn (Mont.sub KBn a b)) := by
  purify_mont_bn

theorem zero_Bn254Base : Mont_zero_Bn254Base = pure (toBn Mont.zero) := rfl

theorem add_Bn254Base (a b : L4) :
    Mont_add_Bn254Base (toBn a) (toBn b) = pure (toBn (Mont.add KBn a b)) := by
  purify_mont_bn

theorem double_Bn254Base (a : L4) :
    Mont_double_Bn254Base (toBn a) = pure (toBn (Mont.add KBn a a)) := by
  simp only [Mont_double_Bn254Base, add_Bn254Base, pure_bind]

theorem square_Bn254Base (a : L4) :
    Mont_square_Bn254Base (toBn a) = pure (toBn (Mont.mul KBn a a)) := by
  simp only [Mont_square_Bn254Base, mul_Bn254Base, pure_bind]

theorem raw_Bn254Base_eq (v : UInt256) : raw_Bn254Base v = pure (toBn (Mont.raw v.toNat)) := by
  simp only [raw_Bn254Base, downcast_truncate_u256_u64_eq,
    shiftRight_toNat _ (show 64 < 256 by decide), shiftRight_toNat _ (show 128 < 256 by decide),
    shiftRight_toNat _ (show 192 < 256 by decide), pure_bind]
  rfl

/-- `new` of a canonical value: `value * R2` reduced. -/
theorem new_Bn254Base (v : UInt256) (hv : v.toNat < Bn254Base.value) :
    Mont_new_Bn254Base v = pure (toBn (Mont.new KBn v.toNat)) := by
  simp only [Mont_new_Bn254Base, Bn254Base_VALUE, MODULUS, Bn254Base_R2, pure_bind,
    raw_Bn254Base_eq, mul_Bn254Base]
  rw [toNat_lit (by decide), toNat_lit (by decide)]
  unfold Bn254Base.value at hv
  simp only [Lib.assert, decide_eq_true hv, Bool.not_true, Bool.false_eq_true, ite_false,
    pure_bind]
  rfl

/-- `value`: `a * 1` reduced, assembled into a word. -/
theorem value_Bn254Base (a : L4) :
    Mont_value_Bn254Base (toBn a) = pure (UInt256.ofNat (Mont.value KBn a)) := by
  simp only [Mont_value_Bn254Base, raw_Bn254Base_eq, toNat_lit (show 1 < 2 ^ 256 by decide),
    mul_Bn254Base, pure_bind, toBn_l0, toBn_l1, toBn_l2, toBn_l3, assemble_eq]
  rfl

theorem one_Bn254Base : Mont_one_Bn254Base = pure (toBn (Mont.new KBn 1)) := by
  simp only [Mont_one_Bn254Base]
  rw [new_Bn254Base _ (by rw [toNat_lit (by decide)]; decide), toNat_lit (by decide)]

/-- `is_zero`: every limb is zero. -/
theorem is_zero_Bn254Base (a : L4) : Mont_is_zero_Bn254Base (toBn a) = pure (Mont.isZero a) := by
  simp only [Mont_is_zero_Bn254Base, toBn_l0, toBn_l1, toBn_l2, toBn_l3, zero_w, Limb.w_inj,
    decide_eq_true_eq, Mont.isZero]
  by_cases h0 : a.l0 = 0 <;> by_cases h1 : a.l1 = 0 <;> by_cases h2 : a.l2 = 0 <;>
    by_cases h3 : a.l3 = 0 <;> simp [h0, h1, h2, h3]

/-- `equals`: the limbs are equal. -/
theorem equals_Bn254Base (a b : L4) :
    Mont_equals_Bn254Base (toBn a) (toBn b) = pure (Mont.equals a b) := by
  simp only [Mont_equals_Bn254Base, toBn_l0, toBn_l1, toBn_l2, toBn_l3, Limb.w_inj,
    decide_eq_true_eq, Mont.equals]
  by_cases h0 : a.l0 = b.l0 <;> by_cases h1 : a.l1 = b.l1 <;> by_cases h2 : a.l2 = b.l2 <;>
    by_cases h3 : a.l3 = b.l3 <;> simp [h0, h1, h2, h3]

end FeProofs.Bn254Add
