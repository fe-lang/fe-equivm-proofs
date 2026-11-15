import FeProofs.Precompiles.Field.MontPure
import FeProofs.Precompiles.Exported.Ecrecover

/-!
# Ecrecover: the exported Montgomery code is pure

Each exported Montgomery method, at limbs, is `pure` of the method of `MontPure.lean` at the
constants of its modulus: `KB` for the field prime `p` (`Base`), `KO` for the group order `n`
(`Order`).  The two copies are the same text at different constants, and one tactic proves
each lemma for both (`purify`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

/-- The constants of `Base`, the field prime. -/
def KB : Modulus where
  P0 := ⟨18446744069414583343, by decide⟩
  P1 := ⟨18446744073709551615, by decide⟩
  P2 := ⟨18446744073709551615, by decide⟩
  P3 := ⟨18446744073709551615, by decide⟩
  INV := ⟨15580212934572586289, by decide⟩
  R2 := 18446752466076602529

/-- The constants of `Order`, the group order. -/
def KO : Modulus where
  P0 := ⟨13822214165235122497, by decide⟩
  P1 := ⟨13451932020343611451, by decide⟩
  P2 := ⟨18446744073709551614, by decide⟩
  P3 := ⟨18446744073709551615, by decide⟩
  INV := ⟨5408259542528602431, by decide⟩
  R2 := 71195301480278335217902614543643724933430614355449737089222010364394701574464

/-- The word form of four limbs, as `Base`. -/
def toB (a : L4) : Mont_Base := ⟨a.l0.w, a.l1.w, a.l2.w, a.l3.w⟩

/-- The word form of four limbs, as `Order`. -/
def toO (a : L4) : Mont_Order := ⟨a.l0.w, a.l1.w, a.l2.w, a.l3.w⟩

theorem Base_P0_eq : Base_P0 = pure KB.P0.w := rfl
theorem Base_P1_eq : Base_P1 = pure KB.P1.w := rfl
theorem Base_P2_eq : Base_P2 = pure KB.P2.w := rfl
theorem Base_P3_eq : Base_P3 = pure KB.P3.w := rfl
theorem Base_INV_eq : Base_INV = pure KB.INV.w := rfl
theorem Order_P0_eq : Order_P0 = pure KO.P0.w := rfl
theorem Order_P1_eq : Order_P1 = pure KO.P1.w := rfl
theorem Order_P2_eq : Order_P2 = pure KO.P2.w := rfl
theorem Order_P3_eq : Order_P3 = pure KO.P3.w := rfl
theorem Order_INV_eq : Order_INV = pure KO.INV.w := rfl

@[simp] theorem toB_l0 (a : L4) : (toB a).l0 = a.l0.w := rfl
@[simp] theorem toB_l1 (a : L4) : (toB a).l1 = a.l1.w := rfl
@[simp] theorem toB_l2 (a : L4) : (toB a).l2 = a.l2.w := rfl
@[simp] theorem toB_l3 (a : L4) : (toB a).l3 = a.l3.w := rfl
@[simp] theorem toO_l0 (a : L4) : (toO a).l0 = a.l0.w := rfl
@[simp] theorem toO_l1 (a : L4) : (toO a).l1 = a.l1.w := rfl
@[simp] theorem toO_l2 (a : L4) : (toO a).l2 = a.l2.w := rfl
@[simp] theorem toO_l3 (a : L4) : (toO a).l3 = a.l3.w := rfl

theorem mk_toB (a b c d : Limb) : (⟨a.w, b.w, c.w, d.w⟩ : Mont_Base) = toB ⟨a, b, c, d⟩ := rfl
theorem mk_toO (a b c d : Limb) : (⟨a.w, b.w, c.w, d.w⟩ : Mont_Order) = toO ⟨a, b, c, d⟩ := rfl

/-- The tactic that turns an exported Montgomery method into its pure form: unfold the method
and the helpers it calls into their pure forms, then compare. -/
macro "purify" : tactic => `(tactic| (
  simp only [Mont_shift_reduced_Base, Mont_shift_reduced_Base_k1, Mont_shift_reduced_Base_k2,
    Mont_shift_reduced_Base_k3, Mont_shift_reduced_Order, Mont_shift_reduced_Order_k1,
    Mont_shift_reduced_Order_k2, Mont_shift_reduced_Order_k3, Mont_first_row_Base,
    Mont_first_row_Base_k1, Mont_first_row_Order, Mont_first_row_Order_k1, Mont_row_Base,
    Mont_row_Base_k1, Mont_row_Base_k2, Mont_row_Base_k3, Mont_row_Order, Mont_row_Order_k1,
    Mont_row_Order_k2, Mont_row_Order_k3, Mont_reduce_Base, Mont_reduce_Order,
    Base_P0_eq, Base_P1_eq, Base_P2_eq, Base_P3_eq, Base_INV_eq, Order_P0_eq, Order_P1_eq,
    Order_P2_eq, Order_P3_eq, Order_INV_eq, toB, toO, zero_w, mul_wide_eq, adc_eq,
    sbb_eq _ _ _ (sbbHi_val_le _ _ _), sbb_eq _ _ _ zero_val_le, u64_wrapping_mul_eq,
    pure_bind, one_w, Limb.w_inj, decide_eq_true_eq]
  first
  | (split <;> rename_i h <;> simp only [Mont.reduce, Mont.sub, h, ↓reduceIte])
  | rfl))

theorem shift_reduced_Base (s0 s1 s2 s3 s4 s5 : Limb) :
    Mont_shift_reduced_Base s0.w s1.w s2.w s3.w s4.w s5.w =
      pure (toB (Mont.shiftReduced KB s0 s1 s2 s3 s4 s5).1,
        (Mont.shiftReduced KB s0 s1 s2 s3 s4 s5).2.w) := by
  purify

theorem first_row_Base (a : L4) (b : Limb) :
    Mont_first_row_Base (toB a) b.w =
      pure (toB (Mont.firstRow KB a b).1, (Mont.firstRow KB a b).2.w) := by
  purify

theorem row_Base (a : L4) (b : Limb) (t : L4) (top : Limb) :
    Mont_row_Base (toB a) b.w (toB t) top.w =
      pure (toB (Mont.row KB a b t top).1, (Mont.row KB a b t top).2.w) := by
  purify

theorem reduce_Base (a : L4) (top : Limb) :
    Mont_reduce_Base (toB a) top.w = pure (toB (Mont.reduce KB a top)) := by
  purify

theorem shift_reduced_Order (s0 s1 s2 s3 s4 s5 : Limb) :
    Mont_shift_reduced_Order s0.w s1.w s2.w s3.w s4.w s5.w =
      pure (toO (Mont.shiftReduced KO s0 s1 s2 s3 s4 s5).1,
        (Mont.shiftReduced KO s0 s1 s2 s3 s4 s5).2.w) := by
  purify

theorem first_row_Order (a : L4) (b : Limb) :
    Mont_first_row_Order (toO a) b.w =
      pure (toO (Mont.firstRow KO a b).1, (Mont.firstRow KO a b).2.w) := by
  purify

theorem row_Order (a : L4) (b : Limb) (t : L4) (top : Limb) :
    Mont_row_Order (toO a) b.w (toO t) top.w =
      pure (toO (Mont.row KO a b t top).1, (Mont.row KO a b t top).2.w) := by
  purify

theorem reduce_Order (a : L4) (top : Limb) :
    Mont_reduce_Order (toO a) top.w = pure (toO (Mont.reduce KO a top)) := by
  purify

namespace Base
/-- The field prime `p` of secp256k1, as the exported `P`. -/
def value : ℕ := 115792089237316195423570985008687907853269984665640564039457584007908834671663
end Base

namespace Order
/-- The group order `n` of secp256k1, as the exported `N`. -/
def value : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337
end Order

/-- The tactic for the methods built on `first_row`, `row` and `reduce`. -/
macro "purify_mont" : tactic => `(tactic| (
  simp only [Mont_mul_Base, Mont_mul_Order, Mont_add_Base, Mont_double_Base, Mont_square_Base,
    Mont_sub_Base, Mont_sub_Base_k1, Mont_sub_Base_k2, Mont_sub_Order, Mont_sub_Order_k1,
    Mont_sub_Order_k2, Mont_neg_Base, Mont_neg_Order, Mont_zero_Base, Mont_zero_Order,
    first_row_Base, first_row_Order, row_Base, row_Order, reduce_Base, reduce_Order,
    toB_l0, toB_l1, toB_l2, toB_l3, toO_l0, toO_l1, toO_l2, toO_l3,
    Base_P0_eq, Base_P1_eq, Base_P2_eq, Base_P3_eq, Order_P0_eq, Order_P1_eq,
    Order_P2_eq, Order_P3_eq, zero_w, adc_eq, sbb_eq _ _ _ (sbbHi_val_le _ _ _),
    sbb_eq _ _ _ zero_val_le, pure_bind, one_w, Limb.w_inj, decide_eq_true_eq, mk_toB, mk_toO]
  first
  | (split <;> rename_i h <;> simp only [Mont.sub, Mont.zero, toB, toO, h, ↓reduceIte])
  | rfl))

theorem mul_Base (a b : L4) :
    Mont_mul_Base (toB a) (toB b) = pure (toB (Mont.mul KB a b)) := by
  purify_mont

theorem sub_Base (a b : L4) :
    Mont_sub_Base (toB a) (toB b) = pure (toB (Mont.sub KB a b)) := by
  purify_mont

theorem zero_Base : Mont_zero_Base = pure (toB Mont.zero) := rfl

theorem neg_Base (a : L4) :
    Mont_neg_Base (toB a) = pure (toB (Mont.sub KB Mont.zero a)) := by
  simp only [Mont_neg_Base, zero_Base, pure_bind, sub_Base]

theorem mul_Order (a b : L4) :
    Mont_mul_Order (toO a) (toO b) = pure (toO (Mont.mul KO a b)) := by
  purify_mont

theorem sub_Order (a b : L4) :
    Mont_sub_Order (toO a) (toO b) = pure (toO (Mont.sub KO a b)) := by
  purify_mont

theorem zero_Order : Mont_zero_Order = pure (toO Mont.zero) := rfl

theorem neg_Order (a : L4) :
    Mont_neg_Order (toO a) = pure (toO (Mont.sub KO Mont.zero a)) := by
  simp only [Mont_neg_Order, zero_Order, pure_bind, sub_Order]

theorem add_Base (a b : L4) :
    Mont_add_Base (toB a) (toB b) = pure (toB (Mont.add KB a b)) := by
  purify_mont

theorem double_Base (a : L4) :
    Mont_double_Base (toB a) = pure (toB (Mont.add KB a a)) := by
  simp only [Mont_double_Base, add_Base, pure_bind]

theorem square_Base (a : L4) :
    Mont_square_Base (toB a) = pure (toB (Mont.mul KB a a)) := by
  simp only [Mont_square_Base, mul_Base, pure_bind]

theorem raw_Base_eq (v : UInt256) : raw_Base v = pure (toB (Mont.raw v.toNat)) := by
  simp only [raw_Base, downcast_truncate_u256_u64_eq, shiftRight_toNat _ (show 64 < 256 by decide),
    shiftRight_toNat _ (show 128 < 256 by decide), shiftRight_toNat _ (show 192 < 256 by decide),
    pure_bind]
  rfl

/-- `new` of a canonical value: `value * R2` reduced. -/
theorem new_Base (v : UInt256) (hv : v.toNat < Base.value) :
    Mont_new_Base v = pure (toB (Mont.new KB v.toNat)) := by
  simp only [Mont_new_Base, Base_VALUE, P, Base_R2, pure_bind, raw_Base_eq, mul_Base]
  rw [toNat_lit (by decide), toNat_lit (by decide)]
  unfold Base.value at hv
  simp only [Lib.assert, decide_eq_true hv, Bool.not_true, Bool.false_eq_true, ite_false,
    pure_bind]
  rfl

theorem raw_Order_eq (v : UInt256) : raw_Order v = pure (toO (Mont.raw v.toNat)) := by
  simp only [raw_Order, downcast_truncate_u256_u64_eq, shiftRight_toNat _ (show 64 < 256 by decide),
    shiftRight_toNat _ (show 128 < 256 by decide), shiftRight_toNat _ (show 192 < 256 by decide),
    pure_bind]
  rfl

/-- `new` of a canonical value: `value * R2` reduced. -/
theorem new_Order (v : UInt256) (hv : v.toNat < Order.value) :
    Mont_new_Order v = pure (toO (Mont.new KO v.toNat)) := by
  simp only [Mont_new_Order, Order_VALUE, N, Order_R2, pure_bind, raw_Order_eq, mul_Order]
  rw [toNat_lit (by decide), toNat_lit (by decide)]
  unfold Order.value at hv
  simp only [Lib.assert, decide_eq_true hv, Bool.not_true, Bool.false_eq_true, ite_false,
    pure_bind]
  rfl

/-- `value`: `a * 1` reduced, assembled into a word. -/
theorem value_Base (a : L4) :
    Mont_value_Base (toB a) = pure (UInt256.ofNat (Mont.value KB a)) := by
  simp only [Mont_value_Base, raw_Base_eq, toNat_lit (show 1 < 2 ^ 256 by decide), mul_Base,
    pure_bind, toB_l0, toB_l1, toB_l2, toB_l3, assemble_eq]
  rfl

/-- `value`: `a * 1` reduced, assembled into a word. -/
theorem value_Order (a : L4) :
    Mont_value_Order (toO a) = pure (UInt256.ofNat (Mont.value KO a)) := by
  simp only [Mont_value_Order, raw_Order_eq, toNat_lit (show 1 < 2 ^ 256 by decide), mul_Order,
    pure_bind, toO_l0, toO_l1, toO_l2, toO_l3, assemble_eq]
  rfl

theorem one_Base : Mont_one_Base = pure (toB (Mont.new KB 1)) := by
  simp only [Mont_one_Base]
  rw [new_Base _ (by rw [toNat_lit (by decide)]; decide), toNat_lit (by decide)]

/-- `is_zero`: every limb is zero. -/
theorem is_zero_Base (a : L4) : Mont_is_zero_Base (toB a) = pure (Mont.isZero a) := by
  simp only [Mont_is_zero_Base, toB_l0, toB_l1, toB_l2, toB_l3, zero_w, Limb.w_inj,
    decide_eq_true_eq, Mont.isZero]
  by_cases h0 : a.l0 = 0 <;> by_cases h1 : a.l1 = 0 <;> by_cases h2 : a.l2 = 0 <;>
    by_cases h3 : a.l3 = 0 <;> simp [h0, h1, h2, h3]

/-- `equals`: the limbs are equal. -/
theorem equals_Base (a b : L4) : Mont_equals_Base (toB a) (toB b) = pure (Mont.equals a b) := by
  simp only [Mont_equals_Base, toB_l0, toB_l1, toB_l2, toB_l3, Limb.w_inj, decide_eq_true_eq,
    Mont.equals]
  by_cases h0 : a.l0 = b.l0 <;> by_cases h1 : a.l1 = b.l1 <;> by_cases h2 : a.l2 = b.l2 <;>
    by_cases h3 : a.l3 = b.l3 <;> simp [h0, h1, h2, h3]

end FeProofs.Ecrecover
