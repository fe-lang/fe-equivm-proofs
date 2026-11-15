import FeProofs.Precompiles.Secp256k1.Purify
import FeProofs.Precompiles.Field.Pow

/-!
# Ecrecover: the Montgomery arithmetic at the two moduli

The constants of the two moduli checked by `decide` (`KB_valid`, `KB_R2`, …), the result of
`MontCorrect.lean` for each exported method (`Mont_mul_Base_rep` and the rest), and the exported
`Mont_pow_Base` as `pure` of `Mont.pow` (`pow_Base`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

/-! ## The two moduli -/

theorem KB_p : KB.p = Ethereum.Secp256k1.p := by decide
theorem KO_p : KO.p = Ethereum.Secp256k1.n := by decide
theorem KB_valid : KB.Valid := by unfold Modulus.Valid; decide
theorem KO_valid : KO.Valid := by unfold Modulus.Valid; decide
theorem KB_R2 : KB.R2 = 2 ^ 512 % KB.p := by decide
theorem KO_R2 : KO.R2 = 2 ^ 512 % KO.p := by decide
theorem Base_value_eq : Base.value = KB.p := by decide
theorem Order_value_eq : Order.value = KO.p := by decide

/-! ## The exported methods

Each exported method on representations returns a representation of the result. -/

open Ethereum Precompiles.Exported.Shared Precompiles.Exported.Ecrecover Mont

section
variable {a b : L4} {x y : ZMod KB.p}

theorem Mont_new_Base_rep (v : UInt256) (hv : v.toNat < KB.p) :
    ∃ c, Mont_new_Base v = pure (toB c) ∧ Rep KB c v.toNat :=
  ⟨_, new_Base v (by rw [Base_value_eq]; exact hv), new_rep KB_valid KB_R2 hv⟩

theorem Mont_one_Base_rep : ∃ c, Mont_one_Base = pure (toB c) ∧ Rep KB c 1 :=
  ⟨_, one_Base, one_rep KB_valid KB_R2 (by decide)⟩

theorem Mont_zero_Base_rep : Mont_zero_Base = pure (toB zero) ∧ Rep KB zero 0 :=
  ⟨zero_Base, zero_rep KB_valid⟩

theorem Mont_value_Base_rep (ha : Rep KB a x) :
    ∃ v < KB.p, Mont_value_Base (toB a) = pure (UInt256.ofNat v) ∧ (v : ZMod KB.p) = x :=
  ⟨_, (value_rep KB_valid ha).1, value_Base a, (value_rep KB_valid ha).2⟩

theorem Mont_mul_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_mul_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x * y) :=
  ⟨_, mul_Base a b, mul_rep KB_valid ha hb⟩

theorem Mont_square_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_square_Base (toB a) = pure (toB c) ∧ Rep KB c (x ^ 2) :=
  ⟨_, square_Base a, square_rep KB_valid ha⟩

theorem Mont_add_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_add_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x + y) :=
  ⟨_, add_Base a b, add_rep ha hb⟩

theorem Mont_double_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_double_Base (toB a) = pure (toB c) ∧ Rep KB c (2 * x) :=
  ⟨_, double_Base a, double_rep ha⟩

theorem Mont_sub_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_sub_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x - y) :=
  ⟨_, sub_Base a b, sub_rep ha hb⟩

theorem Mont_neg_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_neg_Base (toB a) = pure (toB c) ∧ Rep KB c (-x) :=
  ⟨_, neg_Base a, neg_rep KB_valid ha⟩

theorem Mont_is_zero_Base_rep (ha : Rep KB a x) :
    Mont_is_zero_Base (toB a) = pure (decide (x = 0)) := by
  rw [is_zero_Base]
  congr 1
  exact Bool.eq_iff_iff.mpr ((isZero_rep KB_valid ha).trans decide_eq_true_iff.symm)

theorem Mont_equals_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    Mont_equals_Base (toB a) (toB b) = pure (decide (x = y)) := by
  rw [equals_Base]
  congr 1
  exact Bool.eq_iff_iff.mpr ((equals_rep KB_valid ha hb).trans decide_eq_true_iff.symm)

end

section
variable {a b : L4} {x y : ZMod KO.p}

theorem Mont_new_Order_rep (v : UInt256) (hv : v.toNat < KO.p) :
    ∃ c, Mont_new_Order v = pure (toO c) ∧ Rep KO c v.toNat :=
  ⟨_, new_Order v (by rw [Order_value_eq]; exact hv), new_rep KO_valid KO_R2 hv⟩

theorem Mont_zero_Order_rep : Mont_zero_Order = pure (toO zero) ∧ Rep KO zero 0 :=
  ⟨zero_Order, zero_rep KO_valid⟩

theorem Mont_value_Order_rep (ha : Rep KO a x) :
    ∃ v < KO.p, Mont_value_Order (toO a) = pure (UInt256.ofNat v) ∧ (v : ZMod KO.p) = x :=
  ⟨_, (value_rep KO_valid ha).1, value_Order a, (value_rep KO_valid ha).2⟩

theorem Mont_mul_Order_rep (ha : Rep KO a x) (hb : Rep KO b y) :
    ∃ c, Mont_mul_Order (toO a) (toO b) = pure (toO c) ∧ Rep KO c (x * y) :=
  ⟨_, mul_Order a b, mul_rep KO_valid ha hb⟩

theorem Mont_sub_Order_rep (ha : Rep KO a x) (hb : Rep KO b y) :
    ∃ c, Mont_sub_Order (toO a) (toO b) = pure (toO c) ∧ Rep KO c (x - y) :=
  ⟨_, sub_Order a b, sub_rep ha hb⟩

theorem Mont_neg_Order_rep (ha : Rep KO a x) :
    ∃ c, Mont_neg_Order (toO a) = pure (toO c) ∧ Rep KO c (-x) :=
  ⟨_, neg_Order a, neg_rep KO_valid ha⟩

end

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

/-- The exported loop of `pow`, with `k` bits to go, is `powLoop`. -/
theorem pow_loop_Base (a : L4) (e : UInt256) :
    ∀ k ≤ 256, ∀ (r : L4) (r2 r3 : Mont_Base),
      Mont_pow_Base.b1 (toB a) e (toB r) (UInt256.ofNat k) r2 r3 =
        pure (toB (Mont.powLoop KB a e.toNat k r))
  | 0, _, r, r2, r3 => by
    rw [Mont_pow_Base.b1.eq_1]
    simp [toNat_lit (show 0 < 2 ^ 256 by decide), Mont.powLoop]
  | k + 1, hk, r, r2, r3 => by
    rw [Mont_pow_Base.b1.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by decide), toNat_lit (show k + 1 < 2 ^ 256 by omega),
      show 0 < k + 1 by omega, decide_true, ite_true, sub_one_u64 (show k + 1 < 2 ^ 64 by omega),
      pure_bind, square_Base, bit_test e (show k < 256 by omega), Mont.powLoop]
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      simp only [mul_Base, pure_bind, pow_loop_Base a e k (by omega), ite_eq_left h]
    · rename_i h
      simp only [decide_eq_true_eq] at h
      simp only [pow_loop_Base a e k (by omega), ite_eq_right h]

theorem pow_Base (a : L4) (e : UInt256) :
    Mont_pow_Base (toB a) e = pure (toB (Mont.pow KB a e.toNat)) := by
  simp only [Mont_pow_Base, one_Base, pure_bind]
  exact pow_loop_Base a e 256 le_rfl _ _ _

end FeProofs.Ecrecover
