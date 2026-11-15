import FeProofs.Precompiles.Modexp.SmallPure

/-!
# Modexp: the exported `Small<L>` arithmetic is pure

Each exported copy of `Small::mul`, `row2`/`row3`/`row4`, `double` for `L = 1 … 4` is `pure` of
the function of `SmallPure.lean` at that `L`.  The copies are the same text at different `L`, and
one tactic proves each lemma for all four (`spurify`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

theorem ofNat_ne {a b : ℕ} (h : a ≠ b) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (UInt256.ofNat a = UInt256.ofNat b) = False := by
  apply propext; constructor
  · intro e; apply h; have := congrArg UInt256.toNat e; rwa [toNat_lit ha, toNat_lit hb] at this
  · intro f; exact f.elim

theorem ne12 : (UInt256.ofNat 1 = UInt256.ofNat 2) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne13 : (UInt256.ofNat 1 = UInt256.ofNat 3) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne14 : (UInt256.ofNat 1 = UInt256.ofNat 4) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem nn12 : (1 : ℕ) = 2 ↔ False := by decide
theorem nn13 : (1 : ℕ) = 3 ↔ False := by decide
theorem nn14 : (1 : ℕ) = 4 ↔ False := by decide
theorem ne21 : (UInt256.ofNat 2 = UInt256.ofNat 1) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne23 : (UInt256.ofNat 2 = UInt256.ofNat 3) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne24 : (UInt256.ofNat 2 = UInt256.ofNat 4) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem nn21 : (2 : ℕ) = 1 ↔ False := by decide
theorem nn23 : (2 : ℕ) = 3 ↔ False := by decide
theorem nn24 : (2 : ℕ) = 4 ↔ False := by decide
theorem ne31 : (UInt256.ofNat 3 = UInt256.ofNat 1) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne32 : (UInt256.ofNat 3 = UInt256.ofNat 2) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne34 : (UInt256.ofNat 3 = UInt256.ofNat 4) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem nn31 : (3 : ℕ) = 1 ↔ False := by decide
theorem nn32 : (3 : ℕ) = 2 ↔ False := by decide
theorem nn34 : (3 : ℕ) = 4 ↔ False := by decide
theorem ne41 : (UInt256.ofNat 4 = UInt256.ofNat 1) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne42 : (UInt256.ofNat 4 = UInt256.ofNat 2) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem ne43 : (UInt256.ofNat 4 = UInt256.ofNat 3) = False := ofNat_ne (by decide) (by norm_num) (by norm_num)
theorem nn41 : (4 : ℕ) = 1 ↔ False := by decide
theorem nn42 : (4 : ℕ) = 2 ↔ False := by decide
theorem nn43 : (4 : ℕ) = 3 ↔ False := by decide

theorem nw21 : (UInt256.ofNat 2 = (1 : Limb).w) = False := ne21
theorem nw12 : ((1 : Limb).w = UInt256.ofNat 2) = False := ne12
theorem nw31 : (UInt256.ofNat 3 = (1 : Limb).w) = False := ne31
theorem nw13 : ((1 : Limb).w = UInt256.ofNat 3) = False := ne13
theorem nw41 : (UInt256.ofNat 4 = (1 : Limb).w) = False := ne41
theorem nw14 : ((1 : Limb).w = UInt256.ofNat 4) = False := ne14

/-- The tactic that turns an exported `Small` method into its pure form. -/
macro "spurify" : tactic => `(tactic| (
  simp only [Small_mul_1, Small_mul_2, Small_mul_3, Small_mul_4,
    Small_row2_1, Small_row2_1_k1, Small_row2_2, Small_row2_2_k1, Small_row2_3, Small_row2_3_k1,
    Small_row2_4, Small_row2_4_k1, Small_row3_1, Small_row3_1_k1, Small_row3_1_k2,
    Small_row3_2, Small_row3_2_k1, Small_row3_2_k2, Small_row3_3, Small_row3_3_k1,
    Small_row3_3_k2, Small_row3_4, Small_row3_4_k1, Small_row3_4_k2, Small_row4_1,
    Small_row4_1_k1, Small_row4_1_k2, Small_row4_2, Small_row4_2_k1, Small_row4_2_k2,
    Small_row4_3, Small_row4_3_k1, Small_row4_3_k2, Small_row4_4, Small_row4_4_k1,
    Small_row4_4_k2, toW, zero_w, mac_eq, adc_eq, sbb_eq _ _ _ (sbbHi_val_le _ _ _),
    sbb_eq _ _ _ zero_val_le, mulW64_eq, addW64_eq, pure_bind, one_w, Limb.w_inj,
    mulW128_eq, down128_eq, shr64_eq, addW128_LL, addW128_DL, subW128_DL, Limb.toNat_w,
    Dbl.toNat_w, smul1, ne_eq, Small_double_1, Small_double_1_k1, Small_double_1_k2,
    Small_double_2, Small_double_2_k1, Small_double_2_k2, Small_double_3, Small_double_3_k1,
    Small_double_3_k2, Small_double_4, Small_double_4_k1, Small_double_4_k2, shl64_one, shr63,
    lor_shl1, sdouble,
    decide_eq_true_eq, smul, row2, row3, row4, ssub, Z4, ne12, ne13, ne14, nn12, nn13, nn14, ne21, ne23, ne24, nn21, nn23, nn24, ne31, ne32, ne34, nn31, nn32, nn34, ne41, ne42, ne43, nn41, nn42, nn43,
    nw21, nw12, nw31, nw13, nw41, nw14, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true,
    ↓reduceIte]))

theorem smul2_eq (m a b : L4) (inv : Limb) :
    Small_mul_2 ⟨toW m, inv.w⟩ (toW a) (toW b) = pure (toW (smul 2 m inv a b)) := by
  spurify
  -- Lean 4.35 leaves the specification's `if` unsplit (its condition carries another instance):
  -- rewrite it with the split hypothesis.
  split_ifs with h <;> simp only [h, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
    Decidable.not_not] <;> rfl

theorem smul1_eq (m a b : L4) (inv : Limb) :
    Small_mul_1 ⟨toW m, inv.w⟩ (toW a) (toW b) = pure (toW (smul 1 m inv a b)) := by
  spurify
  -- Lean 4.35 leaves the specification's `if` unsplit (its condition carries another instance):
  -- rewrite it with the split hypothesis.
  split_ifs with h <;> simp only [h, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
    Decidable.not_not] <;> rfl

theorem smul3_eq (m a b : L4) (inv : Limb) :
    Small_mul_3 ⟨toW m, inv.w⟩ (toW a) (toW b) = pure (toW (smul 3 m inv a b)) := by
  spurify
  -- Lean 4.35 leaves the specification's `if` unsplit (its condition carries another instance):
  -- rewrite it with the split hypothesis.
  split_ifs with h <;> simp only [h, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
    Decidable.not_not] <;> rfl

theorem smul4_eq (m a b : L4) (inv : Limb) :
    Small_mul_4 ⟨toW m, inv.w⟩ (toW a) (toW b) = pure (toW (smul 4 m inv a b)) := by
  spurify
  -- Lean 4.35 leaves the specification's `if` unsplit (its condition carries another instance):
  -- rewrite it with the split hypothesis.
  split_ifs with h <;> simp only [h, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
    Decidable.not_not] <;> rfl

theorem sdouble1_eq (m x : L4) (inv : Limb) :
    Small_double_1 ⟨toW m, inv.w⟩ (toW x) = pure (toW (sdouble m x)) := by
  spurify; split_ifs <;> rfl

theorem sdouble2_eq (m x : L4) (inv : Limb) :
    Small_double_2 ⟨toW m, inv.w⟩ (toW x) = pure (toW (sdouble m x)) := by
  spurify; split_ifs <;> rfl

theorem sdouble3_eq (m x : L4) (inv : Limb) :
    Small_double_3 ⟨toW m, inv.w⟩ (toW x) = pure (toW (sdouble m x)) := by
  spurify; split_ifs <;> rfl

theorem sdouble4_eq (m x : L4) (inv : Limb) :
    Small_double_4 ⟨toW m, inv.w⟩ (toW x) = pure (toW (sdouble m x)) := by
  spurify; split_ifs <;> rfl

end FeProofs.Modexp
