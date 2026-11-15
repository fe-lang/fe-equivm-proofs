import FeProofs.Precompiles.Field.Words
import Fe.EVM.Entry

/-!
# Precompiles: checked arithmetic on literals

The checked `+`, `/` and `%` of words of natural numbers that do not overflow, as `pure`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

theorem ne_zero_word {b : ℕ} (hb : b < 2 ^ 256) (hb0 : 0 < b) : ¬ UInt256.ofNat b = ⟨0⟩ := by
  intro h
  have := congrArg UInt256.toNat h
  rw [toNat_lit hb] at this
  exact absurd this (by change b ≠ 0; omega)

theorem checkedDiv_lit {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hb0 : 0 < b) :
    checkedDiv (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a / b)) := by
  unfold checkedDiv
  rw [ite_eq_right (ne_zero_word hb hb0)]
  congr 1
  apply word_eq_of_toNat
  change (UInt256.div _ _).toNat = _
  rw [udiv_toNat, toNat_lit ha, toNat_lit hb, toNat_lit (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem checkedRem_lit (a : UInt256) {b : ℕ} (hb : b < 2 ^ 256) (hb0 : 0 < b) :
    checkedRem a (UInt256.ofNat b) = pure (UInt256.ofNat (a.toNat % b)) := by
  unfold checkedRem
  rw [ite_eq_right (ne_zero_word hb hb0)]
  congr 1
  apply word_eq_of_toNat
  rw [toNat_lit (lt_trans (Nat.mod_lt _ hb0) hb)]
  change (UInt256.mod a (UInt256.ofNat b)).toNat = _
  have hv : ¬ ((UInt256.ofNat b).val == 0) = true := by
    intro h; apply ne_zero_word hb hb0; simp at h
    cases hu : UInt256.ofNat b; rw [hu] at h; simp at h; rw [h]
  unfold UInt256.mod
  rw [ite_eq_right hv]
  change a.toNat % (UInt256.ofNat b).toNat = _
  rw [toNat_lit hb]

theorem checkedAdd_small {a b : ℕ} (h : a + b < 2 ^ 256) :
    checkedAdd (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a + b)) := by
  unfold checkedAdd
  rw [toNat_lit (by omega), toNat_lit (by omega), ite_eq_right (by change ¬ 2 ^ 256 ≤ _; omega)]
  congr 1
  exact Fe.EVM.ofNat_add_ofNat h

theorem range_has_eq {k lo hi : ℕ} (hk : k < 2 ^ 256) (hl : lo < 2 ^ 256) (hh : hi < 2 ^ 256) :
    Lib.range_has (UInt256.ofNat k) (UInt256.ofNat lo) (UInt256.ofNat hi) =
      pure (decide (lo ≤ k ∧ k < hi)) := by
  simp only [Lib.range_has, toNat_lit hk, toNat_lit hl, toNat_lit hh]
  by_cases h1 : lo ≤ k <;> by_cases h2 : k < hi <;> simp [h1, h2]

theorem next_eq {k : ℕ} (hk : k + 1 < 2 ^ 256) :
    Lib.usize_wrapping_add (UInt256.ofNat k) (UInt256.ofNat 1) = pure (UInt256.ofNat (k + 1)) := by
  simp only [Lib.usize_wrapping_add]
  congr 1
  exact Fe.EVM.ofNat_add_ofNat hk

theorem checkedMul_small {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a * b < 2 ^ 256) :
    checkedMul (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a * b)) := by
  unfold checkedMul
  rw [toNat_lit ha, toNat_lit hb, ite_eq_right (by change ¬ 2 ^ 256 ≤ _; omega)]
  congr 1
  exact Fe.EVM.ofNat_mul_ofNat ha hb h

end FeProofs.Precompiles
