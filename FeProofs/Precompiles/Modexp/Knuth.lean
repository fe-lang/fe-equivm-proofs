import FeProofs.Precompiles.Modexp.Work

/-!
# Modexp: the arithmetic of Knuth division

`Modulus::reduce` divides by a normalised divisor `D` of `n ≥ 2` limbs, one quotient digit per
step, each from a window `W` of `n + 1` dividend limbs with `W < D β` (`β = 2 ^ 64`):

- `qhat_bounds`: the digit estimated from the top three limbs of `W` and the top two of `D`
  (`β - 1` when the top two of each agree, the 3-by-2 quotient otherwise) is the true digit
  `W / D` or one more (Knuth's Theorem B, with a two-limb divisor);
- `knuth_step`: after subtracting `q̂ D`, the sign says which: no borrow leaves `W % D`, a borrow
  leaves `W % D - D` plus `β ^ (n + 1)`, which adding `D` back once restores.

Also the 128-bit word steps of the multiply-subtract and the add-back (`sbbD` and the rest).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## The quotient digit -/

/-- **The estimated digit is exact or one too large.**  With `D = D' P + Dl`, `Dl < P`, whose top
    two limbs `D' ≥ 2 ^ 127` are normalised, and `W = (T β + u0) P + Wl < D β`, `Wl < P`, with top
    two limbs `T` and next `u0`: `T ≤ D'`, and the estimate (`β - 1` if `T = D'`, the 3-by-2
    quotient otherwise) lies in `[W / D, W / D + 1]`. -/
theorem qhat_bounds {T u0 D' Wl Dl P W D : ℕ} (hu0 : u0 < 2 ^ 64) (hD'big : 2 ^ 127 ≤ D')
    (hP : 0 < P) (hWl : Wl < P) (hDl : Dl < P) (hD : D = D' * P + Dl)
    (hW : W = (T * 2 ^ 64 + u0) * P + Wl) (hWD : W < D * 2 ^ 64) :
    T ≤ D' ∧ W / D ≤ (if T = D' then 2 ^ 64 - 1 else (T * 2 ^ 64 + u0) / D') ∧
      (if T = D' then 2 ^ 64 - 1 else (T * 2 ^ 64 + u0) / D') ≤ W / D + 1 := by
  have hDpos : 0 < D := by rw [hD]; positivity
  have hTD : T ≤ D' := by
    by_contra h
    have h1 : (D' + 1) * P * 2 ^ 64 ≤ T * P * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    nlinarith
  refine ⟨hTD, ?_⟩
  have hqB : W / D < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hDpos).mpr (by rw [Nat.mul_comm]; exact hWD)
  have hqD : W / D * D ≤ W := Nat.div_mul_le_self W D
  by_cases hc : T = D'
  · rw [ite_eq_left hc]
    refine ⟨by omega, ?_⟩
    suffices h : 2 ^ 64 - 2 ≤ W / D by omega
    rw [Nat.le_div_iff_mul_le hDpos]
    have h1 : (2 ^ 64 - 2) * Dl ≤ (2 ^ 64 - 2) * P := Nat.mul_le_mul_left _ hDl.le
    have h2 : (2 ^ 64 - 2) * P ≤ 2 * D' * P := Nat.mul_le_mul_right _ (by omega)
    rw [hD, hW, hc]
    norm_num at h1 h2 ⊢
    nlinarith
  · rw [ite_eq_right hc]
    have hlt : T < D' := lt_of_le_of_ne hTD hc
    have hW'B : (T * 2 ^ 64 + u0) / D' < 2 ^ 64 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
    refine ⟨?_, ?_⟩
    · rw [Nat.le_div_iff_mul_le (by omega)]
      have h1 : W / D * D' * P ≤ W / D * D := by
        rw [hD, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by omega)
      have h3 : W < (T * 2 ^ 64 + u0 + 1) * P := by rw [hW]; nlinarith
      have h2 : W / D * D' * P < (T * 2 ^ 64 + u0 + 1) * P := lt_of_le_of_lt (h1.trans hqD) h3
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h2)
    · obtain ⟨t, ht⟩ : ∃ t, (T * 2 ^ 64 + u0) / D' = t := ⟨_, rfl⟩
      rw [ht] at hW'B ⊢
      rcases t with _ | t
      · exact Nat.zero_le _
      · suffices h : t ≤ W / D from Nat.add_le_add_right h 1
        rw [Nat.le_div_iff_mul_le hDpos]
        have htD : (t + 1) * D' ≤ T * 2 ^ 64 + u0 := by rw [← ht]; exact Nat.div_mul_le_self _ _
        have h1 : t * Dl ≤ t * P := Nat.mul_le_mul_left _ hDl.le
        have h2 : (t * D' + t) * P ≤ (T * 2 ^ 64 + u0) * P :=
          Nat.mul_le_mul_right _ (by nlinarith)
        rw [hD, hW]
        nlinarith

/-- **One step of Knuth division**: subtracting the estimate `q̂ ∈ [W / D, W / D + 1]` times `D`
    from `W` leaves `S < R` and the borrow `fb`; without a borrow `S` is `W % D`, with one
    `S + D` is `W % D + R`. -/
theorem knuth_step {W D q S fb R : ℕ} (hD : 0 < D) (hq1 : W / D ≤ q) (hq2 : q ≤ W / D + 1)
    (hS : S < R) (hfb : fb ≤ 1) (he : S + q * D = W + fb * R) :
    (fb = 0 → S = W % D) ∧ (fb = 1 → S + D = W % D + R) := by
  have hdm := Nat.div_add_mod W D
  have hr := Nat.mod_lt W hD
  generalize W / D = Q at hq1 hq2 hdm
  generalize W % D = r at hdm hr ⊢
  subst hdm
  rcases (show q = Q ∨ q = Q + 1 by omega) with h | h
  · rw [h, Nat.mul_comm Q D] at he
    generalize D * Q = X at he
    constructor <;> intro h' <;> subst h' <;> omega
  · rw [h, Nat.add_mul, Nat.one_mul, Nat.mul_comm Q D] at he
    generalize D * Q = X at he
    constructor <;> intro h' <;> subst h' <;> omega

/-! ## Words of the multiply-subtract and the add-back -/

theorem subW128_LL (a b : Limb) : IntTy.subW (.u 128) a.w b.w = (subD (L2D a) (L2D b)).w :=
  subW128_eq (L2D a) (L2D b)

/-- Bit 127 of a double limb, as a limb. -/
def hbit (x : Dbl) : Limb :=
  ⟨x.val / 2 ^ 127, by have := x.isLt; rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega⟩

theorem shr127_eq (x : Dbl) : x.w >>> UInt256.ofNat 127 = (hbit x).w := by
  apply word_eq_of_toNat
  rw [shiftRight_toNat _ (by decide)]
  simp [hbit]

/-- `x - y - b` in 128 bits. -/
def sbbD (x y b : Limb) : Dbl := subD (subD (L2D x) (L2D y)) (L2D b)

theorem sbbD_val (x y b : Limb) (hb : b.val ≤ 1) :
    (sbbD x y b).val =
      if y.val + b.val ≤ x.val then x.val - y.val - b.val else x.val + 2 ^ 128 - y.val - b.val := by
  have := x.isLt; have := y.isLt
  simp only [sbbD, subD, L2D]
  split_ifs <;> omega

/-- The borrow of `x - y - b`. -/
theorem sbbD_hbit (x y b : Limb) (hb : b.val ≤ 1) :
    (hbit (sbbD x y b)).val = if y.val + b.val ≤ x.val then 0 else 1 := by
  have := x.isLt; have := y.isLt
  simp only [hbit]
  rw [sbbD_val x y b hb]
  split_ifs <;> omega

/-- The limb of `x - y - b` and its borrow. -/
theorem sbbD_lo (x y b : Limb) (hb : b.val ≤ 1) :
    (loD (sbbD x y b)).val + y.val + b.val = x.val + (hbit (sbbD x y b)).val * 2 ^ 64 := by
  have := x.isLt; have := y.isLt
  rw [sbbD_hbit x y b hb]
  simp only [loD]
  rw [sbbD_val x y b hb]
  split_ifs <;> omega

/-- `q m + c`, the product of a limb and a limb of the divisor plus the carry. -/
theorem mac128_val (q m c : Limb) : (addD (mulD q m) (L2D c)).val = q.val * m.val + c.val := by
  have := Nat.mul_le_mul (Nat.le_pred_of_lt q.isLt) (Nat.le_pred_of_lt m.isLt)
  have := c.isLt
  simp only [addD, mulD, L2D, Nat.pred_eq_sub_one] at *
  rw [Nat.mod_eq_of_lt]
  omega

/-- `x + m + a`, the sum of the add-back. -/
theorem add128_val (x m a : Limb) :
    (addD (addD (L2D x) (L2D m)) (L2D a)).val = x.val + m.val + a.val := by
  have := x.isLt; have := m.isLt; have := a.isLt
  simp only [addD, L2D]
  omega

end FeProofs.Modexp
