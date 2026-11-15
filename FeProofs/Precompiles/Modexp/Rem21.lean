import FeProofs.Precompiles.Modexp.Ops
import Mathlib.Tactic.LinearCombination

/-!
# Modexp: the remainder of two limbs by one

`rem_2by1` of `bignum.fe` is Möller and Granlund's division of a two-limb number by a normalized
limb with a precomputed reciprocal (Algorithm 4 of "Improved division by invariant integers",
2011), returning the remainder.  `reciprocal_2by1` computes the reciprocal.

- `reciprocal_2by1_eq`: on a normalized `d` (`2 ^ 63 ≤ d`) it is `⌊(2 ^ 128 - 1) / d⌋ - 2 ^ 64`.
- `rem_2by1_eq`: the exported function is `pure` of `rem21`, which follows the Fe code on limbs.
- `rem21_eq`: with that reciprocal and `u1 < d`, `rem21` is `(u1 2 ^ 64 + u0) mod d`.  The proof
  is the paper's Theorem 2: the candidate remainder `r̃ = U - (q1 + 1) d` lies in
  `[max(β - d, q0 + 1) - β, max(β - d, q0))`, so its residue modulo `β` and `q0` determine it.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## The reciprocal of one limb -/

/-- `⌊(β² - 1) / d⌋ - β`, the reciprocal of a normalized limb. -/
def recip21 (d : ℕ) : ℕ := (2 ^ 128 - 1) / d - 2 ^ 64

theorem recip21_lt {d : ℕ} (hd : 2 ^ 63 ≤ d) : recip21 d < 2 ^ 64 := by
  unfold recip21
  have : (2 ^ 128 - 1) / d < 2 ^ 65 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  omega

/-- The reciprocal as a limb. -/
def recip21L (d : Limb) (hd : 2 ^ 63 ≤ d.val) : Limb := ⟨recip21 d.val, recip21_lt hd⟩

/-- `(β + v) d = β² - k` with `1 ≤ k ≤ d`. -/
theorem recip21_spec {d : ℕ} (hd : 2 ^ 63 ≤ d) (hd' : d < 2 ^ 64) :
    ∃ k, 1 ≤ k ∧ k ≤ d ∧ (2 ^ 64 + recip21 d) * d + k = 2 ^ 128 := by
  have hq : 2 ^ 64 ≤ (2 ^ 128 - 1) / d := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_pred_of_lt hd')
    simp only [Nat.pred_eq_sub_one] at this; omega
  have hm := Nat.mod_lt (2 ^ 128 - 1) (by omega : 0 < d)
  refine ⟨1 + (2 ^ 128 - 1) % d, by omega, by omega, ?_⟩
  unfold recip21
  rw [Nat.add_sub_cancel' hq]
  have := Nat.div_add_mod (2 ^ 128 - 1) d
  rw [Nat.mul_comm] at this
  omega

theorem reciprocal_2by1_eq (d : Limb) (hd : 2 ^ 63 ≤ d.val) :
    reciprocal_2by1 d.w = pure (recip21L d hd).w := by
  have hd' := d.isLt
  have hq : 2 ^ 64 ≤ (2 ^ 128 - 1) / d.val := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_pred_of_lt hd')
    simp only [Nat.pred_eq_sub_one] at this; omega
  have hq' : (2 ^ 128 - 1) / d.val < 2 ^ 65 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hne : d.w ≠ ⟨0⟩ := by
    intro h; have := congrArg UInt256.toNat h; simp at this; omega
  simp only [reciprocal_2by1, checkedDiv, hne, ite_false, pure_bind, LIMB_BASE, IntTy.sub,
    IntTy.checked, IntTy.Fits, val_u]
  have hdiv : (UInt256.ofNat 340282366920938463463374607431768211455 / d.w).toNat =
      (2 ^ 128 - 1) / d.val := by
    show UInt256.toNat (UInt256.ofNat _) / UInt256.toNat d.w = _
    rw [Limb.toNat_w, toNat_lit (by decide)]
    rfl
  rw [hdiv, toNat_lit (show 18446744073709551616 < 2 ^ 256 by decide),
    show (((2 ^ 128 - 1) / d.val : ℕ) : ℤ) - (18446744073709551616 : ℕ) =
      (((2 ^ 128 - 1) / d.val - 2 ^ 64 : ℕ) : ℤ) by rw [Nat.cast_sub hq]; rfl,
    ite_eq_left (by constructor <;> omega), wrap_u_nat, pure_bind, downcast_truncate_u128_u64_eq,
    toNat_lit (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

/-! ## The remainder, as the Fe code computes it -/

/-- `rem_2by1` on limbs: `u1 < d`, `v` the reciprocal of `d`. -/
def rem21 (u1 u0 d v : Limb) : Limb :=
  let x := addD (mulD v u1) (joinD u1 u0)
  let q1 := addMod (hiD x) 1
  let q0 := loD x
  let r := subMod u0 (mulLo q1 d)
  let r := if q0.val < r.val then addMod r d else r
  if d.val ≤ r.val then subMod r d else r

theorem rem_2by1_eq (u1 u0 d v : Limb) :
    rem_2by1 u1.w u0.w d.w v.w = pure (rem21 u1 u0 d v).w := by
  simp only [rem_2by1, mulW128_eq, shl128_join, addW128_eq, shr64_eq, down128_limb_eq,
    down128_eq, one_w, addW64_eq, mulW64_eq, subW64_eq, Limb.toNat_w, pure_bind, rem21]
  split_ifs <;> simp_all

/-- The adjustment steps of `rem21`, from the bounds of Theorem 2 on the candidate remainder
    `U - P - d`, with `P` a multiple of `d`, and its residue `r` modulo `β`. -/
theorem rem21_adjust (u1 u0 d Q q0 r : ℕ) (hd : 2 ^ 63 ≤ d) (hd' : d < 2 ^ 64)
    (hu0 : u0 < 2 ^ 64) (hq0 : q0 < 2 ^ 64)
    (hr : r = (u0 + 2 ^ 64 - (Q * d + d) % 2 ^ 64) % 2 ^ 64)
    (hlo1 : Q * d ≤ u1 * 2 ^ 64 + u0)
    (hlo2 : (q0 : ℤ) - 2 ^ 64 < u1 * 2 ^ 64 + u0 - Q * d - d)
    (hup : (u1 * 2 ^ 64 + u0 - Q * d - d : ℤ) < max (2 ^ 64 - d : ℤ) q0) :
    (let r := if q0 < r then (r + d) % 2 ^ 64 else r
     if d ≤ r then (r + 2 ^ 64 - d) % 2 ^ 64 else r) = (u1 * 2 ^ 64 + u0) % d := by
  obtain ⟨P, hP⟩ : ∃ P, P = Q * d := ⟨_, rfl⟩
  rw [← hP] at hr hlo1
  have hP' : (P : ℤ) = Q * d := by exact_mod_cast hP
  rw [← hP'] at hlo2 hup
  have hres : ∀ s j, s < d → u1 * 2 ^ 64 + u0 = s + (Q + j) * d → s = (u1 * 2 ^ 64 + u0) % d := by
    intro s j hs h
    rw [h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have e : ∀ j, (Q + j) * d = P + j * d := fun j => by rw [hP]; ring
  rw [max_def] at hup
  simp only
  split_ifs at hup ⊢
  all_goals first
    | omega
    | exact hres _ 0 (by omega) (by rw [e]; omega)
    | exact hres _ 1 (by omega) (by rw [e]; omega)
    | exact hres _ 2 (by omega) (by rw [e]; omega)

/-! ## Theorem 2 -/

/-- The value of `rem21`: with the reciprocal of a normalized `d` and `u1 < d`, the remainder of
    `u1 β + u0` by `d`. -/
theorem rem21_eq (u1 u0 d : Limb) (hd : 2 ^ 63 ≤ d.val) (hu : u1.val < d.val) :
    (rem21 u1 u0 d (recip21L d hd)).val = (u1.val * 2 ^ 64 + u0.val) % d.val := by
  obtain ⟨k, hk1, hkd, hk⟩ := recip21_spec hd d.isLt
  have hd' := d.isLt; have hu0 := u0.isLt
  set v := recip21 d.val with hv
  have hvlt : v < 2 ^ 64 := recip21_lt hd
  -- The estimate `x = (β + v) u1 + u0 = q1 β + q0` does not wrap.
  have hx : v * u1.val + (u1.val * 2 ^ 64 + u0.val) < 2 ^ 128 := by
    have h1 : (2 ^ 64 + v) * u1.val + 2 ^ 64 ≤ 2 ^ 128 := by
      have := Nat.mul_le_mul_left (2 ^ 64 + v) (show u1.val + 1 ≤ d.val by omega)
      nlinarith
    nlinarith
  simp only [rem21]
  generalize hxd : addD (mulD (recip21L d hd) u1) (joinD u1 u0) = x
  have hxv : x.val = v * u1.val + (u1.val * 2 ^ 64 + u0.val) := by
    rw [← hxd]; simp only [addD, mulD, joinD, recip21L]; rw [← hv, Nat.mod_eq_of_lt hx]
  set X := x.val with hXdef
  set q1 := X / 2 ^ 64 with hq1
  set q0 := X % 2 ^ 64 with hq0
  have hXq : X = q1 * 2 ^ 64 + q0 := by omega
  have hq1lt : q1 < 2 ^ 64 := by omega
  have hX : v * u1.val + (u1.val * 2 ^ 64 + u0.val) = X := hxv.symm
  have hlo0 : (loD x).val = q0 := rfl
  generalize hqd : addMod (hiD x) 1 = q
  have hqv : q.val = (q1 + 1) % 2 ^ 64 := by rw [← hqd]; rfl
  generalize hrd : subMod u0 (mulLo q d) = r
  have hrv : r.val = (u0.val + 2 ^ 64 - q.val * d.val % 2 ^ 64) % 2 ^ 64 := by rw [← hrd]; rfl
  rw [hlo0]
  -- `β (U - q1 d) = u1 k + u0 (β - d) + q0 d`, with `U = u1 β + u0`.
  have key : 2 ^ 64 * ((u1.val * 2 ^ 64 + u0.val : ℤ) - q1 * d.val) =
      u1.val * k + u0.val * (2 ^ 64 - d.val) + q0 * d.val := by
    have e1 : (X : ℤ) = v * u1.val + (u1.val * 2 ^ 64 + u0.val) := by exact_mod_cast hX.symm
    have e2 : (X : ℤ) = q1 * 2 ^ 64 + q0 := by exact_mod_cast hXq
    have e3 : ((2 ^ 64 + v) * d.val + k : ℤ) = 2 ^ 128 := by exact_mod_cast hk
    linear_combination (d.val : ℤ) * e2 - (d.val : ℤ) * e1 - (u1.val : ℤ) * e3
  -- The candidate remainder `r̃ = U - (q1 + 1) d`, with `P = q1 d`.
  obtain ⟨P, hPdef⟩ : ∃ P, P = q1 * d.val := ⟨_, rfl⟩
  have hPz : (P : ℤ) = q1 * d.val := by exact_mod_cast hPdef
  set U : ℤ := u1.val * 2 ^ 64 + u0.val with hU
  have hbd : (0 : ℤ) ≤ 2 ^ 64 - d.val := by
    have : (d.val : ℤ) < 2 ^ 64 := by exact_mod_cast hd'
    linarith
  have h0 : (0 : ℤ) ≤ u1.val * k + u0.val * (2 ^ 64 - d.val) :=
    add_nonneg (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      (mul_nonneg (Int.natCast_nonneg _) hbd)
  have hq0d : (0 : ℤ) ≤ q0 * d.val := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hlo1 : U - P ≥ 0 := by
    have : (0 : ℤ) ≤ 2 ^ 64 * (U - q1 * d.val) := by rw [key]; linarith
    rw [hPz]
    exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℤ) < 2 ^ 64)).mp this
  have hlo2 : 2 ^ 64 * (U - P - d.val) > (q0 - 2 ^ 64) * 2 ^ 64 := by
    have h2 : ((2 ^ 64 : ℤ) - q0) * d.val < (2 ^ 64 - q0) * 2 ^ 64 := by
      apply mul_lt_mul_of_pos_left (by exact_mod_cast hd')
      have : (q0 : ℤ) < 2 ^ 64 := by exact_mod_cast (show q0 < 2 ^ 64 by omega)
      linarith
    rw [hPz]; linarith
  have hup : 2 ^ 64 * (U - P - d.val) + 2 ^ 64 ≤
      2 ^ 64 * max ((2 ^ 64 : ℤ) - d.val) q0 := by
    have h1 : (u1.val : ℤ) * k ≤ (d.val - 1) * d.val :=
      mul_le_mul (by omega) (by exact_mod_cast hkd) (Int.natCast_nonneg _) (by omega)
    have h2 : (u0.val : ℤ) * (2 ^ 64 - d.val) ≤ (2 ^ 64 - 1) * (2 ^ 64 - d.val) :=
      mul_le_mul_of_nonneg_right (by omega) hbd
    have h3 : ((2 ^ 64 : ℤ) - d.val) * (2 ^ 64 - d.val) ≤
        (2 ^ 64 - d.val) * max ((2 ^ 64 : ℤ) - d.val) q0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hbd
    have h4 : (q0 : ℤ) * d.val ≤ max ((2 ^ 64 : ℤ) - d.val) q0 * d.val :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Int.natCast_nonneg _)
    rw [hPz]; linarith
  -- The residue the code computes and the adjustments.
  have hq1d : q.val * d.val % 2 ^ 64 = (q1 * d.val + d.val) % 2 ^ 64 := by
    rw [hqv, Nat.mod_mul_mod, Nat.add_mul, Nat.one_mul]
  rw [hq1d] at hrv
  have hlo2' : (q0 : ℤ) - 2 ^ 64 < u1.val * 2 ^ 64 + u0.val - q1 * d.val - d.val := by
    have := Int.lt_of_mul_lt_mul_left
      (show 2 ^ 64 * ((q0 : ℤ) - 2 ^ 64) < 2 ^ 64 * (U - P - d.val) by linarith) (by norm_num)
    rw [hPz] at this; exact this
  have hup' : (u1.val * 2 ^ 64 + u0.val - q1 * d.val - d.val : ℤ) <
      max (2 ^ 64 - d.val : ℤ) q0 := by
    have := Int.lt_of_mul_lt_mul_left
      (show 2 ^ 64 * (U - P - d.val) < 2 ^ 64 * max ((2 ^ 64 : ℤ) - d.val) q0 by linarith)
      (by norm_num)
    rw [hPz] at this; exact this
  have hlo1' : q1 * d.val ≤ u1.val * 2 ^ 64 + u0.val := by
    have : (q1 * d.val : ℤ) ≤ u1.val * 2 ^ 64 + u0.val := by rw [← hPz]; linarith
    exact_mod_cast this
  have := rem21_adjust u1.val u0.val d.val q1 q0 r.val hd hd' hu0 (by omega) hrv hlo1' hlo2' hup'
  rw [← this]
  simp only [addMod, subMod]
  split_ifs <;> rfl

end FeProofs.Modexp
