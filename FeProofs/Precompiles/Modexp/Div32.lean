import FeProofs.Precompiles.Modexp.Rem21

/-!
# Modexp: division of three limbs by two

`reciprocal_3by2` and `div_3by2` of `bignum.fe` are Möller and Granlund's Algorithms 6 and 5
("Improved division by invariant integers", 2011): the reciprocal `⌊(β³ - 1) / D⌋ - β` of a
normalized two-limb divisor `D = d1 β + d0` (`β = 2 ^ 64`, `β / 2 ≤ d1`), and with it the quotient
`⌊U / D⌋` of a three-limb `U = u2 β² + u1 β + u0` whose top two limbs are below `D`.

- `reciprocal_3by2_eq`, `div_3by2_eq`: the exported functions are `pure` of `recip32` and
  `div32`, which follow the Fe code on limbs.
- `recip32_val`: `recip32` is the reciprocal.  Its first phase steps the reciprocal of `d1`
  down while `(β + v) d1 + d0` carries out of two limbs; its second while `(β + v) D` reaches
  `β³`.
- `div32_val`: `div32` is the quotient (the paper's Theorem 3).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## The reciprocal of two limbs, as the Fe code computes it -/

/-- The first phase: the reciprocal of `d1` and the low limb of `(β + v) d1 + d0`, stepped down
    past the carries. -/
def recip32a (d1 d0 v : Limb) : Limb × Limb :=
  let p := addMod (mulLo d1 v) d0
  if p.val < d0.val then
    if d1.val ≤ p.val then (subMod (subMod v 1) 1, subMod (subMod p d1) d1)
    else (subMod v 1, subMod p d1)
  else (v, p)

/-- The second phase: the carry of `v d0` into `p`. -/
def recip32b (d1 d0 v p : Limb) : Limb :=
  let t := mulD v d0
  let p := addMod p (hiD t)
  if p.val < (hiD t).val then
    if d1.val < p.val then subMod (subMod v 1) 1
    else if p = d1 then (if d0.val ≤ (loD t).val then subMod (subMod v 1) 1 else subMod v 1)
    else subMod v 1
  else v

/-- `reciprocal_3by2` on limbs. -/
def recip32 (d1 d0 : Limb) (hd : 2 ^ 63 ≤ d1.val) : Limb :=
  let a := recip32a d1 d0 (recip21L d1 hd)
  recip32b d1 d0 a.1 a.2

theorem reciprocal_3by2_eq (d1 d0 : Limb) (hd : 2 ^ 63 ≤ d1.val) :
    reciprocal_3by2 d1.w d0.w = pure (recip32 d1 d0 hd).w := by
  simp only [reciprocal_3by2, reciprocal_2by1_eq _ hd, pure_bind, mulW64_eq, addW64_eq,
    subW64_eq, mulW128_eq, shr64_eq, down128_limb_eq, down128_eq, one_w, Limb.toNat_w,
    Limb.w_inj, recip32, recip32a, recip32b, decide_eq_true_eq]
  split_ifs <;> rfl

/-! ## The reciprocal of two limbs -/

/-- The first phase: `v1 = v0 - j` for the `j` carries of `Q(v) = (β + v) d1 + d0` out of two
    limbs, after which `Q(v1)` has the top limb `β - 1` and `p1` is its low limb. -/
theorem recip32a_spec (d1 d0 : Limb) (hd : 2 ^ 63 ≤ d1.val) :
    ∃ j, j ≤ 2 ∧ j ≤ recip21 d1.val ∧
      (recip32a d1 d0 (recip21L d1 hd)).1.val = recip21 d1.val - j ∧
      2 ^ 128 - 2 ^ 64 + (recip32a d1 d0 (recip21L d1 hd)).2.val + j * d1.val =
        2 ^ 64 * d1.val + recip21 d1.val * d1.val + d0.val ∧
      (0 < j → 2 ^ 128 + (j - 1) * d1.val ≤ 2 ^ 64 * d1.val + recip21 d1.val * d1.val + d0.val) := by
  obtain ⟨k, hk1, hkd, hk⟩ := recip21_spec hd d1.isLt
  have hd1 := d1.isLt; have hd0 := d0.isLt
  have hv := recip21_lt hd
  have h1 : (1 : Limb).val = 1 := rfl
  obtain ⟨A, hA⟩ : ∃ A, A = recip21 d1.val * d1.val := ⟨_, rfl⟩
  have hA' : d1.val * recip21 d1.val = A := by rw [hA, Nat.mul_comm]
  have hk' : 2 ^ 64 * d1.val + A + k = 2 ^ 128 := by rw [hA, ← hk]; ring
  have hAv : 2 ^ 63 * recip21 d1.val ≤ A := by
    rw [hA, Nat.mul_comm (2 ^ 63)]; exact Nat.mul_le_mul_left _ hd
  have hAv' : A ≤ 2 ^ 64 * recip21 d1.val := by
    rw [hA, Nat.mul_comm (2 ^ 64)]; exact Nat.mul_le_mul_left _ hd1.le
  rw [← hA]
  simp only [recip32a]
  have hAm : A % 2 ^ 64 = 2 ^ 64 - k := by
    rw [show A = (2 ^ 64 - d1.val - 1) * 2 ^ 64 + (2 ^ 64 - k) by
      have : 2 ^ 64 * d1.val ≤ 2 ^ 128 - 2 ^ 64 := by
        have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_pred_of_lt hd1)
        simp only [Nat.pred_eq_sub_one] at this; omega
      rw [Nat.sub_sub, Nat.sub_mul]; omega]
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hv1 : 1 ≤ recip21 d1.val := by
    by_contra h
    have : A = 0 := by omega
    omega
  split_ifs <;> simp only [recip21L, addMod, subMod, mulLo, h1, hA', hAm] at * <;> clear hA
  · rename_i c1 c2
    have hkd0 : k ≤ d0.val := by
      by_contra h; rw [addm_lt (p := 2 ^ 64 - k) (d := d0.val) (by omega)] at c1; omega
    rw [addm_ge (p := 2 ^ 64 - k) (by omega) hd0 (by omega)] at c1 c2 ⊢
    have hv2 : 2 ≤ recip21 d1.val := by
      by_contra h
      have : A ≤ 2 ^ 64 := by omega
      omega
    have e : 2 ^ 64 - k + d0.val - 2 ^ 64 = d0.val - k := by omega
    rw [e] at c1 c2 ⊢
    rw [subm_ge (p := d0.val - k) (by omega) c2,
      subm_lt (p := d0.val - k - d1.val) (d := d1.val) (by omega) (by omega), subm_ge hv hv1,
      subm_ge (p := recip21 d1.val - 1) (d := 1) (by omega) (by omega)]
    exact ⟨2, le_rfl, hv2, by omega, by omega, fun _ => by omega⟩
  · rename_i c1 c2
    have hkd0 : k ≤ d0.val := by
      by_contra h; rw [addm_lt (p := 2 ^ 64 - k) (d := d0.val) (by omega)] at c1; omega
    rw [addm_ge (p := 2 ^ 64 - k) (by omega) hd0 (by omega)] at c1 c2 ⊢
    have e : 2 ^ 64 - k + d0.val - 2 ^ 64 = d0.val - k := by omega
    rw [e] at c1 c2 ⊢
    rw [subm_lt (p := d0.val - k) (d := d1.val) (by omega) (by omega), subm_ge hv hv1]
    exact ⟨1, by omega, hv1, rfl, by omega, fun _ => by omega⟩
  · rename_i c1
    have hkd0 : d0.val < k := by
      by_contra h; rw [addm_ge (p := 2 ^ 64 - k) (by omega) hd0 (by omega)] at c1; omega
    rw [addm_lt (p := 2 ^ 64 - k) (d := d0.val) (by omega)]
    exact ⟨0, by omega, by omega, (Nat.sub_zero _).symm, by omega, fun h => by omega⟩

/-- The bounds that characterize `⌊(β³ - 1) / D⌋ = β + w`. -/
theorem recip32_char {d1 d0 w : ℕ} (hd : 2 ^ 63 ≤ d1)
    (h1 : ((2 ^ 64 + w) * (d1 * 2 ^ 64 + d0) : ℤ) ≤ 2 ^ 192 - 1)
    (h2 : (2 ^ 192 : ℤ) ≤ (2 ^ 64 + w + 1) * (d1 * 2 ^ 64 + d0)) :
    w = (2 ^ 192 - 1) / (d1 * 2 ^ 64 + d0) - 2 ^ 64 := by
  have hD : 0 < d1 * 2 ^ 64 + d0 := by positivity
  have := Nat.div_eq_of_lt_le (m := 2 ^ 192 - 1) (n := d1 * 2 ^ 64 + d0) (k := 2 ^ 64 + w)
    (by zify; rw [Nat.cast_sub (by norm_num)]; push_cast; linarith)
    (by zify; rw [Nat.cast_sub (by norm_num)]; push_cast; linarith)
  omega

/-- The second phase: from `Q(v1) = (β + v1) d1 + d0 = β² - β + p1` and `(β + v1 + 1) D ≥ β³`,
    `recip32b` steps `v1` down to the reciprocal. -/
theorem recip32b_val (d1 d0 v1 p1 : Limb) (hd : 2 ^ 63 ≤ d1.val)
    (hQ : ((2 ^ 64 + v1.val) * d1.val + d0.val : ℤ) = 2 ^ 128 - 2 ^ 64 + p1.val)
    (hup : (2 ^ 192 : ℤ) ≤ (2 ^ 64 + v1.val + 1) * (d1.val * 2 ^ 64 + d0.val)) :
    (recip32b d1 d0 v1 p1).val = (2 ^ 192 - 1) / (d1.val * 2 ^ 64 + d0.val) - 2 ^ 64 := by
  have hd1 := d1.isLt; have hd0 := d0.isLt
  obtain ⟨T, hT⟩ : ∃ T, T = v1.val * d0.val := ⟨_, rfl⟩
  have hTd : ((2 ^ 64 + v1.val) * (d1.val * 2 ^ 64 + d0.val) : ℤ) =
      2 ^ 64 * (2 ^ 128 - 2 ^ 64 + p1.val) + T := by
    have : (T : ℤ) = v1.val * d0.val := by exact_mod_cast hT
    rw [this, ← hQ]; ring
  have hTlt : T < 2 ^ 128 := by rw [hT]; exact mul_limbs_lt v1 d0
  have hDlo : (2 ^ 127 : ℤ) ≤ d1.val * 2 ^ 64 + d0.val := by
    have : (2 ^ 63 : ℤ) ≤ d1.val := by exact_mod_cast hd
    nlinarith
  suffices ∃ w : ℕ, (recip32b d1 d0 v1 p1).val = w ∧
      ((2 ^ 64 + w) * (d1.val * 2 ^ 64 + d0.val) : ℤ) ≤ 2 ^ 192 - 1 ∧
      (2 ^ 192 : ℤ) ≤ (2 ^ 64 + w + 1) * (d1.val * 2 ^ 64 + d0.val) by
    obtain ⟨w, hw, h1, h2⟩ := this
    rw [hw]; exact recip32_char hd h1 h2
  have hTdiv := Nat.div_add_mod T (2 ^ 64)
  have ht0 := Nat.mod_lt T (show 0 < 2 ^ 64 by norm_num)
  have ht1 : T / 2 ^ 64 < 2 ^ 64 := by omega
  have hTz : (T : ℤ) = 2 ^ 64 * (T / 2 ^ 64 : ℕ) + (T % 2 ^ 64 : ℕ) := by exact_mod_cast hTdiv.symm
  set D : ℤ := d1.val * 2 ^ 64 + d0.val with hD
  obtain ⟨W, hW⟩ : ∃ W : ℤ, W = (2 ^ 64 + v1.val) * D := ⟨_, rfl⟩
  have hWT : W = 2 ^ 64 * (2 ^ 128 - 2 ^ 64 + p1.val) + T := by rw [hW]; exact hTd
  have h1 : (1 : Limb).val = 1 := rfl
  have hp1lt := p1.isLt
  have hd0z : (d0.val : ℤ) < 2 ^ 64 := by exact_mod_cast hd0
  have hd1z : (d1.val : ℤ) < 2 ^ 64 := by exact_mod_cast hd1
  have hp1z : (p1.val : ℤ) < 2 ^ 64 := by exact_mod_cast hp1lt
  -- `v1 ≥ 1` when `W ≥ β³`, and `v1 ≥ 2` when `W - D ≥ β³`.
  have hv1_1 : (2 ^ 192 : ℤ) ≤ W → 1 ≤ v1.val := by
    intro h; by_contra h'
    have : v1.val = 0 := by omega
    rw [hW, this] at h; push_cast at h; linarith
  have hv1_2 : (2 ^ 192 : ℤ) ≤ W - D → 2 ≤ v1.val := by
    intro h; by_contra h'
    have : (v1.val : ℤ) ≤ 1 := by exact_mod_cast (show v1.val ≤ 1 by omega)
    have : W - D ≤ 2 ^ 64 * D := by
      rw [hW]; nlinarith
    linarith
  have wm1 : ∀ n, n ≤ v1.val → ((2 ^ 64 + (v1.val - n : ℕ)) * D : ℤ) = W - n * D := by
    intro n hn; rw [hW]; push_cast [hn]; ring
  have wp1 : ∀ n, n ≤ v1.val → ((2 ^ 64 + (v1.val - n : ℕ) + 1) * D : ℤ) = W - n * D + D := by
    intro n hn; rw [hW]; push_cast [hn]; ring
  simp only [recip32b, addMod, subMod, mulD, hiD, loD, ← hT]
  have hDlo' : (2 ^ 128 : ℤ) ≤ 2 * D := by linarith
  have hcast : ∀ a b : ℕ, a ≤ b → (a : ℤ) ≤ b := fun a b h => by exact_mod_cast h
  split_ifs with c1 c2 c3 c4 <;> simp only [h1, Fin.ext_iff] at *
  all_goals
    generalize T / 2 ^ 64 = t1 at *
    generalize T % 2 ^ 64 = t0 at *
    have ht0z : (t0 : ℤ) < 2 ^ 64 := by exact_mod_cast ht0
    have hW' : W = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * (p1.val + t1 : ℤ) + t0 := by
      rw [hWT, hTz]; ring
  · have hc : 2 ^ 64 ≤ p1.val + t1 := by
      by_contra h; rw [addm_lt (by omega)] at c1; omega
    rw [addm_ge hp1lt ht1 hc] at c2
    have c2z := hcast (d1.val + 1 + 2 ^ 64) (p1.val + t1) (by omega)
    push_cast at c2z
    have hge : (2 ^ 192 : ℤ) ≤ W - D := by rw [hW', hD]; linarith
    have hv2 := hv1_2 hge
    rw [subm_ge v1.isLt (by omega), subm_ge (p := v1.val - 1) (by omega) (by omega)]
    refine ⟨v1.val - 2, by omega, ?_, ?_⟩
    · rw [wm1 2 hv2, Nat.cast_ofNat]; rw [hW']; linarith
    · rw [wp1 2 hv2, Nat.cast_ofNat]; linarith
  · have hc : 2 ^ 64 ≤ p1.val + t1 := by
      by_contra h; rw [addm_lt (by omega)] at c1; omega
    rw [addm_ge hp1lt ht1 hc] at c3
    have c3a := hcast (p1.val + t1) (d1.val + 2 ^ 64) (by omega)
    have c3b := hcast (d1.val + 2 ^ 64) (p1.val + t1) (by omega)
    have c4z := hcast d0.val t0 c4
    push_cast at c3a c3b
    have hge : (2 ^ 192 : ℤ) ≤ W - D := by rw [hW', hD]; linarith
    have hv2 := hv1_2 hge
    rw [subm_ge v1.isLt (by omega), subm_ge (p := v1.val - 1) (by omega) (by omega)]
    refine ⟨v1.val - 2, by omega, ?_, ?_⟩
    · rw [wm1 2 hv2, Nat.cast_ofNat]; rw [hW']; linarith
    · rw [wp1 2 hv2, Nat.cast_ofNat]; linarith
  · have hc : 2 ^ 64 ≤ p1.val + t1 := by
      by_contra h; rw [addm_lt (by omega)] at c1; omega
    rw [addm_ge hp1lt ht1 hc] at c3
    have c3a := hcast (p1.val + t1) (d1.val + 2 ^ 64) (by omega)
    have c3b := hcast (d1.val + 2 ^ 64) (p1.val + t1) (by omega)
    have c4z := hcast (t0 + 1) d0.val (by omega)
    push_cast at c3a c3b c4z
    have hge : (2 ^ 192 : ℤ) ≤ W := by rw [hW']; linarith
    have hv := hv1_1 hge
    rw [subm_ge v1.isLt hv]
    refine ⟨v1.val - 1, rfl, ?_, ?_⟩
    · rw [wm1 1 hv, Nat.cast_one]; rw [hW', hD]; linarith
    · rw [wp1 1 hv, Nat.cast_one]; linarith
  · have hc : 2 ^ 64 ≤ p1.val + t1 := by
      by_contra h; rw [addm_lt (by omega)] at c1; omega
    rw [addm_ge hp1lt ht1 hc] at c2 c3
    have c3z := hcast (p1.val + t1 + 1) (d1.val + 2 ^ 64) (by omega)
    have hcz := hcast (2 ^ 64) (p1.val + t1) hc
    push_cast at c3z hcz
    have hge : (2 ^ 192 : ℤ) ≤ W := by rw [hW']; linarith
    have hv := hv1_1 hge
    rw [subm_ge v1.isLt hv]
    refine ⟨v1.val - 1, rfl, ?_, ?_⟩
    · rw [wm1 1 hv, Nat.cast_one]; rw [hW', hD]; linarith
    · rw [wp1 1 hv, Nat.cast_one]; linarith
  · have hc : p1.val + t1 < 2 ^ 64 := by
      by_contra h; rw [addm_ge hp1lt ht1 (by omega)] at c1; omega
    have hcz := hcast (p1.val + t1 + 1) (2 ^ 64) hc
    push_cast at hcz
    refine ⟨v1.val, rfl, ?_, hup⟩
    rw [← hW, hW']; linarith


/-- **The reciprocal of two limbs**: `reciprocal_3by2` of a normalized `D = d1 β + d0` is
    `⌊(β³ - 1) / D⌋ - β`. -/
theorem recip32_val (d1 d0 : Limb) (hd : 2 ^ 63 ≤ d1.val) :
    (recip32 d1 d0 hd).val = (2 ^ 192 - 1) / (d1.val * 2 ^ 64 + d0.val) - 2 ^ 64 := by
  obtain ⟨k, hk1, hkd, hk⟩ := recip21_spec hd d1.isLt
  obtain ⟨j, hj2, hjv, hv1, hp1, hcarry⟩ := recip32a_spec d1 d0 hd
  have hd1 := d1.isLt; have hd0 := d0.isLt
  have hv := recip21_lt hd
  simp only [recip32]
  generalize recip32a d1 d0 (recip21L d1 hd) = a at hv1 hp1
  obtain ⟨v1, p1⟩ := a
  simp only at hv1 hp1 ⊢
  set v0 := recip21 d1.val with hv0
  -- `Q(v1) = (β + v1) d1 + d0 = β² - β + p1`.
  have hQ : ((2 ^ 64 + v1.val) * d1.val + d0.val : ℤ) = 2 ^ 128 - 2 ^ 64 + p1.val := by
    have e1 : (v1.val : ℤ) = v0 - j := by rw [hv1]; push_cast [hjv]; ring
    have e2 : ((2 ^ 128 - 2 ^ 64 + p1.val + j * d1.val : ℕ) : ℤ) =
        ((2 ^ 64 * d1.val + v0 * d1.val + d0.val : ℕ) : ℤ) := by rw [hp1]
    push_cast at e2
    rw [e1]; linear_combination -e2
  have hv1' : v1.val + j = v0 := by omega
  have hv1z : (v1.val : ℤ) + j = v0 := by exact_mod_cast hv1'
  -- The next reciprocal up is too large.
  have hup : (2 ^ 192 : ℤ) ≤ (2 ^ 64 + v1.val + 1) * (d1.val * 2 ^ 64 + d0.val) := by
    have hq : (2 ^ 128 : ℤ) ≤ (2 ^ 64 + v1.val + 1) * d1.val + d0.val := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        have hk' : ((2 ^ 64 + v0) * d1.val + k : ℤ) = 2 ^ 128 := by exact_mod_cast hk
        have : (k : ℤ) ≤ d1.val := by exact_mod_cast hkd
        have : (v1.val : ℤ) = v0 := by simpa using hv1z
        rw [this]; linarith
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have h := hcarry h0
        simp only [Nat.add_sub_cancel] at h
        have h' : ((2 ^ 128 + j' * d1.val : ℕ) : ℤ) ≤
            ((2 ^ 64 * d1.val + v0 * d1.val + d0.val : ℕ) : ℤ) := by exact_mod_cast h
        push_cast at h' hv1z
        have : (v1.val : ℤ) + 1 = v0 - j' := by linarith
        rw [add_assoc, this]; linarith
    have h0 : (0 : ℤ) ≤ d0.val := Int.natCast_nonneg _
    have h2 : (2 ^ 64 : ℤ) * d0.val ≤ (2 ^ 64 + v1.val + 1) * d0.val := by
      apply mul_le_mul_of_nonneg_right _ h0
      have : (0 : ℤ) ≤ v1.val := Int.natCast_nonneg _
      linarith
    have h3 := mul_le_mul_of_nonneg_left hq (show (0 : ℤ) ≤ 2 ^ 64 by norm_num)
    linear_combination h3 + h2
  exact recip32b_val d1 d0 v1 p1 hd hQ hup

/-! ## The quotient of three limbs by two, as the Fe code computes it -/

/-- `div_3by2` on limbs: the quotient of `(u2, u1, u0)` by `(d1, d0)` with the reciprocal `v`. -/
def div32 (u2 u1 u0 d1 d0 v : Limb) : Limb :=
  let x := addD (mulD v u2) (joinD u2 u1)
  let q1 := hiD x
  let q0 := loD x
  let r1 := subMod u1 (mulLo q1 d1)
  let d := joinD d1 d0
  let r := subD (subD (joinD r1 u0) (mulD d0 q1)) d
  let q := addMod q1 1
  if q0.val ≤ (hiD r).val then
    if d.val ≤ (addD r d).val then addMod (subMod q 1) 1 else subMod q 1
  else if d.val ≤ r.val then addMod q 1 else q

theorem div_3by2_eq (u2 u1 u0 d1 d0 v : Limb) :
    div_3by2 u2.w u1.w u0.w d1.w d0.w v.w = pure (div32 u2 u1 u0 d1 d0 v).w := by
  simp only [div_3by2, div_3by2_k1, div_3by2_k2, mulW128_eq, shl128_join, addW128_eq, shr64_eq,
    down128_limb_eq, down128_eq, pure_bind, mulW64_eq, subW64_eq, addW64_eq, subW128_eq, one_w,
    Limb.toNat_w, Dbl.toNat_w, div32, decide_eq_true_eq]
  split_ifs <;> rfl

end FeProofs.Modexp
