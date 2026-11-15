import FeProofs.Precompiles.Modexp.Div32

/-!
# Modexp: the quotient of three limbs by two

`div32_val`: with the reciprocal of a normalized `D = d1 β + d0` and `(u2, u1) < (d1, d0)`,
`div_3by2` returns `⌊U / D⌋` for `U = u2 β² + u1 β + u0` (Möller and Granlund's Theorem 3).
`div32_bounds` is the theorem's statement about the candidate remainder `r̃ = U - (q1 + 1) D`:
`-D ≤ r̃`, `q0 β - β² < r̃` and `r̃ < max(β² - D, q0 β)`, with the paper's three cases for the
upper bound.  `div32_adjust` is the adjustment, from those bounds and `r̃ mod β²`.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- Theorem 3's bounds, over the integers. -/
theorem div32_bounds (u2 u1 u0 d1 d0 v K q1 q0 D R : ℤ)
    (hD : D = d1 * 2 ^ 64 + d0) (hR : R = u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 - (q1 + 1) * D)
    (hd1 : 2 ^ 63 ≤ d1) (hd1' : d1 < 2 ^ 64) (hd0 : 0 ≤ d0) (hd0' : d0 < 2 ^ 64)
    (hv : 0 ≤ v) (hK : 1 ≤ K) (hKD : K ≤ D)
    (hV : (2 ^ 64 + v) * D + K = 2 ^ 192)
    (hu2 : 0 ≤ u2) (hu1 : 0 ≤ u1) (hu1' : u1 < 2 ^ 64) (hu0 : 0 ≤ u0) (hu0' : u0 < 2 ^ 64)
    (hu : u2 * 2 ^ 64 + u1 < D)
    (hX : (2 ^ 64 + v) * u2 + u1 = q1 * 2 ^ 64 + q0) (hq0 : 0 ≤ q0) (hq0' : q0 < 2 ^ 64) :
    -D ≤ R ∧ q0 * 2 ^ 64 - 2 ^ 128 < R ∧ R < max (2 ^ 128 - D) (q0 * 2 ^ 64) := by
  have hDlo : 2 ^ 127 ≤ D := by rw [hD]; linarith
  have hDhi : D < 2 ^ 128 := by rw [hD]; linarith
  -- `β r̃ = u2 K + u1 (β² - D) + u0 β + q0 D - β D`.
  have key : 2 ^ 64 * R = u2 * K + u1 * (2 ^ 128 - D) + u0 * 2 ^ 64 + q0 * D - 2 ^ 64 * D := by
    rw [hR]; linear_combination D * hX - u2 * hV
  have h1 : 0 ≤ u2 * K := mul_nonneg hu2 (by linarith)
  have h2 : 0 ≤ u1 * (2 ^ 128 - D) := mul_nonneg hu1 (by linarith)
  have h3 : 0 ≤ u0 * 2 ^ 64 := by positivity
  have hq0D : 0 ≤ q0 * D := mul_nonneg hq0 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ^ 64 * (-D) ≤ 2 ^ 64 * R := by linarith
    linarith
  · have : (2 ^ 64 - q0) * D < (2 ^ 64 - q0) * 2 ^ 128 :=
      mul_lt_mul_of_pos_left hDhi (by linarith)
    have : 2 ^ 64 * (q0 * 2 ^ 64 - 2 ^ 128) < 2 ^ 64 * R := by linarith
    linarith
  · set M := max (2 ^ 128 - D) (q0 * 2 ^ 64) with hM
    have hM1 : 2 ^ 128 - D ≤ M := le_max_left _ _
    have hM2 : q0 * 2 ^ 64 ≤ M := le_max_right _ _
    -- `(β² - D)² + q0 β D ≤ β² M`.
    have hc1 := mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 2 ^ 128 - D by linarith)
    have hc2 := mul_le_mul_of_nonneg_right hM2 (show 0 ≤ D by linarith)
    have hconv : (2 ^ 128 - D) * (2 ^ 128 - D) + q0 * 2 ^ 64 * D ≤ 2 ^ 128 * M := by
      linear_combination hc1 + hc2
    have hu0b : u0 * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by linarith
    have hu1b : u1 * (2 ^ 128 - D) ≤ (2 ^ 64 - 1) * (2 ^ 128 - D) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hd1D : d1 * 2 ^ 64 * D = D * D - d0 * D := by rw [hD]; ring
    have hd0D : 0 ≤ d0 * D := mul_nonneg hd0 (by linarith)
    have hfin : 2 ^ 128 * R < 2 ^ 128 * M → R < M := fun h =>
      lt_of_mul_lt_mul_left h (by norm_num)
    rcases lt_or_eq_of_le (show u2 ≤ d1 by rw [hD] at hu; linarith) with hlt | heq
    · -- `u2 ≤ d1 - 1`.
      have hK' : u2 * K ≤ (d1 - 1) * D :=
        mul_le_mul (by linarith) hKD (by linarith) (by linarith)
      apply hfin
      linear_combination 2 ^ 64 * key + 2 ^ 64 * hK' + 2 ^ 64 * hu1b + 2 ^ 64 * hu0b + hd1D +
        hconv + hd0D
    · subst heq
      have hu1d : u1 + 1 ≤ d0 := by rw [hD] at hu; linarith
      by_cases hDb : D ≤ 2 ^ 64 * (2 ^ 64 - 1)
      · have hK' : u2 * K ≤ u2 * D := mul_le_mul_of_nonneg_left hKD hu2
        have hu1b' : u1 * (2 ^ 128 - D) ≤ (d0 - 1) * (2 ^ 128 - D) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have hneg : (2 ^ 64 - d0) * ((2 ^ 64 + 1) * D - 2 ^ 192) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        apply hfin
        linear_combination 2 ^ 64 * key + 2 ^ 64 * hK' + 2 ^ 64 * hu1b' + 2 ^ 64 * hu0b + hd1D +
          hconv + hneg
      · -- `d1 = β - 1` and `v = 0`: then `q1 = β - 1`, `q0 = u1` and `r̃ < 0`.
        have hd1e : u2 = 2 ^ 64 - 1 := by rw [hD] at hDb; omega
        subst hd1e
        have hv0 : v = 0 := by
          by_contra h
          have : (2 ^ 64 + 1) * D ≤ (2 ^ 64 + v) * D :=
            mul_le_mul_of_nonneg_right (by omega) (by linarith)
          linarith
        subst hv0
        have hq1 : q1 = 2 ^ 64 - 1 := by omega
        subst hq1
        have : R < 0 := by rw [hR, hD]; linarith
        have : 0 ≤ M := le_trans (by linarith) hM1
        linarith

/-- The adjustment steps of `div32`, from Theorem 3's bounds on `R = U - P - D` (`P = q1 D`) and
    its residue `r` modulo `β²`: the quotient they return is `q1 + j` with `U` in
    `[P + j D, P + (j + 1) D)`. -/
theorem div32_adjust (U P D q1 q0 r : ℤ) (hq0 : 0 ≤ q0) (hq0' : q0 < 2 ^ 64)
    (hDlo : 2 ^ 127 ≤ D) (hDhi : D < 2 ^ 128)
    (hr : r = (U - P - D) % 2 ^ 128)
    (h1 : -D ≤ U - P - D) (h2 : q0 * 2 ^ 64 - 2 ^ 128 < U - P - D)
    (h3 : U - P - D < max (2 ^ 128 - D) (q0 * 2 ^ 64)) :
    ∃ j : ℤ, 0 ≤ j ∧ j ≤ 2 ∧ P + j * D ≤ U ∧ U < P + (j + 1) * D ∧
      (if q0 * 2 ^ 64 ≤ r then (if D ≤ (r + D) % 2 ^ 128 then q1 + 1 else q1)
       else (if D ≤ r then q1 + 2 else q1 + 1)) = q1 + j := by
  rw [max_def] at h3
  split_ifs at h3 ⊢ <;>
    first
    | exact ⟨0, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨1, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨2, by omega, by omega, by omega, by omega, by omega⟩

/-- The two-limb residue `div32` computes: `r ≡ U - q1 D - D (mod β²)`. -/
theorem div32_residue (u2 u1 u0 D A Bp : ℕ) (hu1 : u1 < 2 ^ 64) (hu0 : u0 < 2 ^ 64)
    (hD : D < 2 ^ 128) (hBp : Bp < 2 ^ 128) :
    ((((((u1 + 2 ^ 64 - A % 2 ^ 64) % 2 ^ 64) * 2 ^ 64 + u0 + 2 ^ 128 - Bp) % 2 ^ 128 + 2 ^ 128 -
      D) % 2 ^ 128 : ℕ) : ℤ) =
      ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 : ℕ) - ((A * 2 ^ 64 + Bp : ℕ) : ℤ) - D) % 2 ^ 128 := by
  omega

/-- `div32_adjust`'s selection, over the naturals. -/
theorem div32_sel_cast (q0 r D q1 jn : ℕ)
    (h : (if (q0 : ℤ) * 2 ^ 64 ≤ r then (if (D : ℤ) ≤ (r + D) % 2 ^ 128 then (q1 : ℤ) + 1 else q1)
      else (if (D : ℤ) ≤ r then (q1 : ℤ) + 2 else (q1 : ℤ) + 1)) = q1 + (jn : ℤ)) :
    (if q0 * 2 ^ 64 ≤ r then (if D ≤ (r + D) % 2 ^ 128 then q1 + 1 else q1)
      else (if D ≤ r then q1 + 2 else q1 + 1)) = q1 + jn := by
  split_ifs at h ⊢ <;> omega

/-- The selection at the end of `div32`, on limbs. -/
theorem div32_select (x r d : Dbl) (jn : ℕ)
    (hsel : (if (x.val % 2 ^ 64) * 2 ^ 64 ≤ r.val then
        (if d.val ≤ (r.val + d.val) % 2 ^ 128 then x.val / 2 ^ 64 + 1 else x.val / 2 ^ 64)
      else (if d.val ≤ r.val then x.val / 2 ^ 64 + 2 else x.val / 2 ^ 64 + 1)) =
        x.val / 2 ^ 64 + jn)
    (hlt : x.val / 2 ^ 64 + jn < 2 ^ 64) :
    (if (loD x).val ≤ (hiD r).val then
        if d.val ≤ (addD r d).val then addMod (subMod (addMod (hiD x) 1) 1) 1
        else subMod (addMod (hiD x) 1) 1
      else if d.val ≤ r.val then addMod (addMod (hiD x) 1) 1 else addMod (hiD x) 1).val =
      x.val / 2 ^ 64 + jn := by
  have h1 : (1 : Limb).val = 1 := rfl
  have := r.isLt
  split_ifs at hsel ⊢ <;> simp only [loD, hiD, addD, addMod, subMod, h1] at * <;> omega

/-- **Three limbs by two**: with the reciprocal of a normalized `D = d1 β + d0` and
    `u2 β + u1 < D`, `div32` is `⌊(u2 β² + u1 β + u0) / D⌋`. -/
theorem div32_val (u2 u1 u0 d1 d0 : Limb) (hd : 2 ^ 63 ≤ d1.val)
    (hu : u2.val * 2 ^ 64 + u1.val < d1.val * 2 ^ 64 + d0.val) :
    (div32 u2 u1 u0 d1 d0 (recip32 d1 d0 hd)).val =
      (u2.val * 2 ^ 128 + u1.val * 2 ^ 64 + u0.val) / (d1.val * 2 ^ 64 + d0.val) := by
  have hd1 := d1.isLt; have hd0 := d0.isLt; have hu2 := u2.isLt; have hu1 := u1.isLt
  have hu0 := u0.isLt
  obtain ⟨D, hD⟩ : ∃ D, D = d1.val * 2 ^ 64 + d0.val := ⟨_, rfl⟩
  rw [← hD] at hu ⊢
  have hDlo : 2 ^ 127 ≤ D := by omega
  have hDhi : D < 2 ^ 128 := by omega
  have hUD0 : u2.val * 2 ^ 128 + u1.val * 2 ^ 64 + u0.val < D * 2 ^ 64 := by
    have := Nat.mul_le_mul_right (2 ^ 64) (Nat.succ_le_of_lt hu)
    rw [Nat.succ_eq_add_one] at this
    linarith
  -- The reciprocal: `(β + v) D + K = β³` with `1 ≤ K ≤ D`.
  have hvv := recip32_val d1 d0 hd
  rw [← hD] at hvv
  have hvlt := (recip32 d1 d0 hd).isLt
  generalize hv : (recip32 d1 d0 hd).val = v at hvv hvlt
  have hdiv := Nat.div_add_mod (2 ^ 192 - 1) D
  have hmod := Nat.mod_lt (2 ^ 192 - 1) (show 0 < D by omega)
  have hge : 2 ^ 64 ≤ (2 ^ 192 - 1) / D := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_pred_of_lt hDhi)
    simp only [Nat.pred_eq_sub_one] at this; omega
  have hVD : (2 ^ 64 + v) * D + ((2 ^ 192 - 1) % D + 1) = 2 ^ 192 := by
    rw [hvv, Nat.add_sub_cancel' hge, Nat.mul_comm]; omega
  -- The estimate `x = (β + v) u2 + u1 = q1 β + q0` stays below `β²`.
  have hX : v * u2.val + (u2.val * 2 ^ 64 + u1.val) < 2 ^ 128 := by
    have h1 : (2 ^ 64 + v) * (u2.val * 2 ^ 64 + u1.val + 1) ≤ (2 ^ 64 + v) * D :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (2 ^ 64 + v) * (u2.val * 2 ^ 64 + u1.val + 1) = 2 ^ 128 * u2.val + 2 ^ 64 * u1.val +
        2 ^ 64 + 2 ^ 64 * (v * u2.val) + v * u1.val + v := by ring
    rw [e] at h1
    omega
  simp only [div32]
  generalize hxd : addD (mulD (recip32 d1 d0 hd) u2) (joinD u2 u1) = x
  have hxv : x.val = v * u2.val + (u2.val * 2 ^ 64 + u1.val) := by
    rw [← hxd]; simp only [addD, mulD, joinD]; rw [hv, Nat.mod_eq_of_lt hX]
  set q1 := x.val / 2 ^ 64 with hq1
  set q0 := x.val % 2 ^ 64 with hq0
  have hq1lt : q1 < 2 ^ 64 := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = q1 * d1.val := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp, Bp = d0.val * q1 := ⟨_, rfl⟩
  have hBplt : Bp < 2 ^ 128 := by rw [hBp]; exact mul_limbs_lt d0 ⟨q1, hq1lt⟩
  have hP : q1 * D = A * 2 ^ 64 + Bp := by rw [hA, hBp, hD]; ring
  generalize hrd : subD (subD (joinD (subMod u1 (mulLo (hiD x) d1)) u0)
    (mulD d0 (hiD x))) (joinD d1 d0) = r
  have hrv : (r.val : ℤ) = ((u2.val * 2 ^ 128 + u1.val * 2 ^ 64 + u0.val : ℕ) -
      ((q1 * D : ℕ) : ℤ) - D) % 2 ^ 128 := by
    rw [hP, ← div32_residue u2.val u1.val u0.val D A Bp hu1 hu0 hDhi hBplt, ← hrd]
    simp only [subD, joinD, subMod, mulLo, mulD, hiD, ← hq1, ← hA, ← hBp, ← hD]
  -- Theorem 3's bounds and the adjustment.
  obtain ⟨U, hU⟩ : ∃ U, U = u2.val * 2 ^ 128 + u1.val * 2 ^ 64 + u0.val := ⟨_, rfl⟩
  rw [← hU] at hrv ⊢
  have hxq : x.val = q1 * 2 ^ 64 + q0 := by omega
  have hK1 : 1 ≤ (2 ^ 192 - 1) % D + 1 := by omega
  have hKD : (2 ^ 192 - 1) % D + 1 ≤ D := by omega
  have nn : ∀ n : ℕ, (0 : ℤ) ≤ n := fun n => Int.natCast_nonneg n
  have hq0lt : q0 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨b1, b2, b3⟩ := div32_bounds u2.val u1.val u0.val d1.val d0.val v
    ((2 ^ 192 - 1) % D + 1 : ℕ) q1 q0 D (U - (q1 + 1) * D) (by rw [hD]; push_cast; ring)
    (by rw [hU]; push_cast; ring) (by exact_mod_cast hd) (by exact_mod_cast hd1)
    (nn _) (by exact_mod_cast hd0) (nn _) (by exact_mod_cast hK1)
    (by exact_mod_cast hKD) (by exact_mod_cast hVD) (nn _) (nn _)
    (by exact_mod_cast hu1) (nn _) (by exact_mod_cast hu0)
    (by exact_mod_cast hu)
    (by have := congrArg (fun n : ℕ => (n : ℤ)) (hxv.symm.trans hxq); push_cast at this
        linear_combination this)
    (nn _) (by exact_mod_cast hq0lt)
  obtain ⟨j, hj0, hj2, hjlo, hjhi, hsel⟩ := div32_adjust U (q1 * D : ℕ) D q1 q0 r.val
    (nn _) (by exact_mod_cast hq0lt)
    (by exact_mod_cast hDlo) (by exact_mod_cast hDhi) (by rw [hrv]) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; convert b3 using 1; ring)
  -- The quotient is `q1 + j`, below `β`.
  obtain ⟨jn, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  have hlo : (q1 + jn) * D ≤ U := by
    have : ((q1 + jn) * D : ℕ) ≤ (U : ℤ) := by push_cast at hjlo ⊢; linarith
    exact_mod_cast this
  have hhi : U < (q1 + jn + 1) * D := by
    have : (U : ℤ) < ((q1 + jn + 1) * D : ℕ) := by push_cast at hjhi ⊢; linarith
    exact_mod_cast this
  have hq : U / D = q1 + jn := Nat.div_eq_of_lt_le hlo hhi
  have hqlt : q1 + jn < 2 ^ 64 :=
    Nat.lt_of_mul_lt_mul_right (a := D) (lt_of_le_of_lt hlo (by rw [hU]; linarith))
  rw [hq]
  have hsel' := div32_sel_cast q0 r.val D q1 jn hsel
  have hjoin : (joinD d1 d0).val = D := by rw [hD]; rfl
  rw [← hjoin] at hsel'
  exact div32_select x r (joinD d1 d0) jn hsel' hqlt

end FeProofs.Modexp
