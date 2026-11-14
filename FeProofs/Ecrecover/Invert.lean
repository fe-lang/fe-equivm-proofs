import FeProofs.Ecrecover.Normalize
import Fe.Partial
import Mathlib.RingTheory.Coprime.Basic

/-!
# Ecrecover: the loop of `invert`

`invert` keeps `d x ≡ f` and `e x ≡ g (mod m)` with `f, g` coprime and `f` odd, and multiplies
`(d, e)` and `(f, g)` by each transition matrix of `divsteps`, divided by `2 ^ 62` (`InvState`,
`InvState.step`).  When `g = 0`, `f = ±1` and `normalize` returns `x⁻¹ mod m`.  The loop is a
`partial_fixpoint`, so its correctness is partial (`invert_5_spec`): a run either diverges or
returns that inverse.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Ecrecover

open Exported

/-- Limbs that fit the `i128` chains: all below `2 ^ 62`. -/
def Lim (a : ℕ → ℤ) : Prop := ∀ i, |a i| ≤ 2 ^ 62

/-- The modulus: canonical odd limbs, top limb below `2 ^ 8`, and its inverse modulo `2 ^ 62`. -/
structure ModSpec (m : ℕ → ℤ) (inv : Limb) : Prop where
  canon : Canon m
  lim : Lim m
  top : |m 4| ≤ 2 ^ 8
  pos : 0 < val5 m
  lt : val5 m < 2 ^ 256
  odd : val5 m % 2 = 1
  inv : m 0 * inv.val ≡ 1 [ZMOD 2 ^ 62]

/-- The state of the loop of `invert` for `x` modulo `M`. -/
structure InvState (M X : ℤ) (d e f g : ℕ → ℤ) (eta : ℤ) : Prop where
  cd : Canon d
  ce : Canon e
  cf : Canon f
  cg : Canon g
  ld : Lim d
  le : Lim e
  lf : Lim f
  lg : Lim g
  eta : eta.bmod (2 ^ 64) = eta
  fodd : val5 f % 2 = 1
  fb : |val5 f| ≤ M
  gb : |val5 g| ≤ M
  dr : -2 * M < val5 d ∧ val5 d < M
  er : -2 * M < val5 e ∧ val5 e < M
  dx : val5 d * X ≡ val5 f [ZMOD M]
  ex : val5 e * X ≡ val5 g [ZMOD M]
  cop : IsCoprime (val5 f) (val5 g)

theorem isCoprime_two_pow {M : ℤ} (h : M % 2 = 1) : IsCoprime M (2 ^ 62) := by
  apply IsCoprime.pow_right
  exact ⟨1, -(M / 2), by omega⟩

theorem cancel_two_pow {M a b : ℤ} (hM : M % 2 = 1) (h : 2 ^ 62 * a ≡ 2 ^ 62 * b [ZMOD M]) :
    a ≡ b [ZMOD M] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  rw [show 2 ^ 62 * b - 2 ^ 62 * a = 2 ^ 62 * (b - a) by ring] at h
  exact (isCoprime_two_pow hM).dvd_of_dvd_mul_left h

theorem limb0_val {f : ℕ → ℤ} (hf : Canon f) : ((Limb.ofInt (f 0)).val : ℤ) = f 0 := by
  rw [Limb.ofInt_val]
  have := hf 0 (by decide)
  exact Int.emod_eq_of_lt this.1 (by linarith [this.2])

theorem lim_of_canon {a : ℕ → ℤ} (hc : Canon a) (ht : |a 4| ≤ 2 ^ 62) (hrest : ∀ i > 4, |a i| ≤ 2 ^ 62) :
    Lim a := by
  intro i
  rcases Nat.lt_or_ge i 4 with h | h
  · have := hc i h; rw [abs_le]; constructor <;> linarith
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; exact ht
    · exact hrest i h

theorem top20 {a : ℕ → ℤ} (hc : Canon a) {M : ℤ} (hM : M < 2 ^ 256) (h1 : -2 * M < val5 a)
    (h2 : |val5 a| ≤ M ∨ val5 a < M) : |a 4| ≤ 2 ^ 20 := by
  have h3 : val5 a < 2 ^ 257 := by
    rcases h2 with h | h
    · linarith [le_abs_self (val5 a)]
    · linarith
  have := top_small hc (by linarith) h3
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem fgOut_ge (U V : ℤ) (a b : ℕ → ℤ) : ∀ i, 4 ≤ i → fgOut U V a b i = fgC U V a b 4 / 2 ^ 62
  | _ + 4, _ => rfl

theorem deOut_ge (U V k : ℤ) (a b m : ℕ → ℤ) : ∀ i, 4 ≤ i → deOut U V k a b m i = deC U V k a b m 4 / 2 ^ 62
  | _ + 4, _ => rfl

theorem deOut_low (U V k : ℤ) (a b m : ℕ → ℤ) {i : ℕ} (hi : i < 4) :
    0 ≤ deOut U V k a b m i ∧ deOut U V k a b m i < 2 ^ 62 := by
  have h := fun j => Int.emod_nonneg (deC U V k a b m j) (show (2 : ℤ) ^ 62 ≠ 0 by norm_num)
  have h' := fun j => Int.emod_lt_of_pos (deC U V k a b m j) (show (0 : ℤ) < 2 ^ 62 by norm_num)
  interval_cases i <;> exact ⟨h _, h' _⟩

/-- One pass of the loop keeps the state. -/
theorem InvState.step {X : ℤ} {m : ℕ → ℤ} {inv : Limb} (hm : ModSpec m inv)
    {d e f g : ℕ → ℤ} {eta : ℤ} (hs : InvState (val5 m) X d e f g eta) {eta' U V Q R : ℤ}
    (ht : TSpec (Limb.ofInt (f 0)) (Limb.ofInt (g 0)) U V Q R) (he' : eta'.bmod (2 ^ 64) = eta') :
    InvState (val5 m) X (deOut U V (kOf inv U V d e) d e m) (deOut Q R (kOf inv Q R d e) d e m)
      (fgOut U V f g) (fgOut Q R f g) eta' := by
  have hM := hm.pos
  have hU : |U| ≤ 2 ^ 62 := by linarith [ht.row1, abs_nonneg V]
  have hV : |V| ≤ 2 ^ 62 := by linarith [ht.row1, abs_nonneg U]
  have hQ : |Q| ≤ 2 ^ 62 := by linarith [ht.row2, abs_nonneg R]
  have hR : |R| ≤ 2 ^ 62 := by linarith [ht.row2, abs_nonneg Q]
  have tf := top20 hs.cf hm.lt (by linarith [neg_abs_le (val5 f), hs.fb]) (Or.inl hs.fb)
  have tg := top20 hs.cg hm.lt (by linarith [neg_abs_le (val5 g), hs.gb]) (Or.inl hs.gb)
  have td := top20 hs.cd hm.lt hs.dr.1 (Or.inr hs.dr.2)
  have te := top20 hs.ce hm.lt hs.er.1 (Or.inr hs.er.2)
  have hf0 := limb0_val hs.cf
  have hg0 := limb0_val hs.cg
  -- `(f, g)`.
  have hfg1 : 2 ^ 62 ∣ fgC U V f g 0 := by
    have := ht.cong1; rw [hf0, hg0] at this
    exact Int.modEq_zero_iff_dvd.mp this
  have hfg2 : 2 ^ 62 ∣ fgC Q R f g 0 := by
    have := ht.cong2; rw [hf0, hg0] at this
    exact Int.modEq_zero_iff_dvd.mp this
  have hF := fgOut_value U V f g hfg1
  have hG := fgOut_value Q R f g hfg2
  -- `(d, e)`.
  have hD := deOut_value U V (kOf inv U V d e) d e m (deC_dvd inv U V d e m hm.inv)
  have hE := deOut_value Q R (kOf inv Q R d e) d e m (deC_dvd inv Q R d e m hm.inv)
  have hP : (0 : ℤ) < 2 ^ 62 := by norm_num
  -- The bound on a combination of `(f, g)`.
  have comb : ∀ {A B : ℤ}, |A| + |B| ≤ 2 ^ 62 → |A * val5 f + B * val5 g| ≤ 2 ^ 62 * val5 m := by
    intro A B h
    have := abs_add_le (A * val5 f) (B * val5 g)
    rw [abs_mul, abs_mul] at this
    have := mul_le_mul_of_nonneg_left hs.fb (abs_nonneg A)
    have := mul_le_mul_of_nonneg_left hs.gb (abs_nonneg B)
    nlinarith [abs_nonneg A, abs_nonneg B]
  have sel_eq : ∀ A B : ℤ, sel A B d e = (if val5 d < 0 then A else 0) + (if val5 e < 0 then B else 0) := by
    intro A B
    unfold sel
    rw [if_congr (val5_neg_iff hs.cd).symm rfl rfl, if_congr (val5_neg_iff hs.ce).symm rfl rfl]
  refine ⟨fun i hi => deOut_low _ _ _ _ _ _ hi, fun i hi => deOut_low _ _ _ _ _ _ hi,
    fun i hi => fgOut_low _ _ _ _ hi, fun i hi => fgOut_low _ _ _ _ hi, ?_, ?_, ?_, ?_, he', ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases Nat.lt_or_ge i 4 with h | h
    · have := deOut_low U V (kOf inv U V d e) d e m h; rw [abs_le]; constructor <;> linarith
    · rw [deOut_ge _ _ _ _ _ _ i h]
      exact de_top (by linarith [ht.row1]) (abs_kOf ht.row1 inv d e) hs.ld hs.le hm.lim td te hm.top
  · intro i
    rcases Nat.lt_or_ge i 4 with h | h
    · have := deOut_low Q R (kOf inv Q R d e) d e m h; rw [abs_le]; constructor <;> linarith
    · rw [deOut_ge _ _ _ _ _ _ i h]
      exact de_top (by linarith [ht.row2]) (abs_kOf ht.row2 inv d e) hs.ld hs.le hm.lim td te hm.top
  · intro i
    rcases Nat.lt_or_ge i 4 with h | h
    · have := fgOut_low U V f g h; rw [abs_le]; constructor <;> linarith
    · rw [fgOut_ge _ _ _ _ i h]; exact fg_top hU hV hs.lf hs.lg tf tg
  · intro i
    rcases Nat.lt_or_ge i 4 with h | h
    · have := fgOut_low Q R f g h; rw [abs_le]; constructor <;> linarith
    · rw [fgOut_ge _ _ _ _ i h]; exact fg_top hQ hR hs.lf hs.lg tf tg
  · -- `f` stays odd: `u, v` are even and `u f0 + v g0 ≡ 2 ^ 62 (mod 2 ^ 63)`.
    obtain ⟨u', hu'⟩ := ht.even_u
    obtain ⟨v', hv'⟩ := ht.even_v
    obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp ht.odd1.symm)
    rw [hf0, hg0] at hk
    have hFv : val5 f = f 0 + 2 ^ 62 * (f 1 + 2 ^ 62 * f 2 + 2 ^ 124 * f 3 + 2 ^ 186 * f 4) := by
      unfold val5; ring
    have hGv : val5 g = g 0 + 2 ^ 62 * (g 1 + 2 ^ 62 * g 2 + 2 ^ 124 * g 3 + 2 ^ 186 * g 4) := by
      unfold val5; ring
    have : 2 ^ 62 * val5 (fgOut U V f g) = 2 ^ 62 * (1 + 2 * (k + u' * (f 1 + 2 ^ 62 * f 2 +
        2 ^ 124 * f 3 + 2 ^ 186 * f 4) + v' * (g 1 + 2 ^ 62 * g 2 + 2 ^ 124 * g 3 + 2 ^ 186 * g 4))) := by
      rw [hF, hFv, hGv, hu', hv']
      rw [hu', hv'] at hk
      linear_combination hk
    have := mul_left_cancel₀ (by norm_num : (2 : ℤ) ^ 62 ≠ 0) this
    omega
  · have := comb ht.row1
    rw [← hF, abs_mul, abs_of_pos hP] at this
    exact le_of_mul_le_mul_left this hP
  · have := comb ht.row2
    rw [← hG, abs_mul, abs_of_pos hP] at this
    exact le_of_mul_le_mul_left this hP
  · obtain ⟨-, c1, -⟩ := corr_spec inv (lc U V (d 0) (e 0)) (sel U V d e)
    obtain ⟨c0, -, -⟩ := corr_spec inv (lc U V (d 0) (e 0)) (sel U V d e)
    exact de_range ht.row1 hM hs.dr hs.er (by rw [kOf, sel_eq]) ⟨c0, c1⟩ hD
  · obtain ⟨-, c1, -⟩ := corr_spec inv (lc Q R (d 0) (e 0)) (sel Q R d e)
    obtain ⟨c0, -, -⟩ := corr_spec inv (lc Q R (d 0) (e 0)) (sel Q R d e)
    exact de_range ht.row2 hM hs.dr hs.er (by rw [kOf, sel_eq]) ⟨c0, c1⟩ hE
  · apply cancel_two_pow hm.odd
    rw [← mul_assoc, hD, hF]
    calc (U * val5 d + V * val5 e + kOf inv U V d e * val5 m) * X
        = U * (val5 d * X) + V * (val5 e * X) + val5 m * (kOf inv U V d e * X) := by ring
      _ ≡ U * val5 f + V * val5 g + 0 [ZMOD val5 m] :=
          ((hs.dx.mul_left _).add (hs.ex.mul_left _)).add
            (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
      _ = U * val5 f + V * val5 g := by ring
  · apply cancel_two_pow hm.odd
    rw [← mul_assoc, hE, hG]
    calc (Q * val5 d + R * val5 e + kOf inv Q R d e * val5 m) * X
        = Q * (val5 d * X) + R * (val5 e * X) + val5 m * (kOf inv Q R d e * X) := by ring
      _ ≡ Q * val5 f + R * val5 g + 0 [ZMOD val5 m] :=
          ((hs.dx.mul_left _).add (hs.ex.mul_left _)).add
            (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
      _ = Q * val5 f + R * val5 g := by ring
  · -- `(f, g) = adj(t) (f', g')`, so a Bézout pair carries over.
    have e1 : val5 f = R * val5 (fgOut U V f g) - V * val5 (fgOut Q R f g) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ^ 62 ≠ 0)
      linear_combination -R * hF + V * hG - val5 f * ht.det
    have e2 : val5 g = U * val5 (fgOut Q R f g) - Q * val5 (fgOut U V f g) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ^ 62 ≠ 0)
      linear_combination -U * hG + Q * hF - val5 g * ht.det
    obtain ⟨a, b, hab⟩ := hs.cop
    exact ⟨a * R - b * Q, b * U - a * V, by rw [e1, e2] at hab; linear_combination hab⟩

end FeProofs.Ecrecover
