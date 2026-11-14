import FeProofs.Precompiles.Inverse.Normalize
import Fe.Partial
import Mathlib.RingTheory.Coprime.Basic

/-!
# Precompiles: the loop of `invert`

`invert` keeps `d x ≡ f` and `e x ≡ g (mod m)` with `f, g` coprime and `f` odd, and multiplies
`(d, e)` and `(f, g)` by each transition matrix of `divsteps`, divided by `2 ^ 62` (`InvState`,
`InvState.step`).  When `g = 0`, `f = ±1` and `normalize` returns `x⁻¹ mod m`.  The loop is a
`partial_fixpoint`, so its correctness is partial (`invert_5_spec`): a run either diverges or
returns that inverse.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

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

/-! ## The loop -/

/-- What a run of the loop may do: diverge, or return the inverse of `X` modulo `M` on
canonical limbs, the world unchanged. -/
def Good (M X : ℤ) (w : World) (o : Option (Except (Exit World) (Vector UInt256 5 × World))) : Prop :=
  o = none ∨ ∃ out, o = some (.ok (vec5 out, w)) ∧ Canon out ∧ 0 ≤ val5 out ∧ val5 out < M ∧
    val5 out * X ≡ 1 [ZMOD M]

/-- The loop's arguments hold a state. -/
def St (M X : ℤ) (r0 r1 r2 r3 : Vector UInt256 5) (r4 : UInt256) : Prop :=
  ∃ d e f g eta, r0 = vec5 d ∧ r1 = vec5 e ∧ r2 = vec5 f ∧ r3 = vec5 g ∧ r4 = I eta ∧
    InvState M X d e f g eta

theorem R64_of_lim {a : ℕ → ℤ} (h : Lim a) (i : ℕ) : R64 (a i) := by
  have := h i; rw [abs_le] at this; constructor <;> linarith

theorem val5_eq_zero_iff {a : ℕ → ℤ} (ha : Canon a) :
    val5 a = 0 ↔ (a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0) := by
  have h0 := ha 0 (by decide); have h1 := ha 1 (by decide)
  have h2 := ha 2 (by decide); have h3 := ha 3 (by decide)
  unfold val5
  constructor
  · intro h; omega
  · rintro ⟨a0, a1, a2, a3, a4⟩; rw [a0, a1, a2, a3, a4]; ring

theorem odd_limb0 {f : ℕ → ℤ} (hc : Canon f) (h : val5 f % 2 = 1) :
    (Limb.ofInt (f 0)).val % 2 = 1 := by
  have := limb0_val hc
  have hv : val5 f = f 0 + 2 * (2 ^ 61 * (f 1 + 2 ^ 62 * f 2 + 2 ^ 124 * f 3 + 2 ^ 186 * f 4)) := by
    unfold val5; ring
  omega

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
open Lean.Order in
/-- The loop of `invert`, from any state: it diverges or returns `X⁻¹ mod M`. -/
theorem invert_loop {m : ℕ → ℤ} {inv : Limb} (hm : ModSpec m inv) (X : ℤ)
    (r11 : Vector UInt256 5) :
    ∀ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w,
      Good (val5 m) X w ((invert_5.b1 (vec5 m) inv.w r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11).exec env w) := by
  refine invert_5.b1.fixpoint_induct (vec5 m) inv.w r11
    (fun F => ∀ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w,
      Good (val5 m) X w ((F r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10).exec env w)) ?_ ?_
  · refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → UInt256 → Transition → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r0 G => ∀ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r1 r2 r3 r4 r5 r6 r7 r8 r9 r10).exec env w)) (fun r0 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → UInt256 → Transition → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r1 G => ∀ r2 r3 r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r2 r3 r4 r5 r6 r7 r8 r9 r10).exec env w)) (fun r1 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → UInt256 → Transition → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r2 G => ∀ r3 r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r3 r4 r5 r6 r7 r8 r9 r10).exec env w)) (fun r2 => ?_)
    refine Fe.M.admissible_arrow (β := UInt256 → Transition → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r3 G => ∀ r4 r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r4 r5 r6 r7 r8 r9 r10).exec env w)) (fun r3 => ?_)
    refine Fe.M.admissible_arrow (β := Transition → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r4 G => ∀ r5 r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r5 r6 r7 r8 r9 r10).exec env w)) (fun r4 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r5 G => ∀ r6 r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r6 r7 r8 r9 r10).exec env w)) (fun r5 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r6 G => ∀ r7 r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r7 r8 r9 r10).exec env w)) (fun r6 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r7 G => ∀ r8 r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r8 r9 r10).exec env w)) (fun r7 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r8 G => ∀ r9 r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r9 r10).exec env w)) (fun r8 => ?_)
    refine Fe.M.admissible_arrow (β := (Vector UInt256 5) → FeM (Vector UInt256 5))
      (fun r9 G => ∀ r10, St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G r10).exec env w)) (fun r9 => ?_)
    refine Fe.M.admissible_arrow (β := FeM (Vector UInt256 5))
      (fun r10 G => St (val5 m) X r0 r1 r2 r3 r4 → ∀ env w, Good (val5 m) X w ((G).exec env w)) (fun r10 => ?_)
    refine admissible_pi _ (fun _ => ?_)
    exact Fe.M.admissible_outcome (fun _ w o => Good (val5 m) X w o) (fun _ _ => Or.inl rfl)
  · intro F ih r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 hst env w
    obtain ⟨d, e, f, g, eta, rfl, rfl, rfl, rfl, rfl, hs⟩ := hst
    simp only [is_zero_5_eq g (R64_of_lim hs.lg), pure_bind]
    have hM := hm.pos
    have tf := top20 hs.cf hm.lt (by linarith [neg_abs_le (val5 f), hs.fb]) (Or.inl hs.fb)
    have tg := top20 hs.cg hm.lt (by linarith [neg_abs_le (val5 g), hs.gb]) (Or.inl hs.gb)
    have td := top20 hs.cd hm.lt hs.dr.1 (Or.inr hs.dr.2)
    have te := top20 hs.ce hm.lt hs.er.1 (Or.inr hs.er.2)
    by_cases hz : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 ∧ g 3 = 0 ∧ g 4 = 0
    · -- `g = 0`: `f = ±1`, and `normalize` returns `± d`.
      simp only [hz, checkIndex, idx_lits, lt5, if_true, pure_bind, vec5, vget5]
      obtain ⟨out, hout, hco, h0, h1, hc⟩ := normalize_spec d m (f 4) hs.cd hm.canon
        (R64_of_lim hs.lf 4) hm.pos hm.lt hs.dr.1 hs.dr.2
      simp only [vec5] at hout
      rw [hout]
      refine Or.inr ⟨out, rfl, hco, h0, h1, ?_⟩
      have hG : val5 g = 0 := (val5_eq_zero_iff hs.cg).mpr hz
      have hu : IsUnit (val5 f) := by
        have := hs.cop; rw [hG] at this; exact isCoprime_zero_right.mp this
      have hsg := val5_neg_iff hs.cf
      rcases Int.isUnit_iff.mp hu with h | h
      · have : ¬ f 4 < 0 := fun h' => by have := hsg.mpr h'; omega
        rw [if_neg this] at hc
        exact (hc.mul_right X).trans (h ▸ hs.dx)
      · have : f 4 < 0 := hsg.mp (by omega)
        rw [if_pos this] at hc
        have := (hc.mul_right X).trans (show -val5 d * X ≡ -val5 f [ZMOD val5 m] by
          rw [neg_mul]; exact hs.dx.neg)
        rwa [h, neg_neg] at this
    · -- One pass, then the loop again.
      simp only [hz, decide_false, Bool.not_false, if_true, checkIndex, idx_lits, lt5, pure_bind,
        vec5, vget5, downcast_i64_u64_I]
      obtain ⟨eta', U, V, Q, R, hds, he', ht⟩ :=
        divsteps_spec eta hs.eta (Limb.ofInt (f 0)) (Limb.ofInt (g 0)) (odd_limb0 hs.cf hs.fodd)
      have hU : |U| ≤ 2 ^ 62 := by linarith [ht.row1, abs_nonneg V]
      have hV : |V| ≤ 2 ^ 62 := by linarith [ht.row1, abs_nonneg U]
      have hQ : |Q| ≤ 2 ^ 62 := by linarith [ht.row2, abs_nonneg R]
      have hR : |R| ≤ 2 ^ 62 := by linarith [ht.row2, abs_nonneg Q]
      rw [hds]
      simp only [pure_bind, update_de_eq inv ht.row1 ht.row2 hs.ld hs.le hm.lim td te hm.top,
        update_fg_eq hU hV hQ hR hs.lf hs.lg tf tg]
      exact ih _ _ _ _ _ _ _ _ _ _ _
        ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hs.step hm ht he'⟩ env w

theorem replicate_zero : Vector.replicate 5 (UInt256.ofNat 0) = vec5 (fun _ => 0) := rfl

theorem e_init : (vec5 fun _ => 0).set! 0 (UInt256.ofNat 1) =
    vec5 (fun i => if i = 0 then 1 else 0) := rfl

theorem wrap_neg_one : IntTy.wrap (.i 256) (-1) = I (-1) := by
  rw [wrap_i 256 (by decide)]; rfl

/-- `invert` on canonical `x ∈ [0, m)`: every run diverges or returns `x⁻¹ mod m`, which is `0`
for `x = 0`, on canonical limbs, the world unchanged. -/
theorem invert_5_spec {m : ℕ → ℤ} {inv : Limb} (hm : ModSpec m inv) (hm1 : 1 < val5 m)
    {x : ℕ → ℤ} (hx : Canon x) (hxl : Lim x) (hX0 : 0 ≤ val5 x) (hX1 : val5 x < val5 m)
    (hcop : val5 x ≠ 0 → IsCoprime (val5 m) (val5 x)) (env : Env) (w : World) :
    (invert_5 (vec5 x) (vec5 m) inv.w).exec env w = none ∨
      ∃ out, (invert_5 (vec5 x) (vec5 m) inv.w).exec env w = some (.ok (vec5 out, w)) ∧
        Canon out ∧ 0 ≤ val5 out ∧ val5 out < val5 m ∧
        (if val5 x = 0 then val5 out = 0 else val5 out * val5 x ≡ 1 [ZMOD val5 m]) := by
  simp only [invert_5, checkIndex, idx_lits, lt5, if_true, pure_bind, wrap_neg_one]
  rw [replicate_zero, e_init]
  by_cases hz : val5 x = 0
  · -- `x = 0`: the loop exits at once with `d = 0`.
    simp only [hz, if_true]
    have hz' := (val5_eq_zero_iff hx).mp hz
    rw [invert_5.b1.eq_1, is_zero_5_eq x (R64_of_lim hxl)]
    simp only [hz', and_self, decide_true, Bool.not_true,
      Bool.false_eq_true, if_false, checkIndex, idx_lits, lt5, if_true, pure_bind, vec5, vget5]
    have hd0 : Canon (fun _ => (0 : ℤ)) := fun _ _ => ⟨le_rfl, by norm_num⟩
    have hv0 : val5 (fun _ => (0 : ℤ)) = 0 := by simp [val5]
    obtain ⟨out, hout, hco, h0, h1, hc⟩ := normalize_spec (fun _ => 0) m (m 4) hd0 hm.canon
      (R64_of_lim hm.lim 4) hm.pos hm.lt (by rw [hv0]; linarith [hm.pos]) (by rw [hv0]; exact hm.pos)
    simp only [vec5] at hout
    rw [hout]
    refine Or.inr ⟨out, rfl, hco, h0, h1, ?_⟩
    rw [hv0] at hc
    have hc' : val5 out ≡ 0 [ZMOD val5 m] := by split at hc <;> simpa using hc
    unfold Int.ModEq at hc'
    rw [Int.emod_eq_of_lt h0 h1, Int.zero_emod] at hc'
    exact hc'
  · simp only [hz, if_false]
    have hd : val5 (fun _ => (0 : ℤ)) = 0 := by simp [val5]
    have he : val5 (fun i => if i = 0 then (1 : ℤ) else 0) = 1 := by simp [val5]
    have hinv : InvState (val5 m) (val5 x) (fun _ => 0) (fun i => if i = 0 then 1 else 0) m x (-1) := by
      have hM := hm.pos
      refine ⟨fun _ _ => ⟨le_rfl, by norm_num⟩, fun i hi => ?_, hm.canon, hx, fun _ => by norm_num,
        fun i => by split <;> norm_num, hm.lim, hxl, by decide, hm.odd, by rw [abs_of_pos hM],
        by rw [abs_of_nonneg hX0]; exact hX1.le, ?_, ?_, ?_, ?_, hcop hz⟩
      · split <;> norm_num
      · rw [hd]; constructor <;> linarith
      · rw [he]; constructor <;> linarith
      · rw [hd, zero_mul]; exact (Int.emod_self).symm
      · rw [he, one_mul]
    rcases invert_loop hm (val5 x) default _ _ _ _ _ default default default default default default
      ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hinv⟩ env w with h | ⟨out, h, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨out, h, h1, h2, h3, h4⟩

end FeProofs.Precompiles
