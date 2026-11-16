import FeProofs.Precompiles.Inverse.UpdateFG

/-!
# Precompiles: `update_de`

`update_de` computes `t [d, e] / 2 ^ 62` modulo `m`: to each row's combination it adds the
multiple `md` of `m` that makes it divisible by `2 ^ 62`, where `md` starts from the entries of
the row whose operand is negative and subtracts a correction from `INV62 = m⁻¹ mod 2 ^ 62`.
`update_de_eq` is the exported function on limbs, with no wrapping; `deOut_value` what the limbs
out denote, and `de_range` that `d, e ∈ (-2m, m)` is kept.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

/-! ## Signs and masks -/

theorem I_toNat_lt (x : ℤ) : (I x).toNat < 2 ^ 256 := (I x).val.isLt

theorem I_land_neg_one (x : ℤ) : I x &&& I (-1) = I x := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, show (I (-1)).toNat = 2 ^ 256 - 1 by rw [I_toNat]; rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (I_toNat_lt x)]

theorem I_land_zero (x : ℤ) : I x &&& I 0 = I 0 := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, show (I 0).toNat = 0 from rfl, Nat.and_zero]

theorem I_land_sign (x : ℤ) (c : Prop) [Decidable c] :
    I x &&& I (if c then -1 else 0) = I (if c then x else 0) := by
  split
  · exact I_land_neg_one x
  · exact I_land_zero x

/-- The sign of an `i64`, as `>> 63` spreads it. -/
theorem shr63 {x : ℤ} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    IntTy.shr (.i 64) (I x) (UInt256.ofNat 63) = I (if x < 0 then -1 else 0) := by
  rw [shr_i 64 (by decide) (by linarith) (by linarith) (by decide)]
  apply congrArg I
  split
  · rw [show x / 2 ^ 63 = -1 by omega]
    rfl
  · rw [show x / 2 ^ 63 = 0 by omega]
    rfl

theorem bmod64_of_abs {x : ℤ} (h : |x| ≤ 2 ^ 62) : x.bmod (2 ^ 64) = x := by
  rw [abs_le] at h
  apply Int.bmod_eq_of_le <;> norm_num <;> linarith

theorem addW64 {x y : ℤ} (hx : |x| ≤ 2 ^ 62) (hy : |y| ≤ 2 ^ 62) (h : |x + y| ≤ 2 ^ 62) :
    IntTy.addW (.i 64) (I x) (I y) = I (x + y) := by
  rw [addW_i 64 (by decide) (range_of_abs (abs_le126 hx)).1 (range_of_abs (abs_le126 hx)).2
    (range_of_abs (abs_le126 hy)).1 (range_of_abs (abs_le126 hy)).2, bmod64_of_abs h]

theorem subW64 {x y : ℤ} (hx : |x| ≤ 2 ^ 62) (hy : 0 ≤ y) (hy2 : y < 2 ^ 62) :
    IntTy.subW (.i 64) (I x) (I y) = I (x - y) := by
  rw [abs_le] at hx
  rw [subW_i 64 (by decide) (by linarith) (by linarith) (by linarith) (by linarith)]
  apply congrArg I
  apply Int.bmod_eq_of_le <;> norm_num <;> linarith

theorem downcast_i128_u64_I (x : ℤ) :
    downcast_truncate_i128_u64 (I x) = pure (Limb.ofInt x).w := by
  rw [downcast_truncate_i128_u64_eq]
  congr 1
  apply word_eq_of_toNat
  rw [Limb.toNat_w, toNat_lit (by omega), I_toNat]
  simp only [Limb.ofInt]
  have h1 := Int.emod_nonneg x (show (2 : ℤ) ^ 256 ≠ 0 by norm_num)
  have h2 := Int.emod_emod_of_dvd x (show (2 : ℤ) ^ 64 ∣ 2 ^ 256 by norm_num)
  omega

theorem Limb.ofInt_val (x : ℤ) : ((Limb.ofInt x).val : ℤ) = x % 2 ^ 64 := by
  simp only [Limb.ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg x (by norm_num))

/-- The correction `(inv62 · cd + md) mod 2 ^ 62`, as `update_de` computes it on `u64`. -/
def corr (inv : Limb) (cd md : ℤ) : ℤ :=
  ((inv * Limb.ofInt cd + Limb.ofInt md &&& (4611686018427387903 : Limb)).val : ℤ)

theorem corr_spec (inv : Limb) (cd md : ℤ) :
    0 ≤ corr inv cd md ∧ corr inv cd md < 2 ^ 62 ∧
      corr inv cd md ≡ inv.val * cd + md [ZMOD 2 ^ 62] := by
  unfold corr
  rw [Limb.val_land, show ((4611686018427387903 : Limb)).val = 2 ^ 62 - 1 from rfl,
    land_low]
  refine ⟨by positivity, by
    have := Nat.mod_lt (inv * Limb.ofInt cd + Limb.ofInt md).val (show 0 < 2 ^ 62 by norm_num)
    exact_mod_cast this, ?_⟩
  push_cast
  refine (Int.mod_modEq _ _).trans (modEq_two_pow_of_le (c := 62) (d := 64) ((val_add _ _).trans
    ((val_mul _ _).add (Int.ModEq.refl _))) (by norm_num) |>.trans ?_)
  rw [Limb.ofInt_val, Limb.ofInt_val]
  exact (modEq_two_pow_of_le (c := 62) (d := 64) ((Int.mod_modEq _ _).mul_left _) (by norm_num)).add
    (modEq_two_pow_of_le (c := 62) (d := 64) (Int.mod_modEq _ _) (by norm_num))

theorem sgn_corr (inv : Limb) (cd md : ℤ) :
    (inv * Limb.ofInt cd + Limb.ofInt md &&& (4611686018427387903 : Limb)).sgn = corr inv cd md := by
  obtain ⟨h1, h2, -⟩ := corr_spec inv cd md
  exact sgn_eq (Int.ModEq.refl _) (by unfold corr at h1 ⊢; linarith) (by unfold corr at h2 ⊢; linarith)

/-! ## One row -/

/-- The carries of one row of `update_de`, with `k` the multiple of `m` added. -/
def deC (U V k : ℤ) (a b m : ℕ → ℤ) : ℕ → ℤ
  | 0 => lc U V (a 0) (b 0) + m 0 * k
  | j + 1 => deC U V k a b m j / 2 ^ 62 + (lc U V (a (j + 1)) (b (j + 1)) + m (j + 1) * k)

/-- The limbs `update_de` returns for one row. -/
def deOut (U V k : ℤ) (a b m : ℕ → ℤ) : ℕ → ℤ
  | 0 => deC U V k a b m 1 % 2 ^ 62
  | 1 => deC U V k a b m 2 % 2 ^ 62
  | 2 => deC U V k a b m 3 % 2 ^ 62
  | 3 => deC U V k a b m 4 % 2 ^ 62
  | _ => deC U V k a b m 4 / 2 ^ 62

theorem abs_lc_row {U V x y : ℤ} (hUV : |U| + |V| ≤ 2 ^ 62) (hx : |x| ≤ 2 ^ 62)
    (hy : |y| ≤ 2 ^ 62) : |U * x| ≤ 2 ^ 124 ∧ |V * y| ≤ 2 ^ 124 ∧ |lc U V x y| ≤ 2 ^ 124 := by
  have h1 : |U| * |x| ≤ |U| * 2 ^ 62 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h2 : |V| * |y| ≤ |V| * 2 ^ 62 := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have := abs_nonneg U; have := abs_nonneg V
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]; nlinarith
  · rw [abs_mul]; nlinarith
  · unfold lc
    have := abs_add_le (U * x) (V * y)
    rw [abs_mul, abs_mul] at this
    nlinarith

theorem abs_mk {x k : ℤ} (hx : |x| ≤ 2 ^ 62) (hk : |k| ≤ 2 ^ 63) : |x * k| ≤ 2 ^ 125 := by
  rw [abs_mul]
  calc |x| * |k| ≤ 2 ^ 62 * 2 ^ 63 := mul_le_mul hx hk (abs_nonneg _) (by positivity)
    _ = 2 ^ 125 := by norm_num

section
variable {U V k : ℤ} {a b m : ℕ → ℤ} (hUV : |U| + |V| ≤ 2 ^ 62) (hk : |k| ≤ 2 ^ 63)
  (ha : ∀ i, |a i| ≤ 2 ^ 62) (hb : ∀ i, |b i| ≤ 2 ^ 62) (hm : ∀ i, |m i| ≤ 2 ^ 62)
include hUV hk ha hb hm

theorem abs_deC : ∀ j, |deC U V k a b m j| ≤ 2 ^ 126
  | 0 => by
    have := (abs_lc_row hUV (ha 0) (hb 0)).2.2
    have := abs_mk (hm 0) hk
    exact (abs_add_le _ _).trans (by linarith)
  | j + 1 => by
    have := abs_div62 (abs_deC j)
    have := (abs_lc_row hUV (ha (j + 1)) (hb (j + 1))).2.2
    have := abs_mk (hm (j + 1)) hk
    have h1 := abs_add_le (deC U V k a b m j / 2 ^ 62) (lc U V (a (j + 1)) (b (j + 1)) + m (j + 1) * k)
    have h2 := abs_add_le (lc U V (a (j + 1)) (b (j + 1))) (m (j + 1) * k)
    show |deC U V k a b m j / 2 ^ 62 + (lc U V (a (j + 1)) (b (j + 1)) + m (j + 1) * k)| ≤ _
    linarith

omit hk ha hb hm in
theorem lc_row_words (x y : ℤ) (hx : |x| ≤ 2 ^ 62) (hy : |y| ≤ 2 ^ 62) :
    IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I U) (I x)) (IntTy.mulW (.i 128) (I V) (I y)) =
      I (lc U V x y) := by
  obtain ⟨h1, h2, h3⟩ := abs_lc_row hUV hx hy
  have hU : |U| ≤ 2 ^ 62 := by linarith [abs_nonneg V]
  have hV : |V| ≤ 2 ^ 62 := by linarith [abs_nonneg U]
  rw [mulW128 (abs_le126 hU) (abs_le126 hx) (h1.trans (by norm_num)),
    mulW128 (abs_le126 hV) (abs_le126 hy) (h2.trans (by norm_num)),
    addW128 (h1.trans (by norm_num)) (h2.trans (by norm_num)) (h3.trans (by norm_num))]

theorem de_first :
    IntTy.addW (.i 128) (I (lc U V (a 0) (b 0))) (IntTy.mulW (.i 128) (I (m 0)) (I k)) =
      I (deC U V k a b m 0) := by
  have h1 := (abs_lc_row hUV (ha 0) (hb 0)).2.2
  have h2 := abs_mk (hm 0) hk
  rw [mulW128 (abs_le126 (hm 0)) (hk.trans (by norm_num)) (h2.trans (by norm_num)),
    addW128 (h1.trans (by norm_num)) (h2.trans (by norm_num)) (abs_deC hUV hk ha hb hm 0)]
  rfl

theorem de_step (j : ℕ) :
    IntTy.addW (.i 128) (IntTy.shr (.i 128) (I (deC U V k a b m j)) (UInt256.ofNat 62))
        (IntTy.addW (.i 128)
          (IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I U) (I (a (j + 1))))
            (IntTy.mulW (.i 128) (I V) (I (b (j + 1)))))
          (IntTy.mulW (.i 128) (I (m (j + 1))) (I k))) =
      I (deC U V k a b m (j + 1)) := by
  have hC := abs_deC hUV hk ha hb hm j
  have hD := abs_div62 hC
  have h1 := (abs_lc_row hUV (ha (j + 1)) (hb (j + 1))).2.2
  have h2 := abs_mk (hm (j + 1)) hk
  have h3 : |lc U V (a (j + 1)) (b (j + 1)) + m (j + 1) * k| ≤ 2 ^ 126 :=
    (abs_add_le _ _).trans (by linarith)
  rw [shr128 hC, lc_row_words hUV _ _ (ha (j + 1)) (hb (j + 1)),
    mulW128 (abs_le126 (hm (j + 1))) (hk.trans (by norm_num)) (h2.trans (by norm_num)),
    addW128 (h1.trans (by norm_num)) (h2.trans (by norm_num)) h3,
    addW128 (hD.trans (by norm_num)) h3 (abs_deC hUV hk ha hb hm (j + 1))]
  rfl

theorem de_last : IntTy.shr (.i 128) (I (deC U V k a b m 4)) (UInt256.ofNat 62) =
    I (deC U V k a b m 4 / 2 ^ 62) := shr128 (abs_deC hUV hk ha hb hm 4)

theorem de_top (ha4 : |a 4| ≤ 2 ^ 20) (hb4 : |b 4| ≤ 2 ^ 20) (hm4 : |m 4| ≤ 2 ^ 8) :
    |deC U V k a b m 4 / 2 ^ 62| ≤ 2 ^ 62 := by
  have hD := abs_div62 (abs_deC hUV hk ha hb hm 3)
  have h1 : |lc U V (a 4) (b 4)| ≤ 2 ^ 82 := by
    unfold lc
    have := abs_add_le (U * a 4) (V * b 4)
    rw [abs_mul, abs_mul] at this
    have := mul_le_mul_of_nonneg_left ha4 (abs_nonneg U)
    have := mul_le_mul_of_nonneg_left hb4 (abs_nonneg V)
    nlinarith [abs_nonneg U, abs_nonneg V]
  have h2 : |m 4 * k| ≤ 2 ^ 71 := by
    rw [abs_mul]
    calc |m 4| * |k| ≤ 2 ^ 8 * 2 ^ 63 := mul_le_mul hm4 hk (abs_nonneg _) (by positivity)
      _ = 2 ^ 71 := by norm_num
  have hC : |deC U V k a b m 4| ≤ 2 ^ 84 := by
    rw [show deC U V k a b m 4 = deC U V k a b m 3 / 2 ^ 62 + (lc U V (a 4) (b 4) + m 4 * k)
      from deC.eq_2 _ _ _ _ _ _ 3]
    have := abs_add_le (deC U V k a b m 3 / 2 ^ 62) (lc U V (a 4) (b 4) + m 4 * k)
    have := abs_add_le (lc U V (a 4) (b 4)) (m 4 * k)
    linarith
  rw [abs_le] at hC ⊢
  constructor
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) hC.1
    have e : (-2 ^ 84 : ℤ) / 2 ^ 62 = -2 ^ 22 := by norm_num
    linarith
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) hC.2
    have e : (2 ^ 84 : ℤ) / 2 ^ 62 = 2 ^ 22 := by norm_num
    linarith

end

theorem M62_eq : M62 = pure (Limb.w 4611686018427387903) := rfl

/-- The multiple of `m` a row starts from: its entries whose operand is negative. -/
def sel (U V : ℤ) (a b : ℕ → ℤ) : ℤ := (if a 4 < 0 then U else 0) + (if b 4 < 0 then V else 0)

/-- The multiple of `m` a row adds. -/
def kOf (inv : Limb) (U V : ℤ) (a b : ℕ → ℤ) : ℤ :=
  sel U V a b - corr inv (lc U V (a 0) (b 0)) (sel U V a b)

theorem abs_sel {U V : ℤ} (hUV : |U| + |V| ≤ 2 ^ 62) (a b : ℕ → ℤ) : |sel U V a b| ≤ 2 ^ 62 := by
  unfold sel
  have := abs_nonneg U; have := abs_nonneg V
  split_ifs <;> simp <;> first | linarith | (have := abs_add_le U V; linarith)

theorem abs_kOf {U V : ℤ} (hUV : |U| + |V| ≤ 2 ^ 62) (inv : Limb) (a b : ℕ → ℤ) :
    |kOf inv U V a b| ≤ 2 ^ 63 := by
  have h1 := abs_sel hUV a b
  obtain ⟨h2, h3, -⟩ := corr_spec inv (lc U V (a 0) (b 0)) (sel U V a b)
  unfold kOf
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

/-- `update_de` on limbs below `2 ^ 62` (the top ones below `2 ^ 20`), a modulus with limbs
below `2 ^ 62` (the top one below `2 ^ 8`), and rows with `|u| + |v| ≤ 2 ^ 62`. -/
theorem update_de_eq {U V Q R : ℤ} {a b m : ℕ → ℤ} (inv : Limb)
    (hUV : |U| + |V| ≤ 2 ^ 62) (hQR : |Q| + |R| ≤ 2 ^ 62) (ha : ∀ i, |a i| ≤ 2 ^ 62)
    (hb : ∀ i, |b i| ≤ 2 ^ 62) (hm : ∀ i, |m i| ≤ 2 ^ 62) (ha4 : |a 4| ≤ 2 ^ 20)
    (hb4 : |b 4| ≤ 2 ^ 20) (hm4 : |m 4| ≤ 2 ^ 8) :
    update_de_5 #v[I (a 0), I (a 1), I (a 2), I (a 3), I (a 4)]
        #v[I (b 0), I (b 1), I (b 2), I (b 3), I (b 4)] ⟨I U, I V, I Q, I R⟩
        #v[I (m 0), I (m 1), I (m 2), I (m 3), I (m 4)] inv.w =
      pure (#v[I (deOut U V (kOf inv U V a b) a b m 0), I (deOut U V (kOf inv U V a b) a b m 1),
          I (deOut U V (kOf inv U V a b) a b m 2), I (deOut U V (kOf inv U V a b) a b m 3),
          I (deOut U V (kOf inv U V a b) a b m 4)],
        #v[I (deOut Q R (kOf inv Q R a b) a b m 0), I (deOut Q R (kOf inv Q R a b) a b m 1),
          I (deOut Q R (kOf inv Q R a b) a b m 2), I (deOut Q R (kOf inv Q R a b) a b m 3),
          I (deOut Q R (kOf inv Q R a b) a b m 4)]) := by
  have hU : |U| ≤ 2 ^ 62 := by linarith [abs_nonneg V]
  have hV : |V| ≤ 2 ^ 62 := by linarith [abs_nonneg U]
  have hQ : |Q| ≤ 2 ^ 62 := by linarith [abs_nonneg R]
  have hR : |R| ≤ 2 ^ 62 := by linarith [abs_nonneg Q]
  have ra4 := abs_le.mp ((ha 4).trans (show (2 : ℤ) ^ 62 ≤ 2 ^ 62 by norm_num))
  have rb4 := abs_le.mp ((hb 4).trans (show (2 : ℤ) ^ 62 ≤ 2 ^ 62 by norm_num))
  have sa := shr63 (x := a 4) (by linarith [ra4.1]) (by linarith [ra4.2])
  have sb := shr63 (x := b 4) (by linarith [rb4.1]) (by linarith [rb4.2])
  have hkd := abs_kOf hUV inv a b
  have hke := abs_kOf hQR inv a b
  have hsd := abs_sel hUV a b
  have hse := abs_sel hQR a b
  have md : IntTy.addW (.i 64) (I (if a 4 < 0 then U else 0)) (I (if b 4 < 0 then V else 0)) =
      I (sel U V a b) :=
    addW64 (by split; exact hU; simp) (by split; exact hV; simp) hsd
  have me : IntTy.addW (.i 64) (I (if a 4 < 0 then Q else 0)) (I (if b 4 < 0 then R else 0)) =
      I (sel Q R a b) :=
    addW64 (by split; exact hQ; simp) (by split; exact hR; simp) hse
  obtain ⟨c1, c2, -⟩ := corr_spec inv (lc U V (a 0) (b 0)) (sel U V a b)
  obtain ⟨c3, c4, -⟩ := corr_spec inv (lc Q R (a 0) (b 0)) (sel Q R a b)
  have kd : IntTy.subW (.i 64) (I (sel U V a b)) (I (corr inv (lc U V (a 0) (b 0)) (sel U V a b))) =
      I (kOf inv U V a b) := subW64 hsd c1 c2
  have ke : IntTy.subW (.i 64) (I (sel Q R a b)) (I (corr inv (lc Q R (a 0) (b 0)) (sel Q R a b))) =
      I (kOf inv Q R a b) := subW64 hse c3 c4
  have z1 := de_first hUV hkd ha hb hm
  have z2 := de_first hQR hke ha hb hm
  have l1 := lc_row_words hUV _ _ (ha 0) (hb 0)
  have l2 := lc_row_words hQR _ _ (ha 0) (hb 0)
  simp only [update_de_5, update_de_5_k1, update_de_5_k2, update_de_5_k3, update_de_5_k4,
    update_de_5_k5, update_de_5_k6, pure_bind, vget5, checkIndex, idx_lits, lt5, if_true,
    sa, sb, I_land_sign, md, me, l1, l2,
    downcast_i128_u64_I, downcast_i64_u64_I, M62_eq, mulW_w, addW_w, land_w,
    downcast_u64_i64_w, sgn_corr, kd, ke, z1, z2]
  iterate 5
    rw [update_de_5_k6.loop.eq_1]
    simp only [idx_lits, vget5, lt5, checkIndex, de_step hUV hkd ha hb hm, de_step hQR hke ha hb hm,
      downcast_truncate_i128_i64_eq, low62, pure_bind, M62_SIGNED_eq, decide_true, decide_false,
      if_true, if_false, Bool.false_eq_true, de_last hUV hkd ha hb hm, de_last hQR hke ha hb hm,
      top64 (de_top hUV hkd ha hb hm ha4 hb4 hm4), top64 (de_top hQR hke ha hb hm ha4 hb4 hm4)]
  rfl

/-- When the row's low combination is a multiple of `2 ^ 62`, the limbs out denote the row
times `(d, e)` plus `k m`, divided by `2 ^ 62`. -/
theorem deOut_value (U V k : ℤ) (a b m : ℕ → ℤ) (h : 2 ^ 62 ∣ deC U V k a b m 0) :
    2 ^ 62 * val5 (deOut U V k a b m) = U * val5 a + V * val5 b + k * val5 m := by
  obtain ⟨q0, hq0⟩ := h
  have e : ∀ j, deC U V k a b m j = 2 ^ 62 * (deC U V k a b m j / 2 ^ 62) + deC U V k a b m j % 2 ^ 62 :=
    fun j => (Int.mul_ediv_add_emod _ _).symm
  have c1 : deC U V k a b m 1 = deC U V k a b m 0 / 2 ^ 62 + (lc U V (a 1) (b 1) + m 1 * k) := rfl
  have c2 : deC U V k a b m 2 = deC U V k a b m 1 / 2 ^ 62 + (lc U V (a 2) (b 2) + m 2 * k) := rfl
  have c3 : deC U V k a b m 3 = deC U V k a b m 2 / 2 ^ 62 + (lc U V (a 3) (b 3) + m 3 * k) := rfl
  have c4 : deC U V k a b m 4 = deC U V k a b m 3 / 2 ^ 62 + (lc U V (a 4) (b 4) + m 4 * k) := rfl
  have c0 : deC U V k a b m 0 = lc U V (a 0) (b 0) + m 0 * k := rfl
  have hd0 : deC U V k a b m 0 / 2 ^ 62 = q0 := by rw [hq0]; simp
  simp only [val5, deOut, lc] at *
  rw [hd0] at c1
  linear_combination -(2 : ℤ) ^ 62 * e 1 - 2 ^ 124 * e 2 - 2 ^ 186 * e 3 - 2 ^ 248 * e 4 +
    2 ^ 62 * c1 + 2 ^ 124 * c2 + 2 ^ 186 * c3 + 2 ^ 248 * c4 - hq0 + c0

/-- The correction makes the low combination a multiple of `2 ^ 62`, for `inv = m⁻¹ mod 2 ^ 62`. -/
theorem deC_dvd (inv : Limb) (U V : ℤ) (a b m : ℕ → ℤ) (hinv : m 0 * inv.val ≡ 1 [ZMOD 2 ^ 62]) :
    2 ^ 62 ∣ deC U V (kOf inv U V a b) a b m 0 := by
  obtain ⟨-, -, hc⟩ := corr_spec inv (lc U V (a 0) (b 0)) (sel U V a b)
  have : deC U V (kOf inv U V a b) a b m 0 ≡ 0 [ZMOD 2 ^ 62] := by
    show lc U V (a 0) (b 0) + m 0 * (sel U V a b - corr inv (lc U V (a 0) (b 0)) (sel U V a b)) ≡ 0
      [ZMOD 2 ^ 62]
    calc lc U V (a 0) (b 0) + m 0 * (sel U V a b - corr inv (lc U V (a 0) (b 0)) (sel U V a b))
        ≡ lc U V (a 0) (b 0) + m 0 * (sel U V a b - (inv.val * lc U V (a 0) (b 0) + sel U V a b))
          [ZMOD 2 ^ 62] := ((hc.sub_left _).mul_left _).add_left _
      _ = lc U V (a 0) (b 0) * (1 - m 0 * inv.val) := by ring
      _ ≡ lc U V (a 0) (b 0) * (1 - 1) [ZMOD 2 ^ 62] := (hinv.sub_left 1).mul_left _
      _ = 0 := by ring
  exact Int.modEq_zero_iff_dvd.mp this

/-- With canonical low limbs, the sign of the value is the sign of the top limb. -/
theorem val5_neg_iff {a : ℕ → ℤ} (ha : ∀ i < 4, 0 ≤ a i ∧ a i < 2 ^ 62) : val5 a < 0 ↔ a 4 < 0 := by
  have h0 := ha 0 (by decide); have h1 := ha 1 (by decide)
  have h2 := ha 2 (by decide); have h3 := ha 3 (by decide)
  unfold val5
  constructor
  · intro h; by_contra h'; have : 0 ≤ a 4 := by omega
    nlinarith
  · intro h
    have : a 4 ≤ -1 := by omega
    nlinarith

/-- `update_de` keeps `(-2m, m)`. -/
theorem de_range {U V D E M k t D' : ℤ} (hUV : |U| + |V| ≤ 2 ^ 62) (hM : 0 < M)
    (hD : -2 * M < D ∧ D < M) (hE : -2 * M < E ∧ E < M)
    (hk : k = (if D < 0 then U else 0) + (if E < 0 then V else 0) - t) (ht : 0 ≤ t ∧ t < 2 ^ 62)
    (h : 2 ^ 62 * D' = U * D + V * E + k * M) : -2 * M < D' ∧ D' < M := by
  set D1 := D + (if D < 0 then M else 0)
  set E1 := E + (if E < 0 then M else 0)
  have hD1 : |D1| ≤ M - 1 := by
    simp only [D1]; rw [abs_le]; split_ifs <;> constructor <;> linarith
  have hE1 : |E1| ≤ M - 1 := by
    simp only [E1]; rw [abs_le]; split_ifs <;> constructor <;> linarith
  have hX : 2 ^ 62 * D' = U * D1 + V * E1 - t * M := by
    rw [h, hk]; simp only [D1, E1]; split_ifs <;> ring
  have hb : |U * D1 + V * E1| ≤ 2 ^ 62 * (M - 1) := by
    have := abs_add_le (U * D1) (V * E1)
    rw [abs_mul, abs_mul] at this
    have := mul_le_mul_of_nonneg_left hD1 (abs_nonneg U)
    have := mul_le_mul_of_nonneg_left hE1 (abs_nonneg V)
    nlinarith [abs_nonneg U, abs_nonneg V]
  rw [abs_le] at hb
  constructor <;> nlinarith

end FeProofs.Precompiles
