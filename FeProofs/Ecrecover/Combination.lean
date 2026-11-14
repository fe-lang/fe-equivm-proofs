import FeProofs.Ecrecover.Table

/-!
# Ecrecover: `combination`

`combination u v q` computes `u • G + v • Q` by two-bit windows over a table of
`[i] G + [j] Q`, made affine with one inversion.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Ecrecover

open Exported

theorem usize_eq (x : UInt256) : downcast_truncate_u256_usize x = pure x := by
  simp only [Lib.downcast_truncate_u256_usize, Lib.u256_to_word, Lib.usize_IS_SIGNED, Lib.usize_MASK,
    Lib.usize_from_word, pure_bind, Bool.false_eq_true, if_false]
  congr 1
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, show (~~~UInt256.ofNat 0).toNat = 2 ^ 256 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.val.isLt

/-- A table entry for the bit loop: its point is `A`, and when `A ≠ 0` it is affine. -/
def TabOK (P : Point_Mont_Base) (A : W.toAffine.Point) : Prop :=
  (∃ z, GoodP P A z) ∧ (A ≠ 0 → ∃ a b x y, P = ⟨toB a, toB b, toB (Mont.new KB 1)⟩ ∧ RepB a x ∧
    RepB b y ∧ W.Nonsingular ![x, y, 1] ∧ Point.toAffine W ![x, y, 1] = A)

theorem sub_two_u64 {m : ℕ} (hm : 2 * (m + 1) < 2 ^ 64) :
    IntTy.sub (.u 64) (UInt256.ofNat (2 * (m + 1))) (UInt256.ofNat 2) = pure (UInt256.ofNat (2 * m)) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show 2 * (m + 1) < 2 ^ 256 by omega), toNat_lit (show 2 < 2 ^ 256 by decide)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

/-- The window of bits `2m, 2m + 1` of `U` and of `V`, as the table index `4 i + j`. -/
theorem entry_eq (U V : UInt256) {m : ℕ} (hm : 2 * m < 256) :
    (U >>> UInt256.ofNat (2 * m) &&& UInt256.ofNat 3) <<< UInt256.ofNat 2 |||
        V >>> UInt256.ofNat (2 * m) &&& UInt256.ofNat 3 =
      UInt256.ofNat (4 * (U.toNat / 4 ^ m % 4) + V.toNat / 4 ^ m % 4) := by
  have p4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  apply word_eq_of_toNat
  have h3 : ∀ x : UInt256, (x >>> UInt256.ofNat (2 * m) &&& UInt256.ofNat 3).toNat = x.toNat / 4 ^ m % 4 := by
    intro x
    change (UInt256.land _ _).toNat = _
    rw [uland_toNat, shiftRight_toNat _ hm, toNat_lit (by decide),
      show (3 : ℕ) = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, p4]
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, shiftLeft_toNat _ (by decide) (by rw [h3]; omega), h3, h3,
    toNat_lit (by omega)]
  rw [← Nat.two_pow_add_eq_or_of_lt (show V.toNat / 4 ^ m % 4 < 2 ^ 2 by omega)]

theorem window_split (c m : ℕ) : c / 4 ^ m = 4 * (c / 4 ^ (m + 1)) + c / 4 ^ m % 4 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- The bit loop: from `S = (U / 4 ^ m) • G + (V / 4 ^ m) • Q` with `m` windows to go, the
loop returns `U • G + V • Q`. -/
theorem bit_loop (U V : UInt256) (t : ℕ → Point_Mont_Base) (G Q : W.toAffine.Point)
    (htab : ∀ k < 16, TabOK (t k) ((k / 4) • G + (k % 4) • Q)) :
    ∀ m ≤ 128, ∀ (cur : Point_Mont_Base) (zc : Fp),
      GoodP cur ((U.toNat / 4 ^ m) • G + (V.toNat / 4 ^ m) • Q) zc →
      ∀ r0 r2 r3 r4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
        r27 r28 r29 r30 r31 r32 r33 r34 r35 r36,
      ∃ P' z', combination_k2.b1.b9.b16.b22 U V r0 (tbl t) r2 r3 r4 r5 r6 r7 cur (UInt256.ofNat (2 * m))
          r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32
          r33 r34 r35 r36 = pure P' ∧ GoodP P' (U.toNat • G + V.toNat • Q) z'
  | 0, _, cur, zc, hc, r0, r2, r3, r4, r5, r6, r7, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
      r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.b1.b9.b16.b22.eq_1]
    simp only [Nat.mul_zero, toNat_lit (show 0 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, if_false]
    exact ⟨cur, zc, rfl, by simpa using hc⟩
  | m + 1, hm, cur, zc, hc, r0, r2, r3, r4, r5, r6, r7, r10, r11, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.b1.b9.b16.b22.eq_1]
    obtain ⟨P1, z1, e1, h1⟩ := hc.double
    obtain ⟨P2, z2, e2, h2⟩ := h1.double
    simp only [toNat_lit (show 0 < 2 ^ 256 by decide), toNat_lit (show 2 * (m + 1) < 2 ^ 256 by omega),
      show 0 < 2 * (m + 1) by omega, decide_true, if_true, sub_two_u64 (show 2 * (m + 1) < 2 ^ 64 by omega),
      pure_bind, e1, e2, usize_eq, entry_eq U V (show 2 * m < 256 by omega)]
    have hU := window_split U.toNat m
    have hV := window_split V.toNat m
    set a := U.toNat / 4 ^ m % 4
    set b := V.toNat / 4 ^ m % 4
    have ha : a < 4 := Nat.mod_lt _ (by decide)
    have hb : b < 4 := Nat.mod_lt _ (by decide)
    have hk : 4 * a + b < 16 := by omega
    have hA : ((4 * a + b) / 4) • G + ((4 * a + b) % 4) • Q = a • G + b • Q := by
      rw [show (4 * a + b) / 4 = a by omega, show (4 * a + b) % 4 = b by omega]
    have hsum : (U.toNat / 4 ^ m) • G + (V.toNat / 4 ^ m) • Q =
        ((U.toNat / 4 ^ (m + 1)) • G + (V.toNat / 4 ^ (m + 1)) • Q +
          ((U.toNat / 4 ^ (m + 1)) • G + (V.toNat / 4 ^ (m + 1)) • Q) +
          ((U.toNat / 4 ^ (m + 1)) • G + (V.toNat / 4 ^ (m + 1)) • Q +
          ((U.toNat / 4 ^ (m + 1)) • G + (V.toNat / 4 ^ (m + 1)) • Q))) + (a • G + b • Q) := by
      conv_lhs => rw [hU, hV]
      simp only [add_nsmul, mul_nsmul']
      abel_nf
    obtain ⟨⟨zt, ht⟩, haff⟩ := htab _ hk
    rw [hA] at ht haff
    by_cases he : 4 * a + b = 0
    · have hab : a = 0 ∧ b = 0 := by omega
      simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]

      refine bit_loop U V t G Q htab m (by omega) P2 z2 ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _
      rw [hsum, hab.1, hab.2, zero_nsmul, zero_nsmul, _root_.add_zero, _root_.add_zero]; exact h2
    · have hne : (UInt256.ofNat (4 * a + b) = UInt256.ofNat 0) = False := by
        apply propext; constructor
        · intro h
          have := congrArg UInt256.toNat h
          rw [toNat_lit (show 4 * a + b < 2 ^ 256 by omega), toNat_lit (by decide)] at this
          exact he this
        · exact False.elim
      simp only [ne_eq, hne, not_false_eq_true, decide_true, if_true, checkIndex,
        toNat_lit (show 4 * a + b < 2 ^ 256 by omega), hk, pure_bind, tbl_get t hk, ht.is_infinity]
      by_cases hA0 : a • G + b • Q = 0
      · simp only [hA0, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        refine bit_loop U V t G Q htab m (by omega) P2 z2 ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _
        rw [hsum, hA0, _root_.add_zero]; exact h2
      · obtain ⟨a', b', x, y, ht', ha', hb', hv', haff'⟩ := haff hA0
        obtain ⟨P3, z3, e3, h3⟩ := h2.add_affine ha' hb' hv'
        simp only [hA0, decide_false, Bool.not_false, if_true, ht', e3, pure_bind]
        refine bit_loop U V t G Q htab m (by omega) P3 z3 ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _
        rw [hsum, ← haff']; exact h3


theorem checkedSub_one {k : ℕ} (hk : k + 2 < 2 ^ 256) :
    checkedSub (UInt256.ofNat (k + 2)) (UInt256.ofNat 1) = pure (UInt256.ofNat (k + 1)) := by
  unfold checkedSub
  rw [toNat_lit hk, toNat_lit (by decide), if_neg (by omega)]
  congr 1
  apply word_eq_of_toNat
  change (UInt256.sub _ _).toNat = _
  rw [usub_toNat (by rw [toNat_lit hk, toNat_lit (by decide)]; omega), toNat_lit hk,
    toNat_lit (by decide), toNat_lit (by omega)]
  omega

/-- The product of the `z` of the finite entries `1 ≤ i < j`. -/
noncomputable def pr (A : ℕ → W.toAffine.Point) (zs : ℕ → Fp) (j : ℕ) : Fp :=
  ∏ i ∈ (Finset.Ico 1 j).filter (fun i => A i ≠ 0), zs i

theorem pr_succ (A : ℕ → W.toAffine.Point) (zs : ℕ → Fp) {j : ℕ} (hj : 1 ≤ j) :
    pr A zs (j + 1) = pr A zs j * (if A j ≠ 0 then zs j else 1) := by
  unfold pr
  rw [Nat.Ico_succ_right_eq_insert_Ico hj, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.prod_insert (by simp), mul_comm]
  · rw [mul_one]

theorem pr_ne_zero {A : ℕ → W.toAffine.Point} {zs : ℕ → Fp} {j : ℕ}
    (hz : ∀ i < j, A i ≠ 0 → zs i ≠ 0) : pr A zs j ≠ 0 := by
  unfold pr
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
  exact hz i (Finset.mem_Ico.mp h1).2 h2

/-- Making a finite entry affine with the inverse of its `z`. -/
theorem norm_entry {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (hP : GoodP P A z)
    (hA : A ≠ 0) {zi : L4} (hzi : RepB zi z⁻¹) :
    ∃ a b c x y, P = ⟨toB a, toB b, toB c⟩ ∧ RepB c z ∧
      Point_affine_Mont_Base (toB (Mont.mul KB a (Mont.mul KB zi zi)))
        (toB (Mont.mul KB b (Mont.mul KB (Mont.mul KB zi zi) zi))) =
          pure ⟨toB (Mont.mul KB a (Mont.mul KB zi zi)), toB (Mont.mul KB b (Mont.mul KB (Mont.mul KB zi zi) zi)),
            toB (Mont.new KB 1)⟩ ∧
      TabOK ⟨toB (Mont.mul KB a (Mont.mul KB zi zi)), toB (Mont.mul KB b (Mont.mul KB (Mont.mul KB zi zi) zi)),
        toB (Mont.new KB 1)⟩ A ∧ RepB a x ∧ RepB b y := by
  obtain ⟨x, y, ⟨a, b, c, rfl, ha, hb, hc⟩, hv, rfl⟩ := hP
  have hz : z ≠ 0 := fun h => hA (toAffine_eq_zero_of_z h)
  obtain ⟨hns, haff⟩ := toAffine_some hv hz
  have hx := RepB.mul ha (RepB.mul hzi hzi)
  have hy := RepB.mul hb (RepB.mul (RepB.mul hzi hzi) hzi)
  have hv1 : W.Nonsingular ![x * (z⁻¹ * z⁻¹), y * (z⁻¹ * z⁻¹ * z⁻¹), 1] :=
    (nonsingular_some _ _).mpr hns
  have he : Point.toAffine W ![x * (z⁻¹ * z⁻¹), y * (z⁻¹ * z⁻¹ * z⁻¹), 1] =
      Point.toAffine W ![x, y, z] := by rw [Point.toAffine_some hv1, haff]
  exact ⟨a, b, c, x, y, rfl, hc, affine_eq _ _, ⟨⟨1, _, _, ⟨_, _, _, rfl, hx, hy, RepB.one⟩, hv1, he⟩,
    fun _ => ⟨_, _, _, _, rfl, hx, hy, hv1, he⟩⟩, ha, hb⟩

theorem tabOK_of_zero {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (h : GoodP P A z)
    (hA : A = 0) : TabOK P A := ⟨⟨z, h⟩, fun h' => absurd hA h'⟩

theorem nsmul_div_big (U : UInt256) (X : W.toAffine.Point) : (U.toNat / 4 ^ 128) • X = 0 := by
  have h : U.toNat < 4 ^ 128 := by
    have := U.val.isLt
    rw [show (4 : ℕ) ^ 128 = UInt256.size by decide]
    exact this
  rw [Nat.div_eq_of_lt h, zero_nsmul]

/-- The normalization loop, with `k + 1` the counter: entries `1 ≤ j ≤ k` still as built,
the others affine, and the running inverse that of the product of the finite `z`s below
`k + 1`. -/
theorem norm_loop (U V : UInt256) (G Q : W.toAffine.Point) (zs : ℕ → Fp)
    (hz : ∀ i < 16, (i / 4) • G + (i % 4) • Q ≠ 0 → zs i ≠ 0) (pf : ℕ → Mont_Base)
    (hpf : ∀ j, 1 ≤ j → j < 16 → ∃ c, pf j = toB c ∧
      RepB c (pr (fun i => (i / 4) • G + (i % 4) • Q) zs j)) :
    ∀ k, k + 1 ≤ 16 → ∀ (t : ℕ → Point_Mont_Base) (r4 : L4),
      TabOK (t 0) ((0 / 4) • G + (0 % 4) • Q) →
      (∀ j, 1 ≤ j → j ≤ k → GoodP (t j) ((j / 4) • G + (j % 4) • Q) (zs j)) →
      (∀ j, k + 1 ≤ j → j < 16 → TabOK (t j) ((j / 4) • G + (j % 4) • Q)) →
      RepB r4 (pr (fun i => (i / 4) • G + (i % 4) • Q) zs (k + 1))⁻¹ →
      ∀ r0 r3 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
        r28 r29 r30 r31 r32 r33 r34 r35 r36,
      ∃ P' z', combination_k2.b1.b9.b16 U V r0 (tbl t) (tbl pf) r3 (toB r4) (UInt256.ofNat (k + 1))
          r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
          r30 r31 r32 r33 r34 r35 r36 = pure P' ∧ GoodP P' (U.toNat • G + V.toNat • Q) z'
  | 0, _, t, r4, h0, _, hhigh, _, r0, r3, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
      r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.b1.b9.b16.eq_1]
    simp only [Nat.zero_add, toNat_lit (show 1 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, if_false, infinity_eq, pure_bind]
    have htab : ∀ k < 16, TabOK (t k) ((k / 4) • G + (k % 4) • Q) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | h
      · exact h0
      · exact hhigh k h hk
    have := bit_loop U V t G Q htab 128 le_rfl _ 0
      (by rw [nsmul_div_big, nsmul_div_big, _root_.add_zero]; exact GoodP.infinity)
      r0 (tbl pf) r3 (toB r4) (UInt256.ofNat 1) r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
      r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36
    simpa using this
  | k + 1, hk, t, r4, h0, hlow, hhigh, hr4, r0, r3, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34,
      r35, r36 => by
    rw [combination_k2.b1.b9.b16.eq_1]
    have hj : k + 1 < 16 := by omega
    have hg := hlow (k + 1) (by omega) le_rfl
    simp only [toNat_lit (show 1 < 2 ^ 256 by decide), toNat_lit (show k + 1 + 1 < 2 ^ 256 by omega),
      show 1 < k + 1 + 1 by omega, decide_true, if_true, checkedSub_one (show k + 2 < 2 ^ 256 by omega),
      pure_bind, checkIndex, toNat_lit (show k + 1 < 2 ^ 256 by omega), hj, tbl_get t hj,
      hg.is_infinity]
    set A := fun i => (i / 4) • G + (i % 4) • Q with hAdef
    have hprs := pr_succ A zs (j := k + 1) (by omega)
    by_cases hA : A (k + 1) = 0
    · simp only [show ((k + 1) / 4) • G + ((k + 1) % 4) • Q = 0 from hA, decide_true, if_true]
      refine norm_loop U V G Q zs hz pf hpf k (by omega) t r4 h0 (fun j h1 h2 => hlow j h1 (by omega))
        (fun j h1 h2 => ?_) ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · exact tabOK_of_zero hg hA
        · exact hhigh j h h2
      · rw [show k + 1 + 1 = (k + 1) + 1 from rfl, hprs] at hr4
        simpa [hA] using hr4
    · simp only [show ¬ (((k + 1) / 4) • G + ((k + 1) % 4) • Q = 0) from hA, decide_false,
        Bool.false_eq_true, if_false]
      obtain ⟨c, hc, hcr⟩ := hpf (k + 1) (by omega) hj
      have hzk : zs (k + 1) ≠ 0 := hz (k + 1) hj hA
      have hpr0 : pr A zs (k + 1) ≠ 0 := pr_ne_zero fun i hi => hz i (by omega)
      have hzi : RepB (Mont.mul KB r4 c) (zs (k + 1))⁻¹ := by
        have := RepB.mul hr4 hcr
        rw [hprs, if_pos hA] at this
        convert this using 1
        field_simp
      obtain ⟨a, b, cz, x, y, ht, hcz, haff, htab, ha, hb⟩ := norm_entry hg hA hzi
      have hr4' : RepB (Mont.mul KB r4 cz) (pr A zs (k + 1))⁻¹ := by
        have := RepB.mul hr4 hcz
        rw [hprs, if_pos hA] at this
        convert this using 1
        field_simp
      rw [tbl_get pf hj, hc, ht]
      simp only [mul_Base, square_Base, pure_bind]
      rw [haff, pure_bind, tbl_set t hj]
      refine norm_loop U V G Q zs hz pf hpf k (by omega) _ _ ?_ (fun j h1 h2 => ?_) (fun j h1 h2 => ?_)
        hr4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      · rw [Function.update_of_ne (by omega)]; exact h0
      · rw [Function.update_of_ne (by omega)]; exact hlow j h1 (by omega)
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · rw [Function.update_self]; exact htab
        · rw [Function.update_of_ne (by omega)]; exact hhigh j h h2

end FeProofs.Ecrecover
