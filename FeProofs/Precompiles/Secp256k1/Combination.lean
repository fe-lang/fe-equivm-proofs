import FeProofs.Precompiles.Secp256k1.Table
import FeProofs.Precompiles.Field.Checked

/-!
# Ecrecover: `combination`

`combination u v q` computes `u • G + v • Q` by two-bit windows over a table of
`[i] G + [j] Q`, made affine with one inversion.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

theorem usize_eq (x : UInt256) : downcast_truncate_u256_usize x = pure x := by
  simp only [Lib.downcast_truncate_u256_usize, Lib.u256_to_word, Lib.usize_IS_SIGNED, Lib.usize_MASK,
    Lib.usize_from_word, pure_bind, Bool.false_eq_true, ite_false]
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
  rw [ite_eq_left (by constructor <;> omega)]
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
      ∃ P' z', combination_k2.loop.loop_2.loop_3.loop_4 U V r0 (tbl t) r2 r3 r4 r5 r6 r7 cur (UInt256.ofNat (2 * m))
          r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32
          r33 r34 r35 r36 = pure P' ∧ GoodP P' (U.toNat • G + V.toNat • Q) z'
  | 0, _, cur, zc, hc, r0, r2, r3, r4, r5, r6, r7, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
      r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.loop.loop_2.loop_3.loop_4.eq_1]
    simp only [Nat.mul_zero, toNat_lit (show 0 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, ite_false]
    exact ⟨cur, zc, rfl, by simpa using hc⟩
  | m + 1, hm, cur, zc, hc, r0, r2, r3, r4, r5, r6, r7, r10, r11, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.loop.loop_2.loop_3.loop_4.eq_1]
    obtain ⟨P1, z1, e1, h1⟩ := hc.double
    obtain ⟨P2, z2, e2, h2⟩ := h1.double
    simp only [toNat_lit (show 0 < 2 ^ 256 by decide), toNat_lit (show 2 * (m + 1) < 2 ^ 256 by omega),
      show 0 < 2 * (m + 1) by omega, decide_true, ite_true, sub_two_u64 (show 2 * (m + 1) < 2 ^ 64 by omega),
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
      simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]

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
      simp only [ne_eq, hne, not_false_eq_true, decide_true, ite_true, checkIndex,
        toNat_lit (show 4 * a + b < 2 ^ 256 by omega), hk, pure_bind, tbl_get t hk, ht.is_infinity]
      by_cases hA0 : a • G + b • Q = 0
      · simp only [hA0, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        refine bit_loop U V t G Q htab m (by omega) P2 z2 ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _
        rw [hsum, hA0, _root_.add_zero]; exact h2
      · obtain ⟨a', b', x, y, ht', ha', hb', hv', haff'⟩ := haff hA0
        obtain ⟨P3, z3, e3, h3⟩ := h2.add_affine ha' hb' hv'
        simp only [hA0, decide_false, Bool.not_false, ite_true, ht', e3, pure_bind]
        refine bit_loop U V t G Q htab m (by omega) P3 z3 ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _
        rw [hsum, ← haff']; exact h3


theorem checkedSub_one {k : ℕ} (hk : k + 2 < 2 ^ 256) :
    checkedSub (UInt256.ofNat (k + 2)) (UInt256.ofNat 1) = pure (UInt256.ofNat (k + 1)) := by
  unfold checkedSub
  rw [toNat_lit hk, toNat_lit (by decide), ite_eq_right (by omega)]
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
      ∃ P' z', combination_k2.loop.loop_2.loop_3 U V r0 (tbl t) (tbl pf) r3 (toB r4) (UInt256.ofNat (k + 1))
          r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
          r30 r31 r32 r33 r34 r35 r36 = pure P' ∧ GoodP P' (U.toNat • G + V.toNat • Q) z'
  | 0, _, t, r4, h0, _, hhigh, _, r0, r3, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
      r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36 => by
    rw [combination_k2.loop.loop_2.loop_3.eq_1]
    simp only [Nat.zero_add, toNat_lit (show 1 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, ite_false, infinity_eq, pure_bind]
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
    rw [combination_k2.loop.loop_2.loop_3.eq_1]
    have hj : k + 1 < 16 := by omega
    have hg := hlow (k + 1) (by omega) le_rfl
    simp only [toNat_lit (show 1 < 2 ^ 256 by decide), toNat_lit (show k + 1 + 1 < 2 ^ 256 by omega),
      show 1 < k + 1 + 1 by omega, decide_true, ite_true, checkedSub_one (show k + 2 < 2 ^ 256 by omega),
      pure_bind, checkIndex, toNat_lit (show k + 1 < 2 ^ 256 by omega), hj, tbl_get t hj,
      hg.is_infinity]
    set A := fun i => (i / 4) • G + (i % 4) • Q with hAdef
    have hprs := pr_succ A zs (j := k + 1) (by omega)
    by_cases hA : A (k + 1) = 0
    · simp only [show ((k + 1) / 4) • G + ((k + 1) % 4) • Q = 0 from hA, decide_true, ite_true]
      refine norm_loop U V G Q zs hz pf hpf k (by omega) t r4 h0 (fun j h1 h2 => hlow j h1 (by omega))
        (fun j h1 h2 => ?_) ?_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · exact tabOK_of_zero hg hA
        · exact hhigh j h h2
      · rw [show k + 1 + 1 = (k + 1) + 1 from rfl, hprs] at hr4
        simpa [hA] using hr4
    · simp only [show ¬ (((k + 1) / 4) • G + ((k + 1) % 4) • Q = 0) from hA, decide_false,
        Bool.false_eq_true, ite_false]
      obtain ⟨c, hc, hcr⟩ := hpf (k + 1) (by omega) hj
      have hzk : zs (k + 1) ≠ 0 := hz (k + 1) hj hA
      have hpr0 : pr A zs (k + 1) ≠ 0 := pr_ne_zero fun i hi => hz i (by omega)
      have hzi : RepB (Mont.mul KB r4 c) (zs (k + 1))⁻¹ := by
        have := RepB.mul hr4 hcr
        rw [hprs, ite_eq_left hA] at this
        convert this using 1
        field_simp
      obtain ⟨a, b, cz, x, y, ht, hcz, haff, htab, ha, hb⟩ := norm_entry hg hA hzi
      have hr4' : RepB (Mont.mul KB r4 cz) (pr A zs (k + 1))⁻¹ := by
        have := RepB.mul hr4 hcz
        rw [hprs, ite_eq_left hA] at this
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

namespace FeProofs.Ecrecover

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

theorem has16 (r : Range_Known_1_Known_16) {k : ℕ} (hk : k < 2 ^ 256) :
    Range_has_1_16 r (UInt256.ofNat k) = pure (decide (1 ≤ k ∧ k < 16)) := by
  simp only [Range_has_1_16, range_has_eq (lo := 1) (hi := 16) hk (by decide) (by decide), bind_pure]

theorem has4 (r : Range_Known_1_Known_4) {k : ℕ} (hk : k < 2 ^ 256) :
    Range_has_1_4 r (UInt256.ofNat k) = pure (decide (1 ≤ k ∧ k < 4)) := by
  simp only [Range_has_1_4, range_has_eq (lo := 1) (hi := 4) hk (by decide) (by decide), bind_pure]

theorem next16 (r : Range_Known_1_Known_16) {k : ℕ} (hk : k + 1 < 2 ^ 256) :
    Range_next_1_16 r (UInt256.ofNat k) = pure (UInt256.ofNat (k + 1)) := by
  simp only [Range_next_1_16, next_eq hk, pure_bind]

theorem next4 (r : Range_Known_1_Known_4) {k : ℕ} (hk : k + 1 < 2 ^ 256) :
    Range_next_1_4 r (UInt256.ofNat k) = pure (UInt256.ofNat (k + 1)) := by
  simp only [Range_next_1_4, next_eq hk, pure_bind]

/-- What a run of `combination` may do: diverge, or return a representation of `S`. -/
def OutP (S : W.toAffine.Point) (w : World) (o : Option (Except (Exit World) (Point_Mont_Base × World))) :
    Prop :=
  o = none ∨ ∃ P' z', o = some (.ok (P', w)) ∧ GoodP P' S z'

/-- The prefix loop, at counter `k`: the prefixes below `k` stored, the running product that
of the finite `z`s below `k`; then the inversion and the rest. -/
theorem prefix_loop (U V : UInt256) (G Q : W.toAffine.Point) (zs : ℕ → Fp) (t : ℕ → Point_Mont_Base)
    (hz : ∀ i < 16, (i / 4) • G + (i % 4) • Q ≠ 0 → zs i ≠ 0)
    (h0 : TabOK (t 0) ((0 / 4) • G + (0 % 4) • Q))
    (hg : ∀ j, 1 ≤ j → j < 16 → GoodP (t j) ((j / 4) • G + (j % 4) • Q) (zs j)) :
    ∀ n k, k + n = 16 → 1 ≤ k → ∀ (pf : ℕ → Mont_Base) (run : L4),
      (∀ j, 1 ≤ j → j < k → ∃ c, pf j = toB c ∧ RepB c (pr (fun i => (i / 4) • G + (i % 4) • Q) zs j)) →
      RepB run (pr (fun i => (i / 4) • G + (i % 4) • Q) zs k) →
      ∀ r0 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
        r28 r29 r30 r31 r32 r33 r34 r35 r36 env w,
      OutP (U.toNat • G + V.toNat • Q) w ((combination_k2.loop.loop_2 U V r0 (tbl t) (tbl pf) (toB run) r4
        r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
        r30 r31 r32 r33 r34 r35 r36 (UInt256.ofNat k)).exec env w)
  | 0, k, hkn, _, pf, run, hpf, hrun, r0, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16,
      r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      r36, env, w => by
    obtain rfl : k = 16 := by omega
    rw [combination_k2.loop.loop_2.eq_1]
    simp only [has16 _ (show 16 < 2 ^ 256 by decide), pure_bind,
      show (1 ≤ 16 ∧ 16 < 16) = False by decide, decide_false, Bool.false_eq_true, ite_false]
    rw [Fe.M.exec_bind]
    rcases Mont_inverse_Base_spec hrun env w with h | ⟨c, h, hc⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]
      obtain ⟨P', z', e, hP⟩ := norm_loop U V G Q zs hz pf (fun j h1 h2 => hpf j h1 h2) 15 le_rfl t c h0
        (fun j h1 h2 => hg j h1 (by omega)) (fun j h1 h2 => by omega) hc r0 (toB run) r6 r7 r8 r9 r10
        r11 r12 r13 r14 r15 r16 r17 r18 r19 (toB run) r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32
        r33 r34 r35 r36
      refine Or.inr ⟨P', z', ?_, hP⟩
      dsimp only
      rw [show UInt256.ofNat (15 + 1) = UInt256.ofNat 16 from rfl] at e
      rw [e]; rfl
  | n + 1, k, hkn, hk1, pf, run, hpf, hrun, r0, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34,
      r35, r36, env, w => by
    have hk : k < 16 := by omega
    rw [combination_k2.loop.loop_2.eq_1]
    have hgk := hg k hk1 hk
    simp only [has16 _ (show k < 2 ^ 256 by omega), show 1 ≤ k ∧ k < 16 from ⟨hk1, hk⟩, decide_true,
      ite_true, Range_at_1_16, pure_bind, checkIndex, toNat_lit (show k < 2 ^ 256 by omega), hk,
      tbl_get t hk, hgk.is_infinity, next16 _ (show k + 1 < 2 ^ 256 by omega), tbl_set pf hk]
    have hprs := pr_succ (fun i => (i / 4) • G + (i % 4) • Q) zs hk1
    have hpf' : ∀ j, 1 ≤ j → j < k + 1 → ∃ c, Function.update pf k (toB run) j = toB c ∧
        RepB c (pr (fun i => (i / 4) • G + (i % 4) • Q) zs j) := by
      intro j h1 h2
      rcases Nat.lt_or_ge j k with h | h
      · rw [Function.update_of_ne (by omega)]; exact hpf j h1 h
      · obtain rfl : j = k := by omega
        exact ⟨run, Function.update_self .., hrun⟩
    by_cases hA : (k / 4) • G + (k % 4) • Q = 0
    · simp only [hA, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact prefix_loop U V G Q zs t hz h0 hg n (k + 1) (by omega) (by omega) _ run hpf'
        (by rw [hprs]; simpa [hA] using hrun) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w
    · obtain ⟨x, y, ⟨a, b, c, ht, ha, hb, hc⟩, -, -⟩ := hgk
      simp only [hA, decide_false, Bool.not_false, ite_true, ht, mul_Base, pure_bind]
      exact prefix_loop U V G Q zs t hz h0 hg n (k + 1) (by omega) (by omega) _ _ hpf'
        (by rw [hprs, ite_eq_left hA]; exact RepB.mul hrun hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w

end FeProofs.Ecrecover

namespace FeProofs.Ecrecover

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover
/-- The rows of the table done at outer step `p`: the multiples of `G` and `Q` alone, and the
rows below `4 (p + 1)`. -/
def DO (p k : ℕ) : Prop := k % 4 = 0 ∨ k < 4 * (p + 1)

/-- The table is good where it is done. -/
def TabGood (G Q : W.toAffine.Point) (t : ℕ → Point_Mont_Base) (D : ℕ → Prop) : Prop :=
  ∀ k < 16, D k → ∃ z, GoodP (t k) ((k / 4) • G + (k % 4) • Q) z

theorem arr_at {p : ℕ} (hp : p < 3) :
    #v[UInt256.ofNat 4, UInt256.ofNat 8, UInt256.ofNat 12][p]! = UInt256.ofNat (4 * (p + 1)) := by
  interval_cases p <;> rfl

/-- The inner loop of the table, at outer step `p` and column `j`. -/
theorem tab_inner (U V : UInt256) (G Q : W.toAffine.Point) {p : ℕ} (hp : p < 3)
    (ih : ∀ t, TabGood G Q t (DO (p + 1)) → ∀ r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r13 r14 r15 r16 r17
      r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 env w,
      OutP (U.toNat • G + V.toNat • Q) w ((combination_k2.loop U V r0 (tbl t) r2 r3 r4 r5 r6 r7 r8 r9
        r10 r11 #v[UInt256.ofNat 4, UInt256.ofNat 8, UInt256.ofNat 12] r13 r14 r15 r16 r17 r18 r19
        r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36
        (UInt256.ofNat (p + 1))).exec env w)) :
    ∀ m j, j + m = 4 → 1 ≤ j → ∀ t, TabGood G Q t (fun k => DO p k ∨ (k / 4 = p + 1 ∧ k % 4 < j)) →
      ∀ r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
        r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 env w,
      OutP (U.toNat • G + V.toNat • Q) w ((combination_k2.loop.loop_1 U V (UInt256.ofNat p)
        (UInt256.ofNat (4 * (p + 1))) r0 (tbl t) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
        #v[UInt256.ofNat 4, UInt256.ofNat 8, UInt256.ofNat 12] r13 r14 r15 r16 r17 r18 r19 r20 r21
        r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 (UInt256.ofNat j)).exec env w)
  | 0, j, hjm, _, t, ht, r0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, env,
      w => by
    obtain rfl : j = 4 := by omega
    rw [combination_k2.loop.loop_1.eq_1]
    simp only [has4 _ (show 4 < 2 ^ 256 by decide), pure_bind, show (1 ≤ 4 ∧ 4 < 4) = False by decide,
      decide_false, Bool.false_eq_true, ite_false, Lib.array_next_usize_3,
      next_eq (show p + 1 < 2 ^ 256 by omega)]
    refine ih t (fun k hk hd => ht k hk ?_) r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r13 r14 r15 r16 r17 r18
      r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 env w
    unfold DO at hd ⊢
    omega
  | m + 1, j, hjm, hj1, t, ht, r0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13, r14, r15, r16, r17,
      r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
      env, w => by
    have hj : j < 4 := by omega
    rw [combination_k2.loop.loop_1.eq_1]
    have hi16 : 4 * (p + 1) < 16 := by omega
    have hk16 : 4 * (p + 1) + j < 16 := by omega
    obtain ⟨zi, hgi⟩ := ht (4 * (p + 1)) hi16 (Or.inl (Or.inl (by omega)))
    obtain ⟨zj, hgj⟩ := ht j (by omega) (Or.inl (Or.inr (by omega)))
    obtain ⟨P', z', e, hP⟩ := hgi.add hgj
    simp only [has4 _ (show j < 2 ^ 256 by omega), show 1 ≤ j ∧ j < 4 from ⟨hj1, hj⟩,
      ite_true, Range_at_1_4, pure_bind, checkIndex, toNat_lit (show j < 2 ^ 256 by omega),
      toNat_lit (show 4 * (p + 1) < 2 ^ 256 by omega), show j < 16 by omega, hi16,
      tbl_get t hi16, tbl_get t (show j < 16 by omega), e,
      checkedAdd_small (show 4 * (p + 1) + j < 2 ^ 256 by omega),
      toNat_lit (show 4 * (p + 1) + j < 2 ^ 256 by omega), hk16, next4 _ (show j + 1 < 2 ^ 256 by omega),
      tbl_set t hk16]
    refine tab_inner U V G Q hp ih m (j + 1) (by omega) (by omega) _ (fun k hk hd => ?_) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w
    by_cases hkk : k = 4 * (p + 1) + j
    · subst hkk
      rw [Function.update_self]
      refine ⟨z', ?_⟩
      have h1 : (4 * (p + 1) + j) / 4 = p + 1 := by omega
      have h2 : (4 * (p + 1) + j) % 4 = j := by omega
      have h3 : (4 * (p + 1)) / 4 = p + 1 := by omega
      have h4 : (4 * (p + 1)) % 4 = 0 := by omega
      have h5 : j / 4 = 0 := by omega
      have h6 : j % 4 = j := by omega
      rw [h1, h2]
      rw [h3, h4, h5, h6, zero_nsmul, _root_.add_zero, zero_nsmul, zero_add] at hP
      exact hP
    · rw [Function.update_of_ne hkk]
      exact ht k hk (by unfold DO at hd ⊢; omega)

theorem pr_one (A : ℕ → W.toAffine.Point) (zs : ℕ → Fp) : pr A zs 1 = 1 := by
  simp [pr]

/-- The outer loop of the table, at step `p`, then the prefix loop and the rest. -/
theorem tab_outer (U V : UInt256) (G Q : W.toAffine.Point) :
    ∀ n p, p + n = 3 → ∀ t, TabGood G Q t (DO p) → ∀ r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r13 r14 r15
      r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 env w,
      OutP (U.toNat • G + V.toNat • Q) w ((combination_k2.loop U V r0 (tbl t) r2 r3 r4 r5 r6 r7 r8 r9
        r10 r11 #v[UInt256.ofNat 4, UInt256.ofNat 8, UInt256.ofNat 12] r13 r14 r15 r16 r17 r18 r19
        r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 (UInt256.ofNat p)).exec env w)
  | 0, p, hp, t, ht, r0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13, r14, r15, r16, r17, r18, r19,
      r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, env, w => by
    obtain rfl : p = 3 := by omega
    rw [combination_k2.loop.eq_1]
    simp only [Lib.array_has_usize_3, toNat_lit (show 3 < 2 ^ 256 by decide), Nat.lt_irrefl,
      decide_false, Bool.false_eq_true, ite_false, pure_bind, one_Base, Range_start_1_16, tbl_replicate]
    have hall : ∀ k, ∃ z, k < 16 → GoodP (t k) ((k / 4) • G + (k % 4) • Q) z := by
      intro k
      by_cases hk : k < 16
      · obtain ⟨z, hz⟩ := ht k hk (by unfold DO; omega)
        exact ⟨z, fun _ => hz⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose zs hzs using hall
    exact prefix_loop U V G Q zs t (fun i hi hA hz => hA ((hzs i hi).zero_iff.mp hz))
      (tabOK_of_zero (hzs 0 (by decide)) (by simp)) (fun j _ h2 => hzs j h2) 15 1 rfl le_rfl _ _
      (fun j h1 h2 => by omega) (by rw [pr_one]; exact RepB.one) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w
  | n + 1, p, hp, t, ht, r0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, env,
      w => by
    have hp3 : p < 3 := by omega
    rw [combination_k2.loop.eq_1]
    simp only [Lib.array_has_usize_3, toNat_lit (show 3 < 2 ^ 256 by decide),
      toNat_lit (show p < 2 ^ 256 by omega), hp3, decide_true, ite_true, pure_bind,
      Lib.array_at_ref_usize_3, checkIndex, arr_at hp3, Range_start_1_4]
    exact tab_inner U V G Q hp3 (fun t' ht' => tab_outer U V G Q n (p + 1) (by omega) t' ht') 3 1 rfl
      le_rfl t (fun k hk hd => ht k hk (by unfold DO at hd ⊢; omega)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w


/-- The generator `G` of the specification, as a point of `W`. -/
theorem generator_spec : ∃ P, generator = pure P ∧ GoodP P Secp256k1.Spec.G 1 := by
  obtain ⟨cx, ex, hx⟩ := Mont_new_Base_repB (UInt256.ofNat Secp256k1.gx) (by
    rw [toNat_lit (by decide)]; decide)
  obtain ⟨cy, ey, hy⟩ := Mont_new_Base_repB (UInt256.ofNat Secp256k1.gy) (by
    rw [toNat_lit (by decide)]; decide)
  have hgx : GX = pure (UInt256.ofNat Secp256k1.gx) := rfl
  have hgy : GY = pure (UInt256.ofNat Secp256k1.gy) := rfl
  rw [toNat_lit (by decide)] at hx hy
  have hv : W.Nonsingular ![(Secp256k1.gx : Fp), (Secp256k1.gy : Fp), 1] :=
    (nonsingular_some _ _).mpr Secp256k1.Spec.G_nonsingular
  refine ⟨_, ?_, _, _, ⟨cx, cy, _, rfl, hx, hy, RepB.one⟩, hv, Point.toAffine_some hv⟩
  simp only [generator, hgx, hgy, ex, ey, pure_bind, affine_eq]

/-- `combination u v q`: every run diverges or returns a representation of `u • G + v • Q`. -/
theorem combination_spec (U V : UInt256) {q : Point_Mont_Base} {Qpt : W.toAffine.Point} {zq : Fp}
    (hq : GoodP q Qpt zq) (env : Env) (w : World) :
    OutP (U.toNat • Secp256k1.Spec.G + V.toNat • Qpt) w ((combination U V q).exec env w) := by
  obtain ⟨g, eg, hg⟩ := generator_spec
  obtain ⟨q2, z2, e2, h2⟩ := hq.double
  obtain ⟨q3, z3, e3, h3⟩ := h2.add hq
  obtain ⟨g2, z5, e5, h5⟩ := hg.double
  obtain ⟨g3, z6, e6, h6⟩ := h5.add hg
  simp only [combination, combination_k1, combination_k2, eg, infinity_eq, pure_bind, tbl_replicate,
    checkIndex, idx_lits, show (1 : ℕ) < 16 by decide, show (2 : ℕ) < 16 by decide,
    show (3 : ℕ) < 16 by decide, show (4 : ℕ) < 16 by decide, show (8 : ℕ) < 16 by decide,
    show (12 : ℕ) < 16 by decide, toNat_lit (show 3 < 2 ^ 256 by decide),
    toNat_lit (show 8 < 2 ^ 256 by decide), toNat_lit (show 12 < 2 ^ 256 by decide), ite_true,
    tbl_set _ (show 1 < 16 by decide), tbl_set _ (show 2 < 16 by decide),
    tbl_set _ (show 3 < 16 by decide), tbl_set _ (show 4 < 16 by decide),
    tbl_set _ (show 8 < 16 by decide), tbl_set _ (show 12 < 16 by decide),
    tbl_get _ (show 2 < 16 by decide), tbl_get _ (show 8 < 16 by decide), e2, e5, Lib.array_start_usize_3]
  simp only [Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 8 by decide), e3, e6, pure_bind]
  refine tab_outer U V Secp256k1.Spec.G Qpt 3 0 rfl _ (fun k hk hd => ?_) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env w
  have hd' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 8 ∨ k = 12 := by unfold DO at hd; omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Function.update_apply] <;>
    norm_num
  · exact ⟨0, GoodP.infinity⟩
  · exact ⟨zq, hq⟩
  · exact ⟨z2, by rw [two_nsmul]; exact h2⟩
  · exact ⟨z3, by rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]; exact h3⟩
  · exact ⟨1, hg⟩
  · exact ⟨z5, by rw [two_nsmul]; exact h5⟩
  · exact ⟨z6, by rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]; exact h6⟩

end FeProofs.Ecrecover
