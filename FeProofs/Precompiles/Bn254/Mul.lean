import FeProofs.Precompiles.Bn254.MulLadder

/-!
# Bn254Mul: `multiply_g1` and ECMUL on the words of the input

`multiply_g1` of an affine point `P` of the curve and a scalar `k` (`multiply_g1_spec`)
diverges or returns a representation of a nonsingular triple whose point is `k • P`.  The
scalar is reduced and split into `k₁ + k₂ λ ≡ k (mod r)` (`MulScalar.lean`); the code adds
`|k₁| • (±P) + |k₂| • (±φ(P))` by the joint ladder (`MulLadder.lean`) with `φ(P) = λ • P` and
the precomputed sum, which is finite (`MulPoint.lean`); `|kᵢ| • (±Q) = kᵢ • Q` (`natAbs_sgn`)
and the congruence give `k • P` (`mod_r_nsmul`).  Only the inversion in `to_affine` of the
precomputed sum can diverge; everything else is pure or panics nowhere, by the bounds of
`MulScalar.lean`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul Mont

theorem checkedSub_le {a : ℕ} {b : UInt256} (ha : a < 2 ^ 256) (h : b.toNat ≤ a) :
    checkedSub (UInt256.ofNat a) b = pure (UInt256.ofNat (a - b.toNat)) := by
  unfold checkedSub
  rw [toNat_lit ha, if_neg (by omega)]
  congr 1
  apply word_eq_of_toNat
  change (UInt256.sub _ _).toNat = _
  rw [usub_toNat (by rw [toNat_lit ha]; omega), toNat_lit ha, toNat_lit (by omega)]

theorem fp_beta :
    fp (UInt256.ofNat 2203960485148121921418603742825762020974279258880205651966) =
      pure (toBn (Mont.new KBn BN254.BETA)) := by
  rw [fp_eq _ (by rw [toNat_lit (by decide)]; exact beta_lt), toNat_lit (by decide)]
  rfl

theorem multiply_g1_k1_spec {a b : L4} {x y : Fq} (ha : RepBn a x) (hb : RepBn b y)
    (h : BN254.Spec.curve.toAffine.Nonsingular x y) (c : Mont_Bn254Base) (c1 c2 n1 : ℕ)
    (s1 : Bool) (hc1 : c1 * BN254.GLV_B1 < 2 ^ 256) (hc2 : c2 * BN254.GLV_B2 < 2 ^ 256)
    (hz1 : -(2 ^ 255 : ℤ) < (c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ))
    (hz2 : ((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ) < 2 ^ 255)
    (hn1 : n1 < 2 ^ 256)
    (r0 r1 r2 r3 r4 r5 : Mont_Bn254Base) (r6 : Point_Mont_Bn254Base) (r7 : UInt256)
    (r8 r9 r10 r11 : Mont_Bn254Base) (r12 r13 r14 r15 r16 r17 : Point_Mont_Bn254Base)
    (env : Env) (w : World) :
    (multiply_g1_k1 ⟨toBn a, toBn b, c⟩ (UInt256.ofNat c1) (UInt256.ofNat c2)
        (UInt256.ofNat n1, s1) r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
        r17).exec env w = none ∨
      ∃ R, (multiply_g1_k1 ⟨toBn a, toBn b, c⟩ (UInt256.ofNat c1) (UInt256.ofNat c2)
          (UInt256.ofNat n1, s1) r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
          r17).exec env w = some (.ok (R, w)) ∧
        GoodB R (n1 • sgn s1 (.some x y h) +
          (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ)).natAbs •
            sgn (decide (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ) < 0))
              (BN254.LAMBDA • .some x y h)) := by
  have hb1 : 0 < BN254.GLV_B1 := by rw [B1_val]; decide
  have hb2 : 0 < BN254.GLV_B2 := by rw [B2_val]; decide
  simp only [multiply_g1_k1, GLV_B1, GLV_B2, BETA, pure_bind]
  rw [show (147946756881789319000765030803803410728 : ℕ) = BN254.GLV_B1 from rfl,
    show (9931322734385697763 : ℕ) = BN254.GLV_B2 from rfl,
    checkedMul_small (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hb1) hc1)
      (by rw [B1_val]; decide) hc1,
    checkedMul_small (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hb2) hc2)
      (by rw [B2_val]; decide) hc2]
  simp only [Lib.u256_wrapping_sub, pure_bind]
  rw [← toWord_ofNat hc1, ← toWord_ofNat hc2, toWord_sub, magnitude_eq hz1 hz2, pure_bind]
  have hP : (Affine.Point.some x y h : BN254.Spec.Point) ≠ 0 := Affine.Point.some_ne_zero h
  have hA1 := (AffB.of_some ha hb h).sgn s1
  have hA2 := (AffB.phi ha hb h).sgn
    (decide (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ) < 0))
  have hn2 : (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ)).natAbs < 2 ^ 256 := by
    omega
  generalize (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ)).natAbs = n2 at hA2 hn2 ⊢
  generalize decide (((c1 * BN254.GLV_B1 : ℕ) - (c2 * BN254.GLV_B2 : ℕ) : ℤ) < 0) = s2 at hA2 ⊢
  have hlz := leadingZeros_bound (UInt256.ofNat (n1 ||| n2))
  rw [toNat_lit (Nat.or_lt_two_pow (n := 256) hn1 hn2)] at hlz
  have hm1 : n1 / 2 ^ (256 - (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat) = 0 :=
    Nat.div_eq_of_lt (lt_of_le_of_lt Nat.left_le_or hlz.2)
  have hm2 : n2 / 2 ^ (256 - (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat) = 0 :=
    Nat.div_eq_of_lt (lt_of_le_of_lt Nat.right_le_or hlz.2)
  have hinf : GoodB (toBnP (Pt.inf KBn))
      ((n1 / 2 ^ (256 - (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat)) •
          sgn s1 (.some x y h) +
        (n2 / 2 ^ (256 - (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat)) •
          sgn s2 (BN254.LAMBDA • .some x y h)) := by
    rw [hm1, hm2, zero_nsmul, zero_nsmul, _root_.add_zero]; exact GoodB.inf
  have hbit : UInt256.ofNat ((UInt256.ofNat (256 -
      (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat)).toNat % 2 ^ 64) =
      UInt256.ofNat (256 - (IntTy.leadingZeros (.u 256) (UInt256.ofNat (n1 ||| n2))).toNat) := by
    rw [toNat_lit (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [neg_Bn254Base, fp_beta, mul_Bn254Base, point_affine_Bn254Base,
    pure_bind, lor_eq hn1 hn2, checkedSub_le (show 256 < 2 ^ 256 by decide) hlz.1,
    downcast_truncate_u256_u64_eq, point_infinity_Bn254Base, hbit]
  cases s1 <;> cases s2 <;>
    simp only [Bool.false_eq_true, if_true, if_false] at hA1 hA2 ⊢
  all_goals
    obtain ⟨E, eE, hE⟩ := hA1.good.add_affine hA2
    rw [eE, pure_bind, Fe.M.exec_bind]
    rcases hE.to_affine (sum_ne_zero hP _ _) env w with hd | ⟨a3, b3, e3, hA3⟩
    · left; rw [hd]
    · right
      obtain ⟨R, hR, eR⟩ := ladder n1 n2 hn1 hn2 hA1 hA2 hA3 _ (by omega) _ hinf
      rw [e3]
      exact ⟨R, by simp only [eR, Fe.M.exec_pure], hR⟩

/-- Integer multiples congruent modulo `r` are equal. -/
theorem zsmul_congr (P : BN254.Spec.Point) {u v : ℤ} (h : u ≡ v [ZMOD BN254.r]) :
    u • P = v • P := by
  obtain ⟨t, ht⟩ := h.dvd
  have : (v - u) • P = 0 := by
    rw [ht, mul_comm, ← smul_smul, natCast_zsmul, BN254.nsmul_r, zsmul_zero]
  rw [sub_zsmul, add_neg_eq_zero] at this
  exact this.symm

/-- **`multiply_g1`**: for an affine point of the curve, diverges (in the inversion of the
precomputed sum) or returns, the world unchanged, a representation of a nonsingular triple
whose point is `k • P`. -/
theorem multiply_g1_spec {a b : L4} {x y : Fq} (ha : RepBn a x) (hb : RepBn b y)
    (h : BN254.Spec.curve.toAffine.Nonsingular x y) (c : Mont_Bn254Base) (k : UInt256)
    (env : Env) (w : World) :
    (multiply_g1 ⟨toBn a, toBn b, c⟩ k).exec env w = none ∨
      ∃ R, (multiply_g1 ⟨toBn a, toBn b, c⟩ k).exec env w = some (.ok (R, w)) ∧
        GoodB R (k.toNat • .some x y h) := by
  rw [multiply_g1_eq]
  have hk : k.toNat % BN254.r < BN254.r := Nat.mod_lt _ (by rw [r_val]; decide)
  obtain ⟨-, -, -, -, b5, b6⟩ := kr_bounds hk
  have e2 : (((c1Of (k.toNat % BN254.r) * BN254.GLV_B1 : ℕ) -
      (c2Of (k.toNat % BN254.r) * BN254.GLV_B2 : ℕ) : ℤ)) = z2Of (k.toNat % BN254.r) := by
    unfold z2Of; push_cast; ring
  have hz1 := z1_bound hk
  have hz2 := z2_bound hk
  have l1 : -(2 ^ 255 : ℤ) < ((c1Of (k.toNat % BN254.r) * BN254.GLV_B1 : ℕ) -
      (c2Of (k.toNat % BN254.r) * BN254.GLV_B2 : ℕ) : ℤ) := by
    rw [e2]; exact lt_trans (by norm_num) hz2.1
  have l2 : ((c1Of (k.toNat % BN254.r) * BN254.GLV_B1 : ℕ) -
      (c2Of (k.toNat % BN254.r) * BN254.GLV_B2 : ℕ) : ℤ) < 2 ^ 255 := by
    rw [e2]; exact lt_trans hz2.2 (by norm_num)
  have l3 : (z1Of (k.toNat % BN254.r)).natAbs < 2 ^ 256 := by omega
  rcases multiply_g1_k1_spec ha hb h c _ _ _ (decide (z1Of (k.toNat % BN254.r) < 0)) b5 b6
      l1 l2 l3 default default default default default
      default default default default default default default default default default default
      default default env w with hd | ⟨R, eR, hR⟩
  · exact Or.inl hd
  refine Or.inr ⟨R, eR, ?_⟩
  rw [e2, natAbs_sgn, natAbs_sgn, ← natCast_zsmul _ BN254.LAMBDA, smul_smul, ← add_zsmul,
    zsmul_congr _ (glv_congr _), natCast_zsmul, BN254.mod_r_nsmul] at hR
  exact hR

end FeProofs.Bn254Mul
