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

`mul_MemBuffer` reads the input only through `word_at_MemBuffer`, at offsets `0`, `32` and
`64`.  Given the three words it returns there (the world unchanged), it diverges or returns
`mulWords` of their values (`mul_MemBuffer_spec`): `None` when `Spec.decode` of the point fails,
otherwise `Some` of the encoding of `k • P`.  The decoding is `g1_point_spec`'s with the shape of
the point kept (`g1_point_affine`), since `multiply_g1` reads the affine `x`, `y` and not `z`.
The early `(0, 0)` for infinity and for `k = 0` is the encoding of `k • 0 = 0 • P = 0`.
`mul_MemBuffer_correct` states the result against `Spec.mul` and its 64 bytes.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul Mont

theorem checkedSub_le {a : ℕ} {b : UInt256} (ha : a < 2 ^ 256) (h : b.toNat ≤ a) :
    checkedSub (UInt256.ofNat a) b = pure (UInt256.ofNat (a - b.toNat)) := by
  unfold checkedSub
  rw [toNat_lit ha, ite_eq_right (by omega)]
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
    simp only [Bool.false_eq_true, ite_true, ite_false] at hA1 hA2 ⊢
  all_goals
    obtain ⟨E, eE, hE⟩ := hA1.good.add_affine hA2
    rw [eE, pure_bind, Fe.M.exec_bind]
    rcases hE.to_affine (sum_ne_zero hP _ _) env w with hd | ⟨a3, b3, e3, hA3⟩
    · left; rw [hd]
    · right
      obtain ⟨R, hR, eR⟩ := ladder n1 n2 hn1 hn2 hA1 hA2 hA3 _ (by omega) _ hinf
      rw [e3]
      exact ⟨R, by dsimp only; rw [eR, Fe.M.exec_pure], hR⟩

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

/-! ## The decoding, with the shape of the point -/

/-- `r` is the decoding `d`, with the shape `mul` relies on: `None` for `none`, infinity for
`(0, 0)`, otherwise an affine point. -/
def G1A : Option_Point_Mont_Bn254Base → Option BN254.Spec.Point → Prop
  | .None, d => d = none
  | .Some R, d => (R = toBnP (Pt.inf KBn) ∧ d = some 0) ∨
      ∃ a b x y h, R = toBnP (Pt.affine KBn a b) ∧ RepBn a x ∧ RepBn b y ∧ d = some (.some x y h)

/-- `g1_point` at an offset whose two words are `x` and `y` returns, with the world unchanged,
the decoding of `(x, y)`: `g1_point_spec` with the shape of the point. -/
theorem g1_point_affine (input : MemBuffer) (off off32 x y : UInt256) (env : Env) (w : World)
    (hadd : checkedAdd off (UInt256.ofNat 32) = pure off32)
    (hx : (word_at_MemBuffer input off).exec env w = some (.ok (x, w)))
    (hy : (word_at_MemBuffer input off32).exec env w = some (.ok (y, w))) :
    ∃ r, (g1_point_MemBuffer input off).exec env w = some (.ok (r, w)) ∧
      G1A r (BN254.Spec.decode x.toNat y.toNat) := by
  simp only [g1_point_MemBuffer, Fe.M.exec_bind, hx, hadd, hy, MODULUS, pure_bind,
    modulus_toNat]
  unfold BN254.Spec.decode
  by_cases hxp : x.toNat < BN254.p
  swap
  · refine ⟨.None, by simp only [show BN254.p ≤ x.toNat by omega, decide_true, ite_true,
      Fe.M.exec_pure], ?_⟩
    simp only [G1A]; rw [ite_eq_right (by omega)]
  by_cases hyp : y.toNat < BN254.p
  swap
  · refine ⟨.None, by simp only [show ¬ BN254.p ≤ x.toNat by omega, show BN254.p ≤ y.toNat by omega,
      decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false, Fe.M.exec_pure], ?_⟩
    simp only [G1A]; rw [ite_eq_right (by omega)]
  have h3 : (UInt256.ofNat 3).toNat < BN254.p := by rw [toNat_lit (by decide)]; decide
  have hrx := MField.Rep.new (F := FBn) hxp
  have hry := MField.Rep.new (F := FBn) hyp
  have hr3 := MField.Rep.new (F := FBn) h3
  rw [toNat_lit (show 3 < 2 ^ 256 by decide), Nat.cast_ofNat] at hr3
  simp only [show ¬ BN254.p ≤ x.toNat by omega, show ¬ BN254.p ≤ y.toNat by omega, decide_false,
    Bool.false_eq_true, ite_false, ite_eq_left (And.intro hxp hyp), fp_eq x hxp, fp_eq y hyp,
    fp_eq _ h3, pure_bind, point_affine_Bn254Base, toBnP_x, toBnP_y, Pt.affine,
    toNat_lit (show 3 < 2 ^ 256 by decide), on_curve_spec hrx hry hr3, word_eq_zero_iff,
    decide_eq_true_eq, point_infinity_Bn254Base]
  by_cases h0 : x.toNat = 0 ∧ y.toNat = 0
  · simp only [h0, ite_true, Fe.M.exec_pure]
    exact ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hb6 : ∀ (c : Prop) [Decidable c] (m : FeM Option_Point_Mont_Bn254Base),
      (if c then (if y.toNat = 0 then m else
        (if (!decide ((y.toNat : Fq) ^ 2 = (x.toNat : Fq) ^ 3 + 3)) = true then
          pure Option_Point_Mont_Bn254Base.None
        else pure (.Some (toBnP ⟨Mont.new KBn x.toNat, Mont.new KBn y.toNat, Mont.new KBn 1⟩))))
        else
        (if (!decide ((y.toNat : Fq) ^ 2 = (x.toNat : Fq) ^ 3 + 3)) = true then
          pure Option_Point_Mont_Bn254Base.None
        else pure (.Some (toBnP ⟨Mont.new KBn x.toNat, Mont.new KBn y.toNat, Mont.new KBn 1⟩)))) =
      if c ∧ y.toNat = 0 then m else
        (if (y.toNat : Fq) ^ 2 = (x.toNat : Fq) ^ 3 + 3 then
          pure (.Some (toBnP ⟨Mont.new KBn x.toNat, Mont.new KBn y.toNat, Mont.new KBn 1⟩))
        else pure Option_Point_Mont_Bn254Base.None) := by
    intro c _ m
    by_cases hc : c <;> by_cases hy0 : y.toNat = 0 <;>
      by_cases hoc : (y.toNat : Fq) ^ 2 = (x.toNat : Fq) ^ 3 + 3 <;> simp [hc, hy0, hoc]
  rw [hb6, ite_eq_right h0, ite_eq_right h0]
  by_cases hoc : (y.toNat : Fq) ^ 2 = (x.toNat : Fq) ^ 3 + 3
  · have hns := (nonsingular_iff _ _).mpr hoc
    rw [ite_eq_left hoc, dite_eq_left hns, Fe.M.exec_pure]
    exact ⟨_, rfl, Or.inr ⟨_, _, _, _, hns, rfl, hrx, hry, rfl⟩⟩
  · rw [ite_eq_right hoc, dite_eq_right (fun h => hoc ((nonsingular_iff _ _).mp h)), Fe.M.exec_pure]
    exact ⟨_, rfl, rfl⟩

/-! ## ECMUL on the words of the input -/

/- `rw [Fe.M.exec_bind]` and `simp` at a bind of `multiply_g1` into `encode` give terms on which
the kernel recurses too deep; these lemmas instantiate the continuation instead. -/
theorem exec_bind_none {α β : Type} {x : FeM α} {f : α → FeM β} {env : Env} {w : World}
    (h : x.exec env w = none) : (x >>= f).exec env w = none := by
  rw [Fe.M.exec_bind, h]

theorem exec_bind_ok {α β : Type} {x : FeM α} {f : α → FeM β} {env : Env} {w w' : World}
    {a : α} (h : x.exec env w = some (.ok (a, w'))) : (x >>= f).exec env w = (f a).exec env w' := by
  rw [Fe.M.exec_bind, h]

/-- ECMUL on two coordinates and a scalar, as `mul_MemBuffer` returns it: `None` when the
point does not decode, otherwise `Some` of the encoding of the multiple. -/
noncomputable def mulWords (x y k : ℕ) : Option_array_u256_2 :=
  match BN254.Spec.decode x y with
  | some P => .Some (encodeWords (k • P))
  | none => .None

/-- `mulWords` is `Spec.mul`: `Some` of the words whose 32-byte encodings make its output. -/
theorem mulWords_spec (x y k : ℕ) :
    match mulWords x y k with
    | .Some v => ∃ a b, v = #v[UInt256.ofNat a, UInt256.ofNat b] ∧ a < BN254.p ∧ b < BN254.p ∧
        BN254.Spec.mul x y k = some (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)
    | .None => BN254.Spec.mul x y k = none := by
  unfold mulWords BN254.Spec.mul
  rcases BN254.Spec.decode x y with _ | P
  · rfl
  · obtain ⟨a, b, he, ha, hb, hs⟩ := encodeWords_spec (k • P)
    exact ⟨a, b, he, ha, hb, by simp [hs]⟩

theorem encodeWords_zero : encodeWords 0 = #v[UInt256.ofNat 0, UInt256.ofNat 0] := rfl

/-- ECMUL on the input buffer.  Given the words `word_at` returns at offsets `0`, `32` and
`64`, the world unchanged, `mul_MemBuffer` diverges (in an inversion) or returns, with the world
unchanged, `mulWords` of their values. -/
theorem mul_MemBuffer_spec (input : MemBuffer) (x y k : UInt256) (env : Env) (w : World)
    (h0 : (word_at_MemBuffer input (UInt256.ofNat 0)).exec env w = some (.ok (x, w)))
    (h32 : (word_at_MemBuffer input (UInt256.ofNat 32)).exec env w = some (.ok (y, w)))
    (h64 : (word_at_MemBuffer input (UInt256.ofNat 64)).exec env w = some (.ok (k, w))) :
    (mul_MemBuffer input).exec env w = none ∨
      (mul_MemBuffer input).exec env w = some (.ok (mulWords x.toNat y.toNat k.toNat, w)) := by
  obtain ⟨r, e, g⟩ := g1_point_affine input _ _ x y env w checkedAdd_0_32 h0 h32
  unfold mul_MemBuffer mulWords
  simp only [Fe.M.exec_bind, e]
  rcases r with _ | R
  · right
    simp only [G1A] at g
    rw [g]
    rfl
  rcases g with ⟨rfl, hd⟩ | ⟨a, b, x', y', h, rfl, ha, hb, hd⟩
  · right
    simp only [hd, Option_Point_Mont_Bn254Base.Some_0, Fe.M.exec_bind, h64,
      point_is_infinity_Bn254Base, Pt.inf, MField.Rep.isZero (MField.Rep.zero (F := FBn)),
      decide_true, ite_true, pure_bind, Fe.M.exec_pure, nsmul_zero]
    rfl
  · have hz : Mont.isZero (Pt.affine KBn a b).z = false := by
      rw [MField.Rep.isZero (Pt.affine_rep (F := FBn) ha hb).2.2]
      exact decide_eq_false one_ne_zero
    simp only [hd, Option_Point_Mont_Bn254Base.Some_0, Fe.M.exec_bind, h64,
      point_is_infinity_Bn254Base, hz, Bool.false_eq_true, ite_false, pure_bind]
    by_cases hk : k.toNat = 0
    · right
      simp only [(word_eq_zero_iff k).mpr hk, decide_true, ite_true, Fe.M.exec_pure,
        toNat_lit (show 0 < 2 ^ 256 by decide), zero_nsmul]
      rfl
    simp only [show ¬ k = UInt256.ofNat 0 from fun h => hk ((word_eq_zero_iff k).mp h),
      decide_false, Bool.false_eq_true, ite_false,
      show toBnP (Pt.affine KBn a b) = ⟨toBn a, toBn b, toBn (Pt.affine KBn a b).z⟩ from rfl]
    rcases multiply_g1_spec ha hb h (toBn (Pt.affine KBn a b).z) k env w with hm | ⟨R, eR, hR⟩
    · exact Or.inl (exec_bind_none hm)
    obtain ⟨Q, x1, y1, z1, rfl, hr1, hv1, hA⟩ := hR
    rw [exec_bind_ok eR]
    rcases encode_spec hr1 hv1 env w with he | he
    · exact Or.inl (exec_bind_none he)
    · rw [exec_bind_ok he, hA]
      exact Or.inr rfl

/-- ECMUL on the input buffer against `Spec.mul`: diverges, or returns with the world unchanged
`Some` of two words below `p` whose 32-byte encodings make `Spec.mul`'s output, or `None` exactly
when `Spec.mul` fails. -/
theorem mul_MemBuffer_correct (input : MemBuffer) (x y k : UInt256) (env : Env) (w : World)
    (h0 : (word_at_MemBuffer input (UInt256.ofNat 0)).exec env w = some (.ok (x, w)))
    (h32 : (word_at_MemBuffer input (UInt256.ofNat 32)).exec env w = some (.ok (y, w)))
    (h64 : (word_at_MemBuffer input (UInt256.ofNat 64)).exec env w = some (.ok (k, w))) :
    (mul_MemBuffer input).exec env w = none ∨
      ∃ r, (mul_MemBuffer input).exec env w = some (.ok (r, w)) ∧
        match r with
        | .Some v => ∃ a b, v = #v[UInt256.ofNat a, UInt256.ofNat b] ∧ a < BN254.p ∧
            b < BN254.p ∧ BN254.Spec.mul x.toNat y.toNat k.toNat =
              some (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)
        | .None => BN254.Spec.mul x.toNat y.toNat k.toNat = none := by
  rcases mul_MemBuffer_spec input x y k env w h0 h32 h64 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h, mulWords_spec _ _ _⟩

end FeProofs.Bn254Mul
