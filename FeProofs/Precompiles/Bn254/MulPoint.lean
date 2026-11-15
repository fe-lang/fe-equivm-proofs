import FeProofs.Precompiles.Bn254.MulScalar

/-!
# Bn254Mul: the points of the ladder

`Point::add_affine` and `Mont::neg` of `Bn254Mul` are `pure` of `Pt.addAffine` and of `0 − y`
(`point_add_affine_Bn254Base`, `neg_Bn254Base`).  A point word is `GoodB` for a point of
`Spec.Point` when it represents a nonsingular Jacobian triple of that point, and two limbs are
`AffB` for it when they represent its affine coordinates; doubling and mixed addition keep
`GoodB` (`GoodB.double`, `GoodB.add_affine`, from `Pt.double_spec` and `Pt.addAffine_spec`, which
cover equal and opposite points), and `to_affine` of a `GoodB` word of a finite point returns
`AffB` limbs or diverges in the inversion (`GoodB.to_affine`).

Every finite point has order `r` (`nsmul_eq_zero_iff`).  So `P + φ(P)` and `P − φ(P)`, with
`φ(P) = λ • P`, are finite for finite `P`, as `λ ± 1` are not multiples of `r`
(`sum_ne_zero`): the precomputed sum of the ladder is never infinity.  Were it infinity, the
inversion of its `z = 0` would give `0`, `to_affine` the pair `(0, 0)`, which is not on the
curve, and the ladder's `add_affine` with it would add a pair off the curve.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul Mont

/-! ## The methods of `Bn254Mul` are pure -/

theorem neg_Bn254Base (a : L4) :
    Mont_neg_Bn254Base (toBn a) = pure (toBn (Mont.sub KBn Mont.zero a)) := by
  simp only [Mont_neg_Bn254Base, zero_Bn254Base, sub_Bn254Base, pure_bind]

theorem point_add_affine_Bn254Base (P : P3) (a b : L4) :
    Point_add_affine_Mont_Bn254Base (toBnP P) (toBn a) (toBn b) =
      pure (toBnP (Pt.addAffine KBn P a b)) := by
  simp only [Point_add_affine_Mont_Bn254Base, point_is_infinity_Bn254Base, toBnP_x, toBnP_y,
    toBnP_z, is_zero_Bn254Base, square_Bn254Base, mul_Bn254Base, add_Bn254Base, sub_Bn254Base,
    double_Bn254Base, pure_bind, point_infinity_Bn254Base, point_affine_Bn254Base,
    point_double_Bn254Base, Pt.addAffine]
  split_ifs <;> simp only [toBnP_mk]

/-! ## Points of the ladder -/

/-- `R` represents a nonsingular Jacobian triple whose point is `A`. -/
def GoodB (R : Point_Mont_Bn254Base) (A : BN254.Spec.Point) : Prop :=
  ∃ Q x y z, R = toBnP Q ∧ FBn.RepP Q x y z ∧ JBn.Nonsingular ![x, y, z] ∧
    Point.toAffine JBn ![x, y, z] = A

/-- `a`, `b` represent the affine coordinates of the finite point `A`. -/
def AffB (a b : L4) (A : BN254.Spec.Point) : Prop :=
  ∃ x y h, RepBn a x ∧ RepBn b y ∧ A = .some x y h

theorem GoodB.inf : GoodB (toBnP (Pt.inf KBn)) 0 :=
  ⟨_, 1, 1, 0, rfl, Pt.inf_rep, nonsingular_zero, Pt.toAffine_inf (F := FBn) (B := 3)⟩

theorem GoodB.double {R : Point_Mont_Bn254Base} {A : BN254.Spec.Point} (h : GoodB R A) :
    ∃ R', Point_double_Mont_Bn254Base R = pure R' ∧ GoodB R' (A + A) := by
  obtain ⟨Q, x, y, z, rfl, hr, hv, rfl⟩ := h
  obtain ⟨x', y', z', hr', hv', ha⟩ :=
    Pt.double_spec (F := FBn) (B := 3) cube_add_three_ne_zero hr hv
  exact ⟨_, point_double_Bn254Base Q, _, x', y', z', rfl, hr', hv', ha⟩

theorem GoodB.add_affine {R : Point_Mont_Bn254Base} {A B : BN254.Spec.Point} {a b : L4}
    (h : GoodB R A) (hab : AffB a b B) :
    ∃ R', Point_add_affine_Mont_Bn254Base R (toBn a) (toBn b) = pure R' ∧ GoodB R' (A + B) := by
  obtain ⟨Q, x, y, z, rfl, hr, hv, rfl⟩ := h
  obtain ⟨x2, y2, h2, ha, hb, rfl⟩ := hab
  have hj := (nonsingular_some (W' := JBn) _ _).mpr h2
  obtain ⟨x', y', z', hr', hv', haff⟩ :=
    Pt.addAffine_spec (F := FBn) (B := 3) cube_add_three_ne_zero hr ha hb hv hj
  refine ⟨_, point_add_affine_Bn254Base Q a b, _, x', y', z', rfl, hr', hv', ?_⟩
  rw [haff, Point.toAffine_some hj]

/-- `to_affine` of a finite point: diverges (in the inversion) or returns, the world unchanged,
limbs of its affine coordinates. -/
theorem GoodB.to_affine {R : Point_Mont_Bn254Base} {A : BN254.Spec.Point} (h : GoodB R A)
    (hA : A ≠ 0) (env : Env) (w : World) :
    (Point_to_affine_Mont_Bn254Base R).exec env w = none ∨
      ∃ a b, (Point_to_affine_Mont_Bn254Base R).exec env w = some (.ok ((toBn a, toBn b), w)) ∧
        AffB a b A := by
  obtain ⟨Q, x, y, z, rfl, hr, hv, rfl⟩ := h
  have hz : z ≠ 0 := fun hz => hA (Pt.toAffine_eq_zero_of_z (F := FBn) (B := 3) hz)
  rcases Point_to_affine_Bn254Base_spec hr env w with h | ⟨c, h, hc⟩
  · exact Or.inl h
  · obtain ⟨h1, h2⟩ := Pt.toAffineWith_rep hr hc
    obtain ⟨hs, he⟩ := Pt.toAffine_some (F := FBn) (B := 3) hv hz
    exact Or.inr ⟨_, _, h, _, _, hs, h1, h2, he⟩

/-! ## Negation and the endomorphism on affine limbs -/

theorem AffB.of_some {a b : L4} {x y : Fq} (ha : RepBn a x) (hb : RepBn b y)
    (h : BN254.Spec.curve.toAffine.Nonsingular x y) : AffB a b (.some x y h) :=
  ⟨x, y, h, ha, hb, rfl⟩

theorem AffB.good {a b : L4} {A : BN254.Spec.Point} (h : AffB a b A) :
    GoodB (toBnP (Pt.affine KBn a b)) A := by
  obtain ⟨x, y, hxy, ha, hb, rfl⟩ := h
  have hj := (nonsingular_some (W' := JBn) _ _).mpr hxy
  exact ⟨_, x, y, 1, rfl, Pt.affine_rep ha hb, hj, Point.toAffine_some hj⟩

theorem AffB.neg {a b : L4} {A : BN254.Spec.Point} (h : AffB a b A) :
    AffB a (Mont.sub KBn Mont.zero b) (-A) := by
  obtain ⟨x, y, hxy, ha, hb, rfl⟩ := h
  have e : BN254.Spec.curve.toAffine.negY x y = 0 - y := by
    simp [Affine.negY, Ethereum.Weierstrass.short]
  refine ⟨x, 0 - y, e ▸ (Affine.nonsingular_neg ..).mpr hxy, ha,
    MField.Rep.sub MField.Rep.zero hb, ?_⟩
  rw [Affine.Point.neg_some, Affine.Point.some.injEq]
  exact ⟨rfl, e⟩

theorem beta_lt : BN254.BETA < BN254.p := by decide

/-- `φ(x, y) = (x β, y)` is `λ • (x, y)`. -/
theorem AffB.phi {a b : L4} {x y : Fq} (ha : RepBn a x) (hb : RepBn b y)
    (h : BN254.Spec.curve.toAffine.Nonsingular x y) :
    AffB (Mont.mul KBn a (Mont.new KBn BN254.BETA)) b (BN254.LAMBDA • .some x y h) := by
  rw [← BN254.endo_eq_nsmul, BN254.endo_some]
  refine ⟨_, _, _, ?_, hb, rfl⟩
  have := MField.Rep.mul ha (MField.Rep.new (F := FBn) beta_lt)
  rwa [mul_comm] at this

/-! ## Orders: `P ± φ(P)` is finite -/

/-- Every finite point has order `r`. -/
theorem nsmul_eq_zero_iff {P : BN254.Spec.Point} (hP : P ≠ 0) (n : ℕ) :
    n • P = 0 ↔ BN254.r ∣ n := by
  have ho : addOrderOf P = BN254.r := by
    rcases (Nat.dvd_prime BN254.r_prime).mp
        (addOrderOf_dvd_of_nsmul_eq_zero (BN254.nsmul_r P)) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hP
    · exact h
  rw [← ho, addOrderOf_dvd_iff_nsmul_eq_zero]

theorem lambda_bounds : 1 < BN254.LAMBDA ∧ BN254.LAMBDA + 1 < BN254.r := by
  rw [L_val, r_val]; norm_num

theorem add_lambda_ne_zero {P : BN254.Spec.Point} (hP : P ≠ 0) : P + BN254.LAMBDA • P ≠ 0 := by
  intro h
  have hd := (nsmul_eq_zero_iff hP (BN254.LAMBDA + 1)).mp
    (by rw [add_nsmul, one_nsmul, add_comm]; exact h)
  have := lambda_bounds
  exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)

theorem lambda_ne_self {P : BN254.Spec.Point} (hP : P ≠ 0) : BN254.LAMBDA • P ≠ P := by
  intro h
  have := lambda_bounds
  have e : (BN254.LAMBDA - 1) • P + P = 0 + P := by
    rw [zero_add, ← succ_nsmul, Nat.sub_add_cancel (by omega), h]
  have hd := (nsmul_eq_zero_iff hP (BN254.LAMBDA - 1)).mp (add_right_cancel e)
  exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- `P` or `−P` by a sign. -/
def sgn (s : Bool) (P : BN254.Spec.Point) : BN254.Spec.Point := if s then -P else P

/-- **The precomputed sum is finite**: `±P ± φ(P) ≠ 0` for `P ≠ 0`. -/
theorem sum_ne_zero {P : BN254.Spec.Point} (hP : P ≠ 0) (s1 s2 : Bool) :
    sgn s1 P + sgn s2 (BN254.LAMBDA • P) ≠ 0 := by
  cases s1 <;> cases s2 <;> simp only [sgn, ite_true, Bool.false_eq_true, ite_false]
  · exact add_lambda_ne_zero hP
  · intro h; exact lambda_ne_self hP (add_neg_eq_zero.mp h).symm
  · intro h; exact lambda_ne_self hP (neg_add_eq_zero.mp h).symm
  · rw [← neg_add]; exact neg_ne_zero.mpr (add_lambda_ne_zero hP)

theorem AffB.sgn {a b : L4} {A : BN254.Spec.Point} (h : AffB a b A) (s : Bool) :
    AffB a (if s then Mont.sub KBn Mont.zero b else b) (sgn s A) := by
  cases s
  · exact h
  · exact h.neg

/-- A magnitude and a sign: `|z| • (±P) = z • P`. -/
theorem natAbs_sgn (z : ℤ) (P : BN254.Spec.Point) :
    (z.natAbs : ℕ) • sgn (decide (z < 0)) P = z • P := by
  rw [← natCast_zsmul]
  by_cases hz : z < 0
  · simp only [sgn, hz, decide_true, ite_true, zsmul_neg, ← neg_zsmul]
    congr 1
    omega
  · simp only [sgn, hz, decide_false, Bool.false_eq_true, ite_false]
    congr 1
    omega

end FeProofs.Bn254Mul
