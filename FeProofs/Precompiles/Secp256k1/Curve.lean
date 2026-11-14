import FeProofs.Precompiles.Secp256k1.Inverse
import FeProofs.Precompiles.Curve.Point

/-!
# Ecrecover: the curve operations

`bn254_curve.fe`'s `Point<F>` in Jacobian coordinates, at `F = Mont<Base>`, against Mathlib's
Jacobian points of `Spec.curve : y² = x³ + 7` over `Fp`.  Three Montgomery triples represent a
Jacobian triple (`RepP`).  The exported point methods are `pure` of the functions of
`Curve/Point.lean` at `KB` (`point_double_Base` and the rest), which compute the curve
operations for every Montgomery field and every `y² = x³ + B` whose `x ^ 3 + B` has no root.
At `Base` (`FB`) and `B = 7` (`cube_add_seven_ne_zero`): `double`, `add` and `add_affine` are
proved for all nonsingular inputs, the exceptional cases included; the output represents a
nonsingular triple whose affine point is the sum (`Point_double_spec`, `Point_add_spec`,
`Point_add_affine_spec`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover Mont

/-- `Base` as the field `Fp`. -/
abbrev FB : MField := ⟨KB, Secp256k1.p, KB_p, KB_valid, KB_R2, by decide⟩

/-- `RepB` is `MField.Rep` at `FB`. -/
theorem repB_iff {a : L4} {x : Fp} : RepB a x ↔ FB.Rep a x := Iff.rfl

/-! ## The field operations on representations -/

namespace RepB
variable {a b : L4} {x y : Fp}

theorem mul (ha : RepB a x) (hb : RepB b y) : RepB (Mont.mul KB a b) (x * y) :=
  MField.Rep.mul (F := FB) ha hb

theorem add (ha : RepB a x) (hb : RepB b y) : RepB (Mont.add KB a b) (x + y) :=
  MField.Rep.add (F := FB) ha hb

theorem sub (ha : RepB a x) (hb : RepB b y) : RepB (Mont.sub KB a b) (x - y) :=
  MField.Rep.sub (F := FB) ha hb

theorem zero : RepB Mont.zero 0 := MField.Rep.zero (F := FB)

theorem one : RepB (Mont.new KB 1) 1 := MField.Rep.one (F := FB)

theorem isZero (ha : RepB a x) : Mont.isZero a = decide (x = 0) := MField.Rep.isZero (F := FB) ha

end RepB

/-- The curve over `Fp`, in Jacobian coordinates. -/
abbrev W : Jacobian Fp := Secp256k1.Spec.curve.toJacobian

/-- Three Montgomery triples represent the Jacobian triple `![x, y, z]`. -/
def RepP (P : Point_Mont_Base) (x y z : Fp) : Prop :=
  ∃ a b c, P = ⟨toB a, toB b, toB c⟩ ∧ RepB a x ∧ RepB b y ∧ RepB c z

/-! ## The exported point methods are pure -/

/-- The word form of a triple of limbs, as `Point<Mont<Base>>`. -/
def toBP (P : P3) : Point_Mont_Base := ⟨toB P.x, toB P.y, toB P.z⟩

@[simp] theorem toBP_x (P : P3) : (toBP P).x = toB P.x := rfl
@[simp] theorem toBP_y (P : P3) : (toBP P).y = toB P.y := rfl
@[simp] theorem toBP_z (P : P3) : (toBP P).z = toB P.z := rfl

theorem toBP_mk (a b c : L4) : toBP ⟨a, b, c⟩ = ⟨toB a, toB b, toB c⟩ := rfl

theorem RepP.of {P : P3} {x y z : Fp} (h : FB.RepP P x y z) : RepP (toBP P) x y z :=
  ⟨_, _, _, rfl, h.1, h.2.1, h.2.2⟩

theorem infinity_eq : Point_infinity_Mont_Base = pure ⟨toB (Mont.new KB 1), toB (Mont.new KB 1), toB Mont.zero⟩ := by
  simp only [Point_infinity_Mont_Base, one_Base, zero_Base, pure_bind]

theorem infinity_rep : RepP ⟨toB (Mont.new KB 1), toB (Mont.new KB 1), toB Mont.zero⟩ 1 1 0 :=
  ⟨_, _, _, rfl, RepB.one, RepB.one, RepB.zero⟩

theorem is_infinity_eq (a b c : L4) :
    Point_is_infinity_Mont_Base ⟨toB a, toB b, toB c⟩ = pure (Mont.isZero c) := by
  simp only [Point_is_infinity_Mont_Base, is_zero_Base, pure_bind]

theorem affine_eq (a b : L4) :
    Point_affine_Mont_Base (toB a) (toB b) = pure ⟨toB a, toB b, toB (Mont.new KB 1)⟩ := by
  simp only [Point_affine_Mont_Base, one_Base, pure_bind]

theorem point_infinity_Base : Point_infinity_Mont_Base = pure (toBP (Pt.inf KB)) := by
  simp only [infinity_eq, Pt.inf, toBP_mk]

theorem point_is_infinity_Base (P : P3) :
    Point_is_infinity_Mont_Base (toBP P) = pure (Mont.isZero P.z) := by
  simp only [Point_is_infinity_Mont_Base, toBP_z, is_zero_Base, pure_bind]

theorem point_affine_Base (a b : L4) :
    Point_affine_Mont_Base (toB a) (toB b) = pure (toBP (Pt.affine KB a b)) := by
  simp only [affine_eq, Pt.affine, toBP_mk]

theorem point_double_Base (P : P3) :
    Point_double_Mont_Base (toBP P) = pure (toBP (Pt.double KB P)) := by
  simp only [Point_double_Mont_Base, point_is_infinity_Base, toBP_x, toBP_y, toBP_z,
    is_zero_Base, square_Base, mul_Base, add_Base, sub_Base, double_Base, pure_bind,
    point_infinity_Base, Pt.double]
  split_ifs <;> simp only [toBP_mk]

theorem point_add_Base (P Q : P3) :
    Point_add_Mont_Base (toBP P) (toBP Q) = pure (toBP (Pt.add KB P Q)) := by
  simp only [Point_add_Mont_Base, point_is_infinity_Base, toBP_x, toBP_y, toBP_z,
    is_zero_Base, square_Base, mul_Base, add_Base, sub_Base, double_Base, pure_bind,
    point_infinity_Base, point_double_Base, Pt.add]
  split_ifs <;> simp only [toBP_mk]

theorem point_add_affine_Base (P : P3) (a b : L4) :
    Point_add_affine_Mont_Base (toBP P) (toB a) (toB b) = pure (toBP (Pt.addAffine KB P a b)) := by
  simp only [Point_add_affine_Mont_Base, point_is_infinity_Base, toBP_x, toBP_y, toBP_z,
    is_zero_Base, square_Base, mul_Base, add_Base, sub_Base, double_Base, pure_bind,
    point_infinity_Base, point_affine_Base, point_double_Base, Pt.addAffine]
  split_ifs <;> simp only [toBP_mk]

/-! ## The curve operations -/

/-- The point at infinity. -/
theorem toAffine_inf : Point.toAffine W ![1, 1, 0] = 0 := Pt.toAffine_inf (F := FB) (B := 7)

theorem toAffine_eq_zero_of_z {x y z : Fp} (hz : z = 0) : Point.toAffine W ![x, y, z] = 0 :=
  Pt.toAffine_eq_zero_of_z (F := FB) (B := 7) hz

/-- `Point::double`: for every nonsingular triple, a representation of a nonsingular triple
whose point is twice the point. -/
theorem Point_double_spec {P : Point_Mont_Base} {x y z : Fp} (hP : RepP P x y z)
    (hv : W.Nonsingular ![x, y, z]) :
    ∃ P' x' y' z', Point_double_Mont_Base P = pure P' ∧ RepP P' x' y' z' ∧
      W.Nonsingular ![x', y', z'] ∧
      Point.toAffine W ![x', y', z'] = Point.toAffine W ![x, y, z] + Point.toAffine W ![x, y, z] := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  obtain ⟨x', y', z', hr, hn, he⟩ :=
    Pt.double_spec (F := FB) (B := 7) (P := ⟨a, b, c⟩) cube_add_seven_ne_zero ⟨ha, hb, hc⟩ hv
  exact ⟨_, x', y', z', point_double_Base ⟨a, b, c⟩, RepP.of hr, hn, he⟩

/-- `Point::add`: for every two nonsingular triples, a representation of a nonsingular triple
whose point is the sum. -/
theorem Point_add_spec {P Q : Point_Mont_Base} {x1 y1 z1 x2 y2 z2 : Fp} (hP : RepP P x1 y1 z1)
    (hQ : RepP Q x2 y2 z2) (hv1 : W.Nonsingular ![x1, y1, z1]) (hv2 : W.Nonsingular ![x2, y2, z2]) :
    ∃ P' x' y' z', Point_add_Mont_Base P Q = pure P' ∧ RepP P' x' y' z' ∧
      W.Nonsingular ![x', y', z'] ∧
      Point.toAffine W ![x', y', z'] = Point.toAffine W ![x1, y1, z1] + Point.toAffine W ![x2, y2, z2] := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  obtain ⟨d, e, f, rfl, hd, he, hf⟩ := hQ
  obtain ⟨x', y', z', hr, hn, haff⟩ := Pt.add_spec (F := FB) (B := 7) (P := ⟨a, b, c⟩) (Q := ⟨d, e, f⟩)
    cube_add_seven_ne_zero ⟨ha, hb, hc⟩ ⟨hd, he, hf⟩ hv1 hv2
  exact ⟨_, x', y', z', point_add_Base ⟨a, b, c⟩ ⟨d, e, f⟩, RepP.of hr, hn, haff⟩

/-- `Point::add_affine`: for a nonsingular triple and an affine point of the curve, a
representation of a nonsingular triple whose point is the sum, for all inputs, equal and
opposite points included. -/
theorem Point_add_affine_spec {P : Point_Mont_Base} {a2 b2 : L4} {x1 y1 z1 x2 y2 : Fp}
    (hP : RepP P x1 y1 z1) (ha2 : RepB a2 x2) (hb2 : RepB b2 y2)
    (hv1 : W.Nonsingular ![x1, y1, z1]) (hv2 : W.Nonsingular ![x2, y2, 1]) :
    ∃ P' x' y' z', Point_add_affine_Mont_Base P (toB a2) (toB b2) = pure P' ∧ RepP P' x' y' z' ∧
      W.Nonsingular ![x', y', z'] ∧
      Point.toAffine W ![x', y', z'] = Point.toAffine W ![x1, y1, z1] + Point.toAffine W ![x2, y2, 1] := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  obtain ⟨x', y', z', hr, hn, haff⟩ := Pt.addAffine_spec (F := FB) (B := 7) (P := ⟨a, b, c⟩)
    cube_add_seven_ne_zero ⟨ha, hb, hc⟩ ha2 hb2 hv1 hv2
  exact ⟨_, x', y', z', point_add_affine_Base ⟨a, b, c⟩ a2 b2, RepP.of hr, hn, haff⟩

/-- `Point::to_affine`, partial (through the inversion): every run diverges or returns, the
world unchanged, representations of `x / z ^ 2` and `y / z ^ 3` (both `0` for `z = 0`); for a
nonsingular triple with `z ≠ 0` these are its affine coordinates. -/
theorem Point_to_affine_spec {P : Point_Mont_Base} {x y z : Fp} (hP : RepP P x y z)
    (env : Env) (w : World) :
    (Point_to_affine_Mont_Base P).exec env w = none ∨
      ∃ c1 c2, (Point_to_affine_Mont_Base P).exec env w = some (.ok ((toB c1, toB c2), w)) ∧
        RepB c1 (x * (z⁻¹ * z⁻¹)) ∧ RepB c2 (y * (z⁻¹ * z⁻¹ * z⁻¹)) := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  simp only [Point_to_affine_Mont_Base]
  rw [Fe.M.exec_bind]
  rcases Mont_inverse_Base_spec hc env w with h | ⟨i, h, hi⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    simp only [square_Base, mul_Base, pure_bind, Fe.M.exec_pure]
    obtain ⟨h1, h2⟩ := Pt.toAffineWith_rep (F := FB) (P := ⟨a, b, c⟩) ⟨ha, hb, hc⟩ hi
    simp only [Pt.toAffineWith] at h1 h2
    exact Or.inr ⟨_, _, rfl, h1, h2⟩

/-- On a nonsingular triple with `z ≠ 0`, those are the affine coordinates of its point. -/
theorem toAffine_some {x y z : Fp} (hv : W.Nonsingular ![x, y, z]) (hz : z ≠ 0) :
    ∃ h, Point.toAffine W ![x, y, z] = .some (x * (z⁻¹ * z⁻¹)) (y * (z⁻¹ * z⁻¹ * z⁻¹)) h :=
  Pt.toAffine_some (F := FB) (B := 7) hv hz

end FeProofs.Ecrecover
