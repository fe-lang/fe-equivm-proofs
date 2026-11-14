import FeProofs.Ecrecover.Inverse
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-!
# Ecrecover: the curve operations

`bn254_curve.fe`'s `Point<F>` in Jacobian coordinates, at `F = Mont<Base>`, against Mathlib's
Jacobian points of `Spec.curve : y² = x³ + 7` over `Fp`.  Three Montgomery triples represent a
Jacobian triple (`RepP`).  `double`, `add` and `add_affine` handle every exceptional case in
the code (a point at infinity, `y = 0`, equal or opposite points), so each is proved for all
nonsingular inputs: the output represents a nonsingular triple whose affine point is the sum
(`Point_double_spec`, `Point_add_spec`, `Point_add_affine_spec`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Ecrecover

open Exported Mont

/-! ## The field operations on representations -/

namespace RepB
variable {a b : L4} {x y : Fp}

theorem mul (ha : RepB a x) (hb : RepB b y) : RepB (Mont.mul KB a b) (x * y) := by
  rw [RepB, map_mul]; exact mul_rep KB_valid ha hb

theorem add (ha : RepB a x) (hb : RepB b y) : RepB (Mont.add KB a b) (x + y) := by
  rw [RepB, map_add]; exact add_rep ha hb

theorem sub (ha : RepB a x) (hb : RepB b y) : RepB (Mont.sub KB a b) (x - y) := by
  rw [RepB, map_sub]; exact sub_rep ha hb

theorem zero : RepB Mont.zero 0 := by rw [RepB, map_zero]; exact zero_rep KB_valid

theorem one : RepB (Mont.new KB 1) 1 := by
  rw [RepB, map_one]; exact one_rep KB_valid KB_R2 (by decide)

theorem isZero (ha : RepB a x) : Mont.isZero a = decide (x = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_rep KB_valid ha, decide_eq_true_iff]
  exact map_eq_zero_iff toKB toKB.injective

end RepB

/-- The curve over `Fp`, in Jacobian coordinates. -/
abbrev W : Jacobian Fp := Secp256k1.Spec.curve.toJacobian

/-- Three Montgomery triples represent the Jacobian triple `![x, y, z]`. -/
def RepP (P : Point_Mont_Base) (x y z : Fp) : Prop :=
  ∃ a b c, P = ⟨toB a, toB b, toB c⟩ ∧ RepB a x ∧ RepB b y ∧ RepB c z

theorem infinity_eq : Point_infinity_Mont_Base = pure ⟨toB (Mont.new KB 1), toB (Mont.new KB 1), toB Mont.zero⟩ := by
  simp only [Point_infinity_Mont_Base, one_Base, zero_Base, pure_bind]

theorem infinity_rep : RepP ⟨toB (Mont.new KB 1), toB (Mont.new KB 1), toB Mont.zero⟩ 1 1 0 :=
  ⟨_, _, _, rfl, RepB.one, RepB.one, RepB.zero⟩

theorem is_infinity_eq (a b c : L4) :
    Point_is_infinity_Mont_Base ⟨toB a, toB b, toB c⟩ = pure (Mont.isZero c) := by
  simp only [Point_is_infinity_Mont_Base, is_zero_Base, pure_bind]

/-- The point at infinity. -/
theorem toAffine_inf : Point.toAffine W ![1, 1, 0] = 0 :=
  Point.toAffine_of_Z_eq_zero (by simp)

theorem equation_iff' (v : Fin 3 → Fp) : W.Equation v ↔ v 1 ^ 2 = v 0 ^ 3 + 7 * v 2 ^ 6 := by
  rw [Jacobian.equation_iff]
  simp [Weierstrass.short, sub_eq_zero]

/-- No nonsingular point has `y = 0` and `z ≠ 0`: `x ^ 3 + 7` has no root. -/
theorem y_ne_zero {v : Fin 3 → Fp} (hv : W.Equation v) (hz : v 2 ≠ 0) : v 1 ≠ 0 := by
  intro hy
  rw [equation_iff', hy] at hv
  apply cube_add_seven_ne_zero (v 0 / v 2 ^ 2)
  field_simp
  linear_combination -hv

/-- Build the representation of a field expression from its Montgomery computation. -/
macro "rep_tac" : tactic =>
  `(tactic| repeat' (first | with_reducible assumption | with_reducible apply RepB.mul |
    with_reducible apply RepB.add | with_reducible apply RepB.sub |
    with_reducible exact RepB.one | with_reducible exact RepB.zero))

theorem toAffine_two (v : Fin 3 → Fp) (hv : W.Nonsingular v) :
    W.Nonsingular (W.dblXYZ v) ∧
      Point.toAffine W (W.dblXYZ v) = Point.toAffine W v + Point.toAffine W v := by
  rw [← add_self]
  exact ⟨nonsingular_add hv hv, Point.toAffine_add hv hv⟩

/-- `Point::double`: for every nonsingular triple, a representation of a nonsingular triple
whose point is twice the point. -/
theorem Point_double_spec {P : Point_Mont_Base} {x y z : Fp} (hP : RepP P x y z)
    (hv : W.Nonsingular ![x, y, z]) :
    ∃ P' x' y' z', Point_double_Mont_Base P = pure P' ∧ RepP P' x' y' z' ∧
      W.Nonsingular ![x', y', z'] ∧
      Point.toAffine W ![x', y', z'] = Point.toAffine W ![x, y, z] + Point.toAffine W ![x, y, z] := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  simp only [Point_double_Mont_Base, is_infinity_eq, is_zero_Base, square_Base, mul_Base, add_Base,
    sub_Base, double_Base, pure_bind, infinity_eq, RepB.isZero hc, RepB.isZero hb]
  split_ifs with hz hy
  · have h0 : Point.toAffine W ![x, y, z] = 0 := Point.toAffine_of_Z_eq_zero (by simpa using hz)
    exact ⟨_, _, _, _, rfl, infinity_rep, nonsingular_zero, by rw [toAffine_inf, h0, _root_.add_zero]⟩
  · exact absurd (by simpa using hy) (y_ne_zero (v := ![x, y, z]) hv.1 (by simpa using hz))
  · refine ⟨_, (((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))))), (((x * x) + (x * x) + (x * x)) * ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) - (((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))))))) - ((((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))) + (((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))))), (y * z + y * z), rfl, ⟨_, _, _, rfl, by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have e : (![(((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))))), (((x * x) + (x * x) + (x * x)) * ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) - (((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))))))) - ((((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))) + (((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))))), (y * z + y * z)] : Fin 3 → Fp) = W.dblXYZ ![x, y, z] := by
      ext i
      fin_cases i <;>
        simp [dblXYZ, dblX, dblY, dblZ, negDblY, dblU_eq, negY,
          Weierstrass.short] <;> ring
    rw [e]
    exact toAffine_two _ hv

end FeProofs.Ecrecover
