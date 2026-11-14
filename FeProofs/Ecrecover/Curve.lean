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

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover Mont

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

/-- `add-2007-bl` is twice the classical sum, a unit multiple of Mathlib's `addXYZ`. -/
theorem add_formula {x1 y1 z1 x2 y2 z2 : Fp} (h1 : W.Equation ![x1, y1, z1])
    (h2 : W.Equation ![x2, y2, z2]) :
    (![(((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))))))) - (((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((z1 + z2) * (z1 + z2) - (z1 * z1) - (z2 * z2)) * ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))] : Fin 3 → Fp) = (-(2 * (z1 * z2))) • W.addXYZ ![x1, y1, z1] ![x2, y2, z2] := by
  rw [smul_fin3]
  have hX := addX_eq' h1 h2
  have hY := negAddY_eq' (W' := W) ![x1, y1, z1] ![x2, y2, z2]
  simp only [addXYZ, addY, negY_eq, addZ] at hX hY ⊢
  ext i
  fin_cases i <;> simp [Weierstrass.short] at hX hY ⊢
  · linear_combination -4 * hX
  · linear_combination -8 * hY - 8 * (y1 * z2 ^ 3 - y2 * z1 ^ 3) * hX
  · ring

theorem two_ne_zero' : (2 : Fp) ≠ 0 := by
  have := Secp256k1.Spec.natCast_ne_zero (k := 2) (by decide) (by decide)
  exact_mod_cast this

theorem toAffine_eq_zero_of_z {x y z : Fp} (hz : z = 0) : Point.toAffine W ![x, y, z] = 0 :=
  Point.toAffine_of_Z_eq_zero (by simpa using hz)

/-- `Point::add`: for every two nonsingular triples, a representation of a nonsingular triple
whose point is the sum. -/
theorem Point_add_spec {P Q : Point_Mont_Base} {x1 y1 z1 x2 y2 z2 : Fp} (hP : RepP P x1 y1 z1)
    (hQ : RepP Q x2 y2 z2) (hv1 : W.Nonsingular ![x1, y1, z1]) (hv2 : W.Nonsingular ![x2, y2, z2]) :
    ∃ P' x' y' z', Point_add_Mont_Base P Q = pure P' ∧ RepP P' x' y' z' ∧
      W.Nonsingular ![x', y', z'] ∧
      Point.toAffine W ![x', y', z'] = Point.toAffine W ![x1, y1, z1] + Point.toAffine W ![x2, y2, z2] := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := hP
  obtain ⟨d, e, f, rfl, hd, he, hf⟩ := hQ
  simp only [Point_add_Mont_Base, is_infinity_eq, is_zero_Base, square_Base, mul_Base, add_Base,
    sub_Base, double_Base, pure_bind, infinity_eq, RepB.isZero hc, RepB.isZero hf]
  by_cases hz1 : z1 = 0
  · simp only [hz1, decide_true, if_true]
    exact ⟨_, _, _, _, rfl, ⟨d, e, f, rfl, hd, he, hf⟩, hv2, by rw [toAffine_eq_zero_of_z rfl, zero_add]⟩
  simp only [hz1, decide_false, Bool.false_eq_true, if_false]
  by_cases hz2 : z2 = 0
  · simp only [hz2, decide_true, if_true]
    exact ⟨_, _, _, _, rfl, ⟨a, b, c, rfl, ha, hb, hc⟩, hv1,
      by rw [toAffine_eq_zero_of_z rfl, _root_.add_zero]⟩
  simp only [hz2, decide_false, Bool.false_eq_true, if_false]
  have hH := RepB.isZero (x := ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) (by rep_tac)
  have hR := RepB.isZero (x := ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2))))) (by rep_tac)
  rw [hH]
  by_cases h0 : ((x2 * (z1 * z1)) - (x1 * (z2 * z2))) = 0
  · rw [hR]
    simp only [h0, decide_true, if_true]
    have hx : ![x1, y1, z1] 0 * ![x2, y2, z2] 2 ^ 2 = ![x2, y2, z2] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; linear_combination -h0
    by_cases h1 : ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) = 0
    · simp only [h1, decide_true, if_true]
      obtain ⟨P', x', y', z', hd2, hrep, hns, haff⟩ := Point_double_spec ⟨a, b, c, rfl, ha, hb, hc⟩ hv1
      rw [hd2, pure_bind]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, z2] 2 ^ 3 = ![x2, y2, z2] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        have := mul_left_cancel₀ two_ne_zero' (show (2 : Fp) * (y2 * z1 * (z1 * z1) - y1 * z2 * (z2 * z2)) = 2 * 0 by
          linear_combination h1)
        linear_combination -this
      have heq := Point.toAffine_of_equiv (W := W) (equiv_of_X_eq_of_Y_eq (by simpa using hz1) (by simpa using hz2) hx hy)
      exact ⟨P', x', y', z', rfl, hrep, hns, by rw [haff, heq]⟩
    · simp only [h1, decide_false, Bool.false_eq_true, if_false]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, z2] 2 ^ 3 ≠ ![x2, y2, z2] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        intro h; apply h1; linear_combination -2 * h
      have hsum := Point.toAffine_add (W := W) hv1 hv2
      rw [add_of_Y_ne hv1.1 hv2.1 (by simpa using hz1) (by simpa using hz2) hx hy,
        Point.toAffine_smul _ (isUnit_addU_of_Y_ne (by simpa using hz1) (by simpa using hz2) hy),
        Point.toAffine_of_Z_eq_zero (by simp)] at hsum
      exact ⟨_, _, _, _, rfl, infinity_rep, nonsingular_zero, by rw [toAffine_inf, hsum]⟩
  · simp only [h0, decide_false, Bool.false_eq_true, if_false]
    refine ⟨_, (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))))))) - (((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((z1 + z2) * (z1 + z2) - (z1 * z1) - (z2 * z2)) * ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))), rfl, ⟨_, _, _, rfl, by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have hx : ![x1, y1, z1] 0 * ![x2, y2, z2] 2 ^ 2 ≠ ![x2, y2, z2] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; intro h; apply h0; linear_combination -h
    have hu : IsUnit (-(2 * (z1 * z2))) :=
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero' (mul_ne_zero hz1 hz2))).isUnit
    rw [add_formula hv1.1 hv2.1, ← add_of_not_equiv (not_equiv_of_X_ne hx)]
    exact ⟨(nonsingular_smul _ hu).mpr (nonsingular_add hv1 hv2),
      by rw [Point.toAffine_smul _ hu, Point.toAffine_add hv1 hv2]⟩

theorem affine_eq (a b : L4) :
    Point_affine_Mont_Base (toB a) (toB b) = pure ⟨toB a, toB b, toB (Mont.new KB 1)⟩ := by
  simp only [Point_affine_Mont_Base, one_Base, pure_bind]

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
  simp only [Point_add_affine_Mont_Base, is_infinity_eq, is_zero_Base, square_Base, mul_Base,
    add_Base, sub_Base, double_Base, pure_bind, infinity_eq, affine_eq, RepB.isZero hc]
  by_cases hz1 : z1 = 0
  · simp only [hz1, decide_true, if_true]
    exact ⟨_, _, _, _, rfl, ⟨a2, b2, _, rfl, ha2, hb2, RepB.one⟩, hv2,
      by rw [toAffine_eq_zero_of_z rfl, zero_add]⟩
  simp only [hz1, decide_false, Bool.false_eq_true, if_false]
  have hH := RepB.isZero (x := ((x2 * (z1 * z1)) - x1)) (by rep_tac)
  have hR := RepB.isZero (x := ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1))) (by rep_tac)
  rw [hH]
  have hz2 : (1 : Fp) ≠ 0 := one_ne_zero
  by_cases h0 : ((x2 * (z1 * z1)) - x1) = 0
  · rw [hR]
    simp only [h0, decide_true, if_true]
    have hx : ![x1, y1, z1] 0 * ![x2, y2, 1] 2 ^ 2 = ![x2, y2, 1] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; linear_combination -h0
    by_cases h1 : ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) = 0
    · simp only [h1, decide_true, if_true]
      obtain ⟨P', x', y', z', hd2, hrep, hns, haff⟩ := Point_double_spec ⟨a, b, c, rfl, ha, hb, hc⟩ hv1
      rw [hd2]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, 1] 2 ^ 3 = ![x2, y2, 1] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        have := mul_left_cancel₀ two_ne_zero' (show (2 : Fp) * (y2 * z1 * (z1 * z1) - y1) = 2 * 0 by
          linear_combination h1)
        linear_combination -this
      have heq := Point.toAffine_of_equiv (W := W)
        (equiv_of_X_eq_of_Y_eq (by simpa using hz1) (by simp) hx hy)
      exact ⟨P', x', y', z', rfl, hrep, hns, by rw [haff, heq]⟩
    · simp only [h1, decide_false, Bool.false_eq_true, if_false]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, 1] 2 ^ 3 ≠ ![x2, y2, 1] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        intro h; apply h1; linear_combination -2 * h
      have hsum := Point.toAffine_add (W := W) hv1 hv2
      rw [add_of_Y_ne hv1.1 hv2.1 (by simpa using hz1) (by simp) hx hy,
        Point.toAffine_smul _ (isUnit_addU_of_Y_ne (by simpa using hz1) (by simp) hy),
        Point.toAffine_of_Z_eq_zero (by simp)] at hsum
      exact ⟨_, _, _, _, rfl, infinity_rep, nonsingular_zero, by rw [toAffine_inf, hsum]⟩
  · simp only [h0, decide_false, Bool.false_eq_true, if_false]
    refine ⟨_, (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))))))) - (y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), ((z1 + ((x2 * (z1 * z1)) - x1)) * (z1 + ((x2 * (z1 * z1)) - x1)) - (z1 * z1) - (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))), rfl, ⟨_, _, _, rfl, by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have hx : ![x1, y1, z1] 0 * ![x2, y2, 1] 2 ^ 2 ≠ ![x2, y2, 1] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; intro h; apply h0; linear_combination -h
    have hu : IsUnit (-(2 * (z1 * 1))) :=
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero' (mul_ne_zero hz1 hz2))).isUnit
    have e : (![(((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))))))) - (y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), ((z1 + ((x2 * (z1 * z1)) - x1)) * (z1 + ((x2 * (z1 * z1)) - x1)) - (z1 * z1) - (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))] : Fin 3 → Fp) = ![(((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) - (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) - (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1))))))))) - (((y1 * 1 * (1 * 1))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((y1 * 1 * (1 * 1))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))))), (((z1 + 1) * (z1 + 1) - (z1 * z1) - (1 * 1)) * ((x2 * (z1 * z1)) - (x1 * (1 * 1))))] := by
      ext i; fin_cases i <;> simp <;> ring
    rw [e, add_formula hv1.1 hv2.1, ← add_of_not_equiv (not_equiv_of_X_ne hx)]
    exact ⟨(nonsingular_smul _ hu).mpr (nonsingular_add hv1 hv2),
      by rw [Point.toAffine_smul _ hu, Point.toAffine_add hv1 hv2]⟩

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
    exact Or.inr ⟨_, _, rfl, by rep_tac, by rep_tac⟩

/-- On a nonsingular triple with `z ≠ 0`, those are the affine coordinates of its point. -/
theorem toAffine_some {x y z : Fp} (hv : W.Nonsingular ![x, y, z]) (hz : z ≠ 0) :
    ∃ h, Point.toAffine W ![x, y, z] = .some (x * (z⁻¹ * z⁻¹)) (y * (z⁻¹ * z⁻¹ * z⁻¹)) h := by
  have e1 : x * (z⁻¹ * z⁻¹) = ![x, y, z] 0 / ![x, y, z] 2 ^ 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
  have e2 : y * (z⁻¹ * z⁻¹ * z⁻¹) = ![x, y, z] 1 / ![x, y, z] 2 ^ 3 := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    rfl
  rw [e1, e2]
  exact ⟨_, Point.toAffine_of_Z_ne_zero hv (by simpa using hz)⟩

end FeProofs.Ecrecover
