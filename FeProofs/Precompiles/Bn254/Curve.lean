import FeProofs.Precompiles.Bn254.Inverse
import FeProofs.Precompiles.Curve.Point

/-!
# Bn254Add: the curve operations

The exported point methods of `Bn254Add` are `pure` of the functions of `Curve/Point.lean` at
`KBn` (`point_double_Bn254Base` and the rest), and `Point::to_affine` is the inversion of `z`
followed by `Pt.toAffineWith` (`Point_to_affine_Bn254Base_spec`).  `Curve/Point.lean` proves
them at `FBn` against Mathlib's Jacobian points of `Spec.curve : y² = x³ + 3` over `Fq` (`JBn`),
with `cube_add_three_ne_zero` for its hypothesis that no point has `y = 0`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add Mont

/-- The curve over `Fq`, in Jacobian coordinates. -/
abbrev JBn : Jacobian Fq := BN254.Spec.curve.toJacobian

/-- The word form of a triple of limbs, as `Point<Mont<Bn254Base>>`. -/
def toBnP (P : P3) : Point_Mont_Bn254Base := ⟨toBn P.x, toBn P.y, toBn P.z⟩

@[simp] theorem toBnP_x (P : P3) : (toBnP P).x = toBn P.x := rfl
@[simp] theorem toBnP_y (P : P3) : (toBnP P).y = toBn P.y := rfl
@[simp] theorem toBnP_z (P : P3) : (toBnP P).z = toBn P.z := rfl

theorem toBnP_mk (a b c : L4) : toBnP ⟨a, b, c⟩ = ⟨toBn a, toBn b, toBn c⟩ := rfl

/-! ## The exported point methods are pure -/

theorem point_infinity_Bn254Base : Point_infinity_Mont_Bn254Base = pure (toBnP (Pt.inf KBn)) := by
  simp only [Point_infinity_Mont_Bn254Base, one_Bn254Base, zero_Bn254Base, pure_bind, Pt.inf,
    toBnP_mk]

theorem point_is_infinity_Bn254Base (P : P3) :
    Point_is_infinity_Mont_Bn254Base (toBnP P) = pure (Mont.isZero P.z) := by
  simp only [Point_is_infinity_Mont_Bn254Base, toBnP_z, is_zero_Bn254Base, pure_bind]

theorem point_affine_Bn254Base (a b : L4) :
    Point_affine_Mont_Bn254Base (toBn a) (toBn b) = pure (toBnP (Pt.affine KBn a b)) := by
  simp only [Point_affine_Mont_Bn254Base, one_Bn254Base, pure_bind, Pt.affine, toBnP_mk]

theorem point_double_Bn254Base (P : P3) :
    Point_double_Mont_Bn254Base (toBnP P) = pure (toBnP (Pt.double KBn P)) := by
  simp only [Point_double_Mont_Bn254Base, point_is_infinity_Bn254Base, toBnP_x, toBnP_y,
    toBnP_z, is_zero_Bn254Base, square_Bn254Base, mul_Bn254Base, add_Bn254Base, sub_Bn254Base,
    double_Bn254Base, pure_bind, point_infinity_Bn254Base, Pt.double]
  split_ifs <;> simp only [toBnP_mk]

theorem point_add_Bn254Base (P Q : P3) :
    Point_add_Mont_Bn254Base (toBnP P) (toBnP Q) = pure (toBnP (Pt.add KBn P Q)) := by
  simp only [Point_add_Mont_Bn254Base, point_is_infinity_Bn254Base, toBnP_x, toBnP_y, toBnP_z,
    is_zero_Bn254Base, square_Bn254Base, mul_Bn254Base, add_Bn254Base, sub_Bn254Base,
    double_Bn254Base, pure_bind, point_infinity_Bn254Base, point_double_Bn254Base, Pt.add]
  split_ifs <;> simp only [toBnP_mk]

/-- `Point::to_affine`, partial (through the inversion): every run diverges or returns, the
world unchanged, `Pt.toAffineWith` at a representation of `z⁻¹`. -/
theorem Point_to_affine_Bn254Base_spec {P : P3} {x y z : Fq} (hP : FBn.RepP P x y z)
    (env : Env) (w : World) :
    (Point_to_affine_Mont_Bn254Base (toBnP P)).exec env w = none ∨
      ∃ c, (Point_to_affine_Mont_Bn254Base (toBnP P)).exec env w =
          some (.ok ((toBn (Pt.toAffineWith KBn P c).1, toBn (Pt.toAffineWith KBn P c).2), w)) ∧
        RepBn c z⁻¹ := by
  simp only [Point_to_affine_Mont_Bn254Base, toBnP_x, toBnP_y, toBnP_z]
  rw [Fe.M.exec_bind]
  rcases Mont_inverse_Bn254Base_spec hP.2.2 env w with h | ⟨i, h, hi⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    simp only [square_Bn254Base, mul_Bn254Base, pure_bind, Fe.M.exec_pure, Pt.toAffineWith]
    exact Or.inr ⟨i, rfl, hi⟩

end FeProofs.Bn254Add
