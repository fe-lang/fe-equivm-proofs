import FeProofs.Precompiles.Field.MField
import Ethereum.Weierstrass.Curve
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-!
# Precompiles: the curve operations

`bn254_curve.fe`'s `Point<F>` in Jacobian coordinates, for every Montgomery field `F`: the point
methods as pure functions of the modulus on triples of four limbs (`P3`, `Pt.double`, `Pt.add`,
`Pt.addAffine`, …), following the Fe code step by step, and what they compute on the short
Weierstrass curve `y² = x³ + B` over `ZMod q` (`Jac q B`), as Mathlib's Jacobian points.  Each
contract shows its exported copies are `pure` of these at its modulus, and instantiates the
results: secp256k1 at `B = 7`, BN254 at `B = 3`.

Three representations represent a Jacobian triple (`MField.RepP`).  `double`, `add` and
`add_affine` handle every exceptional case in the code (a point at infinity, `y = 0`, equal or
opposite points), so each is proved for all nonsingular inputs: the output represents a
nonsingular triple whose affine point is the sum (`Pt.double_spec`, `Pt.add_spec`,
`Pt.addAffine_spec`).  `double` returns infinity for `y = 0` without the tangent's slope, which
is right only when no point of the curve has `y = 0`: the results assume that `x ^ 3 + B` has
no root, which each curve discharges.
-/

open WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Precompiles

/-- Three coordinates of four limbs each: the fields of `Point<Mont<M>>`. -/
structure P3 where
  x : L4
  y : L4
  z : L4

namespace Pt

open Mont

variable (K : Modulus)

/-- `Point::infinity`: `(1, 1, 0)`. -/
def inf : P3 := ⟨new K 1, new K 1, zero⟩

/-- `Point::affine`: `(x, y, 1)`. -/
def affine (a b : L4) : P3 := ⟨a, b, new K 1⟩

/-- `Point::double`, `dbl-2009-l`: infinity for infinity and for `y = 0`. -/
def double (P : P3) : P3 :=
  if isZero P.z then inf K
  else if isZero P.y then inf K
  else
    let a := mul K P.x P.x
    let b := mul K P.y P.y
    let c := mul K b b
    let t := add K P.x b
    let s := sub K (sub K (mul K t t) a) c
    let d := add K s s
    let e := add K (add K a a) a
    let x3 := sub K (mul K e e) (add K d d)
    let c2 := add K c c
    let c4 := add K c2 c2
    let y3 := sub K (mul K e (sub K d x3)) (add K c4 c4)
    let yz := mul K P.y P.z
    ⟨x3, y3, add K yz yz⟩

/-- `Point::add`, `add-2007-bl`, with `double` for equal points and infinity for opposite ones. -/
def add (P Q : P3) : P3 :=
  if isZero P.z then Q
  else if isZero Q.z then P
  else
    let z1z1 := mul K P.z P.z
    let z2z2 := mul K Q.z Q.z
    let u1 := mul K P.x z2z2
    let u2 := mul K Q.x z1z1
    let s1 := mul K (mul K P.y Q.z) z2z2
    let s2 := mul K (mul K Q.y P.z) z1z1
    let h := sub K u2 u1
    let r := Mont.add K (sub K s2 s1) (sub K s2 s1)
    if isZero h then (if isZero r then double K P else inf K)
    else
      let h2 := Mont.add K h h
      let i := mul K h2 h2
      let j := mul K h i
      let v := mul K u1 i
      let x3 := sub K (sub K (mul K r r) j) (Mont.add K v v)
      let sj := mul K s1 j
      let y3 := sub K (mul K r (sub K v x3)) (Mont.add K sj sj)
      let zz := sub K (sub K (mul K (Mont.add K P.z Q.z) (Mont.add K P.z Q.z)) z1z1) z2z2
      ⟨x3, y3, mul K zz h⟩

/-- `Point::add_affine`, `madd-2007-bl`: the sum with the affine point `(a, b)`. -/
def addAffine (P : P3) (a b : L4) : P3 :=
  if isZero P.z then affine K a b
  else
    let z1z1 := mul K P.z P.z
    let u2 := mul K a z1z1
    let s2 := mul K (mul K b P.z) z1z1
    let h := sub K u2 P.x
    let r := Mont.add K (sub K s2 P.y) (sub K s2 P.y)
    if isZero h then (if isZero r then double K P else inf K)
    else
      let hh := mul K h h
      let i := Mont.add K (Mont.add K hh hh) (Mont.add K hh hh)
      let j := mul K h i
      let v := mul K P.x i
      let x3 := sub K (sub K (mul K r r) j) (Mont.add K v v)
      let yj := mul K P.y j
      let y3 := sub K (mul K r (sub K v x3)) (Mont.add K yj yj)
      ⟨x3, y3, sub K (sub K (mul K (Mont.add K P.z h) (Mont.add K P.z h)) z1z1) hh⟩

/-- `Point::to_affine` after the inversion: `(x c², y c³)` for `c` the inverse of `z`. -/
def toAffineWith (P : P3) (c : L4) : L4 × L4 :=
  (mul K P.x (mul K c c), mul K P.y (mul K (mul K c c) c))

end Pt

/-- The curve `y² = x³ + B` over `ZMod q`, in Jacobian coordinates. -/
abbrev Jac (q : ℕ) (B : ZMod q) : Jacobian (ZMod q) := (Ethereum.Weierstrass.short q B).toJacobian

/-- Three triples of limbs represent the Jacobian triple `![x, y, z]`. -/
def MField.RepP (F : MField) (P : P3) (x y z : ZMod F.q) : Prop :=
  F.Rep P.x x ∧ F.Rep P.y y ∧ F.Rep P.z z

namespace Pt

variable {F : MField} [Fact F.q.Prime] {B : ZMod F.q}

theorem inf_rep : F.RepP (inf F.K) 1 1 0 := by
  simp only [MField.RepP, inf]
  exact ⟨MField.Rep.one, MField.Rep.one, MField.Rep.zero⟩

theorem affine_rep {a b : L4} {x y : ZMod F.q} (ha : F.Rep a x) (hb : F.Rep b y) :
    F.RepP (affine F.K a b) x y 1 := by
  simp only [MField.RepP, affine]
  exact ⟨ha, hb, MField.Rep.one⟩

/-- The point at infinity. -/
theorem toAffine_inf : Point.toAffine (Jac F.q B) ![1, 1, 0] = 0 :=
  Point.toAffine_of_Z_eq_zero (by simp)

theorem toAffine_eq_zero_of_z {x y z : ZMod F.q} (hz : z = 0) : Point.toAffine (Jac F.q B) ![x, y, z] = 0 :=
  Point.toAffine_of_Z_eq_zero (by simpa using hz)

theorem equation_iff' (v : Fin 3 → ZMod F.q) : (Jac F.q B).Equation v ↔ v 1 ^ 2 = v 0 ^ 3 + B * v 2 ^ 6 := by
  rw [Jacobian.equation_iff]
  simp [Ethereum.Weierstrass.short, sub_eq_zero]

/-- No nonsingular point has `y = 0` and `z ≠ 0` when `x ^ 3 + B` has no root. -/
theorem y_ne_zero (hB : ∀ x : ZMod F.q, x ^ 3 + B ≠ 0) {v : Fin 3 → ZMod F.q} (hv : (Jac F.q B).Equation v)
    (hz : v 2 ≠ 0) : v 1 ≠ 0 := by
  intro hy
  rw [equation_iff', hy] at hv
  apply hB (v 0 / v 2 ^ 2)
  field_simp
  linear_combination -hv

theorem two_ne_zero' : (2 : ZMod F.q) ≠ 0 := by
  have hp : F.q.Prime := Fact.out
  have hodd : F.q % 2 = 1 := F.p_eq ▸ F.K.p_odd F.valid
  have h2 : 2 < F.q := by have := hp.two_le; omega
  exact_mod_cast Ethereum.Weierstrass.natCast_ne_zero (k := 2) (by norm_num) h2

/-- Build the representation of a field expression from its Montgomery computation. -/
macro "rep_tac" : tactic =>
  `(tactic| repeat' (first | with_reducible assumption | with_reducible apply MField.Rep.mul |
    with_reducible apply MField.Rep.add | with_reducible apply MField.Rep.sub |
    with_reducible exact MField.Rep.one | with_reducible exact MField.Rep.zero))

theorem toAffine_two (v : Fin 3 → ZMod F.q) (hv : (Jac F.q B).Nonsingular v) :
    (Jac F.q B).Nonsingular ((Jac F.q B).dblXYZ v) ∧
      Point.toAffine (Jac F.q B) ((Jac F.q B).dblXYZ v) = Point.toAffine (Jac F.q B) v + Point.toAffine (Jac F.q B) v := by
  rw [← add_self]
  exact ⟨nonsingular_add hv hv, Point.toAffine_add hv hv⟩

/-- `double`: for every nonsingular triple, a representation of a nonsingular triple whose point
is twice the point. -/
theorem double_spec (hB : ∀ x : ZMod F.q, x ^ 3 + B ≠ 0) {P : P3} {x y z : ZMod F.q}
    (hP : F.RepP P x y z) (hv : (Jac F.q B).Nonsingular ![x, y, z]) :
    ∃ x' y' z', F.RepP (double F.K P) x' y' z' ∧ (Jac F.q B).Nonsingular ![x', y', z'] ∧
      Point.toAffine (Jac F.q B) ![x', y', z'] = Point.toAffine (Jac F.q B) ![x, y, z] + Point.toAffine (Jac F.q B) ![x, y, z] := by
  obtain ⟨ha, hb, hc⟩ := hP
  simp only [double, hc.isZero, hb.isZero]
  split_ifs with hz hy
  · have h0 : Point.toAffine (Jac F.q B) ![x, y, z] = 0 := Point.toAffine_of_Z_eq_zero (by simpa using hz)
    exact ⟨_, _, _, inf_rep, nonsingular_zero, by rw [toAffine_inf, h0, _root_.add_zero]⟩
  · exact absurd (by simpa using hy) (y_ne_zero hB (v := ![x, y, z]) hv.1 (by simpa using hz))
  · refine ⟨(((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))))), (((x * x) + (x * x) + (x * x)) * ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) - (((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))))))) - ((((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))) + (((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))))), (y * z + y * z), ⟨by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have e : (![(((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))))), (((x * x) + (x * x) + (x * x)) * ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) - (((x * x) + (x * x) + (x * x)) * ((x * x) + (x * x) + (x * x)) - ((((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y)))) + (((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))) + ((x + (y * y)) * (x + (y * y)) - (x * x) - ((y * y) * (y * y))))))) - ((((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))) + (((y * y) * (y * y)) + ((y * y) * (y * y)) + (((y * y) * (y * y)) + ((y * y) * (y * y)))))), (y * z + y * z)] : Fin 3 → ZMod F.q) = (Jac F.q B).dblXYZ ![x, y, z] := by
      ext i
      fin_cases i <;>
        simp [dblXYZ, dblX, dblY, dblZ, negDblY, dblU_eq, negY,
          Ethereum.Weierstrass.short] <;> ring
    rw [e]
    exact toAffine_two _ hv

/-- `add-2007-bl` is twice the classical sum, a unit multiple of Mathlib's `addXYZ`. -/
theorem add_formula {x1 y1 z1 x2 y2 z2 : ZMod F.q} (h1 : (Jac F.q B).Equation ![x1, y1, z1])
    (h2 : (Jac F.q B).Equation ![x2, y2, z2]) :
    (![(((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))))))) - (((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((z1 + z2) * (z1 + z2) - (z1 * z1) - (z2 * z2)) * ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))] : Fin 3 → ZMod F.q) = (-(2 * (z1 * z2))) • (Jac F.q B).addXYZ ![x1, y1, z1] ![x2, y2, z2] := by
  rw [smul_fin3]
  have hX := addX_eq' h1 h2
  have hY := negAddY_eq' (W' := Jac F.q B) ![x1, y1, z1] ![x2, y2, z2]
  simp only [addXYZ, addY, negY_eq, addZ] at hX hY ⊢
  ext i
  fin_cases i <;> simp [Ethereum.Weierstrass.short] at hX hY ⊢
  · linear_combination -4 * hX
  · linear_combination -8 * hY - 8 * (y1 * z2 ^ 3 - y2 * z1 ^ 3) * hX
  · ring

/-- `add`: for every two nonsingular triples, a representation of a nonsingular triple whose
point is the sum. -/
theorem add_spec (hB : ∀ x : ZMod F.q, x ^ 3 + B ≠ 0) {P Q : P3} {x1 y1 z1 x2 y2 z2 : ZMod F.q}
    (hP : F.RepP P x1 y1 z1) (hQ : F.RepP Q x2 y2 z2) (hv1 : (Jac F.q B).Nonsingular ![x1, y1, z1])
    (hv2 : (Jac F.q B).Nonsingular ![x2, y2, z2]) :
    ∃ x' y' z', F.RepP (add F.K P Q) x' y' z' ∧ (Jac F.q B).Nonsingular ![x', y', z'] ∧
      Point.toAffine (Jac F.q B) ![x', y', z'] =
        Point.toAffine (Jac F.q B) ![x1, y1, z1] + Point.toAffine (Jac F.q B) ![x2, y2, z2] := by
  obtain ⟨ha, hb, hc⟩ := hP
  obtain ⟨hd, he, hf⟩ := hQ
  simp only [add, hc.isZero, hf.isZero]
  by_cases hz1 : z1 = 0
  · simp only [hz1, decide_true, if_true]
    exact ⟨_, _, _, ⟨hd, he, hf⟩, hv2, by rw [toAffine_eq_zero_of_z rfl, zero_add]⟩
  simp only [hz1, decide_false, Bool.false_eq_true, if_false]
  by_cases hz2 : z2 = 0
  · simp only [hz2, decide_true, if_true]
    exact ⟨_, _, _, ⟨ha, hb, hc⟩, hv1, by rw [toAffine_eq_zero_of_z rfl, _root_.add_zero]⟩
  simp only [hz2, decide_false, Bool.false_eq_true, if_false]
  have hH := MField.Rep.isZero (F := F) (x := ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) (by rep_tac)
  have hR := MField.Rep.isZero (F := F) (x := ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2))))) (by rep_tac)
  rw [hH]
  by_cases h0 : ((x2 * (z1 * z1)) - (x1 * (z2 * z2))) = 0
  · rw [hR]
    simp only [h0, decide_true, if_true]
    have hx : ![x1, y1, z1] 0 * ![x2, y2, z2] 2 ^ 2 = ![x2, y2, z2] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; linear_combination -h0
    by_cases h1 : ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) = 0
    · simp only [h1, decide_true, if_true]
      obtain ⟨x', y', z', hrep, hns, haff⟩ := double_spec hB ⟨ha, hb, hc⟩ hv1
      have hy : ![x1, y1, z1] 1 * ![x2, y2, z2] 2 ^ 3 = ![x2, y2, z2] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        have := mul_left_cancel₀ two_ne_zero' (show (2 : ZMod F.q) * (y2 * z1 * (z1 * z1) - y1 * z2 * (z2 * z2)) = 2 * 0 by
          linear_combination h1)
        linear_combination -this
      have heq := Point.toAffine_of_equiv (W := Jac F.q B) (equiv_of_X_eq_of_Y_eq (by simpa using hz1) (by simpa using hz2) hx hy)
      exact ⟨x', y', z', hrep, hns, by rw [haff, heq]⟩
    · simp only [h1, decide_false, Bool.false_eq_true, if_false]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, z2] 2 ^ 3 ≠ ![x2, y2, z2] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        intro h; apply h1; linear_combination -2 * h
      have hsum := Point.toAffine_add (W := Jac F.q B) hv1 hv2
      rw [add_of_Y_ne hv1.1 hv2.1 (by simpa using hz1) (by simpa using hz2) hx hy,
        Point.toAffine_smul _ (isUnit_addU_of_Y_ne (by simpa using hz1) (by simpa using hz2) hy),
        Point.toAffine_of_Z_eq_zero (by simp)] at hsum
      exact ⟨_, _, _, inf_rep, nonsingular_zero, by rw [toAffine_inf, hsum]⟩
  · simp only [h0, decide_false, Bool.false_eq_true, if_false]
    refine ⟨(((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) * ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)) + ((y2 * z1 * (z1 * z1)) - (y1 * z2 * (z2 * z2)))) - (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) - (((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((x1 * (z2 * z2)) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2))))))))) - (((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))) + ((y1 * z2 * (z2 * z2))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) * ((((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))) * (((x2 * (z1 * z1)) - (x1 * (z2 * z2))) + ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))))))), (((z1 + z2) * (z1 + z2) - (z1 * z1) - (z2 * z2)) * ((x2 * (z1 * z1)) - (x1 * (z2 * z2)))), ⟨by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have hx : ![x1, y1, z1] 0 * ![x2, y2, z2] 2 ^ 2 ≠ ![x2, y2, z2] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; intro h; apply h0; linear_combination -h
    have hu : IsUnit (-(2 * (z1 * z2))) :=
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero' (mul_ne_zero hz1 hz2))).isUnit
    rw [add_formula hv1.1 hv2.1, ← add_of_not_equiv (not_equiv_of_X_ne hx)]
    exact ⟨(nonsingular_smul _ hu).mpr (nonsingular_add hv1 hv2),
      by rw [Point.toAffine_smul _ hu, Point.toAffine_add hv1 hv2]⟩

/-- `add_affine`: for a nonsingular triple and an affine point of the curve, a representation of
a nonsingular triple whose point is the sum, for all inputs, equal and opposite points
included. -/
theorem addAffine_spec (hB : ∀ x : ZMod F.q, x ^ 3 + B ≠ 0) {P : P3} {a2 b2 : L4}
    {x1 y1 z1 x2 y2 : ZMod F.q} (hP : F.RepP P x1 y1 z1) (ha2 : F.Rep a2 x2) (hb2 : F.Rep b2 y2)
    (hv1 : (Jac F.q B).Nonsingular ![x1, y1, z1]) (hv2 : (Jac F.q B).Nonsingular ![x2, y2, 1]) :
    ∃ x' y' z', F.RepP (addAffine F.K P a2 b2) x' y' z' ∧ (Jac F.q B).Nonsingular ![x', y', z'] ∧
      Point.toAffine (Jac F.q B) ![x', y', z'] =
        Point.toAffine (Jac F.q B) ![x1, y1, z1] + Point.toAffine (Jac F.q B) ![x2, y2, 1] := by
  obtain ⟨ha, hb, hc⟩ := hP
  simp only [addAffine, hc.isZero]
  by_cases hz1 : z1 = 0
  · simp only [hz1, decide_true, if_true]
    exact ⟨_, _, _, affine_rep ha2 hb2, hv2, by rw [toAffine_eq_zero_of_z rfl, zero_add]⟩
  simp only [hz1, decide_false, Bool.false_eq_true, if_false]
  have hH := MField.Rep.isZero (F := F) (x := ((x2 * (z1 * z1)) - x1)) (by rep_tac)
  have hR := MField.Rep.isZero (F := F) (x := ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1))) (by rep_tac)
  rw [hH]
  have hz2 : (1 : ZMod F.q) ≠ 0 := one_ne_zero
  by_cases h0 : ((x2 * (z1 * z1)) - x1) = 0
  · rw [hR]
    simp only [h0, decide_true, if_true]
    have hx : ![x1, y1, z1] 0 * ![x2, y2, 1] 2 ^ 2 = ![x2, y2, 1] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; linear_combination -h0
    by_cases h1 : ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) = 0
    · simp only [h1, decide_true, if_true]
      obtain ⟨x', y', z', hrep, hns, haff⟩ := double_spec hB ⟨ha, hb, hc⟩ hv1
      have hy : ![x1, y1, z1] 1 * ![x2, y2, 1] 2 ^ 3 = ![x2, y2, 1] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        have := mul_left_cancel₀ two_ne_zero' (show (2 : ZMod F.q) * (y2 * z1 * (z1 * z1) - y1) = 2 * 0 by
          linear_combination h1)
        linear_combination -this
      have heq := Point.toAffine_of_equiv (W := Jac F.q B)
        (equiv_of_X_eq_of_Y_eq (by simpa using hz1) (by simp) hx hy)
      exact ⟨x', y', z', hrep, hns, by rw [haff, heq]⟩
    · simp only [h1, decide_false, Bool.false_eq_true, if_false]
      have hy : ![x1, y1, z1] 1 * ![x2, y2, 1] 2 ^ 3 ≠ ![x2, y2, 1] 1 * ![x1, y1, z1] 2 ^ 3 := by
        simp
        intro h; apply h1; linear_combination -2 * h
      have hsum := Point.toAffine_add (W := Jac F.q B) hv1 hv2
      rw [add_of_Y_ne hv1.1 hv2.1 (by simpa using hz1) (by simp) hx hy,
        Point.toAffine_smul _ (isUnit_addU_of_Y_ne (by simpa using hz1) (by simp) hy),
        Point.toAffine_of_Z_eq_zero (by simp)] at hsum
      exact ⟨_, _, _, inf_rep, nonsingular_zero, by rw [toAffine_inf, hsum]⟩
  · simp only [h0, decide_false, Bool.false_eq_true, if_false]
    refine ⟨(((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))))))) - (y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), ((z1 + ((x2 * (z1 * z1)) - x1)) * (z1 + ((x2 * (z1 * z1)) - x1)) - (z1 * z1) - (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))), ⟨by rep_tac, by rep_tac, by rep_tac⟩, ?_⟩
    have hx : ![x1, y1, z1] 0 * ![x2, y2, 1] 2 ^ 2 ≠ ![x2, y2, 1] 0 * ![x1, y1, z1] 2 ^ 2 := by
      simp; intro h; apply h0; linear_combination -h
    have hu : IsUnit (-(2 * (z1 * 1))) :=
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero' (mul_ne_zero hz1 hz2))).isUnit
    have e : (![(((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - (((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) * ((y2 * z1 * (z1 * z1)) - y1 + ((y2 * z1 * (z1 * z1)) - y1)) - (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) - ((x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + (x1 * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))))))) - (y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))) + y1 * (((x2 * (z1 * z1)) - x1) * ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + ((((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)) + (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1))))))), ((z1 + ((x2 * (z1 * z1)) - x1)) * (z1 + ((x2 * (z1 * z1)) - x1)) - (z1 * z1) - (((x2 * (z1 * z1)) - x1) * ((x2 * (z1 * z1)) - x1)))] : Fin 3 → ZMod F.q) = ![(((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) - (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))))), (((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) * ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)) + ((y2 * z1 * (z1 * z1)) - (y1 * 1 * (1 * 1)))) - (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) - (((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((x1 * (1 * 1)) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1))))))))) - (((y1 * 1 * (1 * 1))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))) + ((y1 * 1 * (1 * 1))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) * ((((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))) * (((x2 * (z1 * z1)) - (x1 * (1 * 1))) + ((x2 * (z1 * z1)) - (x1 * (1 * 1)))))))), (((z1 + 1) * (z1 + 1) - (z1 * z1) - (1 * 1)) * ((x2 * (z1 * z1)) - (x1 * (1 * 1))))] := by
      ext i; fin_cases i <;> simp <;> ring
    rw [e, add_formula hv1.1 hv2.1, ← add_of_not_equiv (not_equiv_of_X_ne hx)]
    exact ⟨(nonsingular_smul _ hu).mpr (nonsingular_add hv1 hv2),
      by rw [Point.toAffine_smul _ hu, Point.toAffine_add hv1 hv2]⟩

omit [Fact F.q.Prime] in
/-- `to_affine` after the inversion: from a representation of `z⁻¹`, representations of
`x / z ^ 2` and `y / z ^ 3` (both `0` for `z = 0`). -/
theorem toAffineWith_rep {P : P3} {c : L4} {x y z : ZMod F.q} (hP : F.RepP P x y z)
    (hc : F.Rep c z⁻¹) :
    F.Rep (toAffineWith F.K P c).1 (x * (z⁻¹ * z⁻¹)) ∧
      F.Rep (toAffineWith F.K P c).2 (y * (z⁻¹ * z⁻¹ * z⁻¹)) := by
  obtain ⟨ha, hb, -⟩ := hP
  simp only [toAffineWith]
  exact ⟨by rep_tac, by rep_tac⟩

/-- On a nonsingular triple with `z ≠ 0`, those are the affine coordinates of its point. -/
theorem toAffine_some {x y z : ZMod F.q} (hv : (Jac F.q B).Nonsingular ![x, y, z]) (hz : z ≠ 0) :
    ∃ h, Point.toAffine (Jac F.q B) ![x, y, z] = .some (x * (z⁻¹ * z⁻¹)) (y * (z⁻¹ * z⁻¹ * z⁻¹)) h := by
  have e1 : x * (z⁻¹ * z⁻¹) = ![x, y, z] 0 / ![x, y, z] 2 ^ 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
  have e2 : y * (z⁻¹ * z⁻¹ * z⁻¹) = ![x, y, z] 1 / ![x, y, z] 2 ^ 3 := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    rfl
  rw [e1, e2]
  exact ⟨_, Point.toAffine_of_Z_ne_zero hv (by simpa using hz)⟩

end Pt

end FeProofs.Precompiles
