import FeProofs.Precompiles.Secp256k1.Curve

/-!
# Ecrecover: tables as functions

`combination` keeps sixteen points and sixteen field elements in vectors it reads and writes
by index.  `tbl t` is the vector of `t 0, …, t 15`; reading and writing it at an index below
sixteen is reading and updating `t`.
-/

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

/-- The vector of sixteen values of `t`. -/
def tbl {α : Type} (t : ℕ → α) : Vector α 16 := Vector.ofFn fun i => t i

theorem tbl_get {α : Type} [Inhabited α] (t : ℕ → α) {i : ℕ} (hi : i < 16) : (tbl t)[i]! = t i := by
  simp [tbl, hi]

theorem tbl_set {α : Type} (t : ℕ → α) {i : ℕ} (hi : i < 16) (x : α) :
    (tbl t).set! i x = tbl (Function.update t i x) := by
  apply Vector.ext
  intro j hj
  simp only [tbl, Vector.set!, Vector.getElem_mk, Vector.toArray_ofFn, Array.set!,
    Vector.getElem_ofFn, Function.update]
  by_cases h : j = i
  · subst h; simp
  · simp only [h, dite_false]
    rw [Array.getElem_setIfInBounds_ne (by simpa using hj) (Ne.symm h)]
    simp

theorem tbl_replicate {α : Type} (x : α) : Vector.replicate 16 x = tbl fun _ => x := by
  apply Vector.ext; intro j hj; simp [tbl]

end FeProofs.Ecrecover

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

open Ethereum Fe Fe.EVM WeierstrassCurve WeierstrassCurve.Jacobian
open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

/-- `P` represents a nonsingular triple with `z`-coordinate `z` whose point is `A`. -/
def GoodP (P : Point_Mont_Base) (A : W.toAffine.Point) (z : Fp) : Prop :=
  ∃ x y, RepP P x y z ∧ W.Nonsingular ![x, y, z] ∧ Point.toAffine W ![x, y, z] = A

theorem GoodP.of {P : Point_Mont_Base} {x y z : Fp} (h1 : RepP P x y z)
    (h2 : W.Nonsingular ![x, y, z]) : GoodP P (Point.toAffine W ![x, y, z]) z := ⟨x, y, h1, h2, rfl⟩

theorem GoodP.double {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (h : GoodP P A z) :
    ∃ P' z', Point_double_Mont_Base P = pure P' ∧ GoodP P' (A + A) z' := by
  obtain ⟨x, y, h1, h2, rfl⟩ := h
  obtain ⟨P', x', y', z', e, r, n, a⟩ := Point_double_spec h1 h2
  exact ⟨P', z', e, x', y', r, n, a⟩

theorem GoodP.add {P Q : Point_Mont_Base} {A B : W.toAffine.Point} {z1 z2 : Fp} (hP : GoodP P A z1)
    (hQ : GoodP Q B z2) : ∃ P' z', Point_add_Mont_Base P Q = pure P' ∧ GoodP P' (A + B) z' := by
  obtain ⟨x, y, h1, h2, rfl⟩ := hP
  obtain ⟨x2, y2, h3, h4, rfl⟩ := hQ
  obtain ⟨P', x', y', z', e, r, n, a⟩ := Point_add_spec h1 h3 h2 h4
  exact ⟨P', z', e, x', y', r, n, a⟩

theorem GoodP.add_affine {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (hP : GoodP P A z)
    {a2 b2 : L4} {x2 y2 : Fp} (ha : RepB a2 x2) (hb : RepB b2 y2) (hv : W.Nonsingular ![x2, y2, 1]) :
    ∃ P' z', Point_add_affine_Mont_Base P (toB a2) (toB b2) = pure P' ∧
      GoodP P' (A + Point.toAffine W ![x2, y2, 1]) z' := by
  obtain ⟨x, y, h1, h2, rfl⟩ := hP
  obtain ⟨P', x', y', z', e, r, n, a⟩ := Point_add_affine_spec h1 ha hb h2 hv
  exact ⟨P', z', e, x', y', r, n, a⟩

theorem GoodP.infinity : GoodP ⟨toB (Mont.new KB 1), toB (Mont.new KB 1), toB Mont.zero⟩ 0 0 :=
  ⟨1, 1, infinity_rep, nonsingular_zero, toAffine_inf⟩

theorem GoodP.zero_iff {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (h : GoodP P A z) :
    z = 0 ↔ A = 0 := by
  obtain ⟨x, y, h1, h2, rfl⟩ := h
  constructor
  · intro hz; exact toAffine_eq_zero_of_z hz
  · intro hA; by_contra hz
    obtain ⟨_, e⟩ := toAffine_some h2 hz
    rw [e] at hA; exact Affine.Point.some_ne_zero _ hA

theorem GoodP.is_infinity {P : Point_Mont_Base} {A : W.toAffine.Point} {z : Fp} (h : GoodP P A z) :
    Point_is_infinity_Mont_Base P = pure (decide (A = 0)) := by
  obtain ⟨x, y, ⟨a, b, c, rfl, ha, hb, hc⟩, h2, rfl⟩ := h
  rw [is_infinity_eq, RepB.isZero hc]
  congr 2
  exact propext (GoodP.zero_iff ⟨x, y, ⟨a, b, c, rfl, ha, hb, hc⟩, h2, rfl⟩)

end FeProofs.Ecrecover
