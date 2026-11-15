import FeProofs.Precompiles.Bn254.Curve

/-!
# Bn254Add: ECADD on the words of the input

`add_MemBuffer` reads the input only through `word_at_MemBuffer`, at offsets `0`, `32`, `64` and
`96`.  Given the four words it returns there (the world unchanged), it diverges or returns
`addWords` of their values (`add_MemBuffer_spec`): `None` when the specification's decoding of
either point fails, otherwise `Some` of the two words that encode the sum.  `addWords_spec`
crosses to `Ethereum.BN254.Spec.add`, its 64 bytes, and `add_MemBuffer_correct` states the
result in that form.

The decoding matches `Spec.decode` case by case (`g1_point_spec`): a coordinate at or above `p`
is `None`; `(0, 0)` is infinity; any other pair, `(0, y)` and `(x, 0)` included, is the affine
point when `y² = x³ + 3` (`on_curve_spec`) and `None` otherwise.  The sum is `Pt.add`, which
covers a point plus infinity, plus itself and plus its negation, and the encoding is `(0, 0)`
for infinity and the affine coordinates otherwise (`encode_spec`), as `Spec.encode`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add Mont

/-! ## The specification on words -/

/-- The two words of the encoding of a point: `(0, 0)` for infinity. -/
def encodeWords : BN254.Spec.Point → Vector UInt256 2
  | .zero => #v[UInt256.ofNat 0, UInt256.ofNat 0]
  | .some x y _ => #v[UInt256.ofNat x.val, UInt256.ofNat y.val]

/-- ECADD on four coordinates, as `add_MemBuffer` returns it: `None` when either point does not
decode, otherwise `Some` of the encoding of the sum. -/
noncomputable def addWords (x1 y1 x2 y2 : ℕ) : Option_array_u256_2 :=
  match BN254.Spec.decode x1 y1, BN254.Spec.decode x2 y2 with
  | some P, some Q => .Some (encodeWords (P + Q))
  | _, _ => .None

theorem encodeWords_spec (R : BN254.Spec.Point) :
    ∃ a b, encodeWords R = #v[UInt256.ofNat a, UInt256.ofNat b] ∧ a < BN254.p ∧ b < BN254.p ∧
      BN254.Spec.encode R = Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b := by
  rcases R with _ | ⟨x, y, _⟩
  · exact ⟨0, 0, rfl, by decide, by decide, rfl⟩
  · exact ⟨x.val, y.val, rfl, ZMod.val_lt x, ZMod.val_lt y, rfl⟩

/-- `addWords` is `Spec.add`: `Some` of the words whose 32-byte encodings make its output. -/
theorem addWords_spec (x1 y1 x2 y2 : ℕ) :
    match addWords x1 y1 x2 y2 with
    | .Some v => ∃ a b, v = #v[UInt256.ofNat a, UInt256.ofNat b] ∧ a < BN254.p ∧ b < BN254.p ∧
        BN254.Spec.add x1 y1 x2 y2 = some (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)
    | .None => BN254.Spec.add x1 y1 x2 y2 = none := by
  unfold addWords BN254.Spec.add
  rcases BN254.Spec.decode x1 y1 with _ | P <;> rcases BN254.Spec.decode x2 y2 with _ | Q
  · rfl
  · rfl
  · rfl
  · obtain ⟨a, b, he, ha, hb, hs⟩ := encodeWords_spec (P + Q)
    exact ⟨a, b, he, ha, hb, by simp [hs]⟩

/-! ## The field methods of the decoding -/

theorem word_eq_zero_iff (x : UInt256) : x = UInt256.ofNat 0 ↔ x.toNat = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => word_eq_of_toNat (by rw [h]; rfl)⟩

theorem three_ne_zero : (3 : Fq) ≠ 0 :=
  mod_cast Weierstrass.natCast_ne_zero (k := 3) (by norm_num) (by decide)

theorem nonsingular_iff (x y : Fq) :
    BN254.Spec.curve.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 3 :=
  Weierstrass.nonsingular_iff (by decide) three_ne_zero x y

theorem fp_eq (v : UInt256) (hv : v.toNat < BN254.p) : fp v = pure (toBn (Mont.new KBn v.toNat)) := by
  rw [fp, new_Bn254Base v hv, pure_bind]

/-- `on_curve`: `y² = x³ + b`. -/
theorem on_curve_spec {a b c : L4} {x y β : Fq} (ha : RepBn a x) (hb : RepBn b y) (hc : RepBn c β) :
    on_curve_Mont_Bn254Base (toBn a) (toBn b) (toBn c) = pure (decide (y ^ 2 = x ^ 3 + β)) := by
  simp only [on_curve_Mont_Bn254Base, square_Bn254Base, mul_Bn254Base, add_Bn254Base, pure_bind,
    equals_Bn254Base, MField.Rep.equals (MField.Rep.mul hb hb)
      (MField.Rep.add (MField.Rep.mul (MField.Rep.mul ha ha) ha) hc)]
  congr 2
  apply propext
  constructor <;> intro h <;> linear_combination h

/-! ## The decoding -/

/-- `r` is the decoding `d`: `None` for `none`, otherwise a representation of a nonsingular
triple whose point is `d`'s. -/
def G1 : Option_Point_Mont_Bn254Base → Option BN254.Spec.Point → Prop
  | .None, d => d = none
  | .Some R, d => ∃ Q x y z, R = toBnP Q ∧ FBn.RepP Q x y z ∧ JBn.Nonsingular ![x, y, z] ∧
      d = some (Point.toAffine JBn ![x, y, z])

theorem modulus_toNat :
    (UInt256.ofNat 21888242871839275222246405745257275088696311157297823662689037894645226208583).toNat =
      BN254.p := toNat_lit (by decide)

/-- `g1_point` at an offset whose two words are `x` and `y` returns, with the world unchanged,
the decoding of `(x, y)`. -/
theorem g1_point_spec (input : MemBuffer) (off off32 x y : UInt256) (env : Env) (w : World)
    (hadd : checkedAdd off (UInt256.ofNat 32) = pure off32)
    (hx : (word_at_MemBuffer input off).exec env w = some (.ok (x, w)))
    (hy : (word_at_MemBuffer input off32).exec env w = some (.ok (y, w))) :
    ∃ r, (g1_point_MemBuffer input off).exec env w = some (.ok (r, w)) ∧
      G1 r (BN254.Spec.decode x.toNat y.toNat) := by
  simp only [g1_point_MemBuffer, Fe.M.exec_bind, hx, hadd, hy, MODULUS, pure_bind,
    modulus_toNat]
  unfold BN254.Spec.decode
  by_cases hxp : x.toNat < BN254.p
  swap
  · refine ⟨.None, by simp only [show BN254.p ≤ x.toNat by omega, decide_true, ite_true,
      Fe.M.exec_pure], ?_⟩
    simp only [G1]; rw [ite_eq_right (by omega)]
  by_cases hyp : y.toNat < BN254.p
  swap
  · refine ⟨.None, by simp only [show ¬ BN254.p ≤ x.toNat by omega, show BN254.p ≤ y.toNat by omega,
      decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false, Fe.M.exec_pure], ?_⟩
    simp only [G1]; rw [ite_eq_right (by omega)]
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
    exact ⟨_, rfl, Pt.inf KBn, 1, 1, 0, rfl, Pt.inf_rep, nonsingular_zero,
      by rw [Pt.toAffine_inf (F := FBn) (B := 3)]; rfl⟩
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
    have hj := (nonsingular_some (W' := JBn) _ _).mpr hns
    rw [ite_eq_left hoc, dite_eq_left hns, Fe.M.exec_pure]
    exact ⟨_, rfl, _, _, _, _, rfl, Pt.affine_rep hrx hry, hj, by rw [Point.toAffine_some hj]⟩
  · rw [ite_eq_right hoc, dite_eq_right (fun h => hoc ((nonsingular_iff _ _).mp h)), Fe.M.exec_pure]
    exact ⟨_, rfl, rfl⟩

/-! ## The encoding and the sum -/

/-- `encode` of a representation of a nonsingular triple: diverges (in the inversion) or
returns, with the world unchanged, the encoding of its point. -/
theorem encode_spec {P : P3} {x y z : Fq} (hP : FBn.RepP P x y z)
    (hv : JBn.Nonsingular ![x, y, z]) (env : Env) (w : World) :
    (encode (toBnP P)).exec env w = none ∨
      (encode (toBnP P)).exec env w = some (.ok (encodeWords (Point.toAffine JBn ![x, y, z]), w)) := by
  simp only [encode, point_is_infinity_Bn254Base, pure_bind, MField.Rep.isZero hP.2.2]
  by_cases hz : z = 0
  · right
    simp only [hz, decide_true, ite_true, Fe.M.exec_pure]
    rw [Pt.toAffine_eq_zero_of_z (F := FBn) (B := 3) rfl]
    rfl
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    rw [Fe.M.exec_bind]
    rcases Point_to_affine_Bn254Base_spec hP env w with h | ⟨c, h, hc⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; right
      obtain ⟨h1, h2⟩ := Pt.toAffineWith_rep hP hc
      simp only [fp_value, value_Bn254Base, pure_bind, Fe.M.exec_pure]
      rw [MField.Rep.value h1, MField.Rep.value h2]
      obtain ⟨_, ha⟩ := Pt.toAffine_some (F := FBn) (B := 3) hv hz
      rw [ha]
      rfl

theorem checkedAdd_0_32 : checkedAdd (UInt256.ofNat 0) (UInt256.ofNat 32) = pure (UInt256.ofNat 32) := by
  unfold checkedAdd
  rw [ite_eq_right (by rw [toNat_lit (by decide), toNat_lit (by decide)]; decide)]
  rfl

theorem checkedAdd_64_32 :
    checkedAdd (UInt256.ofNat 64) (UInt256.ofNat 32) = pure (UInt256.ofNat 96) := by
  unfold checkedAdd
  rw [ite_eq_right (by rw [toNat_lit (by decide), toNat_lit (by decide)]; decide)]
  rfl

/-- ECADD on the input buffer.  Given the words `word_at` returns at offsets `0`, `32`, `64` and
`96`, the world unchanged, `add_MemBuffer` diverges (in the inversion of `encode`) or returns,
with the world unchanged, `addWords` of their values. -/
theorem add_MemBuffer_spec (input : MemBuffer) (x1 y1 x2 y2 : UInt256) (env : Env) (w : World)
    (h0 : (word_at_MemBuffer input (UInt256.ofNat 0)).exec env w = some (.ok (x1, w)))
    (h32 : (word_at_MemBuffer input (UInt256.ofNat 32)).exec env w = some (.ok (y1, w)))
    (h64 : (word_at_MemBuffer input (UInt256.ofNat 64)).exec env w = some (.ok (x2, w)))
    (h96 : (word_at_MemBuffer input (UInt256.ofNat 96)).exec env w = some (.ok (y2, w))) :
    (add_MemBuffer input).exec env w = none ∨
      (add_MemBuffer input).exec env w =
        some (.ok (addWords x1.toNat y1.toNat x2.toNat y2.toNat, w)) := by
  obtain ⟨r1, e1, g1⟩ := g1_point_spec input _ _ x1 y1 env w checkedAdd_0_32 h0 h32
  obtain ⟨r2, e2, g2⟩ := g1_point_spec input _ _ x2 y2 env w checkedAdd_64_32 h64 h96
  unfold add_MemBuffer addWords
  simp only [Fe.M.exec_bind, e1, e2]
  rcases r2 with _ | R2
  · right
    simp only [G1] at g2
    rw [g2]
    rcases BN254.Spec.decode x1.toNat y1.toNat <;> rfl
  rcases r1 with _ | R1
  · right
    simp only [G1] at g1
    rw [g1]
    rfl
  obtain ⟨Q1, a1, b1, c1, rfl, hr1, hv1, hd1⟩ := g1
  obtain ⟨Q2, a2, b2, c2, rfl, hr2, hv2, hd2⟩ := g2
  obtain ⟨x', y', z', hr, hn, haff⟩ :=
    Pt.add_spec (F := FBn) (B := 3) cube_add_three_ne_zero hr1 hr2 hv1 hv2
  simp only [Option_Point_Mont_Bn254Base.Some_0, point_add_Bn254Base, pure_bind, hd1, hd2]
  rw [Fe.M.exec_bind]
  rcases encode_spec hr hn env w with h | h
  · rw [h]; exact Or.inl rfl
  · rw [h, haff]
    exact Or.inr rfl

/-- ECADD on the input buffer against `Spec.add`: diverges, or returns with the world unchanged
`Some` of two words below `p` whose 32-byte encodings make `Spec.add`'s output, or `None` exactly
when `Spec.add` fails. -/
theorem add_MemBuffer_correct (input : MemBuffer) (x1 y1 x2 y2 : UInt256) (env : Env) (w : World)
    (h0 : (word_at_MemBuffer input (UInt256.ofNat 0)).exec env w = some (.ok (x1, w)))
    (h32 : (word_at_MemBuffer input (UInt256.ofNat 32)).exec env w = some (.ok (y1, w)))
    (h64 : (word_at_MemBuffer input (UInt256.ofNat 64)).exec env w = some (.ok (x2, w)))
    (h96 : (word_at_MemBuffer input (UInt256.ofNat 96)).exec env w = some (.ok (y2, w))) :
    (add_MemBuffer input).exec env w = none ∨
      ∃ r, (add_MemBuffer input).exec env w = some (.ok (r, w)) ∧
        match r with
        | .Some v => ∃ a b, v = #v[UInt256.ofNat a, UInt256.ofNat b] ∧ a < BN254.p ∧
            b < BN254.p ∧ BN254.Spec.add x1.toNat y1.toNat x2.toNat y2.toNat =
              some (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)
        | .None => BN254.Spec.add x1.toNat y1.toNat x2.toNat y2.toNat = none := by
  rcases add_MemBuffer_spec input x1 y1 x2 y2 env w h0 h32 h64 h96 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h, addWords_spec _ _ _ _⟩

end FeProofs.Bn254Add
