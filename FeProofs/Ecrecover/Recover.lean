import FeProofs.Ecrecover.Combination
import Ethereum.Secp256k1.Proofs.Recover

/-!
# Ecrecover: `recover` against `Ethereum.Secp256k1.Spec.recover`

For `recovery_id ≤ 1` and `0 < r, s < n`, every run of the exported `recover` diverges (in an
inversion) or returns, with the world unchanged, the key `Spec.recover` gives
(`recover_spec`).  `keyOf` is the correspondence between `Option_PublicKey` and the
specification's `Option (ZMod p × ZMod p)`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

set_option exponentiation.threshold 512

namespace FeProofs.Ecrecover

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

/-- The exported key of the specification's result. -/
def keyOf : Option (Fp × Fp) → Option_PublicKey
  | none => .None
  | some (x, y) => .Some ⟨UInt256.ofNat x.val, UInt256.ofNat y.val⟩

/-- `-t` read as a natural number and applied to `G` is `-(t • G)`, as `n • G = 0`. -/
theorem neg_val_smul (t : Fn) :
    (-t).val • Secp256k1.Spec.G = -(t.val • Secp256k1.Spec.G) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul]
  have h : (((-t).val + t.val : ℕ) : Fn) = 0 := by push_cast; simp
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h
  rw [hk, mul_nsmul, Secp256k1.nsmul_G, nsmul_zero]

theorem assert_true : Lib.assert true = pure () := by
  simp [Lib.assert]

theorem ne_zero_word {b : ℕ} (hb : b < 2 ^ 256) (hb0 : 0 < b) : ¬ UInt256.ofNat b = ⟨0⟩ := by
  intro h
  have := congrArg UInt256.toNat h
  rw [toNat_lit hb] at this
  exact absurd this (by change b ≠ 0; omega)

theorem checkedDiv_lit {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hb0 : 0 < b) :
    checkedDiv (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a / b)) := by
  unfold checkedDiv
  rw [if_neg (ne_zero_word hb hb0)]
  congr 1
  apply word_eq_of_toNat
  change (UInt256.div _ _).toNat = _
  rw [udiv_toNat, toNat_lit ha, toNat_lit hb, toNat_lit (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem checkedRem_lit (a : UInt256) {b : ℕ} (hb : b < 2 ^ 256) (hb0 : 0 < b) :
    checkedRem a (UInt256.ofNat b) = pure (UInt256.ofNat (a.toNat % b)) := by
  unfold checkedRem
  rw [if_neg (ne_zero_word hb hb0)]
  congr 1
  apply word_eq_of_toNat
  rw [toNat_lit (lt_trans (Nat.mod_lt _ hb0) hb)]
  change (UInt256.mod a (UInt256.ofNat b)).toNat = _
  have hv : ¬ ((UInt256.ofNat b).val == 0) = true := by
    intro h; apply ne_zero_word hb hb0; simp at h
    cases hu : UInt256.ofNat b; rw [hu] at h; simp at h; rw [h]
  unfold UInt256.mod
  rw [if_neg hv]
  change a.toNat % (UInt256.ofNat b).toNat = _
  rw [toNat_lit hb]

/-! ## The field and scalar operations as pure functions on representations -/

theorem RepB.pow {a : L4} {x : Fp} (ha : RepB a x) (e : ℕ) (he : e < 2 ^ 256) :
    RepB (Mont.pow KB a e) (x ^ e) := by
  rw [RepB, map_pow]; exact Mont.pow_rep KB_valid KB_R2 (by decide) ha he

theorem RepB.equals {a b : L4} {x y : Fp} (ha : RepB a x) (hb : RepB b y) :
    Mont.equals a b = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  rw [Mont.equals_rep KB_valid ha hb, decide_eq_true_iff]
  exact toKB.injective.eq_iff

theorem RepB.value {a : L4} {x : Fp} (ha : RepB a x) : Mont.value KB a = x.val := by
  obtain ⟨hv, hx⟩ := Mont.value_rep KB_valid ha
  change Mont.value KB a = (toKB x).val
  rw [← hx, ZMod.val_cast_of_lt hv]

theorem RepB.neg {a : L4} {x : Fp} (ha : RepB a x) : RepB (Mont.sub KB Mont.zero a) (-x) := by
  simpa using RepB.sub RepB.zero ha

theorem RepO.mul {a b : L4} {x y : Fn} (ha : RepO a x) (hb : RepO b y) : RepO (Mont.mul KO a b) (x * y) := by
  rw [RepO, map_mul]; exact Mont.mul_rep KO_valid ha hb

theorem RepO.neg {a : L4} {x : Fn} (ha : RepO a x) : RepO (Mont.sub KO Mont.zero a) (-x) := by
  rw [RepO, map_neg, ← zero_sub]
  have h0 : Mont.Rep KO Mont.zero 0 := Mont.zero_rep KO_valid
  exact Mont.sub_rep h0 ha

theorem RepO.value {a : L4} {x : Fn} (ha : RepO a x) : Mont.value KO a = x.val := by
  obtain ⟨hv, hx⟩ := Mont.value_rep KO_valid ha
  change Mont.value KO a = (toKO x).val
  rw [← hx, ZMod.val_cast_of_lt hv]

theorem N_eq : N = pure (UInt256.ofNat Secp256k1.n) := rfl
theorem P_eq : P = pure (UInt256.ofNat Secp256k1.p) := rfl

theorem word_ne_zero {x : UInt256} (h : 0 < x.toNat) : (x ≠ UInt256.ofNat 0) := by
  intro hx; rw [hx, toNat_lit (by decide)] at h; omega

/-- What `recover` does once it has the point `(x, y)`. -/
def tailM (e r s : UInt256) (cx yL : L4) : FeM Option_PublicKey := do
  let v68 ← Mont_new_Order r
  let v70 ← Mont_inverse_Order v68
  let v74 ← checkedRem e (UInt256.ofNat Secp256k1.n)
  let v75 ← Mont_new_Order v74
  let v77 ← Mont_neg_Order v75
  let v80 ← Mont_mul_Order v77 v70
  let v82 ← Mont_value_Order v80
  let v84 ← Mont_new_Order s
  let v87 ← Mont_mul_Order v84 v70
  let v89 ← Mont_value_Order v87
  let v93 ← Point_affine_Mont_Base (toB cx) (toB yL)
  let v95 ← combination v82 v89 v93
  let v98 ← Point_is_infinity_Mont_Base v95
  if v98 = true then pure Option_PublicKey.None
    else do
      let v103 ← Point_to_affine_Mont_Base v95
      let v109 ← Mont_value_Base v103.1
      let v111 ← Mont_value_Base v103.2
      pure (Option_PublicKey.Some { x := v109, y := v111 })

/-- The specification's key from the point `R`. -/
noncomputable def keyFrom (e r s : ℕ) (R : Secp256k1.Spec.Point) : Option (Fp × Fp) :=
  match (((r : Fn)⁻¹ * s).val • R - ((r : Fn)⁻¹ * e).val • Secp256k1.Spec.G : Secp256k1.Spec.Point) with
  | .zero => none
  | .some x y _ => some (x, y)

theorem key_point (e r s : ℕ) (R : Secp256k1.Spec.Point) :
    ((-((e % Secp256k1.n : ℕ) : Fn)) * (r : Fn)⁻¹).val • Secp256k1.Spec.G +
      (((s : ℕ) : Fn) * (r : Fn)⁻¹).val • R =
    ((r : Fn)⁻¹ * s).val • R - ((r : Fn)⁻¹ * e).val • Secp256k1.Spec.G := by
  have h1 : -((e : ℕ) : Fn) * ((r : ℕ) : Fn)⁻¹ = -(((r : ℕ) : Fn)⁻¹ * ((e : ℕ) : Fn)) := by ring
  rw [ZMod.natCast_mod, h1, neg_val_smul, mul_comm ((s : ℕ) : Fn)]
  abel

/-- The tail of `recover`, from the point `R = (x, y)`. -/
theorem tail_spec (e r s : UInt256) (hr : r.toNat < Secp256k1.n) (hs : s.toNat < Secp256k1.n)
    {cx yL : L4} {x y : Fp} (hx : RepB cx x) (hy : RepB yL y) (hc : W.Nonsingular ![x, y, 1])
    (R : Secp256k1.Spec.Point) (hR : Point.toAffine W ![x, y, 1] = R) (env : Env) (w : World) :
    (tailM e r s cx yL).exec env w = none ∨
      (tailM e r s cx yL).exec env w = some (.ok (keyOf (keyFrom e.toNat r.toNat s.toNat R), w)) := by
  obtain ⟨cr, er, hrr⟩ := Mont_new_Order_repO r hr
  obtain ⟨ce, ee, hee⟩ := Mont_new_Order_repO (UInt256.ofNat (e.toNat % Secp256k1.n))
    (by rw [toNat_lit (lt_trans (Nat.mod_lt _ (by decide)) (by decide))]; exact Nat.mod_lt _ (by decide))
  obtain ⟨cs, es, hss⟩ := Mont_new_Order_repO s hs
  rw [toNat_lit (lt_trans (Nat.mod_lt _ (by decide)) (by decide))] at hee
  simp only [tailM, er, pure_bind]
  rw [Fe.M.exec_bind]
  rcases Mont_inverse_Order_spec hrr env w with h | ⟨ci, h, hci⟩
  · rw [h]; exact Or.inl rfl
  rw [h]
  dsimp only
  have hu := RepO.mul (RepO.neg hee) hci
  have hv := RepO.mul hss hci
  simp only [checkedRem_lit e (show Secp256k1.n < 2 ^ 256 by decide) (by decide), ee, neg_Order,
    mul_Order, es, value_Order, RepO.value hu, RepO.value hv, pure_bind, affine_eq]
  rw [Fe.M.exec_bind]
  have hg : GoodP ⟨toB cx, toB yL, toB (Mont.new KB 1)⟩ R 1 := ⟨x, y, ⟨cx, yL, _, rfl, hx, hy, RepB.one⟩, hc, hR⟩
  rcases combination_spec _ _ hg env w with h | ⟨P', z', h, hP⟩
  · rw [h]; exact Or.inl rfl
  rw [h]
  dsimp only
  rw [toNat_lit (lt_trans (ZMod.val_lt _) (by decide)), toNat_lit (lt_trans (ZMod.val_lt _) (by decide)),
    key_point] at hP
  simp only [hP.is_infinity, pure_bind]
  unfold keyFrom
  generalize hK : (((r.toNat : Fn)⁻¹ * s.toNat).val • R - ((r.toNat : Fn)⁻¹ * e.toNat).val •
    Secp256k1.Spec.G : Secp256k1.Spec.Point) = K at hP ⊢
  obtain ⟨X, Y, hrep, hns, haff⟩ := hP
  rcases K with _ | ⟨x', y', h'⟩
  · exact Or.inr rfl
  · have hne : (Affine.Point.some x' y' h' : Secp256k1.Spec.Point) ≠ 0 := Affine.Point.some_ne_zero h'
    simp only [hne, decide_false, Bool.false_eq_true, if_false]
    rw [Fe.M.exec_bind]
    have hz : z' ≠ 0 := fun h0 => hne ((GoodP.zero_iff ⟨X, Y, hrep, hns, haff⟩).mp h0)
    rcases Point_to_affine_spec hrep env w with h | ⟨c1, c2, h, h1, h2⟩
    · rw [h]; exact Or.inl rfl
    rw [h]
    dsimp only
    obtain ⟨hns', haff'⟩ := toAffine_some hns hz
    rw [haff] at haff'
    obtain ⟨rfl, rfl⟩ := (Affine.Point.some.injEq _ _ _ _ _ _).mp haff'
    simp only [Mont_value_Base_repB h1, Mont_value_Base_repB h2, pure_bind, Fe.M.exec_pure]
    exact Or.inr rfl

theorem land_one_eq (x : ℕ) (hx : x < 2 ^ 256) (v : UInt256) :
    decide (UInt256.ofNat x &&& UInt256.ofNat 1 = v) = decide (x % 2 = v.toNat) := by
  apply decide_eq_decide.mpr
  rw [show UInt256.ofNat x &&& UInt256.ofNat 1 = UInt256.ofNat (x % 2) by
    apply word_eq_of_toNat; rw [land_one_toNat, toNat_lit hx, toNat_lit (by omega)]]
  constructor
  · rintro rfl; rw [toNat_lit (by omega)]
  · intro h; apply word_eq_of_toNat; rw [toNat_lit (by omega), h]

/-- `recover` against `Ethereum.Secp256k1.Spec.recover`: for `recovery_id ≤ 1` and
`0 < r, s < n`, every run diverges or returns, the world unchanged, the key of the
specification. -/
theorem recover_spec (e v r s : UInt256) (hv : v.toNat ≤ 1) (hr0 : 0 < r.toNat)
    (hr : r.toNat < Secp256k1.n) (hs0 : 0 < s.toNat) (hs : s.toNat < Secp256k1.n) (env : Env)
    (w : World) :
    (recover e v r s).exec env w = none ∨
      (recover e v r s).exec env w =
        some (.ok (keyOf (Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat), w)) := by
  have hrp : r.toNat < Secp256k1.p := lt_trans hr (by decide)
  obtain ⟨cx, ex, hx⟩ := Mont_new_Base_repB r hrp
  obtain ⟨c7, e7, h7⟩ := Mont_new_Base_repB (UInt256.ofNat 7) (by rw [toNat_lit (by decide)]; decide)
  rw [toNat_lit (by decide)] at h7
  simp only [recover, toNat_lit (show 1 < 2 ^ 256 by decide), hv, decide_true, ne_eq,
    word_ne_zero hr0, word_ne_zero hs0, not_false_eq_true,
    N_eq, toNat_lit (show Secp256k1.n < 2 ^ 256 by decide), hr, hs, if_true, pure_bind, assert_true,
    ex, e7, square_Base, mul_Base, add_Base, P_eq,
    checkedAdd_small (show Secp256k1.p + 1 < 2 ^ 256 by decide),
    checkedDiv_lit (show Secp256k1.p + 1 < 2 ^ 256 by decide) (show 4 < 2 ^ 256 by decide) (by decide),
    pow_Base, equals_Base, toNat_lit (show (Secp256k1.p + 1) / 4 < 2 ^ 256 by decide)]
  have ha := RepB.add (RepB.mul (RepB.mul hx hx) hx) h7
  have hb := RepB.pow ha ((Secp256k1.p + 1) / 4) (by decide)
  rw [RepB.equals (RepB.mul hb hb) ha]
  unfold Secp256k1.Spec.recover
  rw [if_pos (show 0 < r.toNat ∧ r.toNat < Secp256k1.n ∧ 0 < s.toNat ∧ s.toNat < Secp256k1.n ∧
    v.toNat < 2 from ⟨hr0, hr, hs0, hs, by omega⟩)]
  generalize hxdef : ((r.toNat : ℕ) : Fp) = x at hx ha hb ⊢
  generalize hαdef : x * x * x + ((7 : ℕ) : Fp) = α at ha hb ⊢
  generalize hβdef : α ^ ((Secp256k1.p + 1) / 4) = β at hb ⊢
  have hα : α = x ^ 3 + 7 := by rw [← hαdef]; push_cast; ring
  by_cases hsq : β * β = α
  · simp only [hsq, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    have hβ2 : β ^ 2 = x ^ 3 + 7 := by rw [← hα, sq, hsq]
    obtain ⟨hR, hl⟩ := liftX_eq x β hβ2 (v := v.toNat) (by omega)
    rw [hl]
    simp only [Mont_value_Base_repB hb, pure_bind, land_one_eq _ (lt_trans (ZMod.val_lt β) (by decide))]
    generalize hy : (if β.val % 2 = v.toNat then β else -β) = y at hR hl
    have hns := (nonsingular_some (W' := W) _ _).mpr hR
    have haff := Point.toAffine_some hns
    by_cases hpar : β.val % 2 = v.toNat
    · rw [if_pos hpar] at hy
      subst hy
      simp only [hpar, decide_true, if_true]
      exact tail_spec e r s hr hs hx hb hns _ haff env w
    · rw [if_neg hpar] at hy
      subst hy
      simp only [hpar, decide_false, Bool.false_eq_true, if_false, neg_Base, pure_bind]
      exact tail_spec e r s hr hs hx (RepB.neg hb) hns _ haff env w
  · simp only [hsq, decide_false, Bool.not_false, if_true, Fe.M.exec_pure]
    have hns : ¬ IsSquare (x ^ 3 + 7) := by
      rw [← hα, ← sqrt_iff, hβdef, sq]; exact hsq
    rw [liftX_none x hns]
    exact Or.inr rfl

end FeProofs.Ecrecover
