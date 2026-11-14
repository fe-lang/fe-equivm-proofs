import FeProofs.Precompiles.Field.Pow

/-!
# Precompiles: a Montgomery modulus as a field

`MontCorrect.lean` states the Montgomery arithmetic over `ZMod K.p`, the integers modulo what
the limbs of `K` denote.  A specification names its field by its own prime `q`: `MField` packs a
modulus `K` with `K.p = q` and the facts about its constants that `MontCorrect.lean` asks for,
and `F.Rep a x` is `Rep K a` of `x : ZMod q` carried along `ZMod.ringEquivCongr`.  The operations
of `MontPure.lean` compute the field operations of `ZMod q` on it (`MField.Rep.mul` and the
rest), so each curve states its exported methods once, and the curve layer works over `ZMod q`.
-/

namespace FeProofs.Precompiles

/-- A Montgomery modulus `K` whose limbs denote `q`, with the facts `MontCorrect.lean` asks of
its constants. -/
structure MField where
  K : Modulus
  q : ℕ
  p_eq : K.p = q
  valid : K.Valid
  R2_eq : K.R2 = 2 ^ 512 % K.p
  one_lt : 1 < q

namespace MField

variable (F : MField)

/-- `ZMod q` is the ring the representations of `K` denote. -/
def toK : ZMod F.q ≃+* ZMod F.K.p := ZMod.ringEquivCongr F.p_eq.symm

/-- Four limbs represent `x : ZMod q`. -/
def Rep (a : L4) (x : ZMod F.q) : Prop := Mont.Rep F.K a (F.toK x)

theorem one_lt_p : 1 < F.K.p := F.p_eq ▸ F.one_lt

variable {F} {a b : L4} {x y : ZMod F.q}

theorem Rep.mul (ha : F.Rep a x) (hb : F.Rep b y) : F.Rep (Mont.mul F.K a b) (x * y) := by
  rw [Rep, map_mul]; exact Mont.mul_rep F.valid ha hb

theorem Rep.add (ha : F.Rep a x) (hb : F.Rep b y) : F.Rep (Mont.add F.K a b) (x + y) := by
  rw [Rep, map_add]; exact Mont.add_rep ha hb

theorem Rep.sub (ha : F.Rep a x) (hb : F.Rep b y) : F.Rep (Mont.sub F.K a b) (x - y) := by
  rw [Rep, map_sub]; exact Mont.sub_rep ha hb

theorem Rep.neg (ha : F.Rep a x) : F.Rep (Mont.sub F.K Mont.zero a) (-x) := by
  rw [Rep, map_neg]; exact Mont.neg_rep F.valid ha

theorem Rep.zero : F.Rep Mont.zero 0 := by rw [Rep, map_zero]; exact Mont.zero_rep F.valid

theorem Rep.one : F.Rep (Mont.new F.K 1) 1 := by
  rw [Rep, map_one]; exact Mont.one_rep F.valid F.R2_eq F.one_lt_p

/-- `new v` represents `v`, for `v < q`. -/
theorem Rep.new {v : ℕ} (hv : v < F.q) : F.Rep (Mont.new F.K v) v := by
  rw [Rep, map_natCast]; exact Mont.new_rep F.valid F.R2_eq (F.p_eq ▸ hv)

theorem Rep.pow (ha : F.Rep a x) {e : ℕ} (he : e < 2 ^ 256) : F.Rep (Mont.pow F.K a e) (x ^ e) := by
  rw [Rep, map_pow]; exact Mont.pow_rep F.valid F.R2_eq F.one_lt_p ha he

/-- `value` is the canonical integer of the element represented. -/
theorem Rep.value (ha : F.Rep a x) : Mont.value F.K a = x.val := by
  obtain ⟨hv, hx⟩ := Mont.value_rep F.valid ha
  rw [← ZMod.ringEquivCongr_val F.p_eq.symm x]
  change _ = (F.toK x).val
  rw [← hx, ZMod.val_cast_of_lt hv]

theorem Rep.isZero (ha : F.Rep a x) : Mont.isZero a = decide (x = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [Mont.isZero_rep F.valid ha, decide_eq_true_iff]
  exact map_eq_zero_iff F.toK F.toK.injective

theorem Rep.equals (ha : F.Rep a x) (hb : F.Rep b y) : Mont.equals a b = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  rw [Mont.equals_rep F.valid ha hb, decide_eq_true_iff]
  exact F.toK.injective.eq_iff

theorem Rep.val_lt (ha : F.Rep a x) : Mont.val a < F.K.p := ha.1

end MField

end FeProofs.Precompiles
