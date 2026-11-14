import FeProofs.Ecrecover.Pow
import Ethereum.Secp256k1.Spec
import Mathlib.FieldTheory.Finite.Basic

/-!
# Ecrecover: the two fields, and the square root

`MontCorrect.lean` states the Montgomery arithmetic over `ZMod KB.p` and `ZMod KO.p`, the
moduli its limbs denote.  This file crosses once to the fields of the specification,
`Fp = ZMod Secp256k1.p` and `Fn = ZMod Secp256k1.n`, along the ring isomorphisms `toKB` and
`toKO` that `KB_p` and `KO_p` give: `RepB a x` is `Rep KB a (toKB x)`, and each exported method
is restated on it (`Mont_mul_Base_repB` and the rest).  The curve layer works over `Fp` alone.

Then the square root `recover` takes: `p ≡ 3 (mod 4)`, so `β = α ^ ((p + 1) / 4)` has
`β ^ 2 = α` exactly when `α` is a square (`sqrt_iff`).  As `x ^ 3 + 7` has no root modulo `p`
(`cube_add_seven_ne_zero`, by a fast modular power checked by `decide`), such a `β` is not
zero, its negation has the other parity, and the code's choice between them is the point
`liftX x v` of the specification (`liftX_eq`); with no root, `liftX` is `none` (`liftX_none`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ecrecover

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover Mont

/-- The field of the curve. -/
abbrev Fp := ZMod Secp256k1.p

/-- The field of the scalars. -/
abbrev Fn := ZMod Secp256k1.n

/-- `Fp` is the field `Base`'s representations denote. -/
def toKB : Fp ≃+* ZMod KB.p := ZMod.ringEquivCongr KB_p.symm

/-- `Fn` is the field `Order`'s representations denote. -/
def toKO : Fn ≃+* ZMod KO.p := ZMod.ringEquivCongr KO_p.symm

/-- Four limbs represent `x : Fp` in `Base`. -/
def RepB (a : L4) (x : Fp) : Prop := Rep KB a (toKB x)

/-- Four limbs represent `s : Fn` in `Order`. -/
def RepO (a : L4) (s : Fn) : Prop := Rep KO a (toKO s)

instance : NeZero KB.p := ⟨by decide⟩
instance : NeZero KO.p := ⟨by decide⟩

/-! ## The exported methods on `Fp` and `Fn` -/

section
variable {a b : L4} {x y : Fp}

theorem Mont_new_Base_repB (v : UInt256) (hv : v.toNat < Secp256k1.p) :
    ∃ c, Mont_new_Base v = pure (toB c) ∧ RepB c v.toNat := by
  obtain ⟨c, h, hc⟩ := Mont_new_Base_rep v (by rw [KB_p]; exact hv)
  exact ⟨c, h, by rw [RepB, map_natCast]; exact hc⟩

theorem Mont_one_Base_repB : ∃ c, Mont_one_Base = pure (toB c) ∧ RepB c 1 := by
  obtain ⟨c, h, hc⟩ := Mont_one_Base_rep
  exact ⟨c, h, by rw [RepB, map_one]; exact hc⟩

theorem Mont_zero_Base_repB : Mont_zero_Base = pure (toB zero) ∧ RepB zero 0 := by
  rw [RepB, map_zero]; exact Mont_zero_Base_rep

theorem Mont_value_Base_repB (ha : RepB a x) :
    Mont_value_Base (toB a) = pure (UInt256.ofNat x.val) := by
  obtain ⟨v, hv, h, hx⟩ := Mont_value_Base_rep ha
  rw [h]
  congr 2
  change v = (toKB x).val
  rw [← hx, ZMod.val_cast_of_lt hv]

theorem Mont_mul_Base_repB (ha : RepB a x) (hb : RepB b y) :
    ∃ c, Mont_mul_Base (toB a) (toB b) = pure (toB c) ∧ RepB c (x * y) := by
  obtain ⟨c, h, hc⟩ := Mont_mul_Base_rep ha hb
  exact ⟨c, h, by rw [RepB, map_mul]; exact hc⟩

theorem Mont_square_Base_repB (ha : RepB a x) :
    ∃ c, Mont_square_Base (toB a) = pure (toB c) ∧ RepB c (x ^ 2) := by
  obtain ⟨c, h, hc⟩ := Mont_square_Base_rep ha
  exact ⟨c, h, by rw [RepB, map_pow]; exact hc⟩

theorem Mont_add_Base_repB (ha : RepB a x) (hb : RepB b y) :
    ∃ c, Mont_add_Base (toB a) (toB b) = pure (toB c) ∧ RepB c (x + y) := by
  obtain ⟨c, h, hc⟩ := Mont_add_Base_rep ha hb
  exact ⟨c, h, by rw [RepB, map_add]; exact hc⟩

theorem Mont_double_Base_repB (ha : RepB a x) :
    ∃ c, Mont_double_Base (toB a) = pure (toB c) ∧ RepB c (2 * x) := by
  obtain ⟨c, h, hc⟩ := Mont_double_Base_rep ha
  exact ⟨c, h, by rw [RepB, map_mul, map_ofNat]; exact hc⟩

theorem Mont_sub_Base_repB (ha : RepB a x) (hb : RepB b y) :
    ∃ c, Mont_sub_Base (toB a) (toB b) = pure (toB c) ∧ RepB c (x - y) := by
  obtain ⟨c, h, hc⟩ := Mont_sub_Base_rep ha hb
  exact ⟨c, h, by rw [RepB, map_sub]; exact hc⟩

theorem Mont_neg_Base_repB (ha : RepB a x) :
    ∃ c, Mont_neg_Base (toB a) = pure (toB c) ∧ RepB c (-x) := by
  obtain ⟨c, h, hc⟩ := Mont_neg_Base_rep ha
  exact ⟨c, h, by rw [RepB, map_neg]; exact hc⟩

theorem Mont_pow_Base_repB (ha : RepB a x) (e : UInt256) :
    ∃ c, Mont_pow_Base (toB a) e = pure (toB c) ∧ RepB c (x ^ e.toNat) :=
  ⟨_, pow_Base a e, by
    rw [RepB, map_pow]
    exact pow_rep KB_valid KB_R2 (by decide) ha e.val.isLt⟩

theorem Mont_is_zero_Base_repB (ha : RepB a x) :
    Mont_is_zero_Base (toB a) = pure (decide (x = 0)) := by
  rw [Mont_is_zero_Base_rep ha]
  exact congrArg _ (decide_eq_decide.mpr (map_eq_zero_iff toKB toKB.injective))

theorem Mont_equals_Base_repB (ha : RepB a x) (hb : RepB b y) :
    Mont_equals_Base (toB a) (toB b) = pure (decide (x = y)) := by
  rw [Mont_equals_Base_rep ha hb]
  exact congrArg _ (decide_eq_decide.mpr toKB.injective.eq_iff)

end

section
variable {a b : L4} {x y : Fn}

theorem Mont_new_Order_repO (v : UInt256) (hv : v.toNat < Secp256k1.n) :
    ∃ c, Mont_new_Order v = pure (toO c) ∧ RepO c v.toNat := by
  obtain ⟨c, h, hc⟩ := Mont_new_Order_rep v (by rw [KO_p]; exact hv)
  exact ⟨c, h, by rw [RepO, map_natCast]; exact hc⟩

theorem Mont_zero_Order_repO : Mont_zero_Order = pure (toO zero) ∧ RepO zero 0 := by
  rw [RepO, map_zero]; exact Mont_zero_Order_rep

theorem Mont_value_Order_repO (ha : RepO a x) :
    Mont_value_Order (toO a) = pure (UInt256.ofNat x.val) := by
  obtain ⟨v, hv, h, hx⟩ := Mont_value_Order_rep ha
  rw [h]
  congr 2
  change v = (toKO x).val
  rw [← hx, ZMod.val_cast_of_lt hv]

theorem Mont_mul_Order_repO (ha : RepO a x) (hb : RepO b y) :
    ∃ c, Mont_mul_Order (toO a) (toO b) = pure (toO c) ∧ RepO c (x * y) := by
  obtain ⟨c, h, hc⟩ := Mont_mul_Order_rep ha hb
  exact ⟨c, h, by rw [RepO, map_mul]; exact hc⟩

theorem Mont_sub_Order_repO (ha : RepO a x) (hb : RepO b y) :
    ∃ c, Mont_sub_Order (toO a) (toO b) = pure (toO c) ∧ RepO c (x - y) := by
  obtain ⟨c, h, hc⟩ := Mont_sub_Order_rep ha hb
  exact ⟨c, h, by rw [RepO, map_sub]; exact hc⟩

theorem Mont_neg_Order_repO (ha : RepO a x) :
    ∃ c, Mont_neg_Order (toO a) = pure (toO c) ∧ RepO c (-x) := by
  obtain ⟨c, h, hc⟩ := Mont_neg_Order_rep ha
  exact ⟨c, h, by rw [RepO, map_neg]; exact hc⟩

end

/-! ## The square root -/

/-- With `p ≡ 3 (mod 4)`, `α ^ ((p + 1) / 4)` is a square root of `α` exactly when `α` is a
square. -/
theorem sqrt_iff (α : Fp) : (α ^ ((Secp256k1.p + 1) / 4)) ^ 2 = α ↔ IsSquare α := by
  constructor
  · intro h
    exact ⟨_, by rw [← h, sq]⟩
  · rintro ⟨t, rfl⟩
    rw [← pow_mul, ← sq, ← pow_mul]
    by_cases ht : t = 0
    · subst ht
      rw [zero_pow (by decide), zero_pow (by decide)]
    · rw [show 2 * ((Secp256k1.p + 1) / 4 * 2) = (Secp256k1.p - 1) + 2 by norm_num [Secp256k1.p], pow_add,
        ZMod.pow_card_sub_one_eq_one ht, one_mul]

/-- `b ^ e mod m` by square-and-multiply over `f` bits, times `acc`. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, e, acc => powMod m f (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

theorem powMod_eq (m : ℕ) :
    ∀ f b e acc, e < 2 ^ f → (powMod m f b e acc : ZMod m) = acc * (b : ZMod m) ^ e
  | 0, b, e, acc, he => by
    obtain rfl : e = 0 := by simpa using he
    simp [powMod]
  | f + 1, b, e, acc, he => by
    rw [powMod, powMod_eq m f _ _ _ (by rw [pow_succ] at he; omega)]
    have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [if_neg (by omega)]
      conv_rhs => rw [hsplit, h]
      push_cast [ZMod.natCast_mod]
      ring
    · rw [if_pos h]
      conv_rhs => rw [hsplit, h]
      push_cast [ZMod.natCast_mod]
      ring

/-- `-7` is not a cube modulo `p`: its `(p - 1) / 3`-th power is not one. -/
theorem neg_seven_pow_ne_one :
    powMod Secp256k1.p 256 (Secp256k1.p - 7) ((Secp256k1.p - 1) / 3) 1 % Secp256k1.p ≠ 1 := by
  decide +kernel

/-- `x ^ 3 + 7` has no root modulo `p`: secp256k1 has no point of order two. -/
theorem cube_add_seven_ne_zero (x : Fp) : x ^ 3 + 7 ≠ 0 := by
  intro h
  have hx : x ≠ 0 := by
    rintro rfl
    have h7 : ((7 : ℕ) : Fp) ≠ 0 := Secp256k1.Spec.natCast_ne_zero (by decide) (by decide)
    exact h7 (by simpa using h)
  have hc : x ^ 3 = ((Secp256k1.p - 7 : ℕ) : Fp) := by
    rw [Nat.cast_sub (by decide), ZMod.natCast_self, zero_sub]
    linear_combination h
  apply neg_seven_pow_ne_one
  have hm := powMod_eq Secp256k1.p 256 (Secp256k1.p - 7) ((Secp256k1.p - 1) / 3) 1
    (by norm_num [Secp256k1.p])
  rw [← hc, ← pow_mul,
    show 3 * ((Secp256k1.p - 1) / 3) = Secp256k1.p - 1 by norm_num [Secp256k1.p],
    ZMod.pow_card_sub_one_eq_one hx, Nat.cast_one, mul_one] at hm
  have h1 : ((powMod Secp256k1.p 256 (Secp256k1.p - 7) ((Secp256k1.p - 1) / 3) 1 : ℕ) : Fp) =
      ((1 : ℕ) : Fp) := by rw [hm, Nat.cast_one]
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h1).trans
    (Nat.mod_eq_of_lt (show 1 < Secp256k1.p by decide))

/-! ## The point with a given abscissa and parity -/

open Secp256k1.Spec

theorem p_odd : Secp256k1.p % 2 = 1 := by decide

/-- Negating a nonzero element of `Fp` flips the parity of its value. -/
theorem neg_val_parity {y : Fp} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 := by
  rw [ZMod.neg_val, if_neg hy]
  have := ZMod.val_lt y
  have := p_odd
  omega

/-- When `β ^ 2 = x ^ 3 + 7`, the point `liftX x v` is `(x, β)` or `(x, -β)`, the one whose
ordinate has parity `v`: the choice `recover` makes. -/
theorem liftX_eq (x β : Fp) (hβ : β ^ 2 = x ^ 3 + 7) {v : ℕ} (hv : v < 2) :
    ∃ h, liftX x v = some (.some x (if β.val % 2 = v then β else -β) h) := by
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact cube_add_seven_ne_zero x (by rw [← hβ]; ring)
  set y := if β.val % 2 = v then β else -β with hy_def
  have hy : y ^ 2 = x ^ 3 + 7 := by rw [hy_def]; split_ifs <;> simp [hβ]
  have hpar : y.val % 2 = v := by
    rw [hy_def]
    split_ifs with h
    · exact h
    · have := neg_val_parity hβ0
      omega
  have hy0 : y ≠ 0 := by rw [hy_def]; split_ifs <;> simp [hβ0]
  -- Any ordinate of parity `v` over `x` is `y`.
  have uniq : ∀ y' : Fp, y' ^ 2 = x ^ 3 + 7 → y'.val % 2 = v → y' = y := by
    intro y' h1 h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h1.trans hy.symm) with h | h
    · exact h
    · exact absurd (h ▸ h2) (fun h3 => neg_val_parity hy0 (h3.trans hpar.symm))
  have hex : ∃ y' : Fp, curve.toAffine.Nonsingular x y' ∧ y'.val % 2 = v :=
    ⟨y, (nonsingular_iff _ _).mpr hy, hpar⟩
  refine ⟨(nonsingular_iff _ _).mpr hy, ?_⟩
  rw [liftX, dif_pos hex]
  have hc := uniq _ ((nonsingular_iff _ _).mp hex.choose_spec.1) hex.choose_spec.2
  congr 2

/-- With no square root of `x ^ 3 + 7` there is no point over `x`. -/
theorem liftX_none (x : Fp) (h : ¬ IsSquare (x ^ 3 + 7)) (v : ℕ) : liftX x v = none := by
  rw [liftX, dif_neg]
  rintro ⟨y, hy, -⟩
  exact h ⟨y, by rw [← (nonsingular_iff _ _).mp hy, sq]⟩

end FeProofs.Ecrecover
