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

open Exported

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

end FeProofs.Ecrecover
