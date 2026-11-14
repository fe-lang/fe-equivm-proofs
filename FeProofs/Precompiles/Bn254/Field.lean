import FeProofs.Precompiles.Bn254.Purify
import FeProofs.Precompiles.Field.MField
import Ethereum.BN254.Order

/-!
# Bn254Add: the base field

The constants `KBn` of `Bn254Base` checked by `decide` (`KBn_valid`, `KBn_R2`), with
`KBn.p = BN254.p`: so `Bn254Base` is the field `Fq = ZMod BN254.p` of the specification
(`FBn`), and `RepBn a x` is `MField.Rep` at it.  The exported methods are `pure` of the
functions of `MontPure.lean` (`Purify.lean`), which compute on `RepBn` the field operations
(`MField.Rep.mul` and the rest).  `cube_add_three_ne_zero` is EVMLean's: `x ^ 3 + 3` has no
root modulo `p`, so BN254 has no point with `y = 0`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add

theorem KBn_p : KBn.p = BN254.p := by decide
theorem KBn_valid : KBn.Valid := by unfold Modulus.Valid; decide
theorem KBn_R2 : KBn.R2 = 2 ^ 512 % KBn.p := by decide
theorem Bn254Base_value_eq : Bn254Base.value = BN254.p := rfl

/-- The base field of BN254. -/
abbrev Fq := ZMod BN254.p

/-- `Bn254Base` as the field `Fq`. -/
abbrev FBn : MField := ⟨KBn, BN254.p, KBn_p, KBn_valid, KBn_R2, by decide⟩

/-- Four limbs represent `x : Fq` in `Bn254Base`. -/
abbrev RepBn (a : L4) (x : Fq) : Prop := FBn.Rep a x

/-- `new` (and `fp`) of a canonical value represents it. -/
theorem Mont_new_Bn254Base_repBn (v : UInt256) (hv : v.toNat < BN254.p) :
    Mont_new_Bn254Base v = pure (toBn (Mont.new KBn v.toNat)) ∧
      RepBn (Mont.new KBn v.toNat) v.toNat :=
  ⟨new_Bn254Base v hv, MField.Rep.new hv⟩

theorem Mont_one_Bn254Base_repBn :
    Mont_one_Bn254Base = pure (toBn (Mont.new KBn 1)) ∧ RepBn (Mont.new KBn 1) 1 :=
  ⟨one_Bn254Base, MField.Rep.one⟩

theorem Mont_zero_Bn254Base_repBn : Mont_zero_Bn254Base = pure (toBn Mont.zero) ∧ RepBn Mont.zero 0 :=
  ⟨zero_Bn254Base, MField.Rep.zero⟩

theorem Mont_value_Bn254Base_repBn {a : L4} {x : Fq} (ha : RepBn a x) :
    Mont_value_Bn254Base (toBn a) = pure (UInt256.ofNat x.val) := by
  rw [value_Bn254Base, MField.Rep.value ha]

theorem Mont_is_zero_Bn254Base_repBn {a : L4} {x : Fq} (ha : RepBn a x) :
    Mont_is_zero_Bn254Base (toBn a) = pure (decide (x = 0)) := by
  rw [is_zero_Bn254Base, MField.Rep.isZero ha]

theorem Mont_equals_Bn254Base_repBn {a b : L4} {x y : Fq} (ha : RepBn a x) (hb : RepBn b y) :
    Mont_equals_Bn254Base (toBn a) (toBn b) = pure (decide (x = y)) := by
  rw [equals_Bn254Base, MField.Rep.equals ha hb]

export Ethereum.BN254 (cube_add_three_ne_zero)

end FeProofs.Bn254Add
