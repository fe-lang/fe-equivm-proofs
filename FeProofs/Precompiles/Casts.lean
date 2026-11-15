import FeProofs.Precompiles.Field.Words

/-!
# Precompiles: casts that change nothing

On the EVM target `usize` is a 256-bit word, so std's truncating casts to it from `u64`, `usize`
and `u256` are the identity: each masks with all ones (`land_ones`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

theorem land_ones (x : UInt256) : x &&& ~~~(UInt256.ofNat 0) = x := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat]
  have : (~~~(UInt256.ofNat 0)).toNat = 2 ^ 256 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 256 from x.val.isLt)]

theorem downcast_u64_usize (x : UInt256) : Lib.downcast_truncate_u64_usize x = pure x := by
  simp only [Lib.downcast_truncate_u64_usize, Lib.u64_to_word, Lib.usize_IS_SIGNED, Lib.usize_MASK,
    Lib.usize_from_word, pure_bind, Bool.false_eq_true, ite_false, land_ones]

theorem downcast_usize_usize (x : UInt256) : Lib.downcast_truncate_usize_usize x = pure x := by
  simp only [Lib.downcast_truncate_usize_usize, Lib.usize_to_word, Lib.usize_IS_SIGNED,
    Lib.usize_MASK, Lib.usize_from_word, pure_bind, Bool.false_eq_true, ite_false, land_ones]

theorem downcast_u256_usize (x : UInt256) : Lib.downcast_truncate_u256_usize x = pure x := by
  simp only [Lib.downcast_truncate_u256_usize, Lib.u256_to_word, Lib.usize_IS_SIGNED,
    Lib.usize_MASK, Lib.usize_from_word, pure_bind, Bool.false_eq_true, ite_false, land_ones]

end FeProofs.Precompiles
