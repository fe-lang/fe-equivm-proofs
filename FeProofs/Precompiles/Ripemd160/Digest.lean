import FeProofs.Precompiles.Ripemd160.Words

/-!
# Ripemd160: the digest word

`ripemd160` packs the five state words, each byte-swapped, into one word, most significant first.
`swap32`: a byte-swapped word is the big-endian number of its four little-endian bytes,
`RIPEMD160.wordBytes`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ripemd160

open FeProofs.Precompiles

theorem wordBytes_be (x : UInt32) :
    fromBytesBigEndian (RIPEMD160.wordBytes x) =
      ((x.toNat % 256 * 256 + x.toNat / 2 ^ 8 % 256) * 256 + x.toNat / 2 ^ 16 % 256) * 256 +
        x.toNat / 2 ^ 24 % 256 := by
  simp [RIPEMD160.wordBytes, fromBytesBigEndian, fromBytes', Nat.shiftRight_eq_div_pow,
    UInt8.toFin]
  ring

theorem swap32 (x : UInt32) :
    IntTy.swapBytes (.u 32) (lw32 x) = UInt256.ofNat (fromBytesBigEndian (RIPEMD160.wordBytes x)) := by
  have hx := x.toNat_lt
  rw [wordBytes_be]
  simp only [IntTy.swapBytes, IntTy.pattern, IntTy.bits, IntTy.wrap, lw32_toNat,
    List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.mod_eq_of_lt hx]
  congr 1
  have e : ((((0 * 256 + ((x.toNat / 256 ^ 0 % 256 : ℕ) : ℤ)) * 256 +
      ((x.toNat / 256 ^ 1 % 256 : ℕ) : ℤ)) * 256 + ((x.toNat / 256 ^ 2 % 256 : ℕ) : ℤ)) * 256 +
      ((x.toNat / 256 ^ 3 % 256 : ℕ) : ℤ)) =
      ((((x.toNat % 256 * 256 + x.toNat / 2 ^ 8 % 256) * 256 + x.toNat / 2 ^ 16 % 256) * 256 +
        x.toNat / 2 ^ 24 % 256 : ℕ) : ℤ) := by
    norm_num
  rw [e, Int.emod_eq_of_lt (by positivity) (by omega), Int.toNat_natCast]

end FeProofs.Ripemd160
