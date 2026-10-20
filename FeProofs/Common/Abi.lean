import Reasoning.ABI
import Reasoning.Solc
import Reasoning.Dispatch

/-!
# ABI decoding facts shared by the contracts

Fe's canonical-`address` check `SHR(160, word) = 0`, and the modern decoder on two `uint256`
arguments.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs

/-! ## Selectors -/

/-- The selector word as the dispatcher's blocks compute it, `SHR(224, CALLDATALOAD(0))`. -/
theorem selWord_eq {I : ExecutionEnv} {w : UInt256} (h : solcSelectorWord I = w) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32))
      (UInt256.ofNat 224) = w := h

/-! ## `address` arguments -/

theorem shiftRight160_toNat (w : UInt256) :
    (UInt256.shiftRight w ⟨160⟩).toNat = w.toNat / EVM.twoPow 160 := by
  unfold UInt256.shiftRight
  rw [if_neg (by decide)]
  change (w.val.val >>> 160) % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.shiftRight_eq_div_pow]
  change w.toNat / 2 ^ 160 % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt
    (Nat.div_le_self w.toNat (2 ^ 160)) w.val.isLt)]
  rfl

theorem shiftRight160_eq_zero {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.shiftRight w (UInt256.ofNat 160) = UInt256.ofNat 0 := by
  apply u256_inj
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0
  rw [shiftRight160_toNat]
  rw [Nat.div_eq_of_lt]
  simpa [EVM.addressModulus] using hcanon

theorem shiftRight160_ne_zero {w : UInt256} (hdirty : EVM.addressModulus ≤ w.toNat) :
    UInt256.shiftRight w (UInt256.ofNat 160) ≠ UInt256.ofNat 0 := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0 at hnat
  rw [shiftRight160_toNat] at hnat
  rw [Nat.div_eq_zero_iff] at hnat
  rcases hnat with hpow | hlt
  · exact (by native_decide : EVM.twoPow 160 ≠ 0) hpow
  · exact (not_lt_of_ge (by simpa [EVM.addressModulus] using hdirty)) hlt

/-! ## Two `uint256` arguments -/

theorem decodeCalldata_uint256_uint256_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hdrop : (cd.toList.drop 4).drop 32 = cd.toList.drop 36 := by
    rw [List.drop_drop]
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, List.drop_zero,
    Nat.zero_add, hdrop, htake4, htake36, ↓reduceIte, hword4, hword36, bind, Option.bind]
  have hb4 : ((calldataWord cd 4).val : Nat) < EVM.twoPow 256 := (calldataWord cd 4).val.isLt
  have hb36 : ((calldataWord cd 36).val : Nat) < EVM.twoPow 256 := (calldataWord cd 36).val.isLt
  simp [decodeABIWord?, decodeCalldata.insertValues, hb4, hb36]
  rfl

theorem decodeCalldata_uint256_uint256_none_short {cd : ByteArray} {x y : Ident}
    (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_short (by decide) (by simpa using hshort)

theorem decodeCalldata_uint256_uint256_none_huge {cd : ByteArray} {x y : Ident}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_huge (by decide) rfl hhuge

end FeProofs
