import Reasoning.Storage

/-!
# Byte lanes of a storage word

`std::evm::StoragePackedArray<8>` keeps lane `i` in byte `i % 32` (little-endian, lane 0 lowest)
of word `keccak256(slot) + i / 32`.  These lemmas connect the compiled mask/shift code to Stele's
byte-wide storage locations at any offset: reads of a lane, writes of one lane preserving every
other bit, truncation to eight bits, isolation of distinct lanes, and last-write-wins.

-- LIBRARY CANDIDATE: `Reasoning/PackedStorage.lean` (offset-generic byte lanes; the existing
-- helpers there are fixed to particular widths and offsets).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs

def packedByte0 (word : UInt256) : UInt256 := UInt256.land word ⟨255⟩

theorem packedByte0_toNat (word : UInt256) :
    (packedByte0 word).toNat = word.toNat % 256 := by
  unfold packedByte0
  rw [uland_toNat]
  exact nat_land_mask_eq_mod word.toNat 8

def packedByteLoc (slot : UInt256) (offset : Fin 32) : StorageLoc :=
  { slot, offset, size := 1, hbound := by simp,
    type := .int (.uint ⟨8, by decide⟩) }

/-- Replacing a byte leaves precisely the lower prefix and upper suffix untouched. -/
theorem nat_replaceByte (old value k : Nat) (hold : old < 2 ^ 256)
    (hk : k + 8 ≤ 256) :
    (old &&& ((2 ^ 256 - 1) ^^^ ((2 ^ 8 - 1) <<< k))) ||| ((value % 256) <<< k) =
      (old % 2 ^ k) ||| ((value % 256) <<< k) |||
        ((old >>> (k + 8)) <<< (k + 8)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases hjk : j < k
  · have hj256 : j < 256 := by omega
    have hj8 : j < k + 8 := by omega
    simp [hjk, hj256, hj8]
  · by_cases hj8 : j < k + 8
    · have hj256 : j < 256 := by omega
      have hjsub : j - k < 8 := by omega
      simp [hjk, hj256, hj8, hjsub]
    · have hjsub : ¬ j - k < 8 := by omega
      have hsum : k + 8 + (j - (k + 8)) = j := by omega
      by_cases hj256 : j < 256
      · simp [hjk, hj256, hj8, hjsub, hsum, Bool.or_comm]
      · have holdj : old.testBit j = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hold
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hjk, hj256, hj8, hjsub, hsum, holdj]

def packedByte (word : UInt256) (offset : Fin 32) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat (8 * offset.val))) ⟨255⟩

def setPackedByte (old value : UInt256) (offset : Fin 32) : UInt256 :=
  let shift := UInt256.ofNat (8 * offset.val)
  let mask := UInt256.shiftLeft ⟨255⟩ shift
  UInt256.lor (UInt256.land old (UInt256.xor (UInt256.lnot ⟨0⟩) mask))
    (UInt256.shiftLeft (packedByte0 value) shift)

theorem shiftLeft_toNat_of_lt (word : UInt256) (k : Nat) (hk : k < 256)
    (hbound : word.toNat * 2 ^ k < UInt256.size) :
    (UInt256.shiftLeft word (UInt256.ofNat k)).toNat = word.toNat * 2 ^ k := by
  have hkword : (UInt256.ofNat k).toNat = k := ulit_toNat' _ (by
    norm_num [UInt256.size]; omega)
  unfold UInt256.shiftLeft
  rw [if_neg (by change ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  change (word.toNat <<< (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkword, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hbound]

theorem shiftRight_toNat_of_lt (word : UInt256) (k : Nat) (hk : k < 256) :
    (UInt256.shiftRight word (UInt256.ofNat k)).toNat = word.toNat / 2 ^ k := by
  have hkword : (UInt256.ofNat k).toNat = k := ulit_toNat' _ (by
    norm_num [UInt256.size]; omega)
  unfold UInt256.shiftRight
  rw [if_neg (by change ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  change (word.toNat >>> (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkword, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt
    (lt_of_le_of_lt (Nat.div_le_self word.toNat (2 ^ k)) word.val.isLt)

theorem packedByte_toNat (word : UInt256) (offset : Fin 32) :
    (packedByte word offset).toNat = word.toNat / 256 ^ offset.val % 256 := by
  unfold packedByte
  rw [uland_toNat, shiftRight_toNat_of_lt word _ (by omega)]
  change Nat.land (word.toNat / 2 ^ (8 * offset.val)) 255 = _
  rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, nat_land_mask_eq_mod]
  rw [show (2 : Nat) ^ (8 * offset.val) = 256 ^ offset.val by rw [Nat.pow_mul]]
  rfl

theorem byteShift_bound (value : Nat) (offset : Fin 32) (hvalue : value < 256) :
    value * 2 ^ (8 * offset.val) < UInt256.size := by
  calc
    value * 2 ^ (8 * offset.val) < 2 ^ 8 * 2 ^ (8 * offset.val) :=
      Nat.mul_lt_mul_of_pos_right hvalue (by positivity)
    _ = 2 ^ (8 + 8 * offset.val) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)

theorem uxor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.toNat ^^^ b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt (show a.toNat ^^^ b.toNat < 2 ^ 256 from
    Nat.xor_lt_two_pow a.val.isLt b.val.isLt)

theorem setPackedByte_toNat_mod (old value : UInt256) (offset : Fin 32) :
    (setPackedByte old value offset).toNat =
      ((old.toNat &&& ((2 ^ 256 - 1) ^^^ (255 * 2 ^ (8 * offset.val)))) |||
        (value.toNat % 256 * 2 ^ (8 * offset.val))) % 2 ^ 256 := by
  have hk : 8 * offset.val < 256 := by omega
  have hv : value.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hshiftMask := shiftLeft_toNat_of_lt (⟨255⟩ : UInt256) _ hk
    (byteShift_bound 255 offset (by decide))
  have hshiftValue := shiftLeft_toNat_of_lt (packedByte0 value) _ hk
    (by rw [packedByte0_toNat]; exact byteShift_bound _ offset hv)
  rw [packedByte0_toNat] at hshiftValue
  unfold setPackedByte
  rw [u256_lor_toNat, uland_toNat, uxor_toNat, hshiftMask, hshiftValue]
  rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = 2 ^ 256 - 1 by decide]
  rfl

theorem setPackedByte_toNat (old value : UInt256) (offset : Fin 32) :
    (setPackedByte old value offset).toNat =
      old.toNat % 256 ^ offset.val + value.toNat % 256 * 256 ^ offset.val +
        old.toNat / 256 ^ (offset.val + 1) * 256 ^ (offset.val + 1) := by
  have hv : value.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [setPackedByte_toNat_mod]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq,
    nat_replaceByte old.toNat value.toNat (8 * offset.val) old.val.isLt (by omega)]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  change Nat.lor (Nat.lor (old.toNat % 2 ^ (8 * offset.val))
    (value.toNat % 256 * 2 ^ (8 * offset.val)))
    (old.toNat / 2 ^ (8 * offset.val + 8) * 2 ^ (8 * offset.val + 8)) % UInt256.size = _
  rw [nat_lor_shift_add (old.toNat % 2 ^ (8 * offset.val)) (value.toNat % 256)
    (8 * offset.val) (Nat.mod_lt _ (by positivity))]
  have hlo : old.toNat % 2 ^ (8 * offset.val) +
      value.toNat % 256 * 2 ^ (8 * offset.val) < 2 ^ (8 * offset.val + 8) := by
    rw [Nat.pow_add]
    norm_num
    have hp := Nat.mod_lt old.toNat (show 0 < 2 ^ (8 * offset.val) by positivity)
    calc
      _ < 2 ^ (8 * offset.val) + value.toNat % 256 * 2 ^ (8 * offset.val) :=
        Nat.add_lt_add_right hp _
      _ = (value.toNat % 256 + 1) * 2 ^ (8 * offset.val) := by ring
      _ ≤ 256 * 2 ^ (8 * offset.val) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := Nat.mul_comm _ _
  rw [nat_lor_shift_add _ (old.toNat / 2 ^ (8 * offset.val + 8)) _ hlo]
  have hpow : (2 : Nat) ^ (8 * offset.val) = 256 ^ offset.val := by
    rw [Nat.pow_mul]
  have hpowNext : (2 : Nat) ^ (8 * offset.val + 8) = 256 ^ (offset.val + 1) := by
    rw [show 8 * offset.val + 8 = 8 * (offset.val + 1) by omega, Nat.pow_mul]
  rw [hpow, hpowNext]
  apply Nat.mod_eq_of_lt
  have hsize : 256 ^ (offset.val + 1) ∣ UInt256.size := by
    change 256 ^ (offset.val + 1) ∣ 256 ^ 32
    exact pow_dvd_pow _ (by omega)
  have hdiv : old.toNat / 256 ^ (offset.val + 1) <
      UInt256.size / 256 ^ (offset.val + 1) :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by
      rw [Nat.div_mul_cancel hsize]; exact old.val.isLt)
  rw [hpow, hpowNext] at hlo
  have hle : (old.toNat / 256 ^ (offset.val + 1) + 1) * 256 ^ (offset.val + 1) ≤
      UInt256.size := by
    calc
      _ ≤ (UInt256.size / 256 ^ (offset.val + 1)) * 256 ^ (offset.val + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := Nat.div_mul_cancel hsize
  nlinarith

theorem storageLocStore_packedByte (evm : EVM.State) (slot value : UInt256)
    (offset : Fin 32) :
    storageLocStore evm (packedByteLoc slot offset) (.int (Int.ofNat value.toNat)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value offset)) := by
  unfold storageLocStore storageLocWriteWord packedByteLoc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes' (List.take offset.val _ ++ List.take 1 _ ++ List.drop (offset.val + 1) _) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setPackedByte_toNat,
    List.length_append, List.length_take, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof value).2,
    (EVM.Word.toBytesLEWithSizeProof
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    Nat.min_eq_left offset.isLt.le]
  have hpow (n : Nat) : 2 ^ (8 * n) = 256 ^ n := by rw [Nat.pow_mul]
  simp only [Nat.min_eq_left (show 1 ≤ 32 by decide), Nat.pow_one, hpow]
  ring

theorem setPackedByte_truncate (old value : UInt256) (offset : Fin 32) :
    setPackedByte old (packedByte0 value) offset = setPackedByte old value offset := by
  apply u256_inj
  simp only [setPackedByte_toNat, packedByte0_toNat, Nat.mod_mod]

theorem storageLocLoad_packedByte (evm : EVM.State) (slot : UInt256) (offset : Fin 32) :
    storageLocLoad evm (packedByteLoc slot offset) =
      .int (Int.ofNat (packedByte
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset).toNat) := by
  rw [show packedByteLoc slot offset =
    { slot, offset, size := 1, hbound := by simp,
      type := ABI.ElemType.int (.uint ⟨8, by decide⟩) } from rfl,
    storageLocLoad_uint_offset evm slot offset 1 ⟨8, by decide⟩ (by decide) (by omega) (by decide)]
  congr 2
  rw [packedByte_toNat, uland_toNat, udiv_toNat,
    ulit_toNat' _ (show 256 ^ offset.val < UInt256.size from by
      change 256 ^ offset.val < 256 ^ 32
      exact Nat.pow_lt_pow_right (by decide) offset.isLt)]
  exact nat_land_mask_eq_mod _ 8


/-- Writing a byte `v` at offset 0 keeps the other 31 bytes: `(w & ~0xff) | v`. -/
theorem setPackedByte_low (w v : UInt256) (hv : v.toNat < 2 ^ 8) :
    setPackedByte w v 0 = UInt256.lor v (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) w) := by
  have hw : w.toNat < 2 ^ 256 := w.val.isLt
  apply u256_inj
  rw [setPackedByte_toNat, u256_lor_toNat, uland_toNat,
    show (UInt256.lnot (UInt256.ofNat 255)).toNat = 2 ^ 256 - 2 ^ 8 by decide, Nat.and_comm]
  change _ = Nat.lor v.toNat (Nat.land w.toNat (2 ^ 256 - 2 ^ 8)) % UInt256.size
  rw [natLandClearLow8 w.toNat hw, nat_lor_shift_add v.toNat (w.toNat / 2 ^ 8) 8 hv]
  have hlt : v.toNat + w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size := by change _ < 2 ^ 256; omega
  rw [show ((0 : Fin 32) : ℕ) = 0 from rfl, Nat.mod_eq_of_lt hlt]
  omega

end FeProofs
