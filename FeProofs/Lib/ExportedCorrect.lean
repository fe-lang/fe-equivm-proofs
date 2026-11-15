import FeProofs.Lib.Exported
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# Exported core and std code: what it does

Facts about the shared definitions of `Exported.lean` that the contracts' proofs use: std's
address check, what std's `return_value` does at a word, a boolean, a `u8` and a string, what
`revert_error` of a panic reverts with, what a string's checks do, where a map's entry lies, and
the memory a deployment entry leaves.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.Lib

attribute [local simp]
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

/-- Std's address check, `word >> 160 != 0`, is the hand-written one. -/
theorem shr160_eq_zero_iff (w : UInt256) :
    w >>> UInt256.ofNat 160 = UInt256.ofNat 0 ↔ ¬ NotAddress w := by
  unfold NotAddress
  constructor
  · intro h hd
    exact shiftRight160_ne_zero (by simpa [EVM.addressModulus] using! hd) h
  · intro h
    exact shiftRight160_eq_zero (by simpa [EVM.addressModulus] using! Nat.lt_of_not_le h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `u256` ends the call with the word's 32 bytes.  It changes memory only. -/
theorem returnU256_exec (v : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (Evm_return_value_Sol_u256 v).exec I w =
      some (.error (.stop v.toByteArray { w with memory := returned w.memory v })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [Evm_return_value_Sol_u256, toNat0, toNat32, toNatMax, toNatU64, sub32_0,
    Fe.EVM.add_zero, hsize, UInt256.size, hroom, returned]
  exact returned_read _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `bool` ends the call with the word of the boolean.  It changes memory
    only. -/
theorem returnBool_exec (b : Bool) (hmem : w.memory.size + 32 < UInt256.size) :
    (Evm_return_value_Sol_bool b).exec I w =
      some (.error (.stop (Bool.toUInt256 b).toByteArray
        { w with memory := returned w.memory (Bool.toUInt256 b) })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [Evm_return_value_Sol_bool, toNat0, toNat32, toNatMax, toNatU64, sub32_0,
    Fe.EVM.add_zero, hsize, UInt256.size, hroom, returned]
  exact returned_read _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `u8` ends the call with the word.  It changes memory only. -/
theorem returnU8_exec (v : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (Evm_return_value_Sol_u8 v).exec I w =
      some (.error (.stop v.toByteArray { w with memory := returned w.memory v })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [Evm_return_value_Sol_u8, toNat0, toNat32, toNatMax, toNatU64, sub32_0,
    Fe.EVM.add_zero, hsize, UInt256.size, hroom, returned]
  exact returned_read _ _

/-- Three words written into a fresh 96-byte buffer at the end of memory read back as their
    concatenation. -/
theorem returned3_read (memory : ByteArray) (a b c : UInt256) :
    (c.toByteArray.write 0 (b.toByteArray.write 0 (a.toByteArray.write 0
        ((⟨Array.replicate 96 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 96 0⟩)
          memory.size 96) memory.size 32) (memory.size + 32) 32)
        (memory.size + 64) 32).readWithPadding memory.size 96 =
      a.toByteArray ++ b.toByteArray ++ c.toByteArray := by
  have hz : (⟨Array.replicate 96 0⟩ : ByteArray).size = 96 := rfl
  set m := memory.size
  set B0 := (⟨Array.replicate 96 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 96 0⟩) m 96
  have h0 : B0.size = m + 96 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
      ByteArray.size_append, hz]
  set B1 := a.toByteArray.write 0 B0 m 32
  have h1 : B1.size = m + 96 := by rw [write32_size_of_end_le _ _ _ (by omega), h0]
  set B2 := b.toByteArray.write 0 B1 (m + 32) 32
  have h2 : B2.size = m + 96 := by rw [write32_size_of_end_le _ _ _ (by omega), h1]
  have hs := toByteArray_size
  rw [show (96 : ℕ) = 32 + 64 from rfl,
    byteArray_readWithPadding_split _ _ 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [write32_size_of_end_le _ _ _ (by omega), h2]),
    show (64 : ℕ) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ _ 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [write32_size_of_end_le _ _ _ (by omega), h2])]
  rw [write32_read_below _ _ _ _ (by rw [hs]) (by omega) (by omega),
    write32_read_below _ _ _ _ (by rw [hs]) (by omega) (by omega),
    toByteArray_write32_read_back _ _ _ (by omega),
    write32_read_below _ _ (m + 64) (m + 32) (by rw [hs]) (by omega) (by omega),
    toByteArray_write32_read_back _ _ _ (by omega),
    show m + 32 + 32 = m + 64 by omega, toByteArray_write32_read_back _ _ _ (by omega),
    ByteArray.append_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `(bool, u256, u256)` ends the call with the three words of the tuple, the
    96-byte ABI encoding.  It changes memory only. -/
theorem returnTriple_exec (t : Bool × UInt256 × UInt256)
    (hmem : w.memory.size + 96 < UInt256.size) :
    ∃ memory, (Evm_return_value_Sol_tuple_bool_u256_u256 t).exec I w =
      some (.error (.stop ((Bool.toUInt256 t.1).toByteArray ++ t.2.1.toByteArray ++
        t.2.2.toByteArray) { w with memory := memory })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  have s96_32' : UInt256.ofNat 96 - UInt256.ofNat 32 = UInt256.ofNat 64 := rfl
  have s96_64' : UInt256.ofNat 96 - UInt256.ofNat 64 = UInt256.ofNat 32 := rfl
  have s96_96 : UInt256.ofNat 96 - UInt256.ofNat 96 = UInt256.ofNat 0 := rfl
  have s32_0 : UInt256.ofNat 32 - UInt256.ofNat 0 = UInt256.ofNat 32 := rfl
  have s96_0' : UInt256.ofNat 96 - UInt256.ofNat 0 = UInt256.ofNat 96 := rfl
  simp [Evm_return_value_Sol_tuple_bool_u256_u256, toNat0, toNat32, toNat64, toNat96, toNatMax,
    toNatU64, add32_32, add64_32, s96_96, s96_32', s96_64', s32_0, s96_0', Fe.EVM.add_zero, hsize,
    UInt256.size, hroom]
  rw [ofNat_add_ofNat (by omega), ulit_toNat' _ (by omega), ofNat_add_ofNat (by omega),
    ulit_toNat' _ (by omega)]
  exact returned3_read _ _ _ _

/-! ## Panics -/

/-- The bytes `revert_error` encodes a panic in: the selector of `Panic(uint256)`, left from the
    word it was stored as, then the code. -/
theorem panicBytes (P : ByteArray) (v : UInt256) (hP : P.size = 36)
    (hsel : P.extract 0 4 = ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩) :
    (P.extract 0 4 ++ v.toByteArray.extract 0 (0 + 32) ++ P.extract (4 + 32) P.size).extract 0
      (0 + 36) = ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ v.toByteArray := by
  have hv : v.toByteArray.size = 32 := toByteArray_size v
  rw [hsel, hP, Nat.zero_add, Nat.zero_add, show v.toByteArray.extract 0 32 = v.toByteArray by
      rw [← hv, byteArray_extract_self],
    byteArray_extract_empty_of_le _ (le_refl 36), ByteArray.append_empty]
  rw [show (36 : ℕ) = (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ v.toByteArray : ByteArray).size by
      rw [ByteArray.size_append, hv]; rfl, byteArray_extract_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `revert_error` of a panic reverts with Solidity's `Panic(uint256)` encoding of its code, as
    `panicData` gives it. -/
theorem revertPanic_exec (p : Panic) (hmem : w.memory.size + 64 < UInt256.size) :
    (revert_error_Panic p).exec I w = some (.error (.revert (panicData p.code.toNat))) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hp4 : (UInt256.ofNat w.memory.size + UInt256.ofNat 4).toNat = w.memory.size + 4 := by
    rw [uadd_toNat, hsize, toNat4]; exact Nat.mod_eq_of_lt (by omega)
  simp [revert_error_Panic, revertData, toNat0, toNat32, toNatMax, toNatU64, Fe.EVM.add_zero,
    UInt256.size, hsize, add0_32, hp4,
    show UInt256.ofNat 4 + UInt256.ofNat 32 = UInt256.ofNat 36 from rfl,
    show (UInt256.ofNat 36).toNat = 36 from rfl, show (UInt256.ofNat 28).toNat = 28 from rfl,
    show UInt256.ofNat 32 - UInt256.ofNat 0 = UInt256.ofNat 32 from rfl,
    show w.memory.size + 36 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 by
        unfold UInt256.size at hmem; omega]
  rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [toByteArray_size])
      (by rw [zeros_size]; omega),
    write_tail _ _ _ 0 4 32 (by simp) (by decide) (by rw [zeros_size])
      (by simp [zeros_size]),
    write_tail _ _ _ 0 4 32 (by simp) (by decide) (by rw [toByteArray_size])
      (by simp [zeros_size]),
    readWithPadding_tail _ _ 0 36 (by simp) (by decide) (by simp [zeros_size]),
    panicBytes _ _ (by simp [zeros_size]) (by decide +kernel)]
  simp [panicData, u256_ofNat_toNat]

/-! ## Strings in memory -/

set_option maxHeartbeats 4000000 in
/-- `DynString::from_abi_tail`'s checks pass on a buffer that holds the length word, then
    `32 * ceil(L / 32)` more bytes: the size is the length word's and the padded bytes', and the
    length word reads back. -/
theorem fromAbiTail_exec (M T : ByteArray) (L : ℕ) (hL : L < 2 ^ 255)
    (hmem : w.memory = M ++ ((UInt256.ofNat L).toByteArray ++ T))
    (hM : M.size + 64 + 32 * ((L + 31) / 32) < UInt256.size) :
    (DynString_from_abi_tail (UInt256.ofNat M.size) (UInt256.ofNat L)
        (UInt256.ofNat (32 + (L + 31) / 32 * 32))).exec I w =
      some (.ok (⟨UInt256.ofNat M.size, UInt256.ofNat L, UInt256.ofNat (32 + (L + 31) / 32 * 32)⟩,
        w)) := by
  have hW : (L + 31) / 32 < 2 ^ 251 := by omega
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have hread : uInt256OfByteArray (w.memory.readWithPadding M.size 32) = UInt256.ofNat L := by
    rw [hmem, readWithPadding_tail _ _ 0 32 (by simp) (by decide) (by simp),
      extract_append_left _ _ _ _ (by rw [toByteArray_size]), toByteArray_extract_all,
      uInt256OfByteArray_toByteArray]
  by_cases h0 : L = 0
  · subst h0
    simp [DynString_from_abi_tail, mload, toNat0, toNat32, Fe.EVM.add_zero,
      ulit_toNat' M.size (by omega), hread,
      show UInt256.ofNat 32 + UInt256.ofNat 0 = UInt256.ofNat 32 from rfl,
      show ¬ UInt256.size ≤ 32 by decide]
  have hdiv : UInt256.ofNat (L - 1) / UInt256.ofNat 32 = UInt256.ofNat ((L - 1) / 32) := by
    apply u256_inj
    change (UInt256.div _ _).toNat = _
    rw [udiv_toNat, ulit_toNat' _ (by omega), toNat32, ulit_toNat' _ (by omega)]
  have hwords : (L - 1) / 32 + 1 = (L + 31) / 32 := by omega
  simp [DynString_from_abi_tail, checkedDiv, checkedMul, mload, toNat32, Fe.EVM.add_zero,
    ulit_toNat' M.size (by omega), hread,
    ofNat_ne_ofNat_zero h0 (by omega : L < UInt256.size), ulit_toNat' L (by omega),
    show ¬ L < 1 by omega, show (UInt256.ofNat L).sub (UInt256.ofNat 1) = UInt256.ofNat (L - 1) from
      ofNat_sub_ofNat (a := L) (b := 1) (by omega) (by omega), hdiv,
    show (UInt256.ofNat 1).toNat = 1 from rfl, show UInt256.ofNat 32 ≠ ⟨0⟩ by decide,
    ulit_toNat' ((L - 1) / 32) (by omega), show ¬ UInt256.size ≤ (L + 31) / 32 by omega,
    ofNat_add_ofNat (a := (L - 1) / 32) (b := 1) (by omega), hwords,
    ofNat_mul_ofNat (a := (L + 31) / 32) (b := 32) (by omega) (by decide) (by omega),
    ulit_toNat' ((L + 31) / 32 * 32) (by omega),
    ofNat_add_ofNat (a := 32) (b := (L + 31) / 32 * 32) (by omega),
    ulit_toNat' ((L + 31) / 32) (by omega), show ¬ UInt256.size ≤ (L + 31) / 32 * 32 by omega,
    show ¬ UInt256.size ≤ 32 + (L + 31) / 32 * 32 by omega]

set_option maxHeartbeats 4000000 in
/-- `return_value` of a string whose `S`-byte encoding is the bytes `B` of memory at `p`: the
    offset word `0x20` and the encoding, copied after it into a fresh buffer.  A buffer of
    `2 ^ 64` bytes or more fails with `Panic(0x41)`. -/
theorem returnDynString_exec (p S : ℕ) (L : UInt256) (B : ByteArray) (hB : B.size = S)
    (hd : w.memory.extract p (p + S) = B) (hin : p + S ≤ w.memory.size) (hS : 0 < S)
    (hmem : w.memory.size + 2 ^ 65 < UInt256.size) (hS64 : S < 2 ^ 64) :
    (Evm_return_value_Sol_DynString ⟨UInt256.ofNat p, L, UInt256.ofNat S⟩).exec I w =
      if 32 + S < 2 ^ 64 then
        some (.error (.stop ((UInt256.ofNat 32).toByteArray ++ B)
          { w with memory := w.memory ++ ((UInt256.ofNat 32).toByteArray ++ B) }))
      else some (.error (.panic 0x41)) := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have hmaxa : ¬ UInt256.size - 1 < 18446744073709551615 := by decide
  by_cases h64 : 32 + S < 2 ^ 64
  swap
  · simp [Evm_return_value_Sol_DynString, ulit_toNat' S (by omega), toNat32, toNatMax, toNatU64,
      hmaxa, show ¬ UInt256.size ≤ 32 + S by omega, show ¬ UInt256.size - 1 < 32 + S by omega,
      ofNat_add_ofNat (a := 32) (b := S) (by omega), ulit_toNat' (32 + S) (by omega),
      show 18446744073709551615 < 32 + S by omega, show ¬ 32 + S < 18446744073709551616 by omega,
      show (UInt256.ofNat 65).toNat = 65 from rfl]
  have hp2 : w.memory.size + 32 < UInt256.size := by omega
  simp [Evm_return_value_Sol_DynString, ulit_toNat' S (by omega), toNat32, toNatMax, toNatU64,
    hmaxa, show ¬ UInt256.size ≤ 32 + S by omega, show ¬ UInt256.size - 1 < 32 + S by omega,
    ofNat_add_ofNat (a := 32) (b := S) (by omega), ulit_toNat' (32 + S) (by omega),
    show ¬ 18446744073709551615 < 32 + S by omega, toNat0, Fe.EVM.add_zero,
    show w.memory.size + (32 + S) < UInt256.size by omega, ulit_toNat' w.memory.size (by omega),
    ofNat_sub_ofNat (a := 32 + S) (b := 0) (by omega) (by omega),
    ofNat_sub_ofNat (a := 32 + S) (b := 32) (by omega) (by omega),
    ofNat_sub_ofNat (a := S) (b := 0) (by omega) (by omega),
    ofNat_sub_ofNat (a := 32 + S) (b := S) (by omega) (by omega),
    ofNat_add_ofNat (a := w.memory.size) (b := 32) hp2, ulit_toNat' (w.memory.size + 32) hp2,
    mcopy, show 32 + S < 18446744073709551616 from h64]
  have hw : (UInt256.ofNat 32).toByteArray.size = 32 := toByteArray_size _
  have h1 : (⟨Array.replicate (32 + S) 0⟩ : ByteArray).write 0
      (w.memory ++ ⟨Array.replicate (32 + S) 0⟩) w.memory.size (32 + S) =
        w.memory ++ ⟨Array.replicate (32 + S) 0⟩ := by
    rw [write_tail _ _ _ 0 0 (32 + S) (by simp) (by omega) (by rw [zeros_size]; omega)
        (by rw [zeros_size]; omega)]
    simp [zeros_extract, zeros_size]
  have h2 : (UInt256.ofNat 32).toByteArray.write 0 (w.memory ++ ⟨Array.replicate (32 + S) 0⟩)
      w.memory.size 32 = w.memory ++ ((UInt256.ofNat 32).toByteArray ++ ⟨Array.replicate S 0⟩) := by
    rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [hw]) (by rw [zeros_size]; omega)]
    simp [zeros_extract, zeros_size, toByteArray_extract_all]
  have h3 : (w.memory ++ ((UInt256.ofNat 32).toByteArray ++ ⟨Array.replicate S 0⟩)).write
      (UInt256.ofNat p).toNat
      (w.memory ++ ((UInt256.ofNat 32).toByteArray ++ ⟨Array.replicate S 0⟩))
      (w.memory.size + 32) S = w.memory ++ ((UInt256.ofNat 32).toByteArray ++ B) := by
    rw [write_tail _ _ _ _ 32 S rfl (by omega)
        (by simp [hw, zeros_size, ulit_toNat' p (by omega)]; omega) (by simp [hw, zeros_size]),
      ulit_toNat' p (by omega), extract_append_left _ _ _ _ hin, hd,
      extract_append_left _ _ _ _ (by rw [hw]), toByteArray_extract_all,
      byteArray_extract_empty_of_le _ (by simp [hw, zeros_size]), ByteArray.append_empty]
  have h4 : (w.memory ++ ((UInt256.ofNat 32).toByteArray ++ B)).readWithPadding w.memory.size
      (32 + S) = (UInt256.ofNat 32).toByteArray ++ B := by
    rw [readWithPadding_tail _ _ 0 (32 + S) (by simp) (by omega) (by simp [hw, hB]), Nat.zero_add,
      show 32 + S = ((UInt256.ofNat 32).toByteArray ++ B).size by simp [hw, hB],
      byteArray_extract_self]
  simp [h1, h2, h3, h4]

/-! ## Map entries -/

/-- Std's `mapping_slot` at a `u256` key stores the key and the map's root in a fresh buffer and
    hashes it. -/
theorem mappingSlotU256_exec (root key : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (mapping_slot_u256 root key).exec I w =
      some (.ok (mapSlot key root, { w with memory := keyed w.memory key root })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hnext : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [uadd_toNat, hsize, toNat32]
    exact Nat.mod_eq_of_lt (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [mapping_slot_u256, keccak256, toNat0, toNat32, toNat64, toNatMax, toNatU64, add32_32,
    hsize, hnext, UInt256.size, hroom, keyed]
  exact keyed_slot w.memory key root

/-- Std's `mapping_slot` at an address key does the same. -/
theorem mappingSlotAddress_exec (root key : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (mapping_slot_Address root key).exec I w =
      some (.ok (mapSlot key root, { w with memory := keyed w.memory key root })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hnext : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [uadd_toNat, hsize, toNat32]
    exact Nat.mod_eq_of_lt (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [mapping_slot_Address, keccak256, toNat0, toNat32, toNat64, toNatMax, toNatU64, add32_32,
    hsize, hnext, UInt256.size, hroom, keyed]
  exact keyed_slot w.memory key root

/-- `locate` of a map entry: the entry's slot, at no offset. -/
theorem locateU256_exec (p : Place) (root key : UInt256)
    (hmem : w.memory.size + 64 < UInt256.size) :
    (StorageMap_locate_u256_u256 p root key).exec I w =
      some (.ok (⟨mapSlot key root, UInt256.ofNat 0⟩,
        { w with memory := keyed w.memory key root })) := by
  simp [StorageMap_locate_u256_u256, mappingSlotU256_exec I w root key hmem]

theorem locateAddress_exec (p : Place) (root key : UInt256)
    (hmem : w.memory.size + 64 < UInt256.size) :
    (StorageMap_locate_Address_u256 p root key).exec I w =
      some (.ok (⟨mapSlot key root, UInt256.ofNat 0⟩,
        { w with memory := keyed w.memory key root })) := by
  simp [StorageMap_locate_Address_u256, mappingSlotAddress_exec I w root key hmem]

/-- `locate` of an entry that is itself a map: the slot of that map. -/
theorem locateAddressMap_exec (p : Place) (root key : UInt256)
    (hmem : w.memory.size + 64 < UInt256.size) :
    (StorageMap_locate_Address_StorageMap_Address_u256 p root key).exec I w =
      some (.ok (⟨mapSlot key root, UInt256.ofNat 0⟩,
        { w with memory := keyed w.memory key root })) := by
  simp [StorageMap_locate_Address_StorageMap_Address_u256, mappingSlotAddress_exec I w root key hmem]

/-! ## Deployment -/

/-- Memory after a deployment entry copies its one argument word into a fresh buffer. -/
def withArg (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0 (memory ++ ⟨Array.replicate 32 0⟩) memory.size 32

theorem withArg_size (memory : ByteArray) (v : UInt256) :
    (withArg memory v).size = memory.size + 32 := by
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  unfold withArg
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]

/-! ## Calldata decoders

Std's pieces of `decode_runtime_args` at a message of static fields: the calldata view's length,
the head check, and each `u256` or address field.  A contract's decoder of a message unfolds to
these. -/

set_option maxRecDepth 100000 in
/-- Std's length of the calldata view from offset 0: the calldata size, which fits a `u64`. -/
theorem lenCallData_exec (hfits : I.calldata.size < 2 ^ 64) :
    (len_CallData ⟨UInt256.ofNat 0⟩).exec I w =
      some (.ok (UInt256.ofNat I.calldata.size, w)) := by
  simp [len_CallData, CallData_size, toNat0, truncate_size _ hfits, checkedSub]

set_option maxRecDepth 100000 in
/-- Std's head check of the selector's 4 bytes and a head of `need` bytes: revert on calldata
    too short for it. -/
theorem validateHead_exec {need : Nat} (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) (h0 : need ≠ 0) (hneed : need < 2 ^ 64) :
    (Sol_validate_runtime_head (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4)
      (UInt256.ofNat need)).exec I w =
      if I.calldata.size < 4 + need then some (.error (.revert ByteArray.empty))
      else some (.ok ((), w)) := by
  have hs : I.calldata.size - 4 < need ↔ I.calldata.size < 4 + need := by omega
  simp [Sol_validate_runtime_head, i256_from_word, headCheck hlo hfits hneed, hs,
    ofNat_ne_ofNat_zero h0 (by unfold UInt256.size; omega)]
  split_ifs <;> simp [revertEmpty]

/-- Std's decoding of a `u256` field of a message at offset `off` after the selector. -/
theorem decodeU256Field_exec (base len : UInt256) {off : Nat} (hoff : off < UInt256.size) :
    (decode_msg_field_from_Sol_u256_CallData ⟨UInt256.ofNat 0⟩ base (UInt256.ofNat off)
      len).exec I w = some (.ok (word I.calldata off, w)) := by
  simp [decode_msg_field_from_Sol_u256_CallData, u256_IS_DYNAMIC,
    decode_field_from_Sol_u256_CallData, u256_decode_from_Sol_CallData, CallData_word_at, calldataload, word,
    ofNat_add_ofNat (show 0 + off < UInt256.size by omega), ulit_toNat' _ hoff]

/-- Std's decoding of an address field at offset `off` after the selector: revert on a word that
    is not a canonical address. -/
theorem decodeAddressField_exec (base len : UInt256) {off : Nat} (hoff : off < UInt256.size) :
    (decode_msg_field_from_Sol_Address_CallData ⟨UInt256.ofNat 0⟩ base (UInt256.ofNat off)
      len).exec I w =
      if NotAddress (word I.calldata off) then some (.error (.revert ByteArray.empty))
      else some (.ok (word I.calldata off, w)) := by
  simp [decode_msg_field_from_Sol_Address_CallData, Address_IS_DYNAMIC,
    decode_field_from_Sol_Address_CallData, Address_decode_from_Sol_CallData, CallData_word_at,
    calldataload, word, ofNat_add_ofNat (show 0 + off < UInt256.size by omega), ulit_toNat' _ hoff,
    shr160_eq_zero_iff]
  split_ifs <;> simp [revertEmpty]

end FeProofs.Lib
