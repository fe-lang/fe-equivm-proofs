import FeProofs.Lib.Exported
import Fe.EVM.Entry

/-!
# Exported core and std code: what it does

Facts about the shared definitions of `Exported.lean` that the contracts' proofs use: what
std's `return_value` does at a word, a boolean and a `u8`, where a map's entry lies, and the memory a deployment entry leaves.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.Lib

attribute [local simp]
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

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

end FeProofs.Lib
