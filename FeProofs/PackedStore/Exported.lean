import FeProofs.Lib.Exported
import FeProofs.Common.PackedByte
import Fe.EVM.Entry

/-!
# FePackedStore: exported code

The definitions between the markers are the output of `fe-lean-export` on `FePackedStore.fe`
(Fe branch `lean-export`, golden file `tests/golden/packed_store.lean`), copied in by
`scripts/sync_exported.py`.  The std functions the arms call, `StoragePackedArray<8>::get` and
`set`, and the constants those read are shared with the other exported contracts, in
`FeProofs/Lib/Exported.lean`.

The theorems evaluate the arms: lanes 0 and 1 are bytes 0 and 1 of the word at `wordSlot`,
read and written as `packedByte` and `setPackedByte`.

The definitions end with the runtime entry: one `recv0_arm<n>_entry` per arm and `runtime`, with
the std decoders at the contract's message types.  `RuntimeCorrect.lean` proves that `fePackedStoreBytecode`,
built by the Fe commit the exporter ran on (`22b156fff`), refines the contract whose runtime is
that entry.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.PackedStore.Exported

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: packed_store

export Lib (CallData SELECTOR_SIZE abi_field_head_size_u256 decode_msg_field_from_Sol_u256_CallData get_8 input len_CallData return_value_Sol_u256 set_8 size validate_runtime_head)

def Field.pack : Place :=
  .storage (UInt256.ofNat 0)

structure Get0 where
deriving Inhabited

structure Get1 where
deriving Inhabited

structure Set0 where
  value : UInt256
deriving Inhabited

structure Set1 where
  value : UInt256
deriving Inhabited

structure SetBoth where
  first : UInt256
  second : UInt256
deriving Inhabited

def init : FeM Unit := do
  return ()

def recv0_arm0 : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 := Field.pack
  let v2 := v1
  let v3 ← get_8 v2 v0
  return v3

def recv0_arm1 : FeM UInt256 := do
  let v0 := (UInt256.ofNat 1)
  let v1 := Field.pack
  let v2 := v1
  let v3 ← get_8 v2 v0
  return v3

def recv0_arm2 (v0 : UInt256) : FeM Unit := do
  let v1 := (UInt256.ofNat 0)
  let v2 := Field.pack
  let v3 ← set_8 v2 v1 v0
  return ()

def recv0_arm3 (v0 : UInt256) : FeM Unit := do
  let v1 := (UInt256.ofNat 1)
  let v2 := Field.pack
  let v3 ← set_8 v2 v1 v0
  return ()

def recv0_arm4 (v0 : UInt256) (v1 : UInt256) : FeM Unit := do
  let v2 := (UInt256.ofNat 0)
  let v3 := Field.pack
  let v4 ← set_8 v3 v2 v0
  let v5 := (UInt256.ofNat 1)
  let v6 := Field.pack
  let v7 ← set_8 v6 v5 v1
  return ()

def HEAD_SIZE : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  return v0

def decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Get0 := do
  let v2 := (Get0.mk)
  return v2

def decode_from_prechecked_head_Get0_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM Get0 := do
  let v3 ← decode_from_CallData v0 v1
  return v3

def decode_runtime_args_Evm_Sol_Get0 : FeM Get0 := do
  let mut r0 : CallData := default
  let v2 ← input
  let v3 := v2
  r0 := v3
  let v4 ← SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← HEAD_SIZE
  let v10 ← validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_Get0_Sol_CallData v11 v5 v8
  return v12

def recv0_arm0_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Get0
  let result ← recv0_arm0
  return_value_Sol_u256 result

def decode_from_CallData_1 (v0 : CallData) (v1 : UInt256) : FeM Get1 := do
  let v2 := (Get1.mk)
  return v2

def decode_from_prechecked_head_Get1_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM Get1 := do
  let v3 ← decode_from_CallData_1 v0 v1
  return v3

def decode_runtime_args_Evm_Sol_Get1 : FeM Get1 := do
  let mut r0 : CallData := default
  let v2 ← input
  let v3 := v2
  r0 := v3
  let v4 ← SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← HEAD_SIZE
  let v10 ← validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_Get1_Sol_CallData v11 v5 v8
  return v12

def recv0_arm1_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Get1
  let result ← recv0_arm1
  return_value_Sol_u256 result

def HEAD_SIZE_2 : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd v0 v1
  return v2

def decode_from_CallData_2 (v0 : CallData) (v1 : UInt256) : FeM Set0 := do
  let v2 ← len_CallData v0
  let v3 := v2
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v3
  let v5 := v4
  let v6 := (Set0.mk v5)
  return v6

def decode_from_prechecked_head_Set0_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM Set0 := do
  let v3 ← decode_from_CallData_2 v0 v1
  return v3

def decode_runtime_args_Evm_Sol_Set0 : FeM Set0 := do
  let mut r0 : CallData := default
  let v2 ← input
  let v3 := v2
  r0 := v3
  let v4 ← SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← HEAD_SIZE_2
  let v10 ← validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_Set0_Sol_CallData v11 v5 v8
  return v12

def recv0_arm2_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Set0
  let _ ← recv0_arm2 message.value
  returnData (UInt256.ofNat 0) (UInt256.ofNat 0)

def decode_from_CallData_3 (v0 : CallData) (v1 : UInt256) : FeM Set1 := do
  let v2 ← len_CallData v0
  let v3 := v2
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v3
  let v5 := v4
  let v6 := (Set1.mk v5)
  return v6

def decode_from_prechecked_head_Set1_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM Set1 := do
  let v3 ← decode_from_CallData_3 v0 v1
  return v3

def decode_runtime_args_Evm_Sol_Set1 : FeM Set1 := do
  let mut r0 : CallData := default
  let v2 ← input
  let v3 := v2
  r0 := v3
  let v4 ← SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← HEAD_SIZE_2
  let v10 ← validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_Set1_Sol_CallData v11 v5 v8
  return v12

def recv0_arm3_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Set1
  let _ ← recv0_arm3 message.value
  returnData (UInt256.ofNat 0) (UInt256.ofNat 0)

def HEAD_SIZE_3 : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd v0 v1
  let v3 ← abi_field_head_size_u256
  let v4 ← checkedAdd v2 v3
  return v4

def decode_from_CallData_4 (v0 : CallData) (v1 : UInt256) : FeM SetBoth := do
  let v2 ← len_CallData v0
  let v3 := v2
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v3
  let v5 := v4
  let v6 := v1
  let v7 ← abi_field_head_size_u256
  let v8 ← checkedAdd v6 v7
  let v9 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v8 v3
  let v10 := v9
  let v11 := (SetBoth.mk v5 v10)
  return v11

def decode_from_prechecked_head_SetBoth_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM SetBoth := do
  let v3 ← decode_from_CallData_4 v0 v1
  return v3

def decode_runtime_args_Evm_Sol_SetBoth : FeM SetBoth := do
  let mut r0 : CallData := default
  let v2 ← input
  let v3 := v2
  r0 := v3
  let v4 ← SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← HEAD_SIZE_3
  let v10 ← validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_SetBoth_Sol_CallData v11 v5 v8
  return v12

def recv0_arm4_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_SetBoth
  let _ ← recv0_arm4 message.first message.second
  returnData (UInt256.ofNat 0) (UInt256.ofNat 0)

def runtime : FeM Empty := do
  let size ← calldatasize
  if size.toNat < 4 then
    revertEmpty
  else
    let selector ← calldataSelector
    if selector = UInt256.ofNat 0x054c1a75 then
      recv0_arm1_entry
    else if selector = UInt256.ofNat 0x90bb7b44 then
      recv0_arm0_entry
    else if selector = UInt256.ofNat 0x92cf1ef5 then
      recv0_arm4_entry
    else if selector = UInt256.ofNat 0x9bc39d3c then
      recv0_arm3_entry
    else if selector = UInt256.ofNat 0xf26feec9 then
      recv0_arm2_entry
    else
      revertEmpty

def init_entry (args : ByteArray) : FeM ByteArray := do
  nonPayable
  let _ ← init
  return ByteArray.empty

-- END fe-lean-export

end

/- The proofs name the library's other definitions too. -/
export_all FeProofs.Lib

/-! ## The constants -/

theorem lanesPerSlot : LANES_PER_SLOT_8 = pure ⟨32⟩ := by
  simp [LANES_PER_SLOT_8, checkedDiv]
  rfl

theorem laneMask : LANE_MASK_8 = pure ⟨255⟩ := by
  simp [LANE_MASK_8, checkedSub]
  rfl

theorem u256Mask : U256_MASK = pure (UInt256.lnot ⟨0⟩) := by
  simp [U256_MASK]
  rfl

/-! ## The arms -/

/-- The slot of word 0 of the array in the contract field `pack`: entry 0 of the map `words`
    at slot 0. -/
def wordSlot : UInt256 := mapSlot ⟨0⟩ ⟨0⟩

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `locate` of a word of the array: std's `mapping_slot` stores the key and the map's root in a
    fresh buffer and hashes it. -/
theorem locate_exec (p : Place) (root key : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (locate_u256_u256 p root key).exec I w =
      some (.ok (⟨mapSlot key root, UInt256.ofNat 0⟩,
        { w with memory := keyed w.memory key root })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    Reasoning.Theory.ulit_toNat' _ (by omega)
  have hnext : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [Reasoning.Theory.uadd_toNat, hsize, toNat32]
    exact Nat.mod_eq_of_lt (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [locate_u256_u256, mapping_slot_u256, encoded_len, downcast_saturate_u256_usize, to_word,
    from_word_1, IS_SIGNED, MASK_1, I256_SIGN_BIT, SIGN_BIT, sign_extend, new_uninit, alloc_bytes,
    MAX_ALLOCATION, max, downcast_saturate_u64_usize, to_word_1, PANIC_OUT_OF_MEMORY, ptr,
    write_key, downcast_unchecked_u256_usize, from_raw_parts_ref_u8, keccak256_1, ptr_u8, len_u8,
    drop, dealloc_u8, cast_u8_u8, checkedAdd, checkedSub, alloc, mstore, keccak256, panicCode,
    toNat0, toNat32, toNat64, toNatMax, toNatU64, add32_32, hsize, hnext, UInt256.size, hroom,
    keyed]
  exact keyed_slot w.memory key root

/-- `w` with the buffer a lookup of word 0 of the array leaves: its key and the map's root, both
    zero. -/
def afterLookup (w : World) : World := { w with memory := keyed w.memory ⟨0⟩ ⟨0⟩ }

theorem afterLookup_size : (afterLookup w).memory.size = w.memory.size + 64 := keyed_size _ _ _

theorem get0_exec (hmem : w.memory.size + 64 < UInt256.size) :
    recv0_arm0.exec I w =
      some (.ok (packedByte (slotWord I w.accounts wordSlot) 0, afterLookup w)) := by
  simp [recv0_arm0, get_8, lanesPerSlot, laneMask, Field.pack, Layout.StoragePackedArray_8,
    checkedRem, checkedDiv, locate_exec _ _ _ _ _ hmem, afterLookup]
  exact ⟨rfl, rfl⟩

theorem get1_exec (hmem : w.memory.size + 64 < UInt256.size) :
    recv0_arm1.exec I w =
      some (.ok (packedByte (slotWord I w.accounts wordSlot) 1, afterLookup w)) := by
  simp [recv0_arm1, get_8, lanesPerSlot, laneMask, Field.pack, Layout.StoragePackedArray_8,
    checkedRem, checkedDiv, locate_exec _ _ _ _ _ hmem, afterLookup]
  exact ⟨rfl, rfl⟩

/-- The accounts after lane `lane` of the word at `wordSlot` is set to the low byte of
    `value`. -/
def setLane (I : ExecutionEnv) (σ : AccountMap) (lane : Fin 32) (value : UInt256) : AccountMap :=
  storeWord I.codeOwner σ wordSlot (setPackedByte (slotWord I σ wordSlot) value lane)

theorem set0_exec (value : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm2 value).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup w with accounts := setLane I w.accounts 0 value }))
      else some (.error .static) := by
  simp [recv0_arm2, set_8, lanesPerSlot, laneMask, u256Mask, Field.pack,
    Layout.StoragePackedArray_8, checkedRem, checkedDiv, exec_sstore,
    locate_exec _ _ _ _ _ hmem, afterLookup]
  rfl

theorem set1_exec (value : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm3 value).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup w with accounts := setLane I w.accounts 1 value }))
      else some (.error .static) := by
  simp [recv0_arm3, set_8, lanesPerSlot, laneMask, u256Mask, Field.pack,
    Layout.StoragePackedArray_8, checkedRem, checkedDiv, exec_sstore,
    locate_exec _ _ _ _ _ hmem, afterLookup]
  rfl

theorem setBoth_exec (first second : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    (recv0_arm4 first second).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup (afterLookup w) with
          accounts := setLane I (setLane I w.accounts 0 first) 1 second }))
      else some (.error .static) := by
  cases hperm : I.perm <;>
    simp (disch := (try simp only [keyed_size]); omega) [recv0_arm4, set_8, lanesPerSlot,
      laneMask, u256Mask, Field.pack, Layout.StoragePackedArray_8, checkedRem, checkedDiv,
      exec_sstore, hperm, locate_exec, afterLookup]
  exact ⟨rfl, rfl⟩

end FeProofs.PackedStore.Exported
