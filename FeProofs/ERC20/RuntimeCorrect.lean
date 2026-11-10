import FeProofs.ERC20.ExportedCorrect
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeERC20: the bytecode refines the exported contract

`Exported.lean` ends with the runtime entry as `fe-lean-export` prints it: each arm's entry
decodes the message with std's `decode_runtime_args`, runs the arm and returns through std's
`return_value`, and `runtime` dispatches on the selector.  This file shows that entry ends as
the hand-written one of `ExportedCorrect.lean` does, so the certificate for that one carries over.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.ERC20.Exported

/-- Std's address check, `word >> 160 != 0`, is the hand-written one. -/
theorem shr160_eq_zero_iff (w : UInt256) :
    w >>> UInt256.ofNat 160 = UInt256.ofNat 0 ↔ ¬ NotAddress w := by
  unfold NotAddress
  constructor
  · intro h hd
    exact shiftRight160_ne_zero (by simpa [EVM.addressModulus] using hd) h
  · intro h
    exact shiftRight160_eq_zero (by simpa [EVM.addressModulus] using Nat.lt_of_not_le h)

/-! ## Std code

The std definitions the entry reaches unfold under `simp` in this section. -/

section Std

attribute [local simp]
  new input SELECTOR_SIZE to_word IS_SIGNED U64_MASK MASK SIGN_BIT U256_MASK sign_extend 
  from_word downcast_truncate_u256_u64 size len_CallData IS_DYNAMIC HEAD_SIZE 
  abi_field_head_size_Address abi_field_head_size_u256 HEAD_SIZE_1 from_word_1 
  validate_runtime_head word_at decode_error checked_tail_Sol checked_frame_end_Sol 
  decode_from_Sol_CallData decode_from_bounded_Address_Sol_CallData 
  decode_field_from_prechecked_head_Sol_Address_CallData decode_field_from_Sol_Address_CallData 
  decode_msg_field_from_Sol_Address_CallData decode_from_Sol_CallData_1 
  decode_from_bounded_u256_Sol_CallData decode_field_from_prechecked_head_Sol_u256_CallData 
  decode_field_from_Sol_u256_CallData decode_msg_field_from_Sol_u256_CallData 
  decode_from_CallData decode_from_prechecked_head_Transfer_Sol_CallData 
  decode_runtime_args_Evm_Sol_Transfer max to_word_1 MASK_1 I256_SIGN_BIT 
  downcast_saturate_u64_usize MAX_ALLOCATION PANIC_OUT_OF_MEMORY alloc_bytes alloc_uninit_32 
  zero_bytes alloc_32 ptr_32 from_raw_parts PANIC_INDEX_OUT_OF_BOUNDS index_out_of_bounds 
  word_to_usize ptr_offset slice cast_u8_u256 store_word store_word_1 encode_Sol 
  downcast_unchecked_u256_usize from_raw_parts_ref_u8 ptr_u8 len_u8 return_data alloc_uninit_64 
  alloc_64 ptr_64 new_uninit new_1 ptr span_ref const_bool payload_size_bool 
  abi_payload_size_bool max_1 allocation_len encode_alloc_Sol_bool abi_field_size_bool 
  abi_single_root_size_bool abi_field_head_size_bool abi_single_root_head_size_bool tail len 
  encode_field_Sol_bool encode_single_root_alloc_Sol_bool encode_return_alloc_Sol_bool 
  return_bytes return_value_Sol_bool decode_from_CallData_1 
  decode_from_prechecked_head_Approve_Sol_CallData decode_runtime_args_Evm_Sol_Approve 
  HEAD_SIZE_2 decode_from_CallData_2 decode_from_prechecked_head_TransferFrom_Sol_CallData 
  decode_runtime_args_Evm_Sol_TransferFrom HEAD_SIZE_3 decode_from_CallData_3 
  decode_from_prechecked_head_BalanceOf_Sol_CallData decode_runtime_args_Evm_Sol_BalanceOf 
  encode_Sol_1 const_u256 payload_size_u256 abi_payload_size_u256 encode_alloc_Sol_u256 
  abi_field_size_u256 abi_single_root_size_u256 abi_single_root_head_size_u256 
  encode_field_Sol_u256 encode_single_root_alloc_Sol_u256 encode_return_alloc_Sol_u256 
  return_value_Sol_u256 HEAD_SIZE_4 decode_from_CallData_4 
  decode_from_prechecked_head_Allowance_Sol_CallData decode_runtime_args_Evm_Sol_Allowance 
  HEAD_SIZE_5 decode_from_CallData_5 decode_from_prechecked_head_TotalSupply_Sol_CallData 
  decode_runtime_args_Evm_Sol_TotalSupply with_base decoder_new downcast_truncate_usize_u64 
  size_1 len_MemSlice_u8 word_at_1 read_word_MemSlice_u8 base pos set_base set_pos 
  decode_payload_Sol_SolDecoder_MemSlice_u8 decode_field_Sol_u256_SolDecoder_MemSlice_u8 
  decode_payload_Sol_u256_SolDecoder_MemSlice_u8
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeTransfer_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Transfer.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat4, toNat32, truncate_size _ hfits, UInt256.size, add0_32, add32_32,
    ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 68 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeApprove_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Approve.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat4, toNat32, truncate_size _ hfits, UInt256.size, add0_32, add32_32,
    ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 68 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeBalanceOf_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_BalanceOf.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, UInt256.size, add0_32, ne32, at4,
    headCheck hlo hfits (by norm_num : 32 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 36 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeAllowance_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Allowance.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 36) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat4, toNat32, truncate_size _ hfits, UInt256.size, add0_32, add32_32,
    ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 68 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    by_cases hb : NotAddress (uInt256OfByteArray (I.calldata.readBytes 36 32)) <;>
    simp [h, ha, hb, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeTransferFrom_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_TransferFrom.exec I w =
      if I.calldata.size < 100 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 36) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36, word I.calldata 68⟩, w)) := by
  have hshort : I.calldata.size - 4 < 96 ↔ I.calldata.size < 100 := by omega
  simp [toNat0, toNat4, toNat32, toNat64, toNat4_32, truncate_size _ hfits, UInt256.size,
    add0_32, add32_32, add64_32, ne96, at4, at36, at68,
    headCheck hlo hfits (by norm_num : 96 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 100 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    by_cases hb : NotAddress (uInt256OfByteArray (I.calldata.readBytes 36 32)) <;>
    simp [h, ha, hb, word]

theorem decodeTotalSupply_exec :
    decode_runtime_args_Evm_Sol_TotalSupply.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

/-! ### The returns -/

theorem encodeBool_eq (b : Bool) : Model.encodeBool b = (Bool.toUInt256 b).toByteArray := by
  cases b <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem returnBool_exec (b : Bool) (hmem : w.memory.size < UInt256.size) :
    (return_value_Sol_bool b).exec I w =
      some (.error (.stop (Model.encodeBool b)
        { w with memory := returned w.memory (Bool.toUInt256 b) })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ hmem
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    returned, encodeBool_eq]
  exact returned_read _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem returnU256_exec (v : UInt256) (hmem : w.memory.size < UInt256.size) :
    (return_value_Sol_u256 v).exec I w =
      some (.error (.stop v.toByteArray { w with memory := returned w.memory v })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ hmem
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    returned]
  exact returned_read _ _

/-! ### The constructor argument -/

theorem ctorTail_eq (v : UInt256) : ctorTail v = v.toByteArray := by
  rw [ctorTail, word_toBytesBE_toByteArray_eq_toByteArray]

/-- Memory after the deployment entry copies the one argument word into a fresh buffer. -/
def withArg (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0 (memory ++ ⟨Array.replicate 32 0⟩) memory.size 32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The deployment entry on one argument word: reject call value, then run `init` on the word.
    It changes memory only. -/
theorem initEntry_exec (v : UInt256) (hmem : w.memory.size < UInt256.size) :
    (init_entry (ctorTail v)).exec I w =
      if I.weiValue = ⟨0⟩ then (init v).exec I { w with memory := withArg w.memory v }
      else some (.error (.revert ByteArray.empty)) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ hmem
  have hlen : v.toByteArray.size = 32 := toByteArray_size v
  have hcut : truncate 64 (UInt256.ofNat 32 &&& UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat 32 := by decide
  rw [ctorTail_eq]
  by_cases hwv : I.weiValue = ⟨0⟩
  · simp [init_entry, exec_nonPayable, hwv, toNat0, toNat32, hlen, hsize, Fe.EVM.add_zero,
      UInt256.size, hcut, add0_32, sub32_0, withArg]
    rw [toByteArray_write32_read_back _ _ _ (by rw [ByteArray.size_append]; omega),
      readWithPadding_eq_extract _ 0 (by rw [hlen]), Nat.zero_add, toByteArray_extract_all,
      uInt256OfByteArray_toByteArray]
  · simp [init_entry, exec_nonPayable, hwv]

end Std

/-! ## The arms leave memory alone -/

theorem keeps_transfer (dst value : UInt256) : KeepsMemory (recv0_arm0 dst value) := by
  intro I w a w' h
  rw [transfer_exec] at h
  exact (show KeepsMemory (Model.transfer dst value) by unfold Model.transfer; keeps_memory)
    I w a w' h

theorem keeps_approve (spender value : UInt256) : KeepsMemory (recv0_arm1 spender value) := by
  intro I w a w' h
  rw [approve_exec] at h
  exact (show KeepsMemory (Model.approve spender value) by unfold Model.approve; keeps_memory)
    I w a w' h

theorem keeps_transferFrom (src dst value : UInt256) :
    KeepsMemory (recv0_arm2 src dst value) := by
  intro I w a w' h
  rw [transferFrom_exec] at h
  exact (show KeepsMemory (Model.transferFrom src dst value) by
    unfold Model.transferFrom; keeps_memory) I w a w' h

theorem keeps_balanceOf (owner : UInt256) : KeepsMemory (recv0_arm3 owner) := by
  intro I w a w' h
  rw [balanceOf_exec] at h
  exact (show KeepsMemory (Model.balanceOf owner) by unfold Model.balanceOf; keeps_memory)
    I w a w' h

theorem keeps_allowance (owner spender : UInt256) : KeepsMemory (recv0_arm4 owner spender) := by
  intro I w a w' h
  rw [allowance_exec] at h
  exact (show KeepsMemory (Model.allowance owner spender) by
    unfold Model.allowance; keeps_memory) I w a w' h

theorem keeps_totalSupply : KeepsMemory recv0_arm5 := by
  intro I w a w' h
  rw [totalSupply_exec] at h
  exact (show KeepsMemory Model.totalSupply by unfold Model.totalSupply; keeps_memory)
    I w a w' h

/-! ## The arms' entries -/

section Entries

variable (I : ExecutionEnv) (w : World)

theorem transfer_endsAs (hmem : w.memory.size < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm0_entry).exec I w) ((transferArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv])]
    simp [transferArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort])]
    simp [transferArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort, ha0])]
    simp [transferArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm0_entry).exec I w =
      (entry (recv0_arm0 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort, ha0]
  have eh : (transferArm I.calldata).exec I w =
      (recv0_arm0 (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [transferArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩) (keeps_transfer _ _) hmem

theorem approve_endsAs (hmem : w.memory.size < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm1_entry).exec I w) ((approveArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv])]
    simp [approveArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort])]
    simp [approveArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort, ha0])]
    simp [approveArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm1_entry).exec I w =
      (entry (recv0_arm1 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort, ha0]
  have eh : (approveArm I.calldata).exec I w =
      (recv0_arm1 (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [approveArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩) (keeps_approve _ _) hmem

theorem transferFrom_endsAs (hmem : w.memory.size < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm2_entry).exec I w) ((transferFromArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 3 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv])]
    simp [transferFromArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 100
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort])]
    simp [transferFromArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 3 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0])]
    simp [transferFromArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  by_cases ha1 : NotAddress (word I.calldata 36)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0, ha1])]
    simp [transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1]
    exact .exit _
  have eg : (entry recv0_arm2_entry).exec I w =
      (entry (recv0_arm2 (word I.calldata 4) (word I.calldata 36) (word I.calldata 68) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0, ha1]
  have eh : (transferFromArm I.calldata).exec I w =
      (recv0_arm2 (word I.calldata 4) (word I.calldata 36) (word I.calldata 68) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩) (keeps_transferFrom _ _ _) hmem

theorem balanceOf_endsAs (hmem : w.memory.size < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm3_entry).exec I w) ((balanceOfArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv])]
    simp [balanceOfArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort])]
    simp [balanceOfArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort, ha0])]
    simp [balanceOfArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm3_entry).exec I w =
      (entry (recv0_arm3 (word I.calldata 4) >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort, ha0]
  have eh : (balanceOfArm I.calldata).exec I w =
      (recv0_arm3 (word I.calldata 4) >>= fun r => pure (r.toByteArray)).exec I w := by
    simp [balanceOfArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (keeps_balanceOf _) hmem

theorem allowance_endsAs (hmem : w.memory.size < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm4_entry).exec I w) ((allowanceArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv])]
    simp [allowanceArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort])]
    simp [allowanceArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0])]
    simp [allowanceArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  by_cases ha1 : NotAddress (word I.calldata 36)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0, ha1])]
    simp [allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1]
    exact .exit _
  have eg : (entry recv0_arm4_entry).exec I w =
      (entry (recv0_arm4 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0, ha1]
  have eh : (allowanceArm I.calldata).exec I w =
      (recv0_arm4 (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (r.toByteArray)).exec I w := by
    simp [allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (keeps_allowance _ _) hmem

theorem totalSupply_endsAs (hmem : w.memory.size < UInt256.size) :
    EndsAs ((entry recv0_arm5_entry).exec I w) (totalSupplyArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm5_entry, exec_nonPayable, hwv])]
    simp [totalSupplyArm, exec_nonPayable, hwv]
    exact .exit _
  have eg : (entry recv0_arm5_entry).exec I w =
      (entry (recv0_arm5 >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm5_entry, exec_nonPayable, hwv, decodeTotalSupply_exec]
  have eh : totalSupplyArm.exec I w = (recv0_arm5 >>= fun r => pure r.toByteArray).exec I w := by
    simp [totalSupplyArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) keeps_totalSupply hmem

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written one does, on calldata below `2 ^ 64`
    bytes. -/
theorem runtime_endsAs (hmem : w.memory.size < UInt256.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (handRuntime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (feERC20SelBytes i)) →
      (feERC20SelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [entry_exec (f := .revert ByteArray.empty) (by simp [runtime, hn, hlt])]
    simp [handRuntime, hlt]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feERC20SelBytes 0)
  · have hw := selWord_hit (approveEvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm1_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (approveArm I.calldata).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = true from h0]
    rw [eg, eh]
    exact approve_endsAs I w hmem hsz hfits
  have n0 := miss 0 h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x095ea7b3 := selWord_miss (approveEvmSelector hsz) n0
  by_cases h1 : selIs I (feERC20SelBytes 1)
  · have hw := selWord_hit (totalSupplyEvmSelector hsz) h1
    have eg : (entry runtime).exec I w = (entry recv0_arm5_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (totalSupplyArm).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = true from h1]
    rw [eg, eh]
    exact totalSupply_endsAs I w hmem
  have n1 := miss 1 h1
  have w1 : selWord I.calldata ≠ UInt256.ofNat 0x18160ddd := selWord_miss (totalSupplyEvmSelector hsz) n1
  by_cases h2 : selIs I (feERC20SelBytes 2)
  · have hw := selWord_hit (transferFromEvmSelector hsz) h2
    have eg : (entry runtime).exec I w = (entry recv0_arm2_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (transferFromArm I.calldata).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = true from h2]
    rw [eg, eh]
    exact transferFrom_endsAs I w hmem hsz hfits
  have n2 := miss 2 h2
  have w2 : selWord I.calldata ≠ UInt256.ofNat 0x23b872dd := selWord_miss (transferFromEvmSelector hsz) n2
  by_cases h3 : selIs I (feERC20SelBytes 3)
  · have hw := selWord_hit (balanceOfEvmSelector hsz) h3
    have eg : (entry runtime).exec I w = (entry recv0_arm3_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (balanceOfArm I.calldata).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = true from h3]
    rw [eg, eh]
    exact balanceOf_endsAs I w hmem hsz hfits
  have n3 := miss 3 h3
  have w3 : selWord I.calldata ≠ UInt256.ofNat 0x70a08231 := selWord_miss (balanceOfEvmSelector hsz) n3
  by_cases h4 : selIs I (feERC20SelBytes 4)
  · have hw := selWord_hit (transferEvmSelector hsz) h4
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (transferArm I.calldata).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.transferSelector == I.calldata.extract 0 4) = true from h4]
    rw [eg, eh]
    exact transfer_endsAs I w hmem hsz hfits
  have n4 := miss 4 h4
  have w4 : selWord I.calldata ≠ UInt256.ofNat 0xa9059cbb := selWord_miss (transferEvmSelector hsz) n4
  by_cases h5 : selIs I (feERC20SelBytes 5)
  · have hw := selWord_hit (allowanceEvmSelector hsz) h5
    have eg : (entry runtime).exec I w = (entry recv0_arm4_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (allowanceArm I.calldata).exec I w := by
      simp [handRuntime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.transferSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.allowanceSelector == I.calldata.extract 0 4) = true from h5]
    rw [eg, eh]
    exact allowance_endsAs I w hmem hsz hfits
  have n5 := miss 5 h5
  have w5 : selWord I.calldata ≠ UInt256.ofNat 0xdd62ed3e := selWord_miss (allowanceEvmSelector hsz) n5
  rw [entry_exec (f := .revert ByteArray.empty) (by
    simp [runtime, hn, hn4, selector_exec, w0, w1, w2, w3, w4, w5])]
  simp [handRuntime, hn4,
    show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
    show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
    show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
    show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
    show (Model.transferSelector == I.calldata.extract 0 4) = false from n4,
    show (Model.allowanceSelector == I.calldata.extract 0 4) = false from n5]
  exact .exit _

end Entries

/-! ## Deployment -/

/-- The exported deployment entry ends as the hand-written one does, on one argument word. -/
theorem init_endsAs (v : UInt256) (out : ByteArray) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size < UInt256.size) :
    EndsAs ((init_entry (ctorTail v) >>= fun _ => pure out).exec I w)
      ((initEntry (ctorTail v) >>= fun _ => pure out).exec I w) := by
  have hsz : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hword : word (ctorTail v) 0 = v := by
    show uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v
    rw [readBytes_all32 _ hsz, ctorTail, word_toBytesBE_toByteArray_eq_toByteArray,
      uInt256OfByteArray_toByteArray]
  rw [M.exec_bind, initEntry_exec I w v hmem]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [initEntry, exec_nonPayable, hwv]
    exact .exit _
  by_cases hperm : I.perm = true
  · simp [initEntry, exec_nonPayable, hwv, hsz, hword, init_exec, Model.initBody, exec_sstore,
      exec_emit, hperm]
    exact .ok_ok rfl rfl
  · simp [initEntry, exec_nonPayable, hwv, hsz, hword, init_exec, Model.initBody, exec_sstore,
      hperm]
    exact .exit _

/-! ## The certificate -/

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := ⟨init_entry, entry runtime⟩

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem feERC20RefinesExported : RefinesOn .P0 feERC20Bytecode contract CalldataFits := by
  intro σ σ₀ g A I hcode hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feERC20RefinesHandEntry σ σ₀ g A I hcode hsize with h | h
  · exact Or.inl h
  · exact Or.inr (Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A) (by simp [World.init, UInt256.size]) hfits) h)

/-- Deployment with one ABI-encoded `uint256` argument refines the exported deployment entry. -/
theorem feERC20DeployRefinesExported :
    RefinesDeploy .P0 feERC20CreationBytecode feERC20Bytecode contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  rcases feERC20DeployRefinesHandEntry σ σ₀ g A I _ ⟨v, rfl⟩ hcode hperm with h | h
  · exact Or.inl h
  · exact Or.inr (Agrees.of_endsAs
      (init_endsAs v _ I (World.init σ A) (by simp [World.init, UInt256.size])) h)

end FeProofs.ERC20.Exported
