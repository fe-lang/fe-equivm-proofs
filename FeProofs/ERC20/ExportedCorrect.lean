import FeProofs.ERC20.Exported
import FeProofs.ERC20.ModelCorrect
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeERC20: what the exported code does

`Exported.lean` is the exporter's output and nothing else.  This file proves what it does: the
std code it calls (event encodings, calldata decoders, return encoders, the constructor argument
decoder), and that each exported arm ends as the hand-written model arm does, up to memory.
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

The std definitions the arms and entries reach unfold under `simp` in this section. -/

section Std

attribute [local simp]
  IS_DYNAMIC HEAD_SIZE abi_field_head_size_u256 HEAD_SIZE_u256 payload_size_u256 
  dynamic_payload_size_u256 payload_size_u256_1 abi_payload_size_u256 max PANIC_OUT_OF_MEMORY 
  word_to_usize allocation_len max_1 to_word IS_SIGNED MASK from_word I256_SIGN_BIT SIGN_BIT 
  U256_MASK sign_extend downcast_saturate_u64_usize MAX_ALLOCATION alloc_bytes new_uninit 
  zero_bytes new ptr from_raw_parts PANIC_INDEX_OUT_OF_BOUNDS index_out_of_bounds ptr_offset tail 
  len slice cast_u8_u256 store_word store_word_1 encode_Sol encode_field_Sol_u256 encode_Sol_u256 
  encode_alloc_Sol_u256 encode_abi_payload_u256 from_raw_parts_ref_u8 span_ref as_topic ptr_u8 
  len_u8 log3 cast_u8_u8 dealloc_u8 drop emit_Evm emit_Evm_Transfer emit_Evm_1 emit_Evm_Approval 
  new_1 input SELECTOR_SIZE to_word_1 U64_MASK MASK_1 from_word_1 downcast_truncate_u256_u64 size 
  len_CallData abi_field_head_size_Address HEAD_SIZE_1 validate_runtime_head word_at decode_error 
  checked_tail_Sol checked_frame_end_Sol decode_from_Sol_CallData 
  decode_from_bounded_Address_Sol_CallData decode_field_from_prechecked_head_Sol_Address_CallData 
  decode_field_from_Sol_Address_CallData decode_msg_field_from_Sol_Address_CallData 
  decode_from_Sol_CallData_1 decode_from_bounded_u256_Sol_CallData 
  decode_field_from_prechecked_head_Sol_u256_CallData decode_field_from_Sol_u256_CallData 
  decode_msg_field_from_Sol_u256_CallData decode_from_CallData 
  decode_from_prechecked_head_Transfer_Sol_CallData decode_runtime_args_Evm_Sol_Transfer 
  alloc_uninit_32 alloc_32 ptr_32 encode_Sol_1 downcast_unchecked_u256_usize return_data 
  alloc_uninit_64 alloc_64 ptr_64 const_bool payload_size_bool abi_payload_size_bool 
  encode_alloc_Sol_bool abi_field_size_bool abi_single_root_size_bool abi_field_head_size_bool 
  abi_single_root_head_size_bool encode_field_Sol_bool encode_single_root_alloc_Sol_bool 
  encode_return_alloc_Sol_bool return_bytes return_value_Sol_bool decode_from_CallData_1 
  decode_from_prechecked_head_Approve_Sol_CallData decode_runtime_args_Evm_Sol_Approve 
  HEAD_SIZE_2 decode_from_CallData_2 decode_from_prechecked_head_TransferFrom_Sol_CallData 
  decode_runtime_args_Evm_Sol_TransferFrom HEAD_SIZE_3 decode_from_CallData_3 
  decode_from_prechecked_head_BalanceOf_Sol_CallData decode_runtime_args_Evm_Sol_BalanceOf 
  const_u256 abi_payload_size_u256_1 encode_alloc_Sol_u256_1 abi_field_size_u256 
  abi_single_root_size_u256 abi_single_root_head_size_u256 encode_single_root_alloc_Sol_u256 
  encode_return_alloc_Sol_u256 return_value_Sol_u256 HEAD_SIZE_4 decode_from_CallData_4 
  decode_from_prechecked_head_Allowance_Sol_CallData decode_runtime_args_Evm_Sol_Allowance 
  HEAD_SIZE_5 decode_from_CallData_5 decode_from_prechecked_head_TotalSupply_Sol_CallData 
  decode_runtime_args_Evm_Sol_TotalSupply with_base decoder_new downcast_truncate_usize_u64 
  size_1 len_MemSlice_u8 word_at_1 read_word_MemSlice_u8 base pos set_base set_pos 
  decode_payload_Sol_SolDecoder_MemSlice_u8 decode_field_Sol_u256_SolDecoder_MemSlice_u8 
  decode_payload_Sol_u256_SolDecoder_MemSlice_u8
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData logData
  panicCode

variable (I : ExecutionEnv) (w : World)

/-! ### Events -/

/-- The topic the compiler evaluates for `Transfer` is the hash of its signature. -/
theorem transferTopic_eq : Model.transferTopic =
    UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991 := by
  native_decide

/-- The topic the compiler evaluates for `Approval` is the hash of its signature. -/
theorem approvalTopic_eq : Model.approvalTopic =
    UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925 := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Transfer`: a log entry with the signature hash
    and the two addresses as topics and the value as data, encoded in a fresh buffer.  Under a
    static call it fails. -/
theorem emitTransfer_exec (e : Transfer) :
    (emit_Evm_Transfer e).exec I w =
      if w.memory.size + 32 < UInt256.size then
        if I.perm then
          some (.ok ((), { w with
            logs := w.logs.push ⟨I.codeOwner, #[Model.transferTopic, e.«from», e.«to»],
              e.value.toByteArray⟩,
            memory := returned w.memory e.value }))
        else some (.error .static)
      else none := by
  by_cases hmem : w.memory.size + 32 < UInt256.size
  · have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
      ulit_toNat' _ (by omega)
    have hroom := hmem
    simp only [UInt256.size] at hroom
    simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
      hroom, exec_emit, returned_read, returned, transferTopic_eq]
  · have hroom := hmem
    simp only [UInt256.size] at hroom
    simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, UInt256.size, hroom]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Approval`. -/
theorem emitApproval_exec (e : Approval) :
    (emit_Evm_Approval e).exec I w =
      if w.memory.size + 32 < UInt256.size then
        if I.perm then
          some (.ok ((), { w with
            logs := w.logs.push ⟨I.codeOwner, #[Model.approvalTopic, e.owner, e.spender],
              e.value.toByteArray⟩,
            memory := returned w.memory e.value }))
        else some (.error .static)
      else none := by
  by_cases hmem : w.memory.size + 32 < UInt256.size
  · have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
      ulit_toNat' _ (by omega)
    have hroom := hmem
    simp only [UInt256.size] at hroom
    simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
      hroom, exec_emit, returned_read, returned, approvalTopic_eq]
  · have hroom := hmem
    simp only [UInt256.size] at hroom
    simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, UInt256.size, hroom]

/-! ### Decoders -/

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
theorem returnBool_exec (b : Bool) (hmem : w.memory.size + 32 < UInt256.size) :
    (return_value_Sol_bool b).exec I w =
      some (.error (.stop (Model.encodeBool b)
        { w with memory := returned w.memory (Bool.toUInt256 b) })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, returned, encodeBool_eq]
  exact returned_read _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem returnU256_exec (v : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (return_value_Sol_u256 v).exec I w =
      some (.error (.stop v.toByteArray { w with memory := returned w.memory v })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, returned]
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
theorem initEntry_exec (v : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (init_entry (ctorTail v)).exec I w =
      if I.weiValue = ⟨0⟩ then (init v).exec I { w with memory := withArg w.memory v }
      else some (.error (.revert ByteArray.empty)) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  have hlen : v.toByteArray.size = 32 := toByteArray_size v
  have hcut : truncate 64 (UInt256.ofNat 32 &&& UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat 32 := by decide
  rw [ctorTail_eq]
  by_cases hwv : I.weiValue = ⟨0⟩
  · simp [init_entry, exec_nonPayable, hwv, toNat0, toNat32, hlen, hsize, Fe.EVM.add_zero,
      UInt256.size, hroom, hcut, add0_32, sub32_0, withArg]
    rw [toByteArray_write32_read_back _ _ _ (by rw [ByteArray.size_append]; omega),
      readWithPadding_eq_extract _ 0 (by rw [hlen]), Nat.zero_add, toByteArray_extract_all,
      uInt256OfByteArray_toByteArray]
  · simp [init_entry, exec_nonPayable, hwv]

end Std

/-! ## The arms

Each exported arm runs as the hand-written model arm does.  An arm that emits an event leaves
the encoded value in a fresh buffer, so its memory differs. -/

section Arms

variable (I : ExecutionEnv) (w : World)

theorem ofNat0 : UInt256.ofNat 0 = ⟨0⟩ := rfl

/-! The exported layout places the three fields of `TokenStore` at the model's slots. -/

theorem balancesPlace :
    Field.store.field Layout.TokenStore 0 = .storage Model.balancesRoot := rfl
theorem allowancesPlace :
    Field.store.field Layout.TokenStore 1 = .storage Model.allowancesRoot := rfl
theorem totalSupplyPlace :
    Field.store.field Layout.TokenStore 2 = .storage Model.totalSupplySlot := rfl

/-- Close an agreement goal after unfolding: split every branch of both runs, and discharge each
    case by reflexivity, by contradictory bounds, or by simplification. -/
macro "agree" : tactic =>
  `(tactic| repeat' first
    | rfl
    | (exfalso; omega)
    | split
    | simp_all [checkedSub, checkedAdd, exec_sstore, exec_emit])

set_option maxHeartbeats 4000000 in
theorem init_exec (initialSupply : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (init initialSupply).exec I w =
      withMemory (returned w.memory initialSupply) ((Model.initBody initialSupply).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp [ofNat0, balancesPlace, totalSupplyPlace, init, Model.initBody, Model.balanceSlot,
      Model.balancesRoot, Model.totalSupplySlot, emitTransfer_exec, hmem, hp, exec_sstore,
      exec_emit]

set_option maxHeartbeats 4000000 in
theorem transfer_exec (dst value : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (recv0_arm0 dst value).exec I w =
      withMemory (returned w.memory value) ((Model.transfer dst value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp [balancesPlace, recv0_arm0, Model.transfer, Model.balanceSlot, Model.balancesRoot,
      emitTransfer_exec, hmem, hp, checkedSub, checkedAdd, exec_sstore, exec_emit,
      M.ite_bind, M.exec_ite, apply_ite (withMemory _)] <;>
    agree

set_option maxHeartbeats 4000000 in
theorem approve_exec (spender value : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (recv0_arm1 spender value).exec I w =
      withMemory (returned w.memory value) ((Model.approve spender value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp [allowancesPlace, recv0_arm1, Model.approve, Model.allowanceSlot, Model.allowancesRoot,
      emitApproval_exec, hmem, hp, exec_sstore, exec_emit]

set_option maxHeartbeats 4000000 in
theorem transferFrom_exec (src dst value : UInt256)
    (hmem : w.memory.size + 32 < UInt256.size) :
    (recv0_arm2 src dst value).exec I w =
      withMemory (returned w.memory value) ((Model.transferFrom src dst value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp [balancesPlace, allowancesPlace, recv0_arm2, Model.transferFrom, Model.balanceSlot,
      Model.balancesRoot, Model.allowanceSlot, Model.allowancesRoot, emitTransfer_exec, hmem, hp,
      checkedSub, checkedAdd, exec_sstore, exec_emit, M.ite_bind, M.exec_ite,
      apply_ite (withMemory _)] <;>
    agree

theorem balanceOf_exec (owner : UInt256) :
    (recv0_arm3 owner).exec I w = (Model.balanceOf owner).exec I w := by
  simp [balancesPlace, recv0_arm3, Model.balanceOf, Model.balanceSlot, Model.balancesRoot]

theorem allowance_exec (owner spender : UInt256) :
    (recv0_arm4 owner spender).exec I w = (Model.allowance owner spender).exec I w := by
  simp [allowancesPlace, recv0_arm4, Model.allowance, Model.allowanceSlot, Model.allowancesRoot]

theorem totalSupply_exec : recv0_arm5.exec I w = Model.totalSupply.exec I w := by
  simp [totalSupplyPlace, recv0_arm5, Model.totalSupply, Model.totalSupplySlot]

end Arms

end FeProofs.ERC20.Exported
