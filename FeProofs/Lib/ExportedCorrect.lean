import FeProofs.Lib.Exported

/-!
# Exported core and std code: what it does

Facts about the shared definitions of `Exported.lean` that the contracts' proofs use: what
std's `return_value` does, and the memory a deployment entry leaves.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.Lib

attribute [local simp]
  new input SELECTOR_SIZE to_word IS_SIGNED U64_MASK MASK SIGN_BIT U256_MASK sign_extend from_word
  downcast_truncate_u256_u64 size len_CallData from_word_1 validate_runtime_head IS_DYNAMIC
  HEAD_SIZE_1 max to_word_1 MASK_1 I256_SIGN_BIT downcast_saturate_u64_usize MAX_ALLOCATION
  PANIC_OUT_OF_MEMORY alloc_bytes alloc_uninit_32 zero_bytes alloc_32 ptr_32 from_raw_parts
  PANIC_INDEX_OUT_OF_BOUNDS index_out_of_bounds word_to_usize ptr_offset slice cast_u8_u256
  store_word store_word_1 encode_Sol downcast_unchecked_u256_usize from_raw_parts_ref_u8 ptr_u8
  len_u8 return_data alloc_uninit_64 alloc_64 ptr_64 new_uninit new_1 ptr span_ref const_u256
  payload_size_u256 abi_payload_size_u256 max_1 allocation_len encode_alloc_Sol_u256
  abi_field_size_u256 abi_single_root_size_u256 abi_field_head_size_u256
  abi_single_root_head_size_u256 tail len encode_field_Sol_u256 encode_single_root_alloc_Sol_u256
  encode_return_alloc_Sol_u256 return_bytes return_value_Sol_u256 word_at decode_error
  checked_tail_Sol checked_frame_end_Sol decode_from_Sol_CallData
  decode_from_bounded_u256_Sol_CallData decode_field_from_prechecked_head_Sol_u256_CallData
  decode_field_from_Sol_u256_CallData decode_msg_field_from_Sol_u256_CallData with_base
  decoder_new downcast_truncate_usize_u64 size_1 len_MemSlice_u8 word_at_1 read_word_MemSlice_u8
  base pos set_base set_pos decode_payload_Sol_SolDecoder_MemSlice_u8
  decode_field_Sol_u256_SolDecoder_MemSlice_u8 decode_payload_Sol_u256_SolDecoder_MemSlice_u8
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `u256` ends the call with the word's 32 bytes.  It changes memory only. -/
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
