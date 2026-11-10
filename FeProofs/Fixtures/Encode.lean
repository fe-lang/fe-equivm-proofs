import FeProofs.Fixtures.Exported
import Reasoning.EVMWord
import Reasoning.Memory

/-!
# The std ABI encoder, as exported

`FeProofs.Fixtures.Encode.revert_u256` is `std::evm::revert<u256>` as `fe-lean-export` prints it
from std: size the encoding, allocate and zero a buffer, write the word through a raw pointer,
and revert with the buffer's bytes.  This file proves what that code does.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Fixtures.Encode

theorem add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply u256_inj
  rw [uadd_toNat, show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

/-- `revert(value)` for a `u256` reverts with the value's 32-byte big-endian encoding, whatever
    memory held before. -/
theorem revert_exec (value : UInt256) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size < UInt256.size) :
    (recv0_arm0 value).exec I w = some (.error (.revert value.toByteArray)) := by
  have hmax : (~~~UInt256.ofNat 0).toNat = UInt256.size - 1 := by decide
  have h32 : (UInt256.ofNat 32).toNat = 32 := rfl
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h64 : (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 := rfl
  have hsub : (UInt256.ofNat 32 - UInt256.ofNat 0).toNat = 32 := rfl
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ hmem
  simp [recv0_arm0, HEAD_SIZE, payload_size_u256, IS_DYNAMIC, abi_field_size_u256, abi_single_root_size_u256, max, PANIC_OUT_OF_MEMORY, word_to_usize, allocation_len, max_1, to_word, IS_SIGNED, MASK, from_word, I256_SIGN_BIT, SIGN_BIT, U256_MASK, sign_extend, downcast_saturate_u64_usize, MAX_ALLOCATION, alloc_bytes, new_uninit, zero_bytes, new, ptr, from_raw_parts, abi_field_head_size_u256, abi_single_root_head_size_u256, PANIC_INDEX_OUT_OF_BOUNDS, index_out_of_bounds, ptr_offset, tail, len, slice, cast_u8_u256, store_word, store_word_1, encode_Sol, encode_field_Sol_u256, encode_single_root_alloc_Sol_u256, len_1, revert_u256, checkedAdd, checkedSub, alloc, mstore, zeroMem, revertData, panicCode,
    hmax, h32, h0, h64, hsub, hsize, add_zero, UInt256.size]
  -- The buffer is the 32 zero bytes `alloc` appended; the word written there reads back.
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  apply toByteArray_write32_read_back
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hzeros])
    (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]
  omega

end FeProofs.Fixtures.Encode
