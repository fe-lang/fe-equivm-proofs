import FeProofs.Lib.ExportedCorrect
import FeProofs.ScalarStore.Exported
import FeProofs.ScalarStore.Constructor

/-!
# FeScalarStore: the std code of the exported entries

What the std code the exported entries reach does, independently of any model: each message's
decoder (through std's decoder pieces, `FeProofs/Lib/ExportedCorrect.lean`) and the deployment
entry on one argument word; and the contract as exported, `contract`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (lenCallData_exec validateHead_exec decodeU256Field_exec withArg)

namespace FeProofs.ScalarStore.Exported

attribute [local simp]
  Get_HEAD_SIZE Get_decode_from_CallData decode_from_prechecked_head_Get_Sol_CallData
  decode_runtime_args_Evm_Sol_Get Set_HEAD_SIZE Set_decode_from_CallData
  decode_from_prechecked_head_Set_Sol_CallData decode_runtime_args_Evm_Sol_Set checkedAdd
  checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

/-- `decode_runtime_args` at `Set { value: u256 }`: revert on calldata that cannot hold the
    selector and one word, otherwise the word after the selector. -/
theorem decodeSet_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Set.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  simp only [decode_runtime_args_Evm_Sol_Set, Evm_input, CallData_new, Sol_SELECTOR_SIZE,
    Fe.M.exec_bind, Fe.M.exec_pure, pure_bind]
  rw [lenCallData_exec I w hfits]
  simp only [Set_HEAD_SIZE, abi_field_head_size_u256, u256_IS_DYNAMIC, u256_HEAD_SIZE,
    checkedAdd, add0_32, Fe.M.exec_pure, pure_bind, if_false, Bool.false_eq_true,
    toNat0, toNat32, show ¬ UInt256.size ≤ 0 + 32 by decide]
  rw [validateHead_exec I w hlo hfits (by decide) (by decide)]
  by_cases h : I.calldata.size < 4 + 32
  · simp [h]
  · simp only [h, if_false, decode_from_prechecked_head_Set_Sol_CallData, Set_decode_from_CallData,
      Fe.M.exec_bind, Fe.M.exec_pure, lenCallData_exec I w hfits,
      decodeU256Field_exec I w _ _ (show 4 < UInt256.size by decide)]

/-- `decode_runtime_args` at `Get`: nothing to decode, and no head to check. -/
theorem decodeGet_exec : decode_runtime_args_Evm_Sol_Get.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem ctorTail_eq (v : UInt256) : ctorTail v = v.toByteArray := by
  rw [ctorTail, word_toBytesBE_toByteArray_eq_toByteArray]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The deployment entry on one argument word: reject call value, then run `init` on the word.
    It changes memory only. -/
theorem initEntry_exec (v : UInt256) (hmem : w.memory.size + 32 < UInt256.size) :
    (init_entry (ctorTail v)).exec I w =
      if I.weiValue = ⟨0⟩ then
        (init v >>= fun _ => pure ByteArray.empty).exec I { w with memory := withArg w.memory v }
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

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

end FeProofs.ScalarStore.Exported
