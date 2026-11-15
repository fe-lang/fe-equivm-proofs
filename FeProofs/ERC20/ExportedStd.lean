import FeProofs.Lib.ExportedCorrect
import FeProofs.ERC20.Exported
import FeProofs.ERC20.Model
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeERC20: the std code of the exported entries

What the std code the exported arms and entries reach does, independently of any model: the
event encodings, with the topics the compiler evaluated into the exported code, the calldata
decoders, the return encoding of a boolean, and the deployment entry on one argument word; and
the contract as exported, `contract`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (returnU256_exec withArg locateAddress_exec locateAddressMap_exec
  shr160_eq_zero_iff)

namespace FeProofs.ERC20.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads, and trying them is half the cost of the arms below. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

section Std


attribute [local simp]
  Transfer_emit_Evm emit_Evm_Transfer Approval_emit_Evm emit_Evm_Approval Transfer_HEAD_SIZE
  Approve_HEAD_SIZE Transfer_decode_from_CallData
  decode_from_prechecked_head_Transfer_Sol_CallData decode_runtime_args_Evm_Sol_Transfer
  Approve_decode_from_CallData decode_from_prechecked_head_Approve_Sol_CallData
  decode_runtime_args_Evm_Sol_Approve TransferFrom_HEAD_SIZE TransferFrom_decode_from_CallData
  decode_from_prechecked_head_TransferFrom_Sol_CallData decode_runtime_args_Evm_Sol_TransferFrom
  BalanceOf_HEAD_SIZE BalanceOf_decode_from_CallData
  decode_from_prechecked_head_BalanceOf_Sol_CallData decode_runtime_args_Evm_Sol_BalanceOf
  Allowance_HEAD_SIZE Allowance_decode_from_CallData
  decode_from_prechecked_head_Allowance_Sol_CallData decode_runtime_args_Evm_Sol_Allowance
  TotalSupply_HEAD_SIZE TotalSupply_decode_from_CallData
  decode_from_prechecked_head_TotalSupply_Sol_CallData decode_runtime_args_Evm_Sol_TotalSupply
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData logData
  panicCode keccak256

variable (I : ExecutionEnv) (w : World)

/-! ### Events -/

/-- The topic of `Transfer`, as the compiler evaluated it into the exported code. -/
abbrev transferSig : UInt256 :=
  UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991

/-- The topic of `Approval`, as the compiler evaluated it into the exported code. -/
abbrev approvalSig : UInt256 :=
  UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Transfer`: a log entry with the signature hash
    and the two addresses as topics and the value as data, encoded in a fresh buffer.  Under a
    static call it fails. -/
theorem emitTransferLit_exec (e : Transfer) :
    (emit_Evm_Transfer e).exec I w =
      if w.memory.size + 32 < UInt256.size then
        if I.perm then
          some (.ok ((), { w with
            logs := w.logs.push ⟨I.codeOwner, #[transferSig, e.«from», e.«to»],
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
      hroom, exec_emit, returned_read, returned]
  · have hroom := hmem
    simp only [UInt256.size] at hroom
    simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, UInt256.size, hroom]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Approval`. -/
theorem emitApprovalLit_exec (e : Approval) :
    (emit_Evm_Approval e).exec I w =
      if w.memory.size + 32 < UInt256.size then
        if I.perm then
          some (.ok ((), { w with
            logs := w.logs.push ⟨I.codeOwner, #[approvalSig, e.owner, e.spender],
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
      hroom, exec_emit, returned_read, returned]
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

/-! ### The constructor argument -/

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

end Std

/-! The exported layout places the three fields of `TokenStore` at slots 0, 1 and 2: the roots
of the balances and allowances maps and the supply. -/

theorem balancesField : Field.store.field Layout.TokenStore 0 = .storage (UInt256.ofNat 0) := rfl
theorem allowancesField : Field.store.field Layout.TokenStore 1 = .storage (UInt256.ofNat 1) :=
  rfl
theorem supplyField : Field.store.field Layout.TokenStore 2 = .storage (UInt256.ofNat 2) := rfl

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

end FeProofs.ERC20.Exported
