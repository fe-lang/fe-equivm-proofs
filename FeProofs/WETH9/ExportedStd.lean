import FeProofs.Lib.ExportedCorrect
import FeProofs.WETH9.Exported
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeWETH9: the std code of the exported entries

What the std code the exported arms and entries reach does, independently of any model: the
event encodings, with the topics the compiler evaluated into the exported code, and the calldata
decoders.  Nothing here imports the hand-written model, so the certificate through the machine
IR (`Sonatina*.lean`) does not depend on it.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (shr160_eq_zero_iff)

namespace FeProofs.WETH9.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads, and trying them is half the cost of the arms below. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

section Std

attribute [local simp]
  Approval_emit_Evm emit_Evm_Approval Transfer_emit_Evm emit_Evm_Transfer Deposit_emit_Evm
  emit_Evm_Deposit Withdrawal_emit_Evm emit_Evm_Withdrawal
  Name_HEAD_SIZE Name_decode_from_CallData decode_from_prechecked_head_Name_Sol_CallData
  decode_runtime_args_Evm_Sol_Name
  Approve_HEAD_SIZE Approve_decode_from_CallData decode_from_prechecked_head_Approve_Sol_CallData
  decode_runtime_args_Evm_Sol_Approve
  TotalSupply_HEAD_SIZE TotalSupply_decode_from_CallData
  decode_from_prechecked_head_TotalSupply_Sol_CallData decode_runtime_args_Evm_Sol_TotalSupply
  TransferFrom_HEAD_SIZE TransferFrom_decode_from_CallData
  decode_from_prechecked_head_TransferFrom_Sol_CallData decode_runtime_args_Evm_Sol_TransferFrom
  Withdraw_HEAD_SIZE Withdraw_decode_from_CallData
  decode_from_prechecked_head_Withdraw_Sol_CallData decode_runtime_args_Evm_Sol_Withdraw
  Decimals_HEAD_SIZE Decimals_decode_from_CallData
  decode_from_prechecked_head_Decimals_Sol_CallData decode_runtime_args_Evm_Sol_Decimals
  BalanceOf_HEAD_SIZE BalanceOf_decode_from_CallData
  decode_from_prechecked_head_BalanceOf_Sol_CallData decode_runtime_args_Evm_Sol_BalanceOf
  Symbol_HEAD_SIZE Symbol_decode_from_CallData decode_from_prechecked_head_Symbol_Sol_CallData
  decode_runtime_args_Evm_Sol_Symbol
  Transfer_HEAD_SIZE Transfer_decode_from_CallData
  decode_from_prechecked_head_Transfer_Sol_CallData decode_runtime_args_Evm_Sol_Transfer
  Deposit_HEAD_SIZE Deposit_decode_from_CallData decode_from_prechecked_head_Deposit_Sol_CallData
  decode_runtime_args_Evm_Sol_Deposit
  Allowance_HEAD_SIZE Allowance_decode_from_CallData
  decode_from_prechecked_head_Allowance_Sol_CallData decode_runtime_args_Evm_Sol_Allowance
  checkedAdd checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData logData
  panicCode keccak256

variable (I : ExecutionEnv) (w : World)

/-! ### Events

The event code with the topics the compiler evaluated into the exported code. -/

/-- The topic of `Approval`, as the compiler evaluated it into the exported code. -/
abbrev approvalSig : UInt256 :=
  UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925

/-- The topic of `Transfer`, as the compiler evaluated it into the exported code. -/
abbrev transferSig : UInt256 :=
  UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991

/-- The topic of `Deposit`, as the compiler evaluated it into the exported code. -/
abbrev depositSig : UInt256 :=
  UInt256.ofNat 102222681472383059465863322013072701928378550215632170212813623808969952268444

/-- The topic of `Withdrawal`, as the compiler evaluated it into the exported code. -/
abbrev withdrawalSig : UInt256 :=
  UInt256.ofNat 57810043145978950376228313794938171962422655018555593468903716172405399886693

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Approval`: a log entry with the signature hash
    and the two addresses as topics and the amount as data, encoded in a fresh buffer.  Under a
    static call it fails. -/
theorem emitApprovalLit_exec (e : Approval) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Approval e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[approvalSig, e.src, e.guy], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Transfer`. -/
theorem emitTransferLit_exec (e : Transfer) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Transfer e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[transferSig, e.src, e.dst], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Deposit`: one address topic. -/
theorem emitDepositLit_exec (e : Deposit) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Deposit e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[depositSig, e.dst], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Withdrawal`. -/
theorem emitWithdrawalLit_exec (e : Withdrawal) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Withdrawal e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[withdrawalSig, e.src], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned]

/-! ### Decoders -/

theorem decodeName_exec : decode_runtime_args_Evm_Sol_Name.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem decodeTotalSupply_exec :
    decode_runtime_args_Evm_Sol_TotalSupply.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem decodeDecimals_exec :
    decode_runtime_args_Evm_Sol_Decimals.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem decodeSymbol_exec :
    decode_runtime_args_Evm_Sol_Symbol.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem decodeDeposit_exec :
    decode_runtime_args_Evm_Sol_Deposit.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeApprove_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Approve.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36,
    headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 68 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeTransfer_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Transfer.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36,
    headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
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
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, ne32, at4,
    headCheck hlo hfits (by norm_num : 32 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 36 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeWithdraw_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Withdraw.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, ne32, at4,
    headCheck hlo hfits (by norm_num : 32 < 2 ^ 64), hshort]
  by_cases h : I.calldata.size < 36 <;> simp [h, word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeAllowance_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Allowance.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 36) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36,
    headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
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
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, add64_32, ne96, at4, at36, at68,
    headCheck hlo hfits (by norm_num : 96 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 100 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    by_cases hb : NotAddress (uInt256OfByteArray (I.calldata.readBytes 36 32)) <;>
    simp [h, ha, hb, word]

end Std

/-! ## Storage

The exported layout places the fields of `Weth9Store` at slots 0 to 4. -/

theorem nameField : Field.store.field Layout.Weth9Store 0 = .storage (UInt256.ofNat 0) := rfl
theorem symbolField : Field.store.field Layout.Weth9Store 1 = .storage (UInt256.ofNat 1) := rfl
theorem decimalsField : Field.store.field Layout.Weth9Store 2 = .storage (UInt256.ofNat 2) :=
  rfl
theorem balanceOfField : Field.store.field Layout.Weth9Store 3 = .storage (UInt256.ofNat 3) :=
  rfl
theorem allowanceField : Field.store.field Layout.Weth9Store 4 = .storage (UInt256.ofNat 4) :=
  rfl

end FeProofs.WETH9.Exported
