import FeProofs.Lib.ExportedCorrect
import FeProofs.ERC20.Exported
import FeProofs.ERC20.ExportedStd
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
open scoped FeProofs.Lib
open FeProofs.Lib (returnU256_exec withArg locateAddress_exec locateAddressMap_exec
  shr160_eq_zero_iff)

namespace FeProofs.ERC20.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads, and trying them is half the cost of the arms below. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

/-! ## Std code

The std definitions the arms and entries reach unfold under `simp` in this section. -/

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

/-- The topic the compiler evaluates for `Transfer` is the hash of its signature. -/
theorem transferTopic_eq : Model.transferTopic =
    UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991 := by
  decide +kernel

/-- The topic the compiler evaluates for `Approval` is the hash of its signature. -/
theorem approvalTopic_eq : Model.approvalTopic =
    UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925 := by
  decide +kernel

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
  rw [transferTopic_eq]; exact emitTransferLit_exec I w e

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
  rw [approvalTopic_eq]; exact emitApprovalLit_exec I w e

/-! ### The returns -/

theorem encodeBool_eq (b : Bool) : Model.encodeBool b = (Bool.toUInt256 b).toByteArray := by
  cases b <;> rfl

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

/-- The room a step of an arm needs, from the room the arm has and the buffers made before. -/
macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

theorem emitTransfer_ok (e : Transfer) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Transfer e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.transferTopic, e.«from», e.«to»],
            e.value.toByteArray⟩,
          memory := returned w.memory e.value }))
      else some (.error .static) := by
  rw [emitTransfer_exec, if_pos hmem]

theorem emitApproval_ok (e : Approval) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Approval e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.approvalTopic, e.owner, e.spender],
            e.value.toByteArray⟩,
          memory := returned w.memory e.value }))
      else some (.error .static) := by
  rw [emitApproval_exec, if_pos hmem]

/-- The caller's address word. -/
abbrev sender : UInt256 := UInt256.ofNat I.source.val

set_option maxHeartbeats 4000000 in
theorem init_exec (initialSupply : UInt256) (hmem : w.memory.size + 96 < UInt256.size) :
    (init initialSupply).exec I w =
      withMemory (returned (keyedAll w.memory [(sender I, Model.balancesRoot)]) initialSupply)
        ((Model.initBody initialSupply).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (disch := room) [ofNat0, balancesPlace, totalSupplyPlace, Evm_caller, init,
      Model.initBody, Model.balanceSlot, Model.balancesRoot, Model.totalSupplySlot,
      locateAddress_exec, emitTransfer_ok, hp, exec_sstore, exec_emit]

set_option maxHeartbeats 4000000 in
theorem transfer_exec (dst value : UInt256) (hmem : w.memory.size + 352 < UInt256.size) :
    (recv0_arm0 dst value).exec I w =
      withMemory (returned (keyedAll w.memory [(sender I, Model.balancesRoot),
          (sender I, Model.balancesRoot), (sender I, Model.balancesRoot),
          (dst, Model.balancesRoot), (dst, Model.balancesRoot)]) value)
        ((Model.transfer dst value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (disch := room) [balancesPlace, Evm_caller, recv0_arm0, Model.transfer,
      Model.balanceSlot, Model.balancesRoot, locateAddress_exec, emitTransfer_ok, hp,
      checkedSub, checkedAdd, exec_sstore, exec_emit, M.ite_bind, M.exec_ite,
      apply_ite (withMemory _)] <;>
    agree

set_option maxHeartbeats 4000000 in
theorem approve_exec (spender value : UInt256) (hmem : w.memory.size + 160 < UInt256.size) :
    (recv0_arm1 spender value).exec I w =
      withMemory (returned (keyedAll w.memory [(sender I, Model.allowancesRoot),
          (spender, Fe.EVM.mapSlot (sender I) Model.allowancesRoot)]) value)
        ((Model.approve spender value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (disch := room) [allowancesPlace, Evm_caller, recv0_arm1, Model.approve,
      Model.allowanceSlot, Model.allowancesRoot, locateAddress_exec, locateAddressMap_exec,
      emitApproval_ok, hp, exec_sstore, exec_emit]

set_option maxHeartbeats 4000000 in
theorem transferFrom_exec (src dst value : UInt256)
    (hmem : w.memory.size + 608 < UInt256.size) :
    (recv0_arm2 src dst value).exec I w =
      withMemory (returned (keyedAll w.memory [(src, Model.allowancesRoot),
          (sender I, Fe.EVM.mapSlot src Model.allowancesRoot), (src, Model.balancesRoot),
          (src, Model.allowancesRoot), (sender I, Fe.EVM.mapSlot src Model.allowancesRoot),
          (src, Model.balancesRoot), (src, Model.balancesRoot), (dst, Model.balancesRoot),
          (dst, Model.balancesRoot)]) value)
        ((Model.transferFrom src dst value).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (maxSteps := 2000000) (disch := room) [balancesPlace, allowancesPlace, Evm_caller,
      recv0_arm2,
      Model.transferFrom, Model.balanceSlot, Model.balancesRoot, Model.allowanceSlot,
      Model.allowancesRoot, locateAddress_exec, locateAddressMap_exec, emitTransfer_ok, hp,
      checkedSub, checkedAdd, exec_sstore, exec_emit, M.ite_bind, M.exec_ite,
      apply_ite (withMemory _)] <;>
    agree

theorem balanceOf_exec (owner : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm3 owner).exec I w =
      withMemory (keyedAll w.memory [(owner, Model.balancesRoot)])
        ((Model.balanceOf owner).exec I w) := by
  simp (disch := room) [balancesPlace, recv0_arm3, Model.balanceOf, Model.balanceSlot,
    Model.balancesRoot, locateAddress_exec]

theorem allowance_exec (owner spender : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    (recv0_arm4 owner spender).exec I w =
      withMemory (keyedAll w.memory [(owner, Model.allowancesRoot),
          (spender, Fe.EVM.mapSlot owner Model.allowancesRoot)])
        ((Model.allowance owner spender).exec I w) := by
  simp (disch := room) [allowancesPlace, recv0_arm4, Model.allowance, Model.allowanceSlot,
    Model.allowancesRoot, locateAddress_exec, locateAddressMap_exec]

theorem totalSupply_exec : recv0_arm5.exec I w = Model.totalSupply.exec I w := by
  simp [totalSupplyPlace, recv0_arm5, Model.totalSupply, Model.totalSupplySlot]

end Arms

end FeProofs.ERC20.Exported
