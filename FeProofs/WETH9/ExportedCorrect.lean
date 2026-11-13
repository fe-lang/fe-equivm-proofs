import FeProofs.Lib.ExportedCorrect
import FeProofs.WETH9.Exported
import FeProofs.WETH9.Model
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeWETH9: what the exported code does

`Exported.lean` is the exporter's output and nothing else.  This file proves what it does: the
std code it calls (event encodings, calldata decoders), and that each exported arm ends as the
hand-written model's arm does, up to memory.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (locateAddress_exec locateAddressMap_exec)

namespace FeProofs.WETH9.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads, and trying them is half the cost of the arms below. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

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

/-! ### Events -/

/-- The topics the compiler evaluates for the events are the hashes of their signatures. -/
theorem approvalTopic_eq : Model.approvalTopic =
    UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925 := by
  native_decide

theorem transferTopic_eq : Model.transferTopic =
    UInt256.ofNat
      100389287136786176327247604509743168900146139575972864366142685224231313322991 := by
  native_decide

theorem depositTopic_eq : Model.depositTopic =
    UInt256.ofNat
      102222681472383059465863322013072701928378550215632170212813623808969952268444 := by
  native_decide

theorem withdrawalTopic_eq : Model.withdrawalTopic =
    UInt256.ofNat 57810043145978950376228313794938171962422655018555593468903716172405399886693 := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Approval`: a log entry with the signature hash
    and the two addresses as topics and the amount as data, encoded in a fresh buffer.  Under a
    static call it fails. -/
theorem emitApproval_exec (e : Approval) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Approval e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.approvalTopic, e.src, e.guy],
            e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned, approvalTopic_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Transfer`. -/
theorem emitTransfer_exec (e : Transfer) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Transfer e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.transferTopic, e.src, e.dst],
            e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned, transferTopic_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Deposit`: one address topic. -/
theorem emitDeposit_exec (e : Deposit) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Deposit e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.depositTopic, e.dst], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned, depositTopic_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `Withdrawal`. -/
theorem emitWithdrawal_exec (e : Withdrawal) (hmem : w.memory.size + 32 < UInt256.size) :
    (emit_Evm_Withdrawal e).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[Model.withdrawalTopic, e.src], e.wad.toByteArray⟩,
          memory := returned w.memory e.wad }))
      else some (.error .static) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, Fe.EVM.add_zero, hsize, UInt256.size,
    hroom, exec_emit, returned_read, returned, withdrawalTopic_eq]

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
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
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
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
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
  simp [toNat0, toNat32, truncate_size _ hfits, add0_32, add32_32, ne64, at4, at36, headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
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

/-! ### The returns -/

theorem encodeBool_eq (b : Bool) : Model.encodeBool b = (Bool.toUInt256 b).toByteArray := by
  cases b <;> rfl

end Std

/-! ## The arms

Each exported arm runs as the hand-written model's arm does.  An arm leaves the key of each map
entry it reaches, and the encoded data of the event it emits, in fresh buffers, so its memory
differs. -/

section Arms

variable (I : ExecutionEnv) (w : World)

/-! The exported layout places the fields of `Weth9Store` at the model's slots. -/

theorem decimalsPlace :
    Field.store.field Layout.Weth9Store 2 = .storage Model.decimalsSlot := rfl
theorem balanceOfPlace :
    Field.store.field Layout.Weth9Store 3 = .storage Model.balanceOfRoot := rfl
theorem allowancePlace :
    Field.store.field Layout.Weth9Store 4 = .storage Model.allowanceRoot := rfl

/-- The room a step of an arm needs, from the room the arm has and the buffers made before. -/
macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size, ByteArray.size_empty]); omega))

/-- The caller's address word. -/
abbrev sender : UInt256 := UInt256.ofNat I.source.val

set_option maxHeartbeats 4000000 in
theorem approve_exec (guy wad : UInt256) (hmem : w.memory.size + 160 < UInt256.size) :
    (recv0_arm1 guy wad).exec I w =
      withMemory (returned (keyedAll w.memory [(sender I, Model.allowanceRoot),
          (guy, Fe.EVM.mapSlot (sender I) Model.allowanceRoot)]) wad)
        ((Model.approve guy wad).exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (disch := room) [allowancePlace, Evm_caller, recv0_arm1, Model.approve,
      Model.allowanceSlot, Model.allowanceRoot, locateAddress_exec, locateAddressMap_exec,
      emitApproval_exec, hp, exec_sstore, exec_emit]

theorem totalSupply_exec : recv0_arm2.exec I w = Model.totalSupply.exec I w := by
  simp [recv0_arm2, Model.totalSupply]

theorem balanceOf_exec (owner : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm6 owner).exec I w =
      withMemory (keyedAll w.memory [(owner, Model.balanceOfRoot)])
        ((Model.balanceOf owner).exec I w) := by
  simp (disch := room) [balanceOfPlace, recv0_arm6, Model.balanceOf, Model.balanceSlot,
    Model.balanceOfRoot, locateAddress_exec]

theorem allowance_exec (owner guy : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    (recv0_arm10 owner guy).exec I w =
      withMemory (keyedAll w.memory [(owner, Model.allowanceRoot),
          (guy, Fe.EVM.mapSlot owner Model.allowanceRoot)])
        ((Model.allowance owner guy).exec I w) := by
  simp (disch := room) [allowancePlace, recv0_arm10, Model.allowance, Model.allowanceSlot,
    Model.allowanceRoot, locateAddress_exec, locateAddressMap_exec]

/-- Std's read of the `u8` at offset 0 of a word is its low byte. -/
theorem lowByte_eq (x : UInt256) :
    truncate 8 (x >>> UInt256.ofNat 0 &&& UInt256.ofNat 255 &&& UInt256.ofNat 255) =
      x.land (UInt256.ofNat 255) := by
  have h255 : (UInt256.ofNat 255).toNat = 2 ^ 8 - 1 := rfl
  have hshr : (x >>> UInt256.ofNat 0).toNat = x.toNat := by
    change (UInt256.shiftRight x (UInt256.ofNat 0)).toNat = _
    rw [shiftRight_toNat_of_lt _ 0 (by decide)]
    simp
  apply u256_inj
  unfold truncate
  change (UInt256.ofNat ((UInt256.land (UInt256.land (x >>> UInt256.ofNat 0) (UInt256.ofNat 255))
    (UInt256.ofNat 255)).toNat % 2 ^ 8)).toNat = _
  rw [land_lit_toNat _ 8 _ h255, land_lit_toNat _ 8 _ h255, hshr, land_lit_toNat _ 8 _ h255,
    Nat.mod_mod, Nat.mod_mod, ulit_toNat' _ (by unfold UInt256.size; omega)]

theorem decimals_exec : recv0_arm5.exec I w = Model.decimals.exec I w := by
  have hmask : UInt256.ofNat 1 <<< UInt256.ofNat 8 = UInt256.ofNat 256 := by decide
  have hmul : UInt256.ofNat 0 * UInt256.ofNat 8 = UInt256.ofNat 0 := by decide
  have hsub : (UInt256.ofNat 256).sub (UInt256.ofNat 0) = UInt256.ofNat 256 := by decide
  have hsub1 : (UInt256.ofNat 256).sub (UInt256.ofNat 1) = UInt256.ofNat 255 := by decide
  simp [decimalsPlace, recv0_arm5, Model.decimals, SolSlot_read_u8, checkedMul, checkedSub,
    toNat0, toNat32, hmask, hmul, hsub, hsub1, show UInt256.size ≠ 0 by decide,
    show (UInt256.ofNat 256).toNat = 256 from rfl, show (UInt256.ofNat 8).toNat = 8 from rfl,
    show (UInt256.ofNat 1).toNat = 1 from rfl, Layout.SolSlot, Layout.Payload, Fe.EVM.add_zero,
    lowByte_eq]

set_option maxHeartbeats 4000000 in
theorem deposit_exec (hmem : w.memory.size + 160 < UInt256.size) :
    deposit_Weth9Store_Evm_Evm.exec I w =
      withMemory (returned (keyedAll w.memory [(sender I, Model.balanceOfRoot),
          (sender I, Model.balanceOfRoot)]) I.weiValue)
        (Model.deposit.exec I w) := by
  by_cases hp : I.perm = true <;>
    simp (disch := room) [balanceOfPlace, Evm_caller, deposit_Weth9Store_Evm_Evm, Model.deposit,
      Model.balanceSlot, Model.balanceOfRoot, locateAddress_exec, emitDeposit_exec, callvalue,
      hp, exec_sstore, exec_emit]

/-- The largest word, as std's `u256::max()` gives it. -/
theorem maxWord_eq : UInt256.ofNat (UInt256.size - 1) =
    UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := rfl

/-- Close an `Alike` goal whose two runs are evaluated: both exit the same way, or both return
    the same result with the same accounts and logs. -/
macro "alike" : tactic =>
  `(tactic| first
    | exact Alike.exit _
    | (refine Alike.ok rfl rfl ?_; simp only [keyed_size, returned_size, ByteArray.size_empty]
       omega))

section TransferFrom

attribute [local simp] balanceOfPlace allowancePlace transfer_from_Weth9Store_Evm_Evm
  Model.transferFrom Model.balanceSlot Model.balanceOfRoot Model.allowanceSlot Model.allowanceRoot
  locateAddress_exec locateAddressMap_exec emitTransfer_exec exec_sstore exec_emit M.exec_ite

set_option maxHeartbeats 4000000 in
/-- Fe's `transfer_from`.  It reads an entry again where the model reuses the word it read. -/
theorem transferFrom_alike (src dst wad : UInt256) (hmem : w.memory.size + 864 < UInt256.size) :
    Alike 864 w ((transfer_from_Weth9Store_Evm_Evm src dst wad).exec I w)
      ((Model.transferFrom src dst wad).exec I w) := by
  by_cases hb : (slotWord I w.accounts (Fe.EVM.mapSlot src ⟨3⟩)).toNat < wad.toNat
  · simp (maxSteps := 4000000) (disch := room) [hb, Nat.not_le.mpr hb]
    alike
  by_cases hs : src = sender I
  · subst hs
    by_cases hp : I.perm = true <;> simp (maxSteps := 4000000) (disch := room) [hp, hb, Nat.not_lt.mp hb] <;> alike
  by_cases hm : slotWord I w.accounts (Fe.EVM.mapSlot (sender I) (Fe.EVM.mapSlot src ⟨4⟩)) =
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935
  · by_cases hp : I.perm = true <;>
      simp (maxSteps := 4000000) (disch := room) [hp, hb, Nat.not_lt.mp hb, hs, hm, maxWord_eq] <;> alike
  by_cases ha : (slotWord I w.accounts (Fe.EVM.mapSlot (sender I)
    (Fe.EVM.mapSlot src ⟨4⟩))).toNat < wad.toNat
  · simp (maxSteps := 4000000) (disch := room) [hb, Nat.not_lt.mp hb, hs, hm, ha,
      Nat.not_le.mpr ha, maxWord_eq]
    alike
  by_cases hp : I.perm = true <;>
    simp (maxSteps := 4000000) (disch := room) [hp, hb, Nat.not_lt.mp hb, hs, hm, ha,
      Nat.not_lt.mp ha, maxWord_eq] <;> alike

end TransferFrom

section Withdraw

/-- An allocation of no bytes: the address memory ends at. -/
theorem alloc_zero (hmem : w.memory.size < UInt256.size) :
    (alloc (UInt256.ofNat 0)).exec I w = some (.ok (UInt256.ofNat w.memory.size, w)) := by
  have h : w.memory ++ ({ data := #[] } : ByteArray) = w.memory := ByteArray.append_empty
  simp [alloc, toNat0, hmem, h]

attribute [local simp] balanceOfPlace recv0_arm4 Model.withdraw Model.balanceSlot
  Model.balanceOfRoot locateAddress_exec emitWithdrawal_exec exec_sstore exec_emit M.exec_ite
  toNat0 toNatMax toNatU64

/-- Std's `MAX_ALLOCATION`: `u64::MAX` fits a `usize`. -/
theorem maxAllocation_fits : ¬ UInt256.size - 1 < 18446744073709551615 := by decide

set_option maxHeartbeats 4000000 in
/-- The model's arm runs on empty memory, as the runtime entry starts with it: its call, with no
    input and no output, is then the exported call made on empty memory. -/
theorem withdraw_alike (wad : UInt256) (hw : w.memory = ByteArray.empty) :
    Alike 224 w ((recv0_arm4 wad).exec I w) ((Model.withdraw wad).exec I w) := by
  have hmem : w.memory.size + 224 < UInt256.size := by rw [hw]; decide
  by_cases hb : (slotWord I w.accounts (Fe.EVM.mapSlot (sender I) ⟨3⟩)).toNat < wad.toNat
  · simp (maxSteps := 4000000) (disch := room) [hb, Nat.not_le.mpr hb]
    alike
  by_cases hp : I.perm = true
  swap
  · simp (maxSteps := 4000000) (disch := room) [hb, Nat.not_lt.mp hb, hp]
    alike
  have hz0 : ((⟨0⟩ : UInt256) = UInt256.ofNat 0) = True := eq_true rfl
  by_cases hz : wad = ⟨0⟩
  · simp (maxSteps := 4000000) (disch := room) [hp, hz, hz0, alloc_zero,
      maxAllocation_fits, call_noData, hw]
    generalize M.exec (Fe.EVM.call _ _ _ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩) I _ = r
    rcases r with _ | _ | ⟨a, v⟩
    · exact Alike.diverge
    · exact Alike.exit _
    by_cases ha : a = ⟨0⟩
    · simp [ha, returndatasize]
      exact Alike.exit _
    · simp (disch := room) [ha, show ¬ a = UInt256.ofNat 0 from ha, hp, returndatasize]
      alike
  · simp (maxSteps := 4000000) (disch := room) [hb, Nat.not_lt.mp hb, hp, hz,
      show ¬ wad = UInt256.ofNat 0 from hz, alloc_zero, maxAllocation_fits, call_noData, hw]
    generalize M.exec (Fe.EVM.call _ _ _ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩) I _ = r
    rcases r with _ | _ | ⟨a, v⟩
    · exact Alike.diverge
    · exact Alike.exit _
    by_cases ha : a = ⟨0⟩
    · simp [ha, returndatasize]
      exact Alike.exit _
    · simp (disch := room) [ha, show ¬ a = UInt256.ofNat 0 from ha, hp, returndatasize]
      alike

end Withdraw

end Arms

end FeProofs.WETH9.Exported
