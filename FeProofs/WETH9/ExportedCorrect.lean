import FeProofs.Lib.ExportedCorrect
import FeProofs.WETH9.Exported
import FeProofs.WETH9.ExportedStd
import FeProofs.WETH9.Model
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# FeWETH9: what the exported code does

`Exported.lean` is the exporter's output and nothing else.  This file proves what it does: the
std code it calls (event encodings, calldata decoders), that each exported arm ends as the
hand-written model's arm does, up to memory, that a string getter's load and return end as the
model's `stringReturn` does, and that the constructor ends as the model's does.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (locateAddress_exec locateAddressMap_exec revertPanic_exec fromAbiTail_exec
  returnDynString_exec shr160_eq_zero_iff)
open Stele (solidityDecodeBytesLengthHeader solidityBytesDataBaseSlot solidityShortBytesWord)

namespace FeProofs.WETH9.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads, and trying them is half the cost of the arms below. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

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
    UInt256.ofNat
      63486140976153616755203102783360879283472101686154884697241723088393386309925 := by
  decide +kernel

theorem transferTopic_eq : Model.transferTopic =
    UInt256.ofNat
      100389287136786176327247604509743168900146139575972864366142685224231313322991 := by
  decide +kernel

theorem depositTopic_eq : Model.depositTopic =
    UInt256.ofNat
      102222681472383059465863322013072701928378550215632170212813623808969952268444 := by
  decide +kernel

theorem withdrawalTopic_eq : Model.withdrawalTopic =
    UInt256.ofNat
      57810043145978950376228313794938171962422655018555593468903716172405399886693 := by
  decide +kernel

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

theorem namePlace : Field.store.field Layout.Weth9Store 0 = .storage Model.nameSlot := rfl
theorem symbolPlace : Field.store.field Layout.Weth9Store 1 = .storage Model.symbolSlot := rfl
theorem decimalsPlace :
    Field.store.field Layout.Weth9Store 2 = .storage Model.decimalsSlot := rfl
theorem balanceOfPlace :
    Field.store.field Layout.Weth9Store 3 = .storage Model.balanceOfRoot := rfl
theorem allowancePlace :
    Field.store.field Layout.Weth9Store 4 = .storage Model.allowanceRoot := rfl

/-- The room a step of an arm needs, from the room the arm has and the buffers made before. -/
macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size, ByteArray.size_empty]); omega))

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

/-- Close an `Alike` goal whose two runs are evaluated: both exit the same way, or both return
    the same result with the same accounts and logs. -/
macro "alike" : tactic =>
  `(tactic| first
    | exact Alike.exit _
    | (refine Alike.ok rfl rfl rfl ?_; simp only [keyed_size, returned_size, ByteArray.size_empty]
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
    by_cases hp : I.perm = true <;>
      simp (maxSteps := 4000000) (disch := room) [hp, hb, Nat.not_lt.mp hb] <;> alike
  by_cases hm : slotWord I w.accounts (Fe.EVM.mapSlot (sender I) (Fe.EVM.mapSlot src ⟨4⟩)) =
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935
  · by_cases hp : I.perm = true <;>
      simp (maxSteps := 4000000) (disch := room)
        [hp, hb, Nat.not_lt.mp hb, hs, hm, maxWord_eq] <;> alike
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

attribute [local simp] balanceOfPlace recv0_arm4 Model.withdraw Model.balanceSlot
  Model.balanceOfRoot locateAddress_exec emitWithdrawal_exec exec_sstore exec_emit M.exec_ite
  toNat0 toNatMax toNatU64

set_option maxHeartbeats 4000000 in
/-- The model's arm, run on empty memory: its call, with no input and no output, is then the
    exported call made on empty memory (`call_noData`). -/
theorem withdraw_alike (wad : UInt256) (hmem : w.memory.size + 224 < UInt256.size) :
    Alike 224 w ((recv0_arm4 wad).exec I w)
      ((Model.withdraw wad).exec I { w with memory := ByteArray.empty }) := by
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
      maxAllocation_fits, call_noData]
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
      show ¬ wad = UInt256.ofNat 0 from hz, alloc_zero, maxAllocation_fits, call_noData]
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

/-! ## Strings

`SolString::load` decodes the head with `stored_len`, allocates the length word and the padded
bytes, and copies a short string's head or each data word of a long one, cut to the bytes left;
`return_value` copies the result after the offset word into a fresh buffer.  Both allocations
fail with `Panic(0x41)` at `2 ^ 64` bytes. -/

section Strings

variable (I : ExecutionEnv) (w : World)

set_option maxHeartbeats 4000000 in
/-- A string getter: `SolString::load` at `slot`, returned, ends as the model's `stringReturn`
    does, from the empty memory a call starts with, which the entry reserves. -/
theorem stringReturn_endsAs (slot : UInt256) (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry (SolString_load (.storage slot) >>= Evm_return_value_Sol_DynString)).exec I w)
      ((Model.stringReturn slot).exec I w) := by
  have hv : w.reserved.memory.size = 96 := by rw [World.reserved_size, hw]; rfl
  have hmem : w.reserved.memory.size + 2 ^ 65 < UInt256.size := by rw [hv]; decide
  have hsz : UInt256.size = 2 ^ 256 := rfl
  simp only [entry, M.exec_bind, exec_reserve, solStringLoad_exec I w.reserved slot hmem,
    World.reserved_accounts]
  cases hd : solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) with
  | ok L =>
    have hL : L < 2 ^ 255 := by
      rcases decodeHeader_cases (slotWord I w.accounts slot) with
        ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd
      · have := u256_toNat_lt (slotWord I w.accounts slot); omega
      · omega
    by_cases h32 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    swap
    · simp [Model.stringReturn, hd, show ¬ 32 + (L + 31) / 32 * 32 < 18446744073709551616 from h32,
        show ¬ 64 + 32 * ((L + 31) / 32) < 18446744073709551616 by omega]
      exact .exit _
    have hB : ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L).size =
        32 + (L + 31) / 32 * 32 := by
      simp [loaded, strBytes_size]; omega
    simp only []
    rw [if_pos h32]
    simp only []
    rw [returnDynString_exec I _ w.reserved.memory.size (32 + (L + 31) / 32 * 32)
      (UInt256.ofNat L) _ hB
      (by rw [extract_append_right_window _ _ _ _ (le_refl _), Nat.sub_self,
            show w.reserved.memory.size + (32 + (L + 31) / 32 * 32) - w.reserved.memory.size =
              ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L).size by omega,
            byteArray_extract_self])
      (by simp only [ByteArray.size_append, hB]; omega) (by omega)
      (by simp only [ByteArray.size_append, hB, hv]; omega) h32]
    by_cases h64 : 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64
    · simp [Model.stringReturn, hd,
        show 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 from h64,
        show 64 + 32 * ((L + 31) / 32) < 18446744073709551616 by omega]
      exact .stop_ok rfl rfl rfl
    · simp [Model.stringReturn, hd,
        show ¬ 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 from h64,
        show ¬ 64 + 32 * ((L + 31) / 32) < 18446744073709551616 by omega]
      exact .exit _
  | revert =>
    simp [Model.stringReturn, hd]
    exact .exit _
  | error =>
    rcases decodeHeader_cases (slotWord I w.accounts slot) with
      ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd

end Strings

/-! ## The constructor

`SolString::store` of a short string checks the old head with `stored_len`, stores the new head,
and zeroes the data words of a long old value, as EquiVM's `strWriteMap` writes them; the low
byte of the `decimals` slot is replaced in place. -/

section Constructor

variable (I : ExecutionEnv) (w : World)

theorem storeString_exec (slot : UInt256) (p : ℕ) (bytes : ByteArray) (hb0 : 0 < bytes.size)
    (hb : bytes.size < 32)
    (hword : leadWord (uInt256OfByteArray (bytes.readWithPadding 0 32)) bytes.size |||
      UInt256.ofNat (bytes.size * 2) = solidityShortBytesWord bytes)
    (hread : w.memory.readWithPadding (p + 32) bytes.size = bytes)
    (hp : p + 64 < UInt256.size) (hmem : w.memory.size + 64 < UInt256.size) :
    (SolString_store (.storage slot)
        ⟨UInt256.ofNat p, UInt256.ofNat bytes.size, UInt256.ofNat 64⟩).exec I w =
      (Model.storeString slot bytes).exec I w := by
  have hh := u256_toNat_lt (slotWord I w.accounts slot)
  have hsz : UInt256.size = 2 ^ 256 := rfl
  by_cases hbad : strHeadBad (slotWord I w.accounts slot)
  · have hrev := (strHeadBad_iff _).mp hbad
    simp [SolString_store, Model.storeString, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
      storedLen_exec I w _ hmem, hrev, hbad]
  rcases decodeHeader_cases (slotWord I w.accounts slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · have hfl : slotWord I w.accounts slot &&& UInt256.ofNat 1 = UInt256.ofNat 1 := headFlag_odd ho
    have hp32 : (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
      rw [lit_add_eq (by unfold UInt256.size at hp; omega), ulit_toNat' _ (by omega)]
    by_cases hperm : I.perm = true
    · simp [SolString_store, Model.storeString, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ hmem, hok, hbad, hfl, hperm, payload_word, exec_sstore,
        toNat0, show ¬ bytes.size = 0 by omega,
        show bytes.size < 32 from hb, readPaddedWord, hp32, hread, toNat32,
        show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide,
        ofNat_sub_ofNat (a := bytes.size) (b := 0) (by omega) (by omega),
        ulit_toNat' bytes.size (by omega), Nat.min_eq_left hb.le,
        wordCount_exec I w _
          (by omega : (slotWord I w.accounts slot).toNat / 2 + 31 < UInt256.size),
        fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v bytes.size (by omega),
        ofNat_mul_ofNat (a := bytes.size) (b := 2) (by omega) (by decide) (by omega), hword]
      have hold : strOldWords (slotWord I w.accounts slot) =
          ((slotWord I w.accounts slot).toNat / 2 + 31) / 32 := by
        have hf1 : UInt256.land (slotWord I w.accounts slot) ⟨1⟩ = ⟨1⟩ := headFlag_odd ho
        unfold strOldWords strHeadLen
        rw [hf1, if_neg (by decide), if_neg (by decide), udiv_toNat]
        rfl
      rw [clearLoop_exec I slot hperm (((slotWord I w.accounts slot).toNat / 2 + 31) / 32)
        (by omega) _ _ (((slotWord I w.accounts slot).toNat / 2 + 31) / 32) 0 _ (by omega),
        strWriteMap,
        show strOldWords (Reasoning.Reach.solcSlotWord w.accounts I slot) = _ from hold]
      rfl
    · have hpf : I.perm = false := by simpa using hperm
      simp [SolString_store, Model.storeString, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ hmem, hok, hbad, hfl, payload_word, exec_sstore,
        ulit_toNat' bytes.size (by omega), toNat0, show ¬ bytes.size = 0 by omega,
        show bytes.size < 32 from hb, readPaddedWord, hp32, hread, toNat32,
        show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide,
        ofNat_sub_ofNat (a := bytes.size) (b := 0) (by omega) (by omega),
        Nat.min_eq_left hb.le,
        fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v bytes.size (by omega),
        ofNat_mul_ofNat (a := bytes.size) (b := 2) (by omega) (by decide) (by omega), hword, hpf,
        wordCount_exec I w _
          (by omega : (slotWord I w.accounts slot).toNat / 2 + 31 < UInt256.size)]
  · have hfl : slotWord I w.accounts slot &&& UInt256.ofNat 1 = UInt256.ofNat 0 := headFlag_even he
    have hp32 : (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
      rw [lit_add_eq (by unfold UInt256.size at hp; omega), ulit_toNat' _ (by omega)]
    by_cases hperm : I.perm = true
    · simp [SolString_store, Model.storeString, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ hmem, hok, hbad, hfl, payload_word, exec_sstore,
        ulit_toNat' bytes.size (by omega), toNat0, show ¬ bytes.size = 0 by omega,
        show bytes.size < 32 from hb, readPaddedWord, hp32, hread, toNat32,
        ofNat_sub_ofNat (a := bytes.size) (b := 0) (by omega) (by omega),
        Nat.min_eq_left hb.le,
        fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v bytes.size (by omega),
        ofNat_mul_ofNat (a := bytes.size) (b := 2) (by omega) (by decide) (by omega), hword, hperm]
      have hold : strOldWords (Reasoning.Reach.solcSlotWord w.accounts I slot) = 0 := by
        have hf0 : UInt256.land (Reasoning.Reach.solcSlotWord w.accounts I slot) ⟨1⟩ = ⟨0⟩ :=
          headFlag_even he
        unfold strOldWords
        rw [if_pos hf0]
      rw [clearLoop_exec I slot hperm 0 (by omega) _ _ 0 0 _ rfl, strWriteMap, hold]
      rfl
    · have hpf : I.perm = false := by simpa using hperm
      simp [SolString_store, Model.storeString, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ hmem, hok, hbad, hfl, payload_word, exec_sstore,
        ulit_toNat' bytes.size (by omega), toNat0, show ¬ bytes.size = 0 by omega,
        show bytes.size < 32 from hb, readPaddedWord, hp32, hread, toNat32,
        ofNat_sub_ofNat (a := bytes.size) (b := 0) (by omega) (by omega),
        Nat.min_eq_left hb.le,
        fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v bytes.size (by omega),
        ofNat_mul_ofNat (a := bytes.size) (b := 2) (by omega) (by decide) (by omega), hword, hpf]
  · exact absurd ((strHeadBad_iff _).mpr hrev) hbad

/-- The words the constructor stores for `"Wrapped Ether"` and `"WETH"`. -/
theorem nameWord_eq : leadWord (uInt256OfByteArray (Model.nameBytes.readWithPadding 0 32))
    Model.nameBytes.size ||| UInt256.ofNat (Model.nameBytes.size * 2) =
      solidityShortBytesWord Model.nameBytes := by decide +kernel

theorem symbolWord_eq : leadWord (uInt256OfByteArray (Model.symbolBytes.readWithPadding 0 32))
    Model.symbolBytes.size ||| UInt256.ofNat (Model.symbolBytes.size * 2) =
      solidityShortBytesWord Model.symbolBytes := by decide +kernel

theorem writeDecimals_exec :
    (SolSlot_write_u8 (.storage Model.decimalsSlot) (UInt256.ofNat 0) (UInt256.ofNat 18)).exec I w =
      (sstore Model.decimalsSlot (UInt256.lor (UInt256.ofNat 18) (UInt256.land
        (UInt256.lnot (UInt256.ofNat 255)) (slotWord I w.accounts Model.decimalsSlot)))).exec
        I w := by
  have hmask : UInt256.ofNat 1 <<< UInt256.ofNat 8 = UInt256.ofNat 256 := by decide
  have hmul : UInt256.ofNat 0 * UInt256.ofNat 8 = UInt256.ofNat 0 := by decide
  have hsub : (UInt256.ofNat 256).sub (UInt256.ofNat 0) = UInt256.ofNat 256 := by decide
  have hsub1 : (UInt256.ofNat 256).sub (UInt256.ofNat 1) = UInt256.ofNat 255 := by decide
  simp [SolSlot_write_u8, Layout.SolSlot, Layout.Payload, Fe.EVM.add_zero, checkedMul, checkedSub,
    toNat0, toNat32, hmask, hmul, hsub, hsub1, show UInt256.size ≠ 0 by decide,
    show (UInt256.ofNat 256).toNat = 256 from rfl, show (UInt256.ofNat 8).toNat = 8 from rfl,
    show (UInt256.ofNat 1).toNat = 1 from rfl, show UInt256.ofNat 8 ≠ UInt256.ofNat 256 by decide,
    show UInt256.ofNat 255 <<< UInt256.ofNat 0 = UInt256.ofNat 255 by decide,
    show UInt256.ofNat 18 <<< UInt256.ofNat 0 &&& UInt256.ofNat 255 = UInt256.ofNat 18 by decide,
    complement_eq_lnot]
  have e1 : ∀ a b : UInt256, a &&& b = UInt256.land a b := fun _ _ => rfl
  have e2 : ∀ a b : UInt256, a ||| b = UInt256.lor a b := fun _ _ => rfl
  rw [e2, e1, u256_lor_comm, u256_land_comm]

theorem storeString_model (slot : UInt256) (bytes : ByteArray) (hperm : I.perm = true) :
    (Model.storeString slot bytes).exec I w =
      if strHeadBad (slotWord I w.accounts slot) then some (.error (.revert (panicData 0x22)))
      else some (.ok ((), { w with accounts := strWriteMap I w.accounts slot bytes })) := by
  by_cases hb : strHeadBad (slotWord I w.accounts slot) <;> simp [Model.storeString, hb, hperm]

/-- The exported deployment entry ends as the model's constructor does, on the empty memory a
    call starts with, which the entry reserves, and with write permission, as a creation has. -/
theorem init_endsAs (args rt : ByteArray) (hw : w.memory = ByteArray.empty)
    (hperm : I.perm = true) :
    EndsAs ((deploy init_entry args >>= fun tail => pure (rt ++ tail)).exec I w)
      ((Model.contract.init args >>= fun tail => pure (rt ++ tail)).exec I w) := by
  have hv : w.reserved.memory.size = 96 := by rw [World.reserved_size, hw]; rfl
  rw [deploy_bind_eq]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [init_entry, Model.contract, Model.init, exec_nonPayable, hwv]
    exact .exit _
  have hfold : (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) =
      Model.nameBytes := rfl
  have hfold' : (⟨#[87, 69, 84, 72]⟩ : ByteArray) = Model.symbolBytes := rfl
  have h13 : UInt256.ofNat 13 = UInt256.ofNat Model.nameBytes.size := rfl
  have h4 : UInt256.ofNat 4 = UInt256.ofNat Model.symbolBytes.size := rfl
  simp only [init_entry, Model.contract, Model.init, Fe.M.exec_bind, exec_nonPayable, hwv, if_pos,
    init, hfold, hfold', namePlace, symbolPlace, decimalsPlace, h13, h4]
  rw [stringLiteral_exec I w.reserved Model.nameBytes (by decide) (by decide) (by rw [hv]; decide)]
  simp only []
  rw [storeString_exec I _ Model.nameSlot w.reserved.memory.size Model.nameBytes (by decide)
    (by decide) nameWord_eq (literal_read _ _ (by decide)) (by rw [hv]; decide)
    (by simp [hv, zeros_size]; decide),
    storeString_model I _ _ _ hperm, storeString_model I _ _ _ hperm]
  by_cases hb0 : strHeadBad (slotWord I w.accounts Model.nameSlot)
  · simp [hb0]
    exact .exit _
  simp [hb0, DynString_drop]
  rw [stringLiteral_exec I _ Model.symbolBytes (by decide) (by decide)
    (by simp [hv, zeros_size]; decide)]
  simp only []
  rw [storeString_exec I _ Model.symbolSlot _ Model.symbolBytes (by decide) (by decide)
    symbolWord_eq (literal_read _ _ (by decide))
    (by simp [hv, zeros_size]; decide)
    (by simp [hv, zeros_size]; decide),
    storeString_model I _ _ _ hperm, storeString_model I _ _ _ hperm]
  by_cases hb1 : strHeadBad (slotWord I (strWriteMap I w.accounts Model.nameSlot Model.nameBytes)
    Model.symbolSlot)
  · simp [hb1]
    exact .exit _
  simp [hb1, writeDecimals_exec, exec_sstore, hperm]
  exact .ok_ok rfl rfl rfl

end Constructor

end FeProofs.WETH9.Exported
