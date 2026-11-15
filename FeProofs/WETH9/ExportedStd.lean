import FeProofs.Lib.ExportedCorrect
import FeProofs.WETH9.Exported
import FeProofs.Common.Abi
import FeProofs.Common.SolString
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
open FeProofs.Lib (locateAddress_exec locateAddressMap_exec revertPanic_exec fromAbiTail_exec
  returnDynString_exec shr160_eq_zero_iff)
open Stele (solidityDecodeBytesLengthHeader solidityBytesDataBaseSlot solidityShortBytesWord)

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

/-! ## Arms -/

section Arms

variable (I : ExecutionEnv) (w : World)

/-- The caller's address word. -/
abbrev sender : UInt256 := UInt256.ofNat I.source.val

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

/-- `decimals()`'s arm: the low byte of slot 2. -/
theorem decimalsLit_exec : recv0_arm5.exec I w =
    some (.ok (UInt256.land (slotWord I w.accounts (UInt256.ofNat 2)) (UInt256.ofNat 255), w)) := by
  have hmask : UInt256.ofNat 1 <<< UInt256.ofNat 8 = UInt256.ofNat 256 := by decide
  have hmul : UInt256.ofNat 0 * UInt256.ofNat 8 = UInt256.ofNat 0 := by decide
  have hsub : (UInt256.ofNat 256).sub (UInt256.ofNat 0) = UInt256.ofNat 256 := by decide
  have hsub1 : (UInt256.ofNat 256).sub (UInt256.ofNat 1) = UInt256.ofNat 255 := by decide
  simp [decimalsField, recv0_arm5, SolSlot_read_u8, checkedMul, checkedSub,
    toNat0, toNat32, hmask, hmul, hsub, hsub1, show UInt256.size ≠ 0 by decide,
    show (UInt256.ofNat 256).toNat = 256 from rfl, show (UInt256.ofNat 8).toNat = 8 from rfl,
    show (UInt256.ofNat 1).toNat = 1 from rfl, Layout.SolSlot, Layout.Payload, Fe.EVM.add_zero,
    lowByte_eq]

/-- The largest word, as std's `u256::max()` gives it. -/
theorem maxWord_eq : UInt256.ofNat (UInt256.size - 1) =
    UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := rfl

/-- An allocation of no bytes: the address memory ends at. -/
theorem alloc_zero (hmem : w.memory.size < UInt256.size) :
    (alloc (UInt256.ofNat 0)).exec I w = some (.ok (UInt256.ofNat w.memory.size, w)) := by
  have h : w.memory ++ ({ data := #[] } : ByteArray) = w.memory := ByteArray.append_empty
  simp [alloc, toNat0, hmem, h]

/-- Std's `MAX_ALLOCATION`: `u64::MAX` fits a `usize`. -/
theorem maxAllocation_fits : ¬ UInt256.size - 1 < 18446744073709551615 := by decide

end Arms

/-! ## Strings

`SolString::load` decodes the head with `stored_len`, allocates the length word and the padded
bytes, and copies a short string's head or each data word of a long one, cut to the bytes left;
`return_value` copies the result after the offset word into a fresh buffer.  Both allocations
fail with `Panic(0x41)` at `2 ^ 64` bytes. -/

section Strings

variable (I : ExecutionEnv) (w : World)

theorem storedLen_exec (head : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (stored_len head).exec I w =
      match solidityDecodeBytesLengthHeader head with
      | .ok L => some (.ok (UInt256.ofNat L, w))
      | _ => some (.error (.revert (panicData 0x22))) := by
  have hh := u256_toNat_lt head
  have hdiv : ∀ x : UInt256, x / UInt256.ofNat 2 = UInt256.ofNat (x.toNat / 2) := fun x => by
    apply u256_inj
    change (UInt256.div x (UInt256.ofNat 2)).toNat = _
    rw [udiv_toNat, show (UInt256.ofNat 2).toNat = 2 from rfl,
      ulit_toNat' _ (by have := u256_toNat_lt x; unfold UInt256.size; omega)]
  have hlow : (head &&& UInt256.ofNat 255).toNat = head.toNat % 256 :=
    land_lit_toNat head 8 _ rfl
  have hne : UInt256.ofNat 2 ≠ ⟨0⟩ := by decide
  have h10 : UInt256.ofNat 0 ≠ UInt256.ofNat 1 := by decide
  have h34 : (UInt256.ofNat 34).toNat = 34 := rfl
  rcases decodeHeader_cases head with ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨hbad, hrev⟩
  · rw [hok]
    have hf : head &&& UInt256.ofNat 1 = UInt256.ofNat 1 := headFlag_odd ho
    simp [stored_len, checkedDiv, toNat32, hf, hdiv, hne,
      ulit_toNat' (head.toNat / 2) (by unfold UInt256.size; omega), Nat.not_lt.mpr hge]
  · rw [hok]
    have hf : head &&& UInt256.ofNat 1 = UInt256.ofNat 0 := headFlag_even he
    simp [stored_len, checkedDiv, M.exec_ite, toNat32, hf, hdiv, hne, h10, hlow,
      ulit_toNat' (head.toNat % 256 / 2) (by unfold UInt256.size; omega), hlt]
  · rw [hrev]
    rcases hbad with ⟨ho, hlt⟩ | ⟨he, hge⟩
    · have hf : head &&& UInt256.ofNat 1 = UInt256.ofNat 1 := headFlag_odd ho
      simp [stored_len, checkedDiv, toNat32, hf, hdiv, hne,
        ulit_toNat' (head.toNat / 2) (by unfold UInt256.size; omega), hlt,
        revertPanic_exec I w _ hmem, h34]
    · have hf : head &&& UInt256.ofNat 1 = UInt256.ofNat 0 := headFlag_even he
      simp [stored_len, checkedDiv, toNat32, hf, hdiv, hne, h10, hlow,
        ulit_toNat' (head.toNat % 256 / 2) (by unfold UInt256.size; omega), 
        revertPanic_exec I w _ hmem, h34, hge]

/-- `~~~a` is `UInt256.lnot a`. -/
theorem complement_eq_lnot (a : UInt256) : ~~~a = UInt256.lnot a := by
  apply u256_inj
  rw [show (~~~a).toNat = (UInt256.complement a).toNat from rfl, complement_toNat,
    lnot_toNat_gen]
  rfl

theorem leadingBytes_exec (v : UInt256) (r : ℕ) (hr : r < UInt256.size) :
    (leading_bytes v (UInt256.ofNat r)).exec I w = some (.ok (leadWord v r, w)) := by
  have hrn : (UInt256.ofNat r).toNat = r := ulit_toNat' r hr
  unfold leadWord
  by_cases h : r < 32
  · have hmul : UInt256.ofNat r * UInt256.ofNat 8 =
        UInt256.shiftLeft (UInt256.ofNat r) (UInt256.ofNat 3) := by
      apply u256_inj
      rw [umul_toNat _ _ (by rw [hrn]; unfold UInt256.size; change r * 8 < _; omega),
        shiftLeft_toNat_of_lt _ 3 (by decide) (by rw [hrn]; unfold UInt256.size; omega), hrn]
      rfl
    have hmax : UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935 =
          UInt256.lnot ⟨0⟩ := by decide
    have e1 : ∀ a b : UInt256, a &&& b = UInt256.land a b := fun _ _ => rfl
    have e3 : ∀ a b : UInt256, a >>> b = UInt256.shiftRight a b := fun _ _ => rfl
    simp [leading_bytes, hrn, toNat32, h, Nat.not_le.mpr h, hmul, hmax, e1, complement_eq_lnot, e3]
  · simp [leading_bytes, hrn, toNat32, h, Nat.le_of_not_lt h]

theorem wordCount_exec (L : ℕ) (hL : L + 31 < UInt256.size) :
    (word_count (UInt256.ofNat L)).exec I w = some (.ok (UInt256.ofNat ((L + 31) / 32), w)) := by
  have hdiv : (UInt256.ofNat L + UInt256.ofNat 31) / UInt256.ofNat 32 =
      UInt256.ofNat ((L + 31) / 32) := by
    apply u256_inj
    change (UInt256.div _ _).toNat = _
    rw [udiv_toNat, uadd_toNat, ulit_toNat' L (by omega),
      show (UInt256.ofNat 31).toNat = 31 from rfl,
      Nat.mod_eq_of_lt hL, toNat32, ulit_toNat' _ (by omega)]
  simp [word_count, checkedDiv, hdiv, show UInt256.ofNat 32 ≠ ⟨0⟩ by decide]

theorem arrayDataSlot_exec (slot : UInt256) :
    (array_data_slot slot).exec I w = some (.ok (solidityBytesDataBaseSlot slot, w)) := by
  simp [array_data_slot, keccak_words_1, keccakWords, solidityBytesDataBaseSlot, keccakSlot_eq]

/-- The words `SolString::load` copies of a long string at `slot`: the data words, each cut to
    the `L` bytes' remainder. -/
abbrev loadWords (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256) (L n : ℕ) : ByteArray :=
  wordsBytes (fun j => leadWord (slotWord I σ (solidityBytesDataBaseSlot slot + UInt256.ofNat j))
    (L - 32 * j)) n

theorem keccakWords_single (s : UInt256) : keccakWords #v[s] = solidityBytesDataBaseSlot s := by
  simp [keccakWords, solidityBytesDataBaseSlot, keccakSlot_eq]

/-- The copy loop of `SolString::load` on a long string of `L` bytes at `slot`, from iteration `i`
    with `k` to go: it appends each data word, cut to the bytes left, after the length word at
    `M.size`, then continues with `b3`. -/
theorem loadLoop_exec (slot : UInt256) (L : ℕ) (hL : L < 2 ^ 255) (b3 : UInt256 → FeM DynString)
    (M : ByteArray) (hM : M.size + 64 + 32 * ((L + 31) / 32) < UInt256.size) :
    ∀ k i (wd : World), i + k = (L + 31) / 32 →
      wd.memory = M ++ ((UInt256.ofNat L).toByteArray ++
        (loadWords I wd.accounts slot L i ++ ⟨Array.replicate (32 * k) 0⟩)) →
      (SolString_load.b7 (.storage slot) (UInt256.ofNat L) (UInt256.ofNat M.size) b3
          (UInt256.ofNat i)).exec I wd =
        (b3 (UInt256.ofNat ((L + 31) / 32))).exec I { wd with memory := M ++
          ((UInt256.ofNat L).toByteArray ++ loadWords I wd.accounts slot L ((L + 31) / 32)) } := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  intro k
  induction k with
  | zero =>
    intro i wd hik hmem
    rw [SolString_load.b7.eq_1]
    obtain rfl : i = (L + 31) / 32 := by omega
    simp [wordCount_exec I wd L (by omega), ulit_toNat' ((L + 31) / 32) (by omega)]
    have hz : (⟨Array.replicate (32 * 0) 0⟩ : ByteArray) = ByteArray.empty := rfl
    rw [hz, ByteArray.append_empty] at hmem
    rw [← hmem]
  | succ k ih =>
    intro i wd hik hmem
    have hW : (L + 31) / 32 < 2 ^ 251 := by omega
    have hi : 32 * i < L := by omega
    rw [SolString_load.b7.eq_1]
    simp [wordCount_exec I wd L (by omega), ulit_toNat' i (by omega),
      ulit_toNat' ((L + 31) / 32) (by omega), show i < (L + 31) / 32 by omega, keccakWords_single,
      ofNat_mul_ofNat (a := i) (b := 32) (by omega) (by decide) (by omega),
      ofNat_sub_ofNat (a := L) (b := i * 32) (by omega) (by omega),
      fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v (L - i * 32) (by omega),
      Payload_locate, Layout.SolString, Fe.EVM.add_zero,
      lit_add_eq (a := 32) (b := i * 32) (by omega),
      lit_add_eq (a := M.size) (b := 32 + i * 32) (by omega),
      lit_add_eq (a := i) (b := 1) (by omega), mstore,
      ulit_toNat' (M.size + (32 + i * 32)) (by omega)]
    rw [ih (i + 1) _ (by omega) ?_]
    rw [hmem, show ∀ D Z : ByteArray, M ++ ((UInt256.ofNat L).toByteArray ++ (D ++ Z)) =
        (M ++ ((UInt256.ofNat L).toByteArray ++ D)) ++ Z by
          intro D Z; simp only [ByteArray.append_assoc],
      write_tail _ _ _ 0 0 32 (by simp; omega) (by decide)
        (by rw [toByteArray_size]) (by rw [zeros_size]; omega)]
    simp only [zeros_size, zeros_extract, Nat.zero_add, toByteArray_extract_all,
      show min 0 (32 * (k + 1)) - 0 = 0 by omega,
      show min (32 * (k + 1)) (32 * (k + 1)) - 32 = 32 * k by omega, loadWords, wordsBytes,
      ByteArray.append_assoc, Nat.mul_comm i 32,
      show (⟨Array.replicate 0 0⟩ : ByteArray) = ByteArray.empty from rfl, empty_append]

/-- What `SolString::load` copies after the length word of a string of `L` bytes at `slot`: the
    bytes as EquiVM reads them, zero-padded to words. -/
abbrev loaded (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) (L : ℕ) : ByteArray :=
  strBytes σ I slot L ++ zpad (32 * ((L + 31) / 32) - L)

theorem solStringLoad_exec (slot : UInt256) (hmem : w.memory.size + 2 ^ 65 < UInt256.size) :
    (SolString_load (.storage slot)).exec I w =
      match solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) with
      | .ok L =>
        if 32 + (L + 31) / 32 * 32 < 2 ^ 64 then
          some (.ok (⟨UInt256.ofNat w.memory.size, UInt256.ofNat L,
              UInt256.ofNat (32 + (L + 31) / 32 * 32)⟩,
            { w with memory := w.memory ++ ((UInt256.ofNat L).toByteArray ++
              loaded w.accounts I slot L) }))
        else some (.error (.panic 65))
      | _ => some (.error (.revert (panicData 0x22))) := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have hh := u256_toNat_lt (slotWord I w.accounts slot)
  rcases decodeHeader_cases (slotWord I w.accounts slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · rw [hok]
    generalize hL : (slotWord I w.accounts slot).toNat / 2 = L at hge hok ⊢
    have hL255 : L < 2 ^ 255 := by omega
    have hfl : slotWord I w.accounts slot &&& UInt256.ofNat 1 = UInt256.ofNat 1 := headFlag_odd ho
    have hsize : 32 + (L + 31) / 32 * 32 < UInt256.size := by omega
    have hmaxa : ¬ UInt256.size - 1 < 18446744073709551615 := by decide
    by_cases h64 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    · simp [SolString_load, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ (by omega), hok,
        wordCount_exec I w _ (by omega : L + 31 < UInt256.size),
        ofNat_mul_ofNat (a := (L + 31) / 32) (b := 32) (by omega) (by decide) (by omega),
        lit_add_eq (a := 32) (b := (L + 31) / 32 * 32) (by omega), toNatMax, toNatU64,
        ulit_toNat' _ hsize, hmaxa, show ¬ UInt256.size - 1 < 32 + (L + 31) / 32 * 32 by omega,
        show ¬ 18446744073709551615 < 32 + (L + 31) / 32 * 32 by omega, alloc, mstore,
        show w.memory.size + (32 + (L + 31) / 32 * 32) < UInt256.size by omega, hfl,
        ulit_toNat' w.memory.size (by omega), show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide]
      rw [loadLoop_exec I slot L hL255 _ w.memory (by omega) ((L + 31) / 32) 0 _ (by omega) ?hm,
        fromAbiTail_exec I _ w.memory _ L hL255 rfl (by omega),
        if_pos (show 32 + (L + 31) / 32 * 32 < 18446744073709551616 from h64)]
      · have hlong :
            loadWords I w.accounts slot L ((L + 31) / 32) = loaded w.accounts I slot L := by
          rw [loadWords, leadWords_eq _ L (by omega), loaded, strBytes, if_neg (by omega)]
          rfl
        simp [hlong]
      · rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [toByteArray_size])
          (by rw [zeros_size]; omega)]
        simp [zeros_size, zeros_extract, toByteArray_extract_all, loadWords, wordsBytes,
          Nat.mul_comm 32]
    · simp [SolString_load, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ (by omega), hok,
        wordCount_exec I w _ (by omega : L + 31 < UInt256.size),
        ofNat_mul_ofNat (a := (L + 31) / 32) (b := 32) (by omega) (by decide) (by omega),
        lit_add_eq (a := 32) (b := (L + 31) / 32 * 32) (by omega), toNatMax, toNatU64,
        ulit_toNat' _ hsize, hmaxa, show ¬ UInt256.size - 1 < 32 + (L + 31) / 32 * 32 by omega,
        show 18446744073709551615 < 32 + (L + 31) / 32 * 32 by omega,
        show ¬ 32 + (L + 31) / 32 * 32 < 18446744073709551616 by omega, panicCode,
        show (UInt256.ofNat 65).toNat = 65 from rfl]
  · rw [hok]
    generalize hL : (slotWord I w.accounts slot).toNat % 256 / 2 = L at hlt hok ⊢
    have hfl : slotWord I w.accounts slot &&& UInt256.ofNat 1 = UInt256.ofNat 0 :=
      headFlag_even he
    have hmaxa : ¬ UInt256.size - 1 < 18446744073709551615 := by decide
    have hsize : 32 + (L + 31) / 32 * 32 < UInt256.size := by omega
    by_cases h0 : L = 0
    · subst h0
      simp [SolString_load, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ (by omega), hok,
        wordCount_exec I w _ (by omega : 0 + 31 < UInt256.size),
        toNatMax, toNatU64, hmaxa, alloc, mstore, hfl, ulit_toNat' w.memory.size (by omega),
        show w.memory.size + 32 < UInt256.size by omega,
        show UInt256.ofNat 0 * UInt256.ofNat 32 = UInt256.ofNat 0 from rfl,
        show UInt256.ofNat 32 + UInt256.ofNat 0 = UInt256.ofNat 32 from rfl, toNat32,
        show ¬ UInt256.size - 1 < 32 by decide, show ¬ 18446744073709551615 < 32 by decide]
      have hm : (UInt256.ofNat 0).toByteArray.write 0 (w.memory ++ ⟨Array.replicate 32 0⟩)
          w.memory.size 32 = w.memory ++ ((UInt256.ofNat 0).toByteArray ++ ByteArray.empty) := by
        rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [toByteArray_size])
          (by rw [zeros_size])]
        simp [zeros_size, toByteArray_extract_all]
      have h0 : loaded w.accounts I slot 0 = ByteArray.empty := by
        simp [loaded, strBytes]
      have ht := fromAbiTail_exec I { w with memory := w.memory ++
        ((UInt256.ofNat 0).toByteArray ++ ByteArray.empty) } w.memory ByteArray.empty 0 (by decide)
        rfl (by omega)
      simp only [Nat.zero_add, show (31 : ℕ) / 32 * 32 = 0 from rfl, Nat.add_zero] at ht
      rw [hm, ht, h0]
    have hW : (L + 31) / 32 = 1 := by omega
    have hp : w.memory.size + 64 < UInt256.size := by omega
    simp [SolString_load, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
      storedLen_exec I w _ (by omega), hok, wordCount_exec I w _ (by omega : L + 31 < UInt256.size),
      hW, toNatMax, toNatU64, hmaxa, alloc, mstore, hfl, ulit_toNat' w.memory.size (by omega),
      show UInt256.ofNat 1 * UInt256.ofNat 32 = UInt256.ofNat 32 from rfl,
      show UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 from rfl,
      show (UInt256.ofNat 64).toNat = 64 from rfl, show ¬ UInt256.size - 1 < 64 by decide,
      show ¬ 18446744073709551615 < 64 by decide, hp, ofNat_ne_ofNat_zero h0 (by omega),
      leadingBytes_exec I _ _ L (by omega),
      ofNat_add_ofNat (a := w.memory.size) (b := 32) (by omega),
      ulit_toNat' (w.memory.size + 32) (by omega)]
    have hm : (leadWord (slotWord I w.accounts slot) L).toByteArray.write 0
        ((UInt256.ofNat L).toByteArray.write 0 (w.memory ++ ⟨Array.replicate 64 0⟩)
          w.memory.size 32) (w.memory.size + 32) 32 =
        w.memory ++ ((UInt256.ofNat L).toByteArray ++
          (leadWord (slotWord I w.accounts slot) L).toByteArray) := by
      rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [toByteArray_size])
          (by rw [zeros_size]; omega),
        write_tail _ _ _ 0 32 32 rfl (by decide) (by rw [toByteArray_size])
          (by simp [zeros_size])]
      simp [zeros_size, zeros_extract, toByteArray_extract_all]
      rw [extract_append_left _ _ _ _ (by rw [toByteArray_size]), toByteArray_extract_all]
    have hs :
        (leadWord (slotWord I w.accounts slot) L).toByteArray = loaded w.accounts I slot L := by
      rw [leadWord_toByteArray, loaded, strBytes, if_pos (by omega), Nat.min_eq_left (by omega), hW]
      rfl
    have ht := fromAbiTail_exec I { w with memory := w.memory ++ ((UInt256.ofNat L).toByteArray ++
      (leadWord (slotWord I w.accounts slot) L).toByteArray) } w.memory _ L (by omega) rfl
      (by omega)
    simp only [hW] at ht
    rw [hm, ht, hs]

  · rw [hrev]
    simp [SolString_load, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
      storedLen_exec I w _ (by omega), hrev]

set_option maxHeartbeats 4000000 in
/-- A string getter's body: `SolString::load` at `slot`, returned, from the empty memory a call
    starts with.  The bytes `loaded` copies, after the offset word and the length word, or
    `Panic(0x41)` at `2 ^ 64` bytes, or `Panic(0x22)` on a bad head. -/
theorem stringReturn_exec (slot : UInt256) (hw : w.memory = ByteArray.empty) :
    (SolString_load (.storage slot) >>= Evm_return_value_Sol_DynString).exec I w =
      match solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) with
      | .ok L =>
        if 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64 then
          some (.error (.stop ((UInt256.ofNat 32).toByteArray ++
              ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L))
            { w with memory := w.memory ++ ((UInt256.ofNat L).toByteArray ++
              loaded w.accounts I slot L) ++ ((UInt256.ofNat 32).toByteArray ++
                ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L)) }))
        else some (.error (.panic 0x41))
      | _ => some (.error (.revert (panicData 0x22))) := by
  have hmem : w.memory.size + 2 ^ 65 < UInt256.size := by rw [hw]; decide
  have hsz : UInt256.size = 2 ^ 256 := rfl
  simp only [M.exec_bind, solStringLoad_exec I w slot hmem]
  cases hd : solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) with
  | ok L =>
    have hL : L < 2 ^ 255 := by
      rcases decodeHeader_cases (slotWord I w.accounts slot) with
        ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd
      · have := u256_toNat_lt (slotWord I w.accounts slot); omega
      · omega
    by_cases h32 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    swap
    · simp only [if_neg h32, if_neg (show ¬ 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64 by omega)]
    have hB : ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L).size =
        32 + (L + 31) / 32 * 32 := by
      simp [loaded, strBytes_size]; omega
    simp only [if_pos h32]
    rw [returnDynString_exec I _ w.memory.size (32 + (L + 31) / 32 * 32) (UInt256.ofNat L) _ hB
      (by rw [extract_append_right_window _ _ _ _ (le_refl _), Nat.sub_self,
            show w.memory.size + (32 + (L + 31) / 32 * 32) - w.memory.size =
              ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L).size by omega,
            byteArray_extract_self])
      (by simp only [ByteArray.size_append, hB]; omega) (by omega)
      (by simp only [ByteArray.size_append, hB, hw]; simp; omega) h32]
  | revert => rfl
  | error => rfl

end Strings

/-! ## The constructor -/

section Constructor

variable (I : ExecutionEnv) (w : World)

theorem clearLoop_exec (slot : UInt256) (hperm : I.perm = true) (n : ℕ) (hn : n < 2 ^ 251)
    (r0 r1 : UInt256) :
    ∀ k i (wd : World), i + k = n →
      (SolString_store.b10 (.storage slot) (UInt256.ofNat n) r0 r1 (UInt256.ofNat i)).exec I wd =
        some (.ok ((), { wd with
          accounts := clearDataWordsForwardFrom I.codeOwner wd.accounts
            (solidityBytesDataBaseSlot slot) (UInt256.ofNat i) k })) := by
  intro k
  induction k with
  | zero =>
    intro i wd hik
    obtain rfl : i = n := by omega
    rw [SolString_store.b10.eq_1]
    simp
    rfl
  | succ k ih =>
    intro i wd hik
    rw [SolString_store.b10.eq_1]
    simp [ulit_toNat' i (by unfold UInt256.size; omega),
      ulit_toNat' n (by unfold UInt256.size; omega),
      show i < n by omega, Payload_locate, Layout.SolString, Fe.EVM.add_zero, keccakWords_single,
      exec_sstore, hperm, lit_add_eq (a := i) (b := 1) (by omega),
      ih (i + 1) _ (by omega), clearDataWordsForwardFrom]
    rw [show ({ val := 1 } : UInt256) + UInt256.ofNat i = UInt256.ofNat (i + 1) by
      rw [u256_add_comm]; exact lit_add_eq (a := i) (b := 1) (by omega)]
    rfl

/-- A head whose length contradicts its flag is the one EquiVM's decoder reverts on. -/
theorem strHeadBad_iff (S : UInt256) :
    strHeadBad S ↔ solidityDecodeBytesLengthHeader S = .revert := by
  unfold strHeadBad strHeadLen solidityDecodeBytesLengthHeader
  by_cases h : S.land ⟨1⟩ = ⟨0⟩ <;> simp [h]

/-- A string literal shorter than a word: its length word, then its bytes and zeros to a word,
    in fresh memory. -/
theorem stringLiteral_exec (bytes : ByteArray) (hb0 : 0 < bytes.size) (hb : bytes.size < 32)
    (hmem : w.memory.size + 64 < UInt256.size) :
    (stringLiteral bytes).exec I w = some (.ok (UInt256.ofNat w.memory.size, { w with
      memory := w.memory ++ ((UInt256.ofNat bytes.size).toByteArray ++
        (bytes ++ ⟨Array.replicate (32 - bytes.size) 0⟩)) })) := by
  have hW : 32 + (bytes.size + 31) / 32 * 32 = 64 := by omega
  have hp : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [lit_add_eq (by unfold UInt256.size at hmem; omega), ulit_toNat' _ (by omega)]
  simp [stringLiteral, alloc, mstore, mstoreBytes, hW, show (UInt256.ofNat 64).toNat = 64 from rfl,
    hmem, ulit_toNat' w.memory.size (by omega), hp]
  rw [write_tail _ _ _ 0 0 32 (by simp) (by decide) (by rw [toByteArray_size])
      (by rw [zeros_size]; omega),
    write_tail _ _ _ 0 32 bytes.size rfl (by omega) (by omega)
      (by simp [zeros_size]; omega)]
  simp [zeros_size, zeros_extract, toByteArray_extract_all]
  rw [extract_append_left _ _ _ _ (by rw [toByteArray_size]), toByteArray_extract_all,
    extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega), toByteArray_size,
    zeros_extract, ByteArray.append_assoc,
    show min (64 - 32) 32 - (32 + bytes.size - 32) = 32 - bytes.size by omega]

/-- A short string literal's bytes read back. -/
theorem literal_read (M bytes : ByteArray) (hb : bytes.size < 32) :
    (M ++ ((UInt256.ofNat bytes.size).toByteArray ++
      (bytes ++ ⟨Array.replicate (32 - bytes.size) 0⟩))).readWithPadding (M.size + 32)
        bytes.size = bytes := by
  rcases Nat.eq_zero_or_pos bytes.size with h0 | hpos
  · rw [h0, byteArray_readWithPadding_zero]
    exact (ByteArray.size_eq_zero_iff.mp h0).symm
  rw [readWithPadding_tail _ _ 32 bytes.size rfl hpos (by simp [zeros_size]),
    extract_append_right_window _ _ _ _ (by rw [toByteArray_size]), toByteArray_size,
    Nat.sub_self, show 32 + bytes.size - 32 = bytes.size by omega,
    extract_append_left _ _ _ _ (le_refl _), byteArray_extract_self]

open Classical in
set_option maxHeartbeats 4000000 in
/-- `SolString::store` of a literal shorter than a word at `slot`: `Panic(0x22)` on a bad old head,
    or the head and the old data words zeroed, as EquiVM's `strWriteMap` writes them. -/
theorem storeStringLit_exec (slot : UInt256) (p : ℕ) (bytes : ByteArray) (hb0 : 0 < bytes.size)
    (hb : bytes.size < 32)
    (hword : leadWord (uInt256OfByteArray (bytes.readWithPadding 0 32)) bytes.size |||
      UInt256.ofNat (bytes.size * 2) = solidityShortBytesWord bytes)
    (hread : w.memory.readWithPadding (p + 32) bytes.size = bytes)
    (hp : p + 64 < UInt256.size) (hmem : w.memory.size + 64 < UInt256.size) :
    (SolString_store (.storage slot)
        ⟨UInt256.ofNat p, UInt256.ofNat bytes.size, UInt256.ofNat 64⟩).exec I w =
      if strHeadBad (slotWord I w.accounts slot) then some (.error (.revert (panicData 0x22)))
      else if I.perm then some (.ok ((), { w with accounts := strWriteMap I w.accounts slot bytes }))
      else some (.error .static) := by
  have hh := u256_toNat_lt (slotWord I w.accounts slot)
  have hsz : UInt256.size = 2 ^ 256 := rfl
  by_cases hbad : strHeadBad (slotWord I w.accounts slot)
  · have hrev := (strHeadBad_iff _).mp hbad
    simp [SolString_store, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
      storedLen_exec I w _ hmem, hrev, hbad]
  rcases decodeHeader_cases (slotWord I w.accounts slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · have hfl : slotWord I w.accounts slot &&& UInt256.ofNat 1 = UInt256.ofNat 1 := headFlag_odd ho
    have hp32 : (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
      rw [lit_add_eq (by unfold UInt256.size at hp; omega), ulit_toNat' _ (by omega)]
    by_cases hperm : I.perm = true
    · simp [SolString_store, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
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
      simp [SolString_store, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
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
    · simp [SolString_store, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
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
      simp [SolString_store, Layout.SolString, Layout.Payload, Fe.EVM.add_zero,
        storedLen_exec I w _ hmem, hok, hbad, hfl, payload_word, exec_sstore,
        ulit_toNat' bytes.size (by omega), toNat0, show ¬ bytes.size = 0 by omega,
        show bytes.size < 32 from hb, readPaddedWord, hp32, hread, toNat32,
        ofNat_sub_ofNat (a := bytes.size) (b := 0) (by omega) (by omega),
        Nat.min_eq_left hb.le,
        fun (w' : World) (v : UInt256) => leadingBytes_exec I w' v bytes.size (by omega),
        ofNat_mul_ofNat (a := bytes.size) (b := 2) (by omega) (by decide) (by omega), hword, hpf]
  · exact absurd ((strHeadBad_iff _).mpr hrev) hbad

/-- The words the constructor stores for `"Wrapped Ether"` and `"WETH"`. -/
theorem nameWordLit_eq :
    leadWord (uInt256OfByteArray ((⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ :
      ByteArray).readWithPadding 0 32)) 13 ||| UInt256.ofNat (13 * 2) =
      solidityShortBytesWord ⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ := by
  decide +kernel

theorem symbolWordLit_eq :
    leadWord (uInt256OfByteArray ((⟨#[87, 69, 84, 72]⟩ : ByteArray).readWithPadding 0 32)) 4 |||
      UInt256.ofNat (4 * 2) = solidityShortBytesWord ⟨#[87, 69, 84, 72]⟩ := by
  decide +kernel

theorem writeDecimalsLit_exec :
    (SolSlot_write_u8 (.storage (UInt256.ofNat 2)) (UInt256.ofNat 0) (UInt256.ofNat 18)).exec I w =
      (sstore (UInt256.ofNat 2) (UInt256.lor (UInt256.ofNat 18) (UInt256.land
        (UInt256.lnot (UInt256.ofNat 255)) (slotWord I w.accounts (UInt256.ofNat 2))))).exec
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

end Constructor

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

end FeProofs.WETH9.Exported
