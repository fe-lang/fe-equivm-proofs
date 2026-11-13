import FeProofs.Lib.ExportedCorrect
import FeProofs.ScalarStore.Exported
import FeProofs.ScalarStore.ModelCorrect
import Fe.EVM.Entry

/-!
# FeScalarStore: the bytecode refines the exported contract

`Exported.lean` is the whole contract as `fe-lean-export` prints it: each arm's entry decodes the
message with std's `decode_runtime_args`, runs the arm and returns through std's `return_value`,
`runtime` dispatches on the selector, and `init_entry` decodes the constructor argument.  This
file shows each entry ends as the hand-written model's does, so the certificates for that model
carry over.  The two differ in memory only: exported code copies the constructor argument and
encodes return data in fresh buffers.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (returnU256_exec withArg)

namespace FeProofs.ScalarStore.Exported

/-! ## The arms

Each exported arm is the hand-written model's. -/

theorem init_eq (initial : UInt256) : init initial = Model.initBody initial := by
  simp [init, Field.stored, Model.initBody, Model.storedSlot]
  rfl

theorem recv0_arm0_eq : recv0_arm0 = Model.get := by
  simp [recv0_arm0, Field.stored, Model.get, Model.storedSlot]
  rfl

theorem recv0_arm1_eq (value : UInt256) : recv0_arm1 value = Model.set value := by
  simp [recv0_arm1, Field.stored, Model.set, Model.storedSlot]
  rfl

/-! ## Std code

The std definitions the entries reach unfold under `simp` in this section. -/

section Std

attribute [local simp]
  Get_HEAD_SIZE Get_decode_from_CallData decode_from_prechecked_head_Get_Sol_CallData
  decode_runtime_args_Evm_Sol_Get Set_HEAD_SIZE Set_decode_from_CallData
  decode_from_prechecked_head_Set_Sol_CallData decode_runtime_args_Evm_Sol_Set checkedAdd
  checkedSub alloc mstore mstoreBytes readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

/-! ### Decoders -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `decode_runtime_args` at `Set { value: u256 }`: revert on calldata that cannot hold the
    selector and one word, otherwise the word after the selector. -/
theorem decodeSet_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Set.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, UInt256.size, add0_32, ne32, at4,
    headCheck hlo hfits (by norm_num : 32 < 2 ^ 64), hshort]
  by_cases h : I.calldata.size < 36 <;> simp [h, word]

/-- `decode_runtime_args` at `Get`: nothing to decode, and no head to check. -/
theorem decodeGet_exec : decode_runtime_args_Evm_Sol_Get.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

/-! ### The return -/

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

/-! ## The arms' entries

The hand-written model has one runtime entry, so each exported arm entry is compared with that
entry on calldata that carries the arm's selector. -/

section Entries

variable (I : ExecutionEnv) (w : World)

/-- The `Get` entry ends as the model's entry does on calldata with the selector of `get()`. -/
theorem get_endsAs (hmem : w.memory.size + 32 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (h1 : selIs I (feScalarStoreSelBytes 1)) :
    EndsAs ((entry recv0_arm0_entry).exec I w) (Model.runtime.exec I w) := by
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hlo
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv]), runtime_get_value hlo h0 h1 hwv]
    exact .exit _
  have eg : (entry recv0_arm0_entry).exec I w =
      (entry (Model.get >>= Evm_return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm0_entry, exec_nonPayable, hwv, decodeGet_exec, recv0_arm0_eq]
  have eh : Model.runtime.exec I w = (Model.get >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.runtime, exec_nonPayable, hwv, hn4, sel0_not h0, sel1 h1]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (keepsMemory_sload _) hmem

/-- The `Set` entry ends as the model's entry does on calldata with the selector of
    `set(uint256)`. -/
theorem set_endsAs (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (h0 : selIs I (feScalarStoreSelBytes 0)) :
    EndsAs ((entry recv0_arm1_entry).exec I w) (Model.runtime.exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv]), runtime_set_value hlo h0 hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeSet_exec I w hlo hfits, hshort]),
      runtime_set_head hlo h0 hwv (hbad.mpr (by omega))]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { w with accounts := storeWord I.codeOwner w.accounts ⟨0⟩ (word I.calldata 4) }) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeSet_exec I w hlo hfits, hshort,
        recv0_arm1_eq, Model.set, Model.storedSlot, exec_sstore, hperm, returnNone_exec]),
      runtime_set hlo h0 hwv hgood hperm]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeSet_exec I w hlo hfits, hshort,
        recv0_arm1_eq, Model.set, exec_sstore, hperm]),
      runtime_set_static hlo h0 hwv hgood (by simpa using hperm)]
    exact .exit _

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written model's does, on calldata below
    `2 ^ 64` bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 32 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (feScalarStoreSelBytes i)) →
      (feScalarStoreSelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [entry_exec (f := .revert ByteArray.empty) (by simp [runtime, hn, hlt]),
      runtime_short hlt]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feScalarStoreSelBytes 0)
  · have hw := selWord_hit (setEvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm1_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    rw [eg]
    exact set_endsAs I w hsz hfits h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x60fe47b1 :=
    selWord_miss (setEvmSelector hsz) (miss 0 h0)
  by_cases h1 : selIs I (feScalarStoreSelBytes 1)
  · have hw := selWord_hit (getEvmSelector hsz) h1
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    rw [eg]
    exact get_endsAs I w hmem hsz h0 h1
  have w1 : selWord I.calldata ≠ UInt256.ofNat 0x6d4ce63c :=
    selWord_miss (getEvmSelector hsz) (miss 1 h1)
  rw [entry_exec (f := .revert ByteArray.empty) (by
    simp [runtime, hn, hn4, selector_exec, w0, w1]), runtime_noMatch hsz h0 h1]
  exact .exit _

end Entries

/-! ## Deployment -/

/-- The exported deployment entry ends as the hand-written model's does, on one argument word. -/
theorem init_endsAs (v : UInt256) (out : ByteArray) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size + 32 < UInt256.size) :
    EndsAs ((init_entry (ctorTail v) >>= fun tail => pure (out ++ tail)).exec I w)
      ((Model.init (ctorTail v) >>= fun _ => pure out).exec I w) := by
  have hsz : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hword : uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v := by
    rw [readBytes_all32 _ hsz, ctorTail_eq, uInt256OfByteArray_toByteArray]
  rw [M.exec_bind, initEntry_exec I w v hmem]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [Model.init, exec_nonPayable, hwv]
    exact .exit _
  rw [if_pos hwv, init_eq]
  by_cases hperm : I.perm = true
  · simp [Model.init, exec_nonPayable, hwv, hsz, hword, Model.initBody, exec_sstore, hperm]
    exact .ok_ok rfl rfl
  · simp [Model.init, exec_nonPayable, hwv, hsz, hword, Model.initBody, exec_sstore, hperm]
    exact .exit _

/-! ## The certificate -/

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem feScalarStoreRefinesExported :
    RefinesOn .P0 feScalarStoreBytecode contract CalldataFits := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feScalarStoreRefinesModel σ σ₀ g A I ByteArray.empty
      (by rw [ByteArray.append_empty]; exact hcode) rfl hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A feed) (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment with one ABI-encoded `uint256` argument refines the exported deployment entry. -/
theorem feScalarStoreDeployRefinesExported :
    RefinesDeploy .P0 feScalarStoreCreationBytecode feScalarStoreBytecode contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  rcases feScalarStoreDeployRefinesModel σ σ₀ g A I _ ⟨v, rfl⟩ hcode hperm with h | ⟨feed, h⟩
  · exact Or.inl h
  · replace h : Agrees .P0 (Ξ σ σ₀ g A I) ((Model.init (ctorTail v) >>= fun _ =>
        pure feScalarStoreBytecode).exec I (World.init σ A feed)) := by
      simpa [Model.contract, ByteArray.append_empty] using h
    exact Or.inr ⟨feed, Agrees.of_endsAs
      (init_endsAs v _ I (World.init σ A feed) (by simp [World.init, UInt256.size])) h⟩

end FeProofs.ScalarStore.Exported
