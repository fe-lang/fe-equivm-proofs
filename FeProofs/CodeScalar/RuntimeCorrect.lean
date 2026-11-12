import FeProofs.CodeScalar.Exported
import FeProofs.CodeScalar.ModelCorrect
import Fe.EVM.Entry

/-!
# FeCodeScalar: the bytecode refines the exported contract

`Exported.lean` is the whole contract as `fe-lean-export` prints it.  The `Get` entry decodes
with std's `decode_runtime_args`, reads the immutable word from the end of the running code and
returns through std's `return_value`.  `init_entry` decodes the constructor argument, runs
`init`, and returns the word of the immutable field.  This file shows each entry ends as the
hand-written model's does, so the certificates for that model carry over: the first for a
contract whose deployed code is its runtime bytecode followed by data.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.CodeScalar.Exported

/-! ## Std code

The std definitions the entries reach unfold under `simp` in this section. -/

section Std

attribute [local simp]
  new input SELECTOR_SIZE to_word IS_SIGNED U64_MASK MASK SIGN_BIT U256_MASK sign_extend
  from_word downcast_truncate_u256_u64 size len_CallData HEAD_SIZE from_word_1
  validate_runtime_head decode_from_CallData decode_from_prechecked_head_Get_Sol_CallData
  decode_runtime_args_Evm_Sol_Get IS_DYNAMIC HEAD_SIZE_1 max to_word_1 MASK_1 I256_SIGN_BIT
  downcast_saturate_u64_usize MAX_ALLOCATION PANIC_OUT_OF_MEMORY alloc_bytes alloc_uninit_32
  zero_bytes alloc_32 ptr_32 from_raw_parts PANIC_INDEX_OUT_OF_BOUNDS index_out_of_bounds
  word_to_usize ptr_offset slice cast_u8_u256 store_word store_word_1 encode_Sol
  downcast_unchecked_u256_usize from_raw_parts_ref_u8 ptr_u8 len_u8 return_data alloc_uninit_64
  alloc_64 ptr_64 new_uninit new_1 ptr span_ref const_u256 payload_size_u256
  abi_payload_size_u256 max_1 allocation_len encode_alloc_Sol_u256 abi_field_size_u256
  abi_single_root_size_u256 abi_field_head_size_u256 abi_single_root_head_size_u256 tail len
  encode_field_Sol_u256 encode_single_root_alloc_Sol_u256 encode_return_alloc_Sol_u256
  return_bytes return_value_Sol_u256 with_base decoder_new downcast_truncate_usize_u64 size_1
  len_MemSlice_u8 word_at read_word_MemSlice_u8 base pos decode_error checked_tail_Sol set_base
  set_pos decode_payload_Sol_SolDecoder_MemSlice_u8 decode_field_Sol_u256_SolDecoder_MemSlice_u8
  decode_payload_Sol_u256_SolDecoder_MemSlice_u8 checkedAdd checkedSub alloc mstore mstoreBytes
  readPaddedWord zeroMem returnData panicCode memoryBytes

variable (I : ExecutionEnv) (w : World)

/-- `decode_runtime_args` at `Get`: nothing to decode, and no head to check. -/
theorem decodeGet_exec : decode_runtime_args_Evm_Sol_Get.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

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

/-- Memory after the deployment entry copies the one argument word into a fresh buffer. -/
def withArg (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0 (memory ++ ⟨Array.replicate 32 0⟩) memory.size 32

theorem withArg_size (memory : ByteArray) (v : UInt256) :
    (withArg memory v).size = memory.size + 32 := by
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  unfold withArg
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]

/-- Memory after the deployment entry also writes the immutable word into its fresh buffer. -/
def withWord (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0 (withArg memory v ++ ⟨Array.replicate 32 0⟩) (memory.size + 32) 32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The deployment entry on one argument word: reject call value, then return the word, which
    `init` set the immutable field to.  It changes memory only. -/
theorem initEntry_exec (v : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (init_entry v.toByteArray).exec I w =
      if I.weiValue = ⟨0⟩ then
        some (.ok (v.toByteArray, { w with memory := withWord w.memory v }))
      else some (.error (.revert ByteArray.empty)) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    ulit_toNat' _ (by omega)
  have hsize2 : (UInt256.ofNat (w.memory.size + 32)).toNat = w.memory.size + 32 :=
    ulit_toNat' _ (by omega)
  have hroom := hmem
  simp only [UInt256.size] at hroom
  have hroom32 : w.memory.size + 32 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by omega
  have hroom64 : w.memory.size + 32 + 32 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by omega
  have hlen : v.toByteArray.size = 32 := toByteArray_size v
  have hcut : truncate 64 (UInt256.ofNat 32 &&& UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat 32 := by decide
  have harg := withArg_size w.memory v
  have hback : (withArg w.memory v).readWithPadding w.memory.size 32 = v.toByteArray :=
    toByteArray_write32_read_back _ _ _ (by
      rw [ByteArray.size_append]; exact Nat.le_add_right _ _)
  have hword : uInt256OfByteArray (v.toByteArray.readWithPadding 0 32) = v := by
    rw [readWithPadding_eq_extract _ 0 (by rw [hlen]), Nat.zero_add, toByteArray_extract_all,
      uInt256OfByteArray_toByteArray]
  unfold withArg at harg hback
  by_cases hwv : I.weiValue = ⟨0⟩
  · simp [init_entry, exec_nonPayable, hwv, toNat0, toNat32, hlen, hsize, hsize2, Fe.EVM.add_zero,
      UInt256.size, hroom32, hroom64, harg, hback, hword, hcut, add0_32, sub32_0, init_eq, withWord,
      withArg]
    exact toByteArray_write32_read_back _ _ _ (by
      rw [ByteArray.size_append, harg]; exact Nat.le_add_right _ _)
  · simp [init_entry, exec_nonPayable, hwv]

end Std

/-! ## The arm's entry -/

section Entries

variable (I : ExecutionEnv) (w : World)

/-- Reading the immutable word leaves memory alone. -/
theorem keepsMemory_get : KeepsMemory Model.get := by
  intro I w a w' h
  simp [Model.get, cload, immutableAt] at h
  rw [← h.2]

/-- The `Get` entry ends as the model's entry does on calldata with the selector of `get()`. -/
theorem get_endsAs (hmem : w.memory.size + 32 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (h0 : selIs I (feCodeScalarSelBytes 0)) :
    EndsAs ((entry recv0_arm0_entry).exec I w) (Model.runtime.exec I w) := by
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hlo
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv]), runtime_get_value hlo h0 hwv]
    exact .exit _
  have eg : (entry recv0_arm0_entry).exec I w =
      (entry (Model.get >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm0_entry, exec_nonPayable, hwv, decodeGet_exec, recv0_arm0_eq]
  have eh : Model.runtime.exec I w = (Model.get >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.runtime, exec_nonPayable, hwv, hn4, sel0 h0]
  rw [eg, eh]
  exact endsAs_arm (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) keepsMemory_get hmem

/-- The exported runtime entry ends as the hand-written model's does, on calldata below
    `2 ^ 64` bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 32 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [entry_exec (f := .revert ByteArray.empty) (by simp [runtime, hn, hlt]),
      runtime_short hlt]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feCodeScalarSelBytes 0)
  · have hw := selWord_hit (getEvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    rw [eg]
    exact get_endsAs I w hmem hsz h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x6d4ce63c :=
    selWord_miss (getEvmSelector hsz) (by simpa [selIs] using h0)
  rw [entry_exec (f := .revert ByteArray.empty) (by
    simp [runtime, hn, hn4, selector_exec, w0]), runtime_noMatch hsz h0]
  exact .exit _

end Entries

/-! ## Deployment -/

/-- The exported deployment entry ends as the hand-written model's does, on one argument word:
    both return the word, the bytes of the immutable field. -/
theorem init_endsAs (v : UInt256) (out : ByteArray) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size + 64 < UInt256.size) :
    EndsAs ((init_entry v.toByteArray >>= fun tail => pure (out ++ tail)).exec I w)
      ((Model.init v.toByteArray >>= fun tail => pure (out ++ tail)).exec I w) := by
  rw [M.exec_bind, initEntry_exec I w v hmem]
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [if_pos hwv, init_ok out v hwv]
    exact .ok_ok rfl rfl
  · rw [if_neg hwv, init_value out hwv]
    exact .exit _

/-! ## The certificate -/

/-- The contract as exported: the deployment entry, the runtime entry, and the 32 bytes of its
    immutable field. -/
def contract : ContractModel :=
  { init := init_entry, runtime := entry runtime, immutables := 32 }

/-- The runtime bytecode followed by any 32 bytes refines the exported contract, on calldata
    below `2 ^ 64` bytes. -/
theorem feCodeScalarRefinesExported :
    RefinesOn .P0 feCodeScalarBytecode contract CalldataFits := by
  intro σ σ₀ g A I tail hcode htail hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feCodeScalarRefinesModel σ σ₀ g A I tail hcode htail hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A feed) (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment with one ABI-encoded `uint256` argument refines the exported deployment entry:
    the deployed code is the runtime bytecode followed by the argument word. -/
theorem feCodeScalarDeployRefinesExported :
    RefinesDeploy .P0 feCodeScalarCreationBytecode feCodeScalarBytecode contract
      (fun args => ∃ v : UInt256, args = v.toByteArray) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  rcases feCodeScalarDeployRefinesModel σ σ₀ g A I _ ⟨v, rfl⟩ hcode hperm with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (init_endsAs v _ I (World.init σ A feed) (by simp [World.init, UInt256.size])) h⟩

/-- The bytes a deployment returns after the runtime bytecode are as many as the runtime
    certificate assumes, so the code a deployment leaves is code that certificate covers. -/
theorem deployed_tail_size {I : ExecutionEnv} {w w' : World} {v : UInt256} {tail : ByteArray}
    (hmem : w.memory.size + 64 < UInt256.size)
    (h : (contract.init v.toByteArray).exec I w = some (.ok (tail, w'))) :
    tail.size = contract.immutables := by
  have h' : (init_entry v.toByteArray).exec I w = some (.ok (tail, w')) := h
  rw [initEntry_exec I w v hmem] at h'
  split at h'
  · injection h' with h'
    injection h' with h'
    rw [← (Prod.mk.inj h').1]
    exact toByteArray_size v
  · cases h'

end FeProofs.CodeScalar.Exported
