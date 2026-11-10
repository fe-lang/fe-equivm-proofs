import FeProofs.PackedStore.ExportedCorrect
import Fe.EVM.Entry

/-!
# FePackedStore: the bytecode refines the exported contract

`Exported.lean` ends with the runtime entry as `fe-lean-export` prints it: each arm's entry
decodes the message with std's `decode_runtime_args`, runs the arm and returns through std's
`return_value`, and `runtime` dispatches on the selector.  This file shows that entry ends as
the hand-written one of `ExportedCorrect.lean` does, so the certificate for that one carries over.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.PackedStore.Exported

/-! ## Std code

The std definitions the entry reaches unfold under `simp` in this section. -/

section Std

attribute [local simp]
  new input SELECTOR_SIZE to_word IS_SIGNED U64_MASK MASK SIGN_BIT sign_extend from_word 
  downcast_truncate_u256_u64 size len_CallData HEAD_SIZE from_word_1 validate_runtime_head 
  decode_from_CallData decode_from_prechecked_head_Get0_Sol_CallData 
  decode_runtime_args_Evm_Sol_Get0 IS_DYNAMIC HEAD_SIZE_1 max to_word_1 MASK_1 I256_SIGN_BIT 
  downcast_saturate_u64_usize MAX_ALLOCATION PANIC_OUT_OF_MEMORY alloc_bytes alloc_uninit_32 
  zero_bytes alloc_32 ptr_32 from_raw_parts PANIC_INDEX_OUT_OF_BOUNDS index_out_of_bounds 
  word_to_usize ptr_offset slice cast_u8_u256 store_word store_word_1 encode_Sol 
  downcast_unchecked_u256_usize from_raw_parts_ref_u8 ptr_u8 len_u8 return_data alloc_uninit_64 
  alloc_64 ptr_64 new_uninit new_1 ptr span_ref const_u256 payload_size_u256 
  abi_payload_size_u256 max_1 allocation_len encode_alloc_Sol_u256 abi_field_size_u256 
  abi_single_root_size_u256 abi_field_head_size_u256 abi_single_root_head_size_u256 tail len 
  encode_field_Sol_u256 encode_single_root_alloc_Sol_u256 encode_return_alloc_Sol_u256 
  return_bytes return_value_Sol_u256 decode_from_CallData_1 
  decode_from_prechecked_head_Get1_Sol_CallData decode_runtime_args_Evm_Sol_Get1 HEAD_SIZE_2 
  word_at decode_error checked_tail_Sol checked_frame_end_Sol decode_from_Sol_CallData 
  decode_from_bounded_u256_Sol_CallData decode_field_from_prechecked_head_Sol_u256_CallData 
  decode_field_from_Sol_u256_CallData decode_msg_field_from_Sol_u256_CallData 
  decode_from_CallData_2 decode_from_prechecked_head_Set0_Sol_CallData 
  decode_runtime_args_Evm_Sol_Set0 decode_from_CallData_3 
  decode_from_prechecked_head_Set1_Sol_CallData decode_runtime_args_Evm_Sol_Set1 HEAD_SIZE_3 
  decode_from_CallData_4 decode_from_prechecked_head_SetBoth_Sol_CallData 
  decode_runtime_args_Evm_Sol_SetBoth
  u256Mask checkedAdd checkedSub alloc mstore zeroMem returnData panicCode

/-! ## The decoders -/

section Decode

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `decode_runtime_args` at `Set0 { value: u256 }`: revert on calldata that cannot hold the
    selector and one word, otherwise the word after the selector. -/
theorem decodeSet0_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Set0.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).toNat = I.calldata.size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat I.calldata.size) (b := UInt256.ofNat 4)
      (by rw [hn, toNat4]; omega)
    rw [hn, toNat4] at h
    exact h
  have hslt : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).sltBool (UInt256.ofNat 32) =
      decide (I.calldata.size - 4 < 32) := by
    rw [sltBool_small (by rw [hsub]; omega) (by rw [toNat32]; omega), hsub, toNat32]
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, UInt256.size, word, add0_32, ne32, at4, hslt,
    hshort]
  by_cases h : I.calldata.size < 36 <;> simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeSet1_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Set1.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4⟩, w)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).toNat = I.calldata.size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat I.calldata.size) (b := UInt256.ofNat 4)
      (by rw [hn, toNat4]; omega)
    rw [hn, toNat4] at h
    exact h
  have hslt : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).sltBool (UInt256.ofNat 32) =
      decide (I.calldata.size - 4 < 32) := by
    rw [sltBool_small (by rw [hsub]; omega) (by rw [toNat32]; omega), hsub, toNat32]
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  simp [toNat0, toNat32, truncate_size _ hfits, UInt256.size, word, add0_32, ne32, at4, hslt,
    hshort]
  by_cases h : I.calldata.size < 36 <;> simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeSetBoth_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_SetBoth.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).toNat = I.calldata.size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat I.calldata.size) (b := UInt256.ofNat 4)
      (by rw [hn, toNat4]; omega)
    rw [hn, toNat4] at h
    exact h
  have hslt : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).sltBool (UInt256.ofNat 64) =
      decide (I.calldata.size - 4 < 64) := by
    rw [sltBool_small (by rw [hsub]; omega) (by rw [toNat64]; omega), hsub, toNat64]
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [toNat0, toNat4, toNat32, truncate_size _ hfits, UInt256.size, word, add0_32, add32_32,
    ne64, at4, at36, hslt, hshort]
  by_cases h : I.calldata.size < 68 <;> simp [h]

theorem decodeGet0_exec : decode_runtime_args_Evm_Sol_Get0.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

theorem decodeGet1_exec : decode_runtime_args_Evm_Sol_Get1.exec I w = some (.ok (⟨⟩, w)) := by
  simp [toNat0]

end Decode

/-! ## The return -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `return_value` at `u256` ends the call with the word's 32 bytes.  It changes memory only. -/
theorem returnU256_exec (I : ExecutionEnv) (w : World) (v : UInt256)
    (hmem : w.memory.size < UInt256.size) :
    (return_value_Sol_u256 v).exec I w =
      some (.error (.stop v.toByteArray { w with memory := returned w.memory v })) := by
  have hsize : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ hmem
  simp [toNat0, toNat32, toNatMax, toNatU64, sub32_0, add_zero, hsize, UInt256.size, returned]
  exact returned_read _ _

end Std

/-! ## The arms' entries -/

section Entries

variable (I : ExecutionEnv) (w : World)

theorem get0_endsAs (hmem : w.memory.size < UInt256.size) :
    EndsAs ((entry recv0_arm0_entry).exec I w) (get0Arm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [entry_exec (f := .stop _ _) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeGet0_exec, get0_exec,
        returnU256_exec _ _ _ hmem]
      exact ⟨rfl, rfl⟩)]
    simp [get0Arm, exec_nonPayable, hwv, get0_exec]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv])]
    simp [get0Arm, exec_nonPayable, hwv]
    exact .exit _

theorem get1_endsAs (hmem : w.memory.size < UInt256.size) :
    EndsAs ((entry recv0_arm1_entry).exec I w) (get1Arm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [entry_exec (f := .stop _ _) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeGet1_exec, get1_exec,
        returnU256_exec _ _ _ hmem]
      exact ⟨rfl, rfl⟩)]
    simp [get1Arm, exec_nonPayable, hwv, get1_exec]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv])]
    simp [get1Arm, exec_nonPayable, hwv]
    exact .exit _

theorem set0_endsAs (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm2_entry).exec I w) ((set0Arm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv])]
    simp [set0Arm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w hlo hfits, hshort])]
    simp [set0Arm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { w with accounts := setLane I w.accounts 0 (word I.calldata 4) }) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w hlo hfits, hshort,
        set0_exec, hperm, returnNone_exec])]
    simp [set0Arm, exec_nonPayable, hwv, hgood, set0_exec, hperm]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w hlo hfits, hshort,
        set0_exec, hperm])]
    simp [set0Arm, exec_nonPayable, hwv, hgood, set0_exec, hperm]
    exact .exit _

theorem set1_endsAs (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm3_entry).exec I w) ((set1Arm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv])]
    simp [set1Arm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w hlo hfits, hshort])]
    simp [set1Arm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { w with accounts := setLane I w.accounts 1 (word I.calldata 4) }) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w hlo hfits, hshort,
        set1_exec, hperm, returnNone_exec])]
    simp [set1Arm, exec_nonPayable, hwv, hgood, set1_exec, hperm]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w hlo hfits, hshort,
        set1_exec, hperm])]
    simp [set1Arm, exec_nonPayable, hwv, hgood, set1_exec, hperm]
    exact .exit _

theorem setBoth_endsAs (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm4_entry).exec I w) ((setBothArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv])]
    simp [setBothArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w hlo hfits, hshort])]
    simp [setBothArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { w with accounts :=
            setLane I (setLane I w.accounts 0 (word I.calldata 4)) 1 (word I.calldata 36) }) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w hlo hfits, hshort,
        setBoth_exec, hperm, returnNone_exec])]
    simp [setBothArm, exec_nonPayable, hwv, hgood, setBoth_exec, hperm]
    exact .stop_ok rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w hlo hfits, hshort,
        setBoth_exec, hperm])]
    simp [setBothArm, exec_nonPayable, hwv, hgood, setBoth_exec, hperm]
    exact .exit _

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written one does, on calldata below `2 ^ 64`
    bytes. -/
theorem runtime_endsAs (hmem : w.memory.size < UInt256.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (handRuntime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (fePackedStoreSelBytes i)) →
      (fePackedStoreSelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [entry_exec (f := .revert ByteArray.empty) (by simp [runtime, hn, hlt])]
    simp [handRuntime, hlt]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h1 : selIs I (fePackedStoreSelBytes 1)
  · have hw := selWord_hit (get0EvmSelector hsz) h1
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = get0Arm.exec I w := by
      simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = true from h1]
    rw [eg, eh]
    exact get0_endsAs I w hmem
  have n1 := miss 1 h1
  have w1 : selWord I.calldata ≠ UInt256.ofNat 0x90bb7b44 := selWord_miss (get0EvmSelector hsz) n1
  by_cases h0 : selIs I (fePackedStoreSelBytes 0)
  · have hw := selWord_hit (get1EvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm1_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = get1Arm.exec I w := by
      simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = false from n1,
        show (get1Selector == I.calldata.extract 0 4) = true from h0]
    rw [eg, eh]
    exact get1_endsAs I w hmem
  have n0 := miss 0 h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x054c1a75 := selWord_miss (get1EvmSelector hsz) n0
  by_cases h4 : selIs I (fePackedStoreSelBytes 4)
  · have hw := selWord_hit (set0EvmSelector hsz) h4
    have eg : (entry runtime).exec I w = (entry recv0_arm2_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (set0Arm I.calldata).exec I w := by
      simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = false from n1,
        show (get1Selector == I.calldata.extract 0 4) = false from n0,
        show (set0Selector == I.calldata.extract 0 4) = true from h4]
    rw [eg, eh]
    exact set0_endsAs I w hsz hfits
  have n4 := miss 4 h4
  have w4 : selWord I.calldata ≠ UInt256.ofNat 0xf26feec9 := selWord_miss (set0EvmSelector hsz) n4
  by_cases h3 : selIs I (fePackedStoreSelBytes 3)
  · have hw := selWord_hit (set1EvmSelector hsz) h3
    have eg : (entry runtime).exec I w = (entry recv0_arm3_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (set1Arm I.calldata).exec I w := by
      simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = false from n1,
        show (get1Selector == I.calldata.extract 0 4) = false from n0,
        show (set0Selector == I.calldata.extract 0 4) = false from n4,
        show (set1Selector == I.calldata.extract 0 4) = true from h3]
    rw [eg, eh]
    exact set1_endsAs I w hsz hfits
  have n3 := miss 3 h3
  have w3 : selWord I.calldata ≠ UInt256.ofNat 0x9bc39d3c := selWord_miss (set1EvmSelector hsz) n3
  by_cases h2 : selIs I (fePackedStoreSelBytes 2)
  · have hw := selWord_hit (setBothEvmSelector hsz) h2
    have eg : (entry runtime).exec I w = (entry recv0_arm4_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : handRuntime.exec I w = (setBothArm I.calldata).exec I w := by
      simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = false from n1,
        show (get1Selector == I.calldata.extract 0 4) = false from n0,
        show (set0Selector == I.calldata.extract 0 4) = false from n4,
        show (set1Selector == I.calldata.extract 0 4) = false from n3,
        show (setBothSelector == I.calldata.extract 0 4) = true from h2]
    rw [eg, eh]
    exact setBoth_endsAs I w hsz hfits
  have n2 := miss 2 h2
  have w2 : selWord I.calldata ≠ UInt256.ofNat 0x92cf1ef5 :=
    selWord_miss (setBothEvmSelector hsz) n2
  rw [entry_exec (f := .revert ByteArray.empty) (by
    simp [runtime, hn, hn4, selector_exec, w0, w1, w2, w3, w4])]
  simp [handRuntime, hn4, show (get0Selector == I.calldata.extract 0 4) = false from n1,
    show (get1Selector == I.calldata.extract 0 4) = false from n0,
    show (set0Selector == I.calldata.extract 0 4) = false from n4,
    show (set1Selector == I.calldata.extract 0 4) = false from n3,
    show (setBothSelector == I.calldata.extract 0 4) = false from n2]
  exact .exit _

end Entries

/-! ## The certificate -/

/-- The contract as exported: `init` behind the call-value check deployment makes, and the
    exported runtime entry. -/
def contract : ContractModel := ⟨initEntry, entry runtime⟩

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem fePackedStoreRefinesExported :
    RefinesOn .P0 fePackedStoreBytecode contract CalldataFits := by
  intro σ σ₀ g A I hcode hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases fePackedStoreRefinesHandEntry σ σ₀ g A I hcode hsize with h | h
  · exact Or.inl h
  · exact Or.inr (Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A) (by simp [World.init, UInt256.size]) hfits) h)

/-- Deployment: the creation bytecode does what `init` does and returns the runtime bytecode. -/
theorem fePackedStoreDeployRefinesExported :
    RefinesDeploy .P0 fePackedStoreCreationBytecode fePackedStoreBytecode contract
      (· = ByteArray.empty) :=
  fePackedStoreDeployRefinesHandEntry

end FeProofs.PackedStore.Exported
