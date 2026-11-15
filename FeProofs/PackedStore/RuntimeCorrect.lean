import FeProofs.Lib.ExportedCorrect
import FeProofs.PackedStore.HandEntry
import Fe.EVM.Entry

/-!
# FePackedStore: the bytecode refines the exported contract

`Exported.lean` ends with the runtime entry as `fe-lean-export` prints it: each arm's entry
decodes the message with std's `decode_runtime_args`, runs the arm and returns through std's
`return_value`, and `runtime` dispatches on the selector.  This file shows that entry ends as
the hand-written one of `HandEntry.lean` does, so the certificate for that one carries over.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (returnU256_exec)

namespace FeProofs.PackedStore.Exported

/-! ## Std code

The std definitions the entry reaches unfold under `simp` in this section. -/

section Std

attribute [local simp]
  Get0_HEAD_SIZE Get1_HEAD_SIZE Get0_decode_from_CallData
  decode_from_prechecked_head_Get0_Sol_CallData decode_runtime_args_Evm_Sol_Get0
  Get1_decode_from_CallData decode_from_prechecked_head_Get1_Sol_CallData
  decode_runtime_args_Evm_Sol_Get1 Set0_HEAD_SIZE Set1_HEAD_SIZE Set0_decode_from_CallData
  decode_from_prechecked_head_Set0_Sol_CallData decode_runtime_args_Evm_Sol_Set0
  Set1_decode_from_CallData decode_from_prechecked_head_Set1_Sol_CallData
  decode_runtime_args_Evm_Sol_Set1 SetBoth_HEAD_SIZE SetBoth_decode_from_CallData
  decode_from_prechecked_head_SetBoth_Sol_CallData decode_runtime_args_Evm_Sol_SetBoth u256Mask
  checkedAdd checkedSub alloc mstore zeroMem returnData panicCode

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

end Std

/-! ## The arms' entries -/

section Entries

variable (I : ExecutionEnv) (w : World)

theorem get0_endsAs (hmem : w.memory.size + 1024 < UInt256.size) :
    EndsAs ((entry recv0_arm0_entry).exec I w) (get0Arm.exec I w) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size := reserveMemory_room hmem (by decide)
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [entry_exec (f := .stop _ _) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeGet0_exec,
        get0_exec I w.reserved (by omega),
        returnU256_exec _ _ _ (show (afterLookup w.reserved).memory.size + 32 < UInt256.size by
          rw [afterLookup_size]; omega)]
      exact ⟨rfl, rfl⟩)]
    simp [get0Arm, exec_nonPayable, hwv, get0_exec I w (by omega)]
    exact .stop_ok rfl rfl rfl
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv])]
    simp [get0Arm, exec_nonPayable, hwv]
    exact .exit _

theorem get1_endsAs (hmem : w.memory.size + 1024 < UInt256.size) :
    EndsAs ((entry recv0_arm1_entry).exec I w) (get1Arm.exec I w) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size := reserveMemory_room hmem (by decide)
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [entry_exec (f := .stop _ _) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeGet1_exec,
        get1_exec I w.reserved (by omega),
        returnU256_exec _ _ _ (show (afterLookup w.reserved).memory.size + 32 < UInt256.size by
          rw [afterLookup_size]; omega)]
      exact ⟨rfl, rfl⟩)]
    simp [get1Arm, exec_nonPayable, hwv, get1_exec I w (by omega)]
    exact .stop_ok rfl rfl rfl
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv])]
    simp [get1Arm, exec_nonPayable, hwv]
    exact .exit _

theorem set0_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm2_entry).exec I w) ((set0Arm I.calldata).exec I w) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size := reserveMemory_room hmem (by decide)
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv])]
    simp [set0Arm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w.reserved hlo hfits,
        hshort])]
    simp [set0Arm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { afterLookup w.reserved with accounts := setLane I w.accounts 0 (word I.calldata 4) }) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w.reserved hlo hfits, hshort,
        set0_exec I w.reserved _ (by omega), hperm, returnNone_exec])]
    simp [set0Arm, exec_nonPayable, hwv, hgood, set0_exec I w _ (by omega), hperm]
    exact .stop_ok rfl rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeSet0_exec I w.reserved hlo hfits, hshort,
        set0_exec I w.reserved _ (by omega), hperm])]
    simp [set0Arm, exec_nonPayable, hwv, hgood, set0_exec I w _ (by omega), hperm]
    exact .exit _

theorem set1_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm3_entry).exec I w) ((set1Arm I.calldata).exec I w) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size := reserveMemory_room hmem (by decide)
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv])]
    simp [set1Arm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w.reserved hlo hfits,
        hshort])]
    simp [set1Arm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { afterLookup w.reserved with accounts := setLane I w.accounts 1 (word I.calldata 4) }) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w.reserved hlo hfits, hshort,
        set1_exec I w.reserved _ (by omega), hperm, returnNone_exec])]
    simp [set1Arm, exec_nonPayable, hwv, hgood, set1_exec I w _ (by omega), hperm]
    exact .stop_ok rfl rfl rfl
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeSet1_exec I w.reserved hlo hfits, hshort,
        set1_exec I w.reserved _ (by omega), hperm])]
    simp [set1Arm, exec_nonPayable, hwv, hgood, set1_exec I w _ (by omega), hperm]
    exact .exit _

theorem setBoth_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm4_entry).exec I w) ((setBothArm I.calldata).exec I w) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size := reserveMemory_room hmem (by decide)
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv])]
    simp [setBothArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w.reserved hlo hfits,
        hshort])]
    simp [setBothArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases hperm : I.perm = true
  · rw [entry_exec (f := .stop ByteArray.empty
        { afterLookup (afterLookup w.reserved) with
          accounts :=
            setLane I (setLane I w.accounts 0 (word I.calldata 4)) 1 (word I.calldata 36) }) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w.reserved hlo hfits,
        hshort,
        setBoth_exec I w.reserved _ _ (by omega), hperm, returnNone_exec])]
    simp [setBothArm, exec_nonPayable, hwv, hgood, setBoth_exec I w _ _ (by omega), hperm]
    exact .stop_ok rfl (by simp [afterLookup]) (by simp [afterLookup])
  · rw [entry_exec (f := .static) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeSetBoth_exec I w.reserved hlo hfits,
        hshort,
        setBoth_exec I w.reserved _ _ (by omega), hperm])]
    simp [setBothArm, exec_nonPayable, hwv, hgood, setBoth_exec I w _ _ (by omega), hperm]
    exact .exit _

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written one does, on calldata below `2 ^ 64`
    bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hfits : I.calldata.size < 2 ^ 64) :
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
    exact set0_endsAs I w hmem hsz hfits
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
    exact set1_endsAs I w hmem hsz hfits
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
    exact setBoth_endsAs I w hmem hsz hfits
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

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := deploy init_entry, runtime := entry runtime }

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem fePackedStoreRefinesExported :
    RefinesOn .P0 fePackedStoreBytecode contract CalldataFits := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hown hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases fePackedStoreRefinesHandEntry σ σ₀ g A I ByteArray.empty
      (by rw [ByteArray.append_empty]; exact hcode) rfl hown hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A feed) (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment: the creation bytecode does what the exported deployment entry does and returns
    the runtime bytecode.  The contract takes no arguments, so that entry is the hand-written
    one, the call-value check, then `init`, on reserved memory, which neither reads. -/
theorem fePackedStoreDeployRefinesExported :
    RefinesDeploy .P0 fePackedStoreCreationBytecode fePackedStoreBytecode contract
      (· = ByteArray.empty) := by
  have hinit : ∀ args, init_entry args = handContract.init args := fun args => by
    simp [handContract, init_entry, initEntry]
  have hign : ∀ args out, IgnoresMemory (handContract.init args >>= fun tail =>
      pure (out ++ tail)) := fun args out => by
    simp only [handContract, initEntry, init]
    ignores_memory
  intro σ σ₀ g A I args hargs hcode hown hperm
  refine (fePackedStoreDeployRefinesHandEntry σ σ₀ g A I args hargs hcode hown hperm).imp id
    fun ⟨feed, h⟩ => ⟨feed, Agrees.of_endsAs ?_ h⟩
  rw [show contract.init args = deploy init_entry args from rfl, deploy_bind_eq, hinit]
  exact (hign args _).endsAs I _ _

end FeProofs.PackedStore.Exported
