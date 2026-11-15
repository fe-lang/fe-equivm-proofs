import FeProofs.WETH9.SonatinaRun

/-!
# FeWETH9's arms without a loop or a message call, against the machine IR

Each theorem says that an exported arm entry ends as the machine IR's run from the arm's entry
block does, from any environment and world: the exported side by `simp` with the std lemmas,
the machine IR's by `ir_step`, closed by an `EndsAs` constructor.  The machine IR's memory is any
`M`: the runtime's prologue has stored the free pointer, and these arms read only memory they
write first.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/- The exported entries, their arms and the primitives they reach unfold under `simp` here. -/
attribute [local simp] Exported.recv0_arm2_entry Exported.recv0_arm2 Exported.recv0_arm9_entry
  Exported.recv0_arm9 Exported.recv1_arm0_entry Exported.recv1_arm0
  Exported.deposit_Weth9Store_Evm_Evm Exported.recv0_arm5_entry Exported.recv0_arm6_entry
  Exported.recv0_arm6 Exported.recv0_arm10_entry Exported.recv0_arm10 Exported.recv0_arm1_entry
  Exported.recv0_arm1 Exported.balanceOfField Exported.allowanceField Place.storage store load
  sload entry exec_nonPayable exec_sstore

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

set_option maxHeartbeats 4000000 in
/-- `totalSupply()`: the contract's own balance. -/
theorem arm_totalSupply (hmem : w.memory.size + 32 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm2_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 15).exec I { w with memory := M })) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
    simp [hwv, Exported.decodeTotalSupply_exec, Exported.Evm_selfbalance, Exported.Wei_as_wei,
      Exported.wei, Fe.EVM.selfbalance, FeProofs.Lib.returnU256_exec I w _ hmem]
    repeat ir_step [Fe.EVM.selfbalance]
    exact .stop_stop rfl rfl rfl
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _

set_option maxHeartbeats 4000000 in
/-- `deposit()`: payable, the caller's balance grows by the call's value. -/
theorem arm_deposit (hdep : m.func? "deposit" = some depositFunc)
    (hmem : w.memory.size + 256 < UInt256.size) (M : ByteArray) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm9_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 59).exec I { w with memory := M })) := by
  by_cases hp : I.perm = true <;>
  · simp (disch := room) [Exported.decodeDeposit_exec, Exported.Evm_caller, Exported.Evm_value,
      Exported.Wei_as_wei, Exported.wei, Fe.EVM.callvalue, FeProofs.Lib.locateAddress_exec,
      Exported.emitDepositLit_exec, hp]
    ir_step [deposit_run ic I _ hdep, hp]
    first | exact .stop_stop rfl rfl rfl | exact .exit _

set_option maxHeartbeats 4000000 in
/-- The fallback, on calldata too short for a selector or of no arm's: a deposit. -/
theorem arm_fallback (hdep : m.func? "deposit" = some depositFunc)
    (hmem : w.memory.size + 256 < UInt256.size) (M : ByteArray) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv1_arm0_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 4).exec I { w with memory := M })) := by
  by_cases hp : I.perm = true <;>
  · simp (disch := room) [Exported.Evm_caller, Exported.Evm_value, Exported.Wei_as_wei,
      Exported.wei, Fe.EVM.callvalue, FeProofs.Lib.locateAddress_exec,
      Exported.emitDepositLit_exec, hp]
    ir_step [deposit_run ic I _ hdep, hp]
    first | exact .stop_stop rfl rfl rfl | exact .exit _

set_option maxHeartbeats 4000000 in
/-- `decimals()`: the low byte of slot 2. -/
theorem arm_decimals (hmem : w.memory.size + 32 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm5_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 39).exec I { w with memory := M })) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
    have hl : ∀ x : UInt256, UInt256.ofNat (x.toNat &&& 255) = x.land (UInt256.ofNat 255) :=
      fun x => Check.eq_of_toNat (by
        rw [FeProofs.land_lit_toNat x 8 _ rfl, Check.toNat_ofNat_lt
          (lt_of_le_of_lt Nat.and_le_right (by decide)), Nat.and_two_pow_sub_one_eq_mod _ 8])
    simp [hwv, Exported.decodeDecimals_exec, Exported.decimalsLit_exec,
      FeProofs.Lib.returnU8_exec I w _ hmem]
    repeat ir_step [hl]
    exact .stop_stop rfl rfl rfl
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 4000000 in
/-- `balanceOf(address)`. -/
theorem arm_balanceOf (hmem : w.memory.size + 96 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm6_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 42).exec I { w with memory := M })) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeBalanceOf_exec I w hsz hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 36
  · have hlt : (I.calldata.size : Int) - 4 < 32 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 32 := by omega
  by_cases hna : NotAddress (word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  · have ha : (word I.calldata 4).toNat >>> 160 = 0 := by
      by_contra h; exact hna ((notAddress_iff _).mpr h)
    simp only [Fe.EVM.word] at ha
    simp (disch := room) [hwv, hdec, hshort, hna, FeProofs.Lib.locateAddress_exec,
      FeProofs.Lib.returnU256_exec]
    repeat ir_step [pair_slot_gap]
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl

set_option maxHeartbeats 4000000 in
/-- `allowance(address,address)`. -/
theorem arm_allowance (hmem : w.memory.size + 160 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm10_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 60).exec I { w with memory := M })) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeAllowance_exec I w hsz hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 68
  · have hlt : (I.calldata.size : Int) - 4 < 64 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 64 := by omega
  by_cases hna : NotAddress (Fe.EVM.word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  have ha : (Fe.EVM.word I.calldata 4).toNat >>> 160 = 0 := by
    by_contra h; exact hna ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at ha
  by_cases hnb : NotAddress (Fe.EVM.word I.calldata 36)
  · have hb := (notAddress_iff _).mp hnb
    simp only [Fe.EVM.word] at hb
    simp [hwv, hdec, hshort, hna, hnb]
    repeat ir_step
    exact .exit _
  have hb : (Fe.EVM.word I.calldata 36).toNat >>> 160 = 0 := by
    by_contra h; exact hnb ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at hb
  simp (disch := room) [hwv, hdec, hshort, hna, hnb, FeProofs.Lib.locateAddress_exec,
    FeProofs.Lib.locateAddressMap_exec, FeProofs.Lib.returnU256_exec]
  repeat ir_step [pair_slot_gap]
  simp only [Fe.EVM.word]
  exact .stop_stop rfl rfl rfl

set_option maxHeartbeats 8000000 in
/-- `approve(address,uint256)`. -/
theorem arm_approve (hmem : w.memory.size + 256 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm1_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 8).exec I { w with memory := M })) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeApprove_exec I w hsz hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 68
  · have hlt : (I.calldata.size : Int) - 4 < 64 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 64 := by omega
  by_cases hna : NotAddress (Fe.EVM.word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  have ha : (Fe.EVM.word I.calldata 4).toNat >>> 160 = 0 := by
    by_contra h; exact hna ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at ha
  by_cases hperm : I.perm = true
  · simp (disch := room) [hwv, hdec, hshort, hna, hperm, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      Exported.emitApprovalLit_exec, FeProofs.Lib.returnBool_exec]
    repeat ir_step [pair_slot_gap, word_read_gap]
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl
  · simp (disch := room) [hwv, hdec, hshort, hna, hperm, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec]
    repeat ir_step [pair_slot_gap]
    exact .exit _

end FeProofs.WETH9.Sonatina
