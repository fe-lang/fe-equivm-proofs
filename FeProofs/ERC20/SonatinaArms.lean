import FeProofs.ERC20.SonatinaRun

/-!
# FeERC20's arms without a checked operation, against the machine IR

Each theorem says that an exported arm entry ends as the machine IR's run from the arm's entry
block does: the exported side by `simp` with the std lemmas, the machine IR's by `ir_step`,
closed by an `EndsAs` constructor.
-/
namespace FeProofs.ERC20.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open Exported (decodeTransfer_exec decodeApprove_exec decodeTransferFrom_exec
  decodeBalanceOf_exec decodeAllowance_exec decodeTotalSupply_exec initEntry_exec)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/- The exported entries, their arms and the primitives they reach unfold under `simp` here. -/
attribute [local simp] Exported.recv_Transfer_entry Exported.recv_Approve_entry
  Exported.recv_TransferFrom_entry Exported.recv_BalanceOf_entry Exported.recv_Allowance_entry
  Exported.recv_TotalSupply_entry Exported.recv_Transfer Exported.recv_Approve Exported.recv_TransferFrom
  Exported.recv_BalanceOf Exported.recv_Allowance Exported.recv_TotalSupply Exported.balancesField
  Exported.allowancesField Exported.supplyField Place.storage store load sload entry
  exec_nonPayable exec_sstore

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

set_option maxHeartbeats 4000000 in
/-- `totalSupply()`. -/
theorem arm_totalSupply (hmem : w.memory.size + 32 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_TotalSupply_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p
        (runtimeFunc.caseBlock 0x18160ddd)).exec I w)) := by
  have hr : w.reserved.memory.size + 32 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
    simp [hwv, decodeTotalSupply_exec, FeProofs.Lib.returnU256_exec I w.reserved _ hr]
    repeat ir_step [Reasoning.Theory.toByteArray_write32_read_back]
    exact .stop_stop rfl rfl rfl
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 4000000 in
/-- `balanceOf(address)`. -/
theorem arm_balanceOf (hmem : w.memory.size + 96 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_BalanceOf_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p
        (runtimeFunc.caseBlock 0x70a08231)).exec I w)) := by
  have hr : w.reserved.memory.size + 96 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := decodeBalanceOf_exec I w.reserved hsz hfits
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
    repeat ir_step
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl

set_option maxHeartbeats 4000000 in
/-- `allowance(address,address)`. -/
theorem arm_allowance (hmem : w.memory.size + 160 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_Allowance_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p
        (runtimeFunc.caseBlock 0xdd62ed3e)).exec I w)) := by
  have hr : w.reserved.memory.size + 160 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := decodeAllowance_exec I w.reserved hsz hfits
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
  repeat ir_step
  simp only [Fe.EVM.word]
  exact .stop_stop rfl rfl rfl

set_option maxHeartbeats 8000000 in
/-- `approve(address,uint256)`. -/
theorem arm_approve (hmem : w.memory.size + 256 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_Approve_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p
        (runtimeFunc.caseBlock 0x095ea7b3)).exec I w)) := by
  have hr : w.reserved.memory.size + 256 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := decodeApprove_exec I w.reserved hsz hfits
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
  · have hk : ∀ k r k' r',
      (keyed (keyed w.reserved.memory k r) k' r').size + 32 < UInt256.size := by
      intro k r k' r'; simp only [keyed_size]; omega
    have hr : ∀ k r k' r' v, (returned (keyed (keyed w.reserved.memory k r) k' r') v).size + 32 <
        UInt256.size := by
      intro k r k' r' v; simp only [keyed_size, returned_size]; omega
    simp (disch := room) [hwv, hdec, hshort, hna, hperm, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      Exported.emitApprovalLit_exec, FeProofs.Lib.returnBool_exec, hk]
    repeat ir_step
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl
  · simp (disch := room) [hwv, hdec, hshort, hna, hperm, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec]
    repeat ir_step
    exact .exit _

end FeProofs.ERC20.Sonatina
