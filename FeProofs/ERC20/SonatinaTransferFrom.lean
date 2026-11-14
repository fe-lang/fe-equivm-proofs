import FeProofs.ERC20.SonatinaRun

/-!
# FeERC20's `transferFrom` against the machine IR

Both sides read `from`'s balance again after the allowance is written, and both panic if it is
now below the value, so they agree even where the two slots coincide.
-/
namespace FeProofs.ERC20.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open Exported (decodeTransfer_exec decodeApprove_exec decodeTransferFrom_exec
  decodeBalanceOf_exec decodeAllowance_exec decodeTotalSupply_exec initEntry_exec)

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/- The exported entries, their arms and the primitives they reach unfold under `simp` here. -/
attribute [local simp] Exported.recv0_arm0_entry Exported.recv0_arm1_entry
  Exported.recv0_arm2_entry Exported.recv0_arm3_entry Exported.recv0_arm4_entry
  Exported.recv0_arm5_entry Exported.recv0_arm0 Exported.recv0_arm1 Exported.recv0_arm2
  Exported.recv0_arm3 Exported.recv0_arm4 Exported.recv0_arm5 Exported.balancesField
  Exported.allowancesField Exported.supplyField Place.storage store load sload entry
  exec_nonPayable exec_sstore ofNat_zero_eq

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- `transferFrom(address,address,uint256)`.  Both sides read `from`'s balance again after the
    allowance is written, so they agree even where the two slots coincide. -/
theorem arm_transferFrom (hmem : w.memory.size + 1024 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm2_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 15).exec I w)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := decodeTransferFrom_exec I w hsz hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 100
  · have hlt : (I.calldata.size : Int) - 4 < 96 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 96 := by omega
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
  have hk : ∀ k r k' r' k'' r'', (keyed (keyed (keyed w.memory k r) k' r') k'' r'').size + 64 <
      UInt256.size := by
    intro _ _ _ _ _ _; simp only [keyed_size]; omega
  have hk4 : ∀ k r k' r' k'' r'' k3 r3,
      (keyed (keyed (keyed (keyed w.memory k r) k' r') k'' r'') k3 r3).size + 64 <
        UInt256.size := by
    intro _ _ _ _ _ _ _ _; simp only [keyed_size]; omega
  -- The allowance check.
  by_cases hA : (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
      (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1)))).toNat <
      (Fe.EVM.word I.calldata 68).toNat
  · simp (disch := room) [hwv, hdec, hshort, hna, hnb, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec, Nat.not_le.mpr hA]
    simp only [Fe.EVM.word] at hA
    repeat ir_step
    exact endsAs_revert (by decide +kernel)
  have hAW := Nat.le_of_not_lt hA
  have hAN := hA
  simp only [Fe.EVM.word] at hA
  -- The balance check, before any write.
  by_cases hB : (slotWord I w.accounts (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) ⟨0⟩)).toNat <
      (Fe.EVM.word I.calldata 68).toNat
  · simp (disch := room) [hwv, hdec, hshort, hna, hnb, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec, hAW,
      Nat.not_le.mpr hB]
    simp only [Fe.EVM.word] at hB
    repeat ir_step
    exact endsAs_revert (by decide +kernel)
  have hBW := Nat.le_of_not_lt hB
  have hBN := hB
  simp only [Fe.EVM.word] at hB
  by_cases hperm : I.perm = true
  swap
  · simp (maxSteps := 2000000) (disch := room) [hwv, hdec, hshort, hna, hnb,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      hAW, hAN, hBW, hperm, checkedSub, Fe.M.ite_bind]
    repeat ir_step
    exact .exit _
  -- `from`'s balance read again after the allowance is written.
  by_cases hU : (slotWord I (storeWord I.codeOwner w.accounts
      (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
        (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1)))
      (UInt256.sub (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
        (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1))))
        (Fe.EVM.word I.calldata 68)))
      (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) ⟨0⟩)).toNat < (Fe.EVM.word I.calldata 68).toNat
  · have hUW := hU
    simp only [Fe.EVM.word] at hU
    simp (maxSteps := 2000000) (disch := room) [hwv, hdec, hshort, hna, hnb,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      hAW, hAN, hBW, hperm, checkedSub, Fe.M.ite_bind, hUW]
    repeat ir_step
    exact .panic_revert 17
  have hUW := hU
  simp only [Fe.EVM.word] at hU
  -- The receiver's balance after both writes, which both sides read.
  by_cases hO : UInt256.size ≤ (slotWord I (storeWord I.codeOwner (storeWord I.codeOwner
      w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
        (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1)))
      (UInt256.sub (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
        (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1))))
        (Fe.EVM.word I.calldata 68)))
      (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) ⟨0⟩)
      (UInt256.sub (slotWord I (storeWord I.codeOwner w.accounts
        (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
          (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1)))
        (UInt256.sub (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val)
          (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) (UInt256.ofNat 1))))
          (Fe.EVM.word I.calldata 68)))
        (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) ⟨0⟩)) (Fe.EVM.word I.calldata 68)))
      (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 36) ⟨0⟩)).toNat + (Fe.EVM.word I.calldata 68).toNat
  · have hOW := hO
    have hOL := hO
    simp only [UInt256.size] at hOL
    simp only [Fe.EVM.word] at hO
    have hOB := hO
    simp only [UInt256.size] at hOB
    simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, hna, hnb,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      hAW, hAN, hBW, hperm, checkedSub, checkedAdd, Fe.M.ite_bind, 
      hUW, hOW]
    repeat ir_step
    exact .panic_revert 17
  · have hOW := hO
    have hOL := hO
    simp only [UInt256.size] at hOL
    simp only [Fe.EVM.word] at hO
    have hOB := hO
    simp only [UInt256.size] at hOB
    simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, hna, hnb,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec,
      hAW, hAN, hBW, hperm, checkedSub, checkedAdd, Fe.M.ite_bind, 
      hUW, hOW, Exported.emitTransferLit_exec]
    -- The room the event's buffer needs, from the room the arm has.
    split_ifs with hroom
    swap
    · exact absurd (by simp only [keyed_size]; omega) hroom
    simp (disch := room) [FeProofs.Lib.returnBool_exec]
    repeat ir_step
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl

end FeProofs.ERC20.Sonatina
