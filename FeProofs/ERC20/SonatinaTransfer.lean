import FeProofs.ERC20.SonatinaRun

/-!
# FeERC20's `transfer` against the machine IR

The checked subtraction never fails, after the balance check; the checked addition's overflow
is the machine IR's `lt (a + b) a`, and both panic with `0x11`.
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
attribute [local simp] Exported.recv0_arm0_entry Exported.recv0_arm1_entry
  Exported.recv0_arm2_entry Exported.recv0_arm3_entry Exported.recv0_arm4_entry
  Exported.recv0_arm5_entry Exported.recv0_arm0 Exported.recv0_arm1 Exported.recv0_arm2
  Exported.recv0_arm3 Exported.recv0_arm4 Exported.recv0_arm5 Exported.balancesField
  Exported.allowancesField Exported.supplyField Place.storage store load sload entry
  exec_nonPayable exec_sstore

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 8000000 in
/-- `transfer(address,uint256)`. -/
theorem arm_transfer (hmem : w.memory.size + 512 < UInt256.size) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm0_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 40).exec I w)) := by
  have hr : w.reserved.memory.size + 512 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := decodeTransfer_exec I w.reserved hsz hfits
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
  -- The sender's balance and the value.
  by_cases hlow : (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val) ⟨0⟩)).toNat <
      (Fe.EVM.word I.calldata 36).toNat
  · have hlow' := Nat.not_le.mpr hlow
    simp (disch := room) [hwv, hdec, hshort, hna, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec]
    simp only [Fe.EVM.word] at hlow
    repeat ir_step
    exact endsAs_revert (by decide +kernel)
  have hlowW := Nat.le_of_not_lt hlow
  have hlowN := hlow
  simp only [Fe.EVM.word] at hlow
  by_cases hperm : I.perm = true
  swap
  · simp (disch := room) [hwv, hdec, hshort, hna, Exported.Evm_caller,
      FeProofs.Lib.locateAddress_exec, hperm, checkedSub, Fe.M.ite_bind,
      Fe.M.exec_ite]
    repeat ir_step
    exact .exit _
  -- The receiver's balance after the sender's is written, which both sides read.
  have hk : ∀ k r k' r' k'' r'',
    (keyed (keyed (keyed w.reserved.memory k r) k' r') k'' r'').size + 64 <
      UInt256.size := by
    intro _ _ _ _ _ _; simp only [keyed_size]; omega
  simp (maxSteps := 2000000) (disch := room) [hwv, hdec, hshort, hna, Exported.Evm_caller,
    FeProofs.Lib.locateAddress_exec, hperm, checkedSub, checkedAdd, Fe.M.ite_bind,
    Fe.M.exec_ite, Exported.emitTransferLit_exec, ofNat_zero_eq]
  by_cases hover : UInt256.size ≤ (slotWord I (storeWord I.codeOwner w.accounts
      (Fe.EVM.mapSlot (UInt256.ofNat I.source.val) ⟨0⟩)
      (UInt256.sub (slotWord I w.accounts (Fe.EVM.mapSlot (UInt256.ofNat I.source.val) ⟨0⟩))
        (Fe.EVM.word I.calldata 36))) (Fe.EVM.mapSlot (Fe.EVM.word I.calldata 4) ⟨0⟩)).toNat +
      (Fe.EVM.word I.calldata 36).toNat
  · have hoverW := hover
    have hoverL := hover
    simp only [UInt256.size] at hoverL
    simp only [Fe.EVM.word] at hover
    have hoverB := hover
    simp only [UInt256.size] at hoverB
    simp only [hoverW, ↓reduceIte]
    repeat ir_step
    exact .panic_revert 17
  · have hoverW := hover
    have hoverL := hover
    simp only [UInt256.size] at hoverL
    simp only [Fe.EVM.word] at hover
    have hoverB := hover
    simp only [UInt256.size] at hoverB
    have he : ∀ k r k' r' k'' r'' k3 r3 k4 r4,
        (keyed (keyed (keyed (keyed
          (keyed w.reserved.memory k r) k' r') k'' r'') k3 r3) k4 r4).size + 32 <
          UInt256.size := by
      intro _ _ _ _ _ _ _ _ _ _; simp only [keyed_size]; omega
    have hr : ∀ k r k' r' k'' r'' k3 r3 k4 r4 v,
        (returned (keyed (keyed (keyed (keyed
          (keyed w.reserved.memory k r) k' r') k'' r'') k3 r3) k4 r4)
          v).size + 32 < UInt256.size := by
      intro _ _ _ _ _ _ _ _ _ _ _; simp only [keyed_size, returned_size]; omega
    simp only [hoverW, ↓reduceIte]
    simp (disch := room) [he, FeProofs.Lib.returnBool_exec]
    repeat ir_step
    simp only [Fe.EVM.word]
    exact .stop_stop rfl rfl rfl

end FeProofs.ERC20.Sonatina
