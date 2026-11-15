import FeProofs.WETH9.SonatinaRun

/-!
# FeWETH9's `withdraw` arm, against the machine IR

`withdraw(wad)` checks the caller's balance (`Panic(1)` when short), stores it less `wad`, and
sends `wad` to the caller with no data: gas 2300 when `wad` is zero, else 0 and the EVM's
stipend.  A failed call is `Panic(1)`; a successful one is followed by the `Withdrawal` log.

The exported arm makes its call with the empty buffers std allocates, at the end of memory; the
machine IR with windows at its free pointer, 224.  Both have no input and no output, so both
are the call on empty memory with the memory put back (`call_noData`, `call_noData0`): the same
term, of the same world but for memory, which `generalize` names `r`.  Whatever the callee does,
re-entry into this contract included, is in `r`: the accounts, logs and recorded calls after
the call are `r`'s on both sides, so the `calls` of the two runs' endings are equal by `rfl`.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open scoped FeProofs.Lib

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) {I : ExecutionEnv} (w : World)

attribute [local simp] Exported.recv0_arm4_entry Exported.recv0_arm4 Exported.balanceOfField
  Place.storage store load sload entry exec_nonPayable exec_sstore M.exec_ite toNat0 toNatMax
  toNatU64

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

/-- The calldata word at `n`, as the machine IR loads it. -/
local notation "cdw" n => uInt256OfByteArray (I.calldata.readBytes n 32)

set_option hygiene false in
/-- After the call: both sides hold the same call on the same world but memory, named `r`; on
    each of its endings both go on alike. -/
local macro "wd_after" : tactic => `(tactic| (
  generalize Fe.M.exec (Fe.EVM.call _ _ _ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩) I _ = r
  rcases r with _ | _ | ⟨a, v⟩
  · exact .diverge
  · exact .exit _
  by_cases ha : a = ⟨0⟩
  · have haN : a.toNat = 0 := by rw [ha]; rfl
    simp only [withMemory, ha, ite_true]
    repeat ir_step [haN]
    exact .panic_revert 1
  · have haN : ¬ a.toNat = 0 := fun h => ha (Check.eq_of_toNat h)
    simp (disch := room) [withMemory, ha, Exported.emitWithdrawalLit_exec, hp]
    repeat ir_step [haN, word_read_gap, hp]
    exact .stop_stop rfl rfl rfl))

variable (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 8000000 in
/-- `withdraw(uint256)`. -/
theorem arm_withdraw (hmem : w.memory.size + 256 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm4_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 27).exec I { w with memory := M })) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeWithdraw_exec I w hsz hfits
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
  simp only [Fe.EVM.word] at hdec ⊢
  by_cases hb : (slotWord I w.accounts (mapSlot (callerWord I) (UInt256.ofNat 3))).toNat <
      (cdw 4).toNat
  · simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, Nat.not_le.mpr hb,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec]
    repeat ir_step [pair_slot_gap, hb]
    exact .panic_revert 1
  have hb' := Nat.not_lt.mp hb
  by_cases hp : I.perm = true
  swap
  · simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, hb', hp,
      Exported.Evm_caller, FeProofs.Lib.locateAddress_exec]
    repeat ir_step [pair_slot_gap, hb, hp]
    exact .exit _
  simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, hb', hp,
    Exported.Evm_caller, FeProofs.Lib.locateAddress_exec, Exported.alloc_zero,
    Exported.maxAllocation_fits, call_noData, returndatasize]
  repeat ir_step [pair_slot_gap, hb, hp]
  by_cases hz : (cdw 4) = ⟨0⟩
  · have hzN : (cdw 4).toNat = 0 := by rw [hz]; rfl
    ir_simp [hzN]
    repeat ir_step [word_read_gap, Reasoning.Theory.uInt256OfByteArray_toByteArray, hzN]
    simp only [call_noData0 _ _ _ (UInt256.ofNat 224) (UInt256.ofNat 224)]
    wd_after
  · have hzN : ¬ (cdw 4).toNat = 0 := fun h => hz (Check.eq_of_toNat h)
    ir_simp [hzN]
    repeat ir_step [word_read_gap, Reasoning.Theory.uInt256OfByteArray_toByteArray, hzN]
    simp only [call_noData0 _ _ _ (UInt256.ofNat 224) (UInt256.ofNat 224)]
    wd_after
end FeProofs.WETH9.Sonatina
