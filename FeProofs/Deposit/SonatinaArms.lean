import FeProofs.Deposit.Sonatina
import FeProofs.Deposit.ExportedStd

/-!
# FeDeposit's `supportsInterface` and `get_deposit_count`, against the machine IR

Each theorem says that an exported arm entry ends as the machine IR's run from the arm's entry
block does, from any environment and world: the exported side by `simp` with the std lemmas,
the machine IR's by `ir_step`, closed by an `EndsAs` constructor.  The machine IR's memory is any
`M`: these arms read only memory they write first.
-/

namespace FeProofs.Deposit.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open scoped FeProofs.Lib

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) {I : ExecutionEnv} (w : World)

attribute [local simp] Exported.recv0_arm3_entry Exported.recv0_arm3 entry exec_nonPayable

variable (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 4000000 in
/-- `supportsInterface(bytes4)`: true of ERC-165's and the deposit contract's interface ids. -/
theorem arm_supportsInterface (hmem : w.memory.size + 32 < UInt256.size) (M : ByteArray)
    (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm3_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 5).exec I { w with memory := M })) := by
  have hr : w.reserved.memory.size + 32 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeSupportsInterface_exec I w.reserved hsz hfits
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
  simp only [Fe.EVM.word] at hdec
  have hzw : ∀ x : UInt256, (x <<< UInt256.ofNat 32 = UInt256.ofNat 0) ↔
      wrap 256 ((x.toNat : Int) <<< 32) = 0 := fun x => by
    rw [Exported.word_eq_iff, Exported.shl_toNat x (by decide)]; rfl
  have hsel : ∀ (x : UInt256) (k : Nat), k < UInt256.size →
      ((x >>> UInt256.ofNat 224) = UInt256.ofNat k ↔ x.toNat >>> 224 = k) := fun x k hk => by
    rw [Exported.word_eq_iff, Exported.shr_toNat x (by decide), Check.toNat_ofNat_lt hk]
  by_cases hz : wrap 256 (((uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat : Int) <<< 32) = 0
  swap
  · simp [hwv, hdec, hshort, (hzw _).not.mpr hz]
    repeat ir_step
    exact .exit _
  have hs1 := hsel (uInt256OfByteArray (I.calldata.readBytes 4 32)) 33540519 (by decide)
  have hs2 := hsel (uInt256OfByteArray (I.calldata.readBytes 4 32)) 2237925639 (by decide)
  by_cases h1 : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat >>> 224 = 33540519 <;>
  by_cases h2 : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat >>> 224 = 2237925639 <;>
  · simp [hwv, hdec, hshort, (hzw _).mpr hz, hs1, hs2, h1, h2,
      FeProofs.Lib.returnBool_exec I _ _ hr]
    repeat ir_step
    exact .stop_stop rfl rfl rfl

end FeProofs.Deposit.Sonatina
