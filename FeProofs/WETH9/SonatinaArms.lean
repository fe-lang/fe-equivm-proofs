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
  Exported.deposit_Weth9Store_Evm_Evm Exported.balanceOfField Place.storage store load sload
  entry exec_nonPayable exec_sstore

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

end FeProofs.WETH9.Sonatina
