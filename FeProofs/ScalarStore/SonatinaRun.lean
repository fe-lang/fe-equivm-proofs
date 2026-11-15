import FeProofs.ScalarStore.Sonatina
import Fe.Sonatina.Run

/-!
# FeScalarStore's machine IR, run

The machine IR's runtime function as the sidecar has it (`runtimeFunc`, read from the sidecar by
`sonatina_func` and proved equal to the sidecar's by `rfl`), and its runs from the entry block on
each kind of call.
-/

namespace FeProofs.ScalarStore.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

-- The machine IR's runtime function, as the sidecar has it.
sonatina_func runtimeFunc "Fe/Sonatina/Fixtures/FeScalarStore.sidecar.json" "runtime"
  "contract_runtime_root_FeScalarStore"

theorem runtimeFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_runtime_root_FeScalarStore") = some (some runtimeFunc) := by
  rfl

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- Calldata shorter than a selector: the machine IR reverts with no data. -/
theorem ir_short (h : I.calldata.size < 4) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  have h' : I.calldata.size % UInt256.size = I.calldata.size :=
    Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  simp only [UInt256.size] at h'
  repeat ir_step

/-- The selector of `set(uint256)`, as the machine IR computes it. -/
abbrev SetSel : Prop := (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 = 1627277233

/-- The selector of `get()`, as the machine IR computes it. -/
abbrev GetSel : Prop := (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 = 1833756220

section Arms

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

/-- `set(uint256)` with call value: the machine IR reverts with no data. -/
theorem ir_set_value (hsel : SetSel I) (hwv : I.weiValue ≠ ⟨0⟩) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
  repeat ir_step

/-- `set(uint256)` on calldata too short for its argument: the machine IR reverts with no
    data. -/
theorem ir_set_head (hsel : SetSel I) (hwv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 36) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hlt : (I.calldata.size : Int) - 4 < 32 := by omega
  repeat ir_step

/-- `set(uint256)` with its argument: the machine IR stores it at slot 0 and stops with no
    data. -/
theorem ir_set (hsel : SetSel I) (hwv : I.weiValue = ⟨0⟩) (hlong : 36 ≤ I.calldata.size)
    (hperm : I.perm = true) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.stop ByteArray.empty
      { w with
        accounts := storeWord I.codeOwner w.accounts ⟨0⟩
          (uInt256OfByteArray (I.calldata.readBytes 4 32)) })) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hlt : ¬ (I.calldata.size : Int) - 4 < 32 := by omega
  repeat ir_step

/-- `set(uint256)` with its argument in a static call: the machine IR fails. -/
theorem ir_set_static (hsel : SetSel I) (hwv : I.weiValue = ⟨0⟩) (hlong : 36 ≤ I.calldata.size)
    (hperm : I.perm = false) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error .static) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hlt : ¬ (I.calldata.size : Int) - 4 < 32 := by omega
  repeat ir_step

/-- `get()` with call value: the machine IR reverts with no data. -/
theorem ir_get_value (hsel : GetSel I) (hwv : I.weiValue ≠ ⟨0⟩) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
  repeat ir_step

/-- `get()`: the machine IR stores the word at slot 0 at address 0 and returns it. -/
theorem ir_get (hsel : GetSel I) (hwv : I.weiValue = ⟨0⟩) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.stop
      (slotWord I w.accounts ⟨0⟩).toByteArray
      { w with memory := (slotWord I w.accounts ⟨0⟩).toByteArray.write 0 w.memory 0 32 })) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hb := Reasoning.Theory.toByteArray_write32_read_back w.memory (slotWord I w.accounts ⟨0⟩) 0
    (Nat.zero_le _)
  repeat ir_step

/-- A selector of neither arm: the machine IR reverts with no data. -/
theorem ir_noMatch (h0 : ¬ SetSel I) (h1 : ¬ GetSel I) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold SetSel at h0
  unfold GetSel at h1
  have h0' := Ne.symm h0
  have h1' := Ne.symm h1
  repeat ir_step

end Arms

/-- The machine IR's runtime: the runtime function from its entry block.  The runtime section
    names no free pointer, so there is no prologue. -/
theorem ir_runtime {I : ExecutionEnv} {w : World}
    {r : Option (Except (Fe.Exit World) (List Val × World))}
    (h : ∀ m ic, (runBlocks m ic runtimeFunc ∅ none 0).exec I w = r) :
    (sidecar.model .machine).runtime.exec I w = Check.endRun r := by
  rw [show (sidecar.model .machine).runtime = sidecar.runSection "runtime" .machine from rfl,
    Check.runSection_eq (f := runtimeFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp [Check.pre, h]

/-! ## The constructor -/

-- The machine IR's init function, as the sidecar has it.
sonatina_func initFunc "Fe/Sonatina/Fixtures/FeScalarStore.sidecar.json" "init"
  "contract_init_root_FeScalarStore"

theorem initFunc_eq : (((sidecar.section? "init").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_init_root_FeScalarStore") = some (some initFunc) := by
  rfl

section Init

variable {I}

/-- The constructor with call value: the machine IR reverts with no data. -/
theorem ir_init_value (hwv : I.weiValue ≠ ⟨0⟩) :
    (runBlocks m ic initFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
  repeat ir_step

/-- The constructor on code of 165 bytes, whose last 32 bytes, copied to address 96, read as
    `v`: the machine IR stores `v` at slot 0 and returns the 80 bytes of code at offset 53. -/
theorem ir_init {v : UInt256} (hs0 : ic.symbol "." = some (0, 133))
    (hs1 : ic.symbol "&FeScalarStore_runtime" = some (53, 80)) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsize : I.code.size = 165)
    (hword : uInt256OfByteArray ((I.code.write 133 w.memory 96 32).readWithPadding 96 32) = v) :
    (runBlocks m ic initFunc ∅ none 0).exec I w = some (.error (.stop
      ((I.code.write 53 (I.code.write 133 w.memory 96 32) 0 80).readWithPadding 0 80)
      { w with
        accounts := storeWord I.codeOwner w.accounts ⟨0⟩ v
        memory := I.code.write 53 (I.code.write 133 w.memory 96 32) 0 80 })) := by
  repeat ir_step [wrap]

end Init

/-- The machine IR's constructor: the prologue stores the free pointer 96 at address 64, then
    the init function runs from its entry block, with the symbols of the init section. -/
theorem ir_init_run {I : ExecutionEnv} {w : World} {args : ByteArray}
    {r : Option (Except (Fe.Exit World) (List Val × World))}
    (h : ∀ m ic, ic.symbol "." = some (0, 133) →
      ic.symbol "&FeScalarStore_runtime" = some (53, 80) →
      (runBlocks m ic initFunc ∅ none 0).exec I
        { w with memory := (UInt256.ofNat 96).toByteArray.write 0 w.memory 64 32 } = r) :
    ((sidecar.model .machine).init args).exec I w = Check.endRun r := by
  rw [show (sidecar.model .machine).init args = sidecar.runSection "init" .machine from rfl,
    Check.runSection_eq (f := initFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, ite_eq_left, Fe.M.exec_bind]
  simp [Fe.EVM.mstore, Check.toNat_ofNat, UInt256.size]
  rw [h] <;> rfl

end FeProofs.ScalarStore.Sonatina
