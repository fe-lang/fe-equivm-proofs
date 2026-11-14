import FeProofs.ScalarStore.Sonatina
import Fe.Sonatina.Run

/-!
# FeScalarStore's machine IR, run

The machine IR's runtime function as the sidecar has it (`runtimeFunc`, proved equal to the
sidecar's by `rfl`), and its runs from the entry block on each kind of call.
-/

namespace FeProofs.ScalarStore.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/-- The machine IR's runtime function, as the sidecar has it. -/
def runtimeFunc : Func :=
  { name := "contract_runtime_root_FeScalarStore",
    params := [],
    rets := [],
    blocks := [{ id := 0,
                 phis := [],
                 body := [{ dsts := [(0, Ty.int 256)],
                            inst := Inst.evm (EvmOp.calldataSize) [] },
                          { dsts := [(2, Ty.int 256)],
                            inst := Inst.cmp
                                      (CmpOp.lt)
                                      (Operand.var 0)
                                      (Operand.imm 256 4) }],
                 term := Term.br (Operand.var 2) 13 1 },
               { id := 1,
                 phis := [],
                 body := [{ dsts := [(4, Ty.int 256)],
                            inst := Inst.evm
                                      (EvmOp.calldataLoad)
                                      [Operand.imm 256 0] },
                          { dsts := [(6, Ty.int 256)],
                            inst := Inst.bin
                                      (BinOp.shr)
                                      (Operand.imm 256 224)
                                      (Operand.var 4) }],
                 term := Term.brTable
                           (Operand.var 6)
                           (some 14)
                           [(Operand.imm 256 1627277233, 5), (Operand.imm 256 1833756220, 10)] },
               { id := 13, phis := [], body := [], term := Term.jump 4 },
               { id := 14, phis := [], body := [], term := Term.jump 4 },
               { id := 4,
                 phis := [],
                 body := [],
                 term := Term.evmRevert (Operand.imm 256 0) (Operand.imm 256 0) },
               { id := 5,
                 phis := [],
                 body := [{ dsts := [(9, Ty.int 256)],
                            inst := Inst.evm (EvmOp.callValue) [] }],
                 term := Term.br (Operand.var 9) 6 7 },
               { id := 6,
                 phis := [],
                 body := [],
                 term := Term.evmRevert (Operand.imm 256 0) (Operand.imm 256 0) },
               { id := 7,
                 phis := [],
                 body := [{ dsts := [(11, Ty.int 256)],
                            inst := Inst.evm (EvmOp.calldataSize) [] },
                          { dsts := [(12, Ty.int 256)],
                            inst := Inst.bin
                                      (BinOp.sub)
                                      (Operand.var 11)
                                      (Operand.imm 256 4) },
                          { dsts := [(14, Ty.int 256)],
                            inst := Inst.cmp
                                      (CmpOp.slt)
                                      (Operand.var 12)
                                      (Operand.imm 256 32) }],
                 term := Term.br (Operand.var 14) 8 9 },
               { id := 8,
                 phis := [],
                 body := [],
                 term := Term.evmRevert (Operand.imm 256 0) (Operand.imm 256 0) },
               { id := 9,
                 phis := [],
                 body := [{ dsts := [(15, Ty.int 256)],
                            inst := Inst.evm
                                      (EvmOp.calldataLoad)
                                      [Operand.imm 256 4] },
                          { dsts := [],
                            inst := Inst.evm
                                      (EvmOp.sstore)
                                      [Operand.imm 256 0, Operand.var 15] }],
                 term := Term.evmReturn (Operand.imm 256 0) (Operand.imm 256 0) },
               { id := 10,
                 phis := [],
                 body := [{ dsts := [(16, Ty.int 256)],
                            inst := Inst.evm (EvmOp.callValue) [] }],
                 term := Term.br (Operand.var 16) 11 12 },
               { id := 11,
                 phis := [],
                 body := [],
                 term := Term.evmRevert (Operand.imm 256 0) (Operand.imm 256 0) },
               { id := 12,
                 phis := [],
                 body := [{ dsts := [(18, Ty.int 256)],
                            inst := Inst.evm (EvmOp.sload) [Operand.imm 256 0] },
                          { dsts := [],
                            inst := Inst.evm
                                      (EvmOp.mstore)
                                      [Operand.imm 256 0, Operand.var 18] }],
                 term := Term.evmReturn (Operand.imm 256 0) (Operand.imm 256 32) }] }

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
  repeat ir_step [runtimeFunc]

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
  repeat ir_step [runtimeFunc]

/-- `set(uint256)` on calldata too short for its argument: the machine IR reverts with no
    data. -/
theorem ir_set_head (hsel : SetSel I) (hwv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 36) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hlt : (I.calldata.size : Int) - 4 < 32 := by omega
  repeat ir_step [runtimeFunc]

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
  repeat ir_step [runtimeFunc]

/-- `set(uint256)` with its argument in a static call: the machine IR fails. -/
theorem ir_set_static (hsel : SetSel I) (hwv : I.weiValue = ⟨0⟩) (hlong : 36 ≤ I.calldata.size)
    (hperm : I.perm = false) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error .static) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hlt : ¬ (I.calldata.size : Int) - 4 < 32 := by omega
  repeat ir_step [runtimeFunc]

/-- `get()` with call value: the machine IR reverts with no data. -/
theorem ir_get_value (hsel : GetSel I) (hwv : I.weiValue ≠ ⟨0⟩) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
  repeat ir_step [runtimeFunc]

/-- `get()`: the machine IR stores the word at slot 0 at address 0 and returns it. -/
theorem ir_get (hsel : GetSel I) (hwv : I.weiValue = ⟨0⟩) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.stop
      (slotWord I w.accounts ⟨0⟩).toByteArray
      { w with memory := (slotWord I w.accounts ⟨0⟩).toByteArray.write 0 w.memory 0 32 })) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := calldata_facts hsz hfits
  have hb := Reasoning.Theory.toByteArray_write32_read_back w.memory (slotWord I w.accounts ⟨0⟩) 0
    (Nat.zero_le _)
  repeat ir_step [runtimeFunc]

/-- A selector of neither arm: the machine IR reverts with no data. -/
theorem ir_noMatch (h0 : ¬ SetSel I) (h1 : ¬ GetSel I) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold SetSel at h0
  unfold GetSel at h1
  have h0' := Ne.symm h0
  have h1' := Ne.symm h1
  repeat ir_step [runtimeFunc]

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

end FeProofs.ScalarStore.Sonatina
