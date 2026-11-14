import FeProofs.ScalarStore.Sonatina

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
  rw [runBlocks.eq_1]
  simp [runtimeFunc, Func.block?, enter, Fe.Sonatina.bind, runBody.eq_2, runBody.eq_1, runInst,
    EvmOp.run, Fe.EVM.calldatasize, evalPair, evalInt, evalOperand, Fe.Sonatina.word, Val.as,
    Ty.bits, CmpOp.eval, Sonatina.bool, Check.toNat_ofNat, UInt256.size, h', h]
  rw [runBlocks.eq_1]
  simp [Func.block?, enter, Fe.Sonatina.bind, runBody.eq_1]
  rw [runBlocks.eq_1]
  simp [Func.block?, enter, Fe.Sonatina.bind, runBody.eq_1, revertData, evalWord,
    evalInt, evalOperand, Check.toNat_ofNat, Reasoning.Theory.byteArray_readWithPadding_zero]

end FeProofs.ScalarStore.Sonatina
