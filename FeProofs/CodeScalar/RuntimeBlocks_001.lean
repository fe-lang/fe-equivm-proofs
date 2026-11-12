import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.CodeScalar.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feCodeScalarBlocks

set_option maxRecDepth 10000

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feCodeScalar_block_0_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) 0).contains (UInt256.ofNat 32) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 32) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨0⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨1⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨3⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨4⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨5⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨7⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 32)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feCodeScalar_block_0_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 8) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨0⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨1⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨3⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨4⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨5⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨7⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feCodeScalar_block_8_taken`. -/
def feCodeScalar_block_8_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feCodeScalar_block_8_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1833756220)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) 0).contains (UInt256.ofNat 26) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 26) (feCodeScalar_block_8_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨8⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨9⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨10⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r4 := r3.shr (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨12⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1833756220) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨13⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1833756220), 4))) (by evm_ov)
  have r6 := r5.dup2 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨18⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r7 := r6.eq (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨19⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 26) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨20⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 26), 1))) (by evm_ov)
  have r9 := r8.jumpiT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨22⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 26)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feCodeScalar_block_8_fallthrough`. -/
def feCodeScalar_block_8_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feCodeScalar_block_8_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1833756220)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 23) (feCodeScalar_block_8_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨8⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨9⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨10⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r4 := r3.shr (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨12⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1833756220) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨13⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1833756220), 4))) (by evm_ov)
  have r6 := r5.dup2 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨18⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r7 := r6.eq (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨19⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 26) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨20⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 26), 1))) (by evm_ov)
  have r9 := r8.jumpiNT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨22⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 23. -/
theorem feCodeScalar_block_23 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) 0).contains (UInt256.ofNat 32) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 23) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 32) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨23⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.jump (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨25⟩ : UInt256), .JUMP, none)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 32)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem feCodeScalar_block_26_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) 0).contains (UInt256.ofNat 36) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨26⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.callvalue (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨27⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r3 := r2.iszero (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨28⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 36) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨29⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r5 := r4.jumpiT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨31⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 36)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem feCodeScalar_block_26_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 32) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨26⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.callvalue (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨27⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r3 := r2.iszero (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨28⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 36) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨29⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r5 := r4.jumpiNT (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨31⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 32)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 32. -/
theorem feCodeScalar_block_32 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 32) R mem aw rdata σ k C)
    : RDrev (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨32⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨33⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨34⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨35⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 36. -/
theorem feCodeScalar_block_36 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : RDret (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix) g s0 σ (((memLoad (⟨0⟩ : UInt256) ((FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix).write ((UInt256.lnot (UInt256.ofNat 31)) + (UInt256.ofNat (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix).size)).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)).toByteArray.write 0 ((FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix).write ((UInt256.lnot (UInt256.ofNat 31)) + (UInt256.ofNat (FeProofs.CodeScalar.feCodeScalarBytecode ++ suffix).size)).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨36⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.codesize (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨37⟩ : UInt256), .CODESIZE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨38⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r4 := r3.not (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨40⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r5 := r4.add (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨41⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨42⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r7 := r6.swap1 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨44⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨45⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genCodecopy r8 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨46⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r10 := r9.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨47⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨48⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨49⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨50⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨51⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r15 := r14.push0 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨53⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRet r15 (by append_decode(FeProofs.CodeScalar.feCodeScalarBytecode, suffix, (⟨54⟩ : UInt256), .RETURN, none)) (by evm_ov)

end feCodeScalarBlocks
