import Reasoning.Reach
import FeProofs.NarrowAbi.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feNarrowAbiBlocks

/-- Automatically generated RD summary for bytecode block at pc 197. -/
theorem feNarrowAbi_block_197 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 197) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.NarrowAbi.feNarrowAbiBytecode g s0 σ ((x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r5 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feNarrowAbi_block_204_taken`. -/
def feNarrowAbi_block_204_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 204. -/
theorem feNarrowAbi_block_204_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 204) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 98) (feNarrowAbi_block_204_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_204_fallthrough`. -/
def feNarrowAbi_block_204_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 204. -/
theorem feNarrowAbi_block_204_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 204) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 210) (feNarrowAbi_block_204_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 210)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 210. -/
theorem feNarrowAbi_block_210_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 210) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 98) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 210. -/
theorem feNarrowAbi_block_210_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 210) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 222) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 222)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_222_taken`. -/
def feNarrowAbi_block_222_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 222. -/
theorem feNarrowAbi_block_222_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 222) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 98) (feNarrowAbi_block_222_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_222_fallthrough`. -/
def feNarrowAbi_block_222_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 222. -/
theorem feNarrowAbi_block_222_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 222) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 232) (feNarrowAbi_block_222_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 232)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 232. -/
theorem feNarrowAbi_block_232 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 232) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.NarrowAbi.feNarrowAbiBytecode g s0 σ ((x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r4 (by native_decide) (by evm_ov)

end feNarrowAbiBlocks
