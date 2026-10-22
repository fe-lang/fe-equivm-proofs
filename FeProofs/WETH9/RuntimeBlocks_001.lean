import Reasoning.Reach
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9Blocks

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feWETH9_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 723) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 723) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 723)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_0_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 723) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feWETH9_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 723) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_0_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_9_taken`. -/
def feWETH9_block_9_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9. -/
theorem feWETH9_block_9_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 117300739)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 137) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) (feWETH9_block_9_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 117300739) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 137) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 137)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_9_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 117300739)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 137) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) (feWETH9_block_9_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_9_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_9_fallthrough`. -/
def feWETH9_block_9_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9. -/
theorem feWETH9_block_9_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 117300739)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (feWETH9_block_9_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 117300739) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 137) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_9_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 117300739)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (feWETH9_block_9_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_9_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feWETH9_block_24_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 157198259)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 162) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 157198259) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 162) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 162)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_24_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 157198259)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 162) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_24_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feWETH9_block_24_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 157198259)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 157198259) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 162) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 34)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_24_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 157198259)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_24_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 34. -/
theorem feWETH9_block_34_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 404098525)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 272) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 404098525) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 272) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 272)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_34_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 404098525)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 272) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_34_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 34. -/
theorem feWETH9_block_34_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 404098525)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 404098525) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 272) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 45)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_34_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 404098525)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_34_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 45. -/
theorem feWETH9_block_45_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 599290589)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 284) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 599290589) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 284) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 284)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_45_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 599290589)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 284) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_45_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 45. -/
theorem feWETH9_block_45_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 599290589)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 599290589) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 284) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 56)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_45_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 599290589)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 45) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_45_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 56. -/
theorem feWETH9_block_56_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 340) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 340) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 773487949) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 340) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 340)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_56_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 340) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 340) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_56_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 56. -/
theorem feWETH9_block_56_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 773487949) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 340) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 67)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_56_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_56_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 67. -/
theorem feWETH9_block_67_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 826074471)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 506) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 826074471) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 506) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 506)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_67_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 826074471)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 506) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_67_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 67. -/
theorem feWETH9_block_67_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 826074471)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 826074471) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 506) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 78)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_67_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 826074471)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 67) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_67_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 78. -/
theorem feWETH9_block_78_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 523) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 523) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 523) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 523)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_78_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 523) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 523) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_78_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 78. -/
theorem feWETH9_block_78_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 523) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 89)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_78_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 78) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_78_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 89. -/
theorem feWETH9_block_89_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2514000705)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 571) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 571) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2514000705) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 571) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 571)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_89_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2514000705)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 571) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 571) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_89_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 89. -/
theorem feWETH9_block_89_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2514000705)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2514000705) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 571) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 100)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_89_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2514000705)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 89) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_89_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 100. -/
theorem feWETH9_block_100_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 592) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2835717307) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 592) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 592)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_100_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 592) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_100_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 100. -/
theorem feWETH9_block_100_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2835717307) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 592) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_100_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 100) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_100_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end feWETH9Blocks
