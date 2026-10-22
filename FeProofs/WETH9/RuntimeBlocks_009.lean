import Reasoning.Reach
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9Blocks

/-- Final stack for bytecode block summary `feWETH9_block_1210_taken`. -/
def feWETH9_block_1210_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1210. -/
theorem feWETH9_block_1210_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1225) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1210) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1225) (feWETH9_block_1210_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1225) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1225)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1210_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1225) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1210) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1225) (feWETH9_block_1210_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1210_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1210_fallthrough`. -/
def feWETH9_block_1210_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1210. -/
theorem feWETH9_block_1210_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1210) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1216) (feWETH9_block_1210_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1225) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1216)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1210_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1210) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1216) (feWETH9_block_1210_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1210_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_1216`. -/
def feWETH9_block_1216_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1216. -/
theorem feWETH9_block_1216 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1230) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1216) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1230) R (feWETH9_block_1216_memory (mem := mem)) (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1230) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1230)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1216_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1230) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1216) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1230) R (feWETH9_block_1216_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1216 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_1225`. -/
def feWETH9_block_1225_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1225. -/
theorem feWETH9_block_1225 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1230) R (feWETH9_block_1225_memory (mem := mem)) (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((9) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1230)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1225_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1230) R (feWETH9_block_1225_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1225 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1230. -/
theorem feWETH9_block_1230 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1230) R mem aw rdata σ k C)
    : RDret FeProofs.WETH9.feWETH9Bytecode g s0 σ (mem.readWithPadding (UInt256.ofNat 224).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  exact RD.genRet r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feWETH9_block_1236_taken`. -/
def feWETH9_block_1236_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1236. -/
theorem feWETH9_block_1236_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((UInt256.ofNat 32) + x1) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1256) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (feWETH9_block_1236_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1256) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1256)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1236_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((UInt256.ofNat 32) + x1) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1256) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (feWETH9_block_1236_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1236_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1236_fallthrough`. -/
def feWETH9_block_1236_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1236. -/
theorem feWETH9_block_1236_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((UInt256.ofNat 32) + x1) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1250) (feWETH9_block_1236_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1256) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1250)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1236_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((UInt256.ofNat 32) + x1) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1250) (feWETH9_block_1236_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1236_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1250`. -/
def feWETH9_block_1250_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 17) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1250. -/
theorem feWETH9_block_1250 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1572) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1250) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1572) (feWETH9_block_1250_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 17) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1572) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1572)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1250_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1572) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1250) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1572) (feWETH9_block_1250_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1250 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1256. -/
theorem feWETH9_block_1256_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1565) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1565) (x0 :: R) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.not (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1565) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1565)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1256_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1565) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1565) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1256_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1256. -/
theorem feWETH9_block_1256_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) (x0 :: R) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.not (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1565) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1268)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1256_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1256) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1256_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1268_taken`. -/
def feWETH9_block_1268_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1268. -/
theorem feWETH9_block_1268_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1283) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1283) (feWETH9_block_1268_taken_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 223) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1283) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1283)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1268_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1283) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1283) (feWETH9_block_1268_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1268_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1268_fallthrough`. -/
def feWETH9_block_1268_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1268. -/
theorem feWETH9_block_1268_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1280) (feWETH9_block_1268_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 223) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1283) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1280)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1268_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1268) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1280) (feWETH9_block_1268_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1268_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1280`. -/
def feWETH9_block_1280_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 224) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1280. -/
theorem feWETH9_block_1280 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1280) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1283) (feWETH9_block_1280_stack (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1283)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1280_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1280) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1283) (feWETH9_block_1280_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1280 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1283. -/
theorem feWETH9_block_1283 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1283) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDret FeProofs.WETH9.feWETH9Bytecode g s0 σ ((((UInt256.ofNat 32).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem x0.toNat x1.toNat) x0.toNat 32).write x2.toNat ((UInt256.ofNat 32).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem x0.toNat x1.toNat) x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat x3.toNat).readWithPadding x0.toNat x1.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := RD.genCalldatacopy r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.swap3 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.swap4 (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := RD.genMcopy r17 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  exact RD.genRet r19 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `feWETH9_block_1305_taken`. -/
def feWETH9_block_1305_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1305. -/
theorem feWETH9_block_1305_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1539) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1305) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1539) (x0 :: x1 :: x2 :: R) (feWETH9_block_1305_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.lt (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1539) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1539)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1305_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1539) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1305) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1539) (x0 :: x1 :: x2 :: R) (feWETH9_block_1305_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_1305_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_1305_fallthrough`. -/
def feWETH9_block_1305_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1305. -/
theorem feWETH9_block_1305_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))) x2) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1305) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: x1 :: x2 :: R) (feWETH9_block_1305_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.lt (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1539) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1328)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1305_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))) x2) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1305) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: x1 :: x2 :: R) (feWETH9_block_1305_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_1305_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1328_taken`. -/
def feWETH9_block_1328_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1328. -/
theorem feWETH9_block_1328_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1448) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1448) (feWETH9_block_1328_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1448) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1448)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1328_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1448) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1448) (feWETH9_block_1328_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1328_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_1328_fallthrough`. -/
def feWETH9_block_1328_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1328. -/
theorem feWETH9_block_1328_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (feWETH9_block_1328_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1448) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1337)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1328_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1328) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (feWETH9_block_1328_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_1328_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_1337_taken`. -/
def feWETH9_block_1337_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1337. -/
theorem feWETH9_block_1337_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1442) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) (feWETH9_block_1337_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := r19.not (by native_decide) (by evm_ov)
  have r21 := r20.eq (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1442) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1442)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1337_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1442) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) (feWETH9_block_1337_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_1337_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_1337_fallthrough`. -/
def feWETH9_block_1337_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1337. -/
theorem feWETH9_block_1337_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1371) (x0 :: x1 :: R) (feWETH9_block_1337_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := r19.not (by native_decide) (by evm_ov)
  have r21 := r20.eq (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1442) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1371)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_1337_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1337) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1371) (x0 :: x1 :: R) (feWETH9_block_1337_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_1337_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end feWETH9Blocks
