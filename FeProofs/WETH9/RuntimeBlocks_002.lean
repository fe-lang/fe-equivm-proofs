import Reasoning.Reach
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9Blocks

/-- Automatically generated RD summary for bytecode block at pc 111. -/
theorem feWETH9_block_111_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3504541104)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 640) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 640) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3504541104) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 640)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_111_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3504541104)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 640) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 640) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_111_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 111. -/
theorem feWETH9_block_111_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3504541104)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3504541104) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 122)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_111_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3504541104)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 111) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_111_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 122. -/
theorem feWETH9_block_122_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 652) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 652) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3714247998) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 652) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 652)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_122_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 652) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 652) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_122_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 122. -/
theorem feWETH9_block_122_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 133) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3714247998) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 652) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 133)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_122_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 122) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 133) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_122_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 133. -/
theorem feWETH9_block_133 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 723) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 133) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 723) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 723)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_133_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 723) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 133) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_133 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 137. -/
theorem feWETH9_block_137_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 147) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 147) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 147) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 147)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_137_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 147) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 147) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_137_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 137. -/
theorem feWETH9_block_137_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 147) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_137_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 137) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_137_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 143. -/
theorem feWETH9_block_143 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw rdata σ k C)
    : RDrev FeProofs.WETH9.feWETH9Bytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feWETH9_block_147`. -/
def feWETH9_block_147_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (UInt256.ofNat 156) :: R)

/-- Automatically generated RD summary for bytecode block at pc 147. -/
theorem feWETH9_block_147 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 800) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 800) (feWETH9_block_147_stack (R := R)) mem aw rdata σ (k + 6) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 156) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 800)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_147_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 800) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 800) (feWETH9_block_147_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_147 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 156. -/
theorem feWETH9_block_156 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1236) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 156) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1236) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1236)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_156_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1236) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 156) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1236) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_156 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 161. -/
theorem feWETH9_block_161 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 161) R mem aw rdata σ k C)
    : RDinvalid FeProofs.WETH9.feWETH9Bytecode g s0 := by
  let r0 := h
  exact RD.invalid r0 (by native_decide)

/-- Final stack for bytecode block summary `feWETH9_block_162_taken`. -/
def feWETH9_block_162_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 162. -/
theorem feWETH9_block_162_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_162_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_162_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_162_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_162_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_162_fallthrough`. -/
def feWETH9_block_162_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 162. -/
theorem feWETH9_block_162_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) (feWETH9_block_162_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 168)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_162_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) (feWETH9_block_162_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_162_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 168. -/
theorem feWETH9_block_168_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_168_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_168_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 168. -/
theorem feWETH9_block_168_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 180)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_168_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 168) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_168_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_180_taken`. -/
def feWETH9_block_180_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 180. -/
theorem feWETH9_block_180_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_180_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_180_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_180_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_180_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_180_fallthrough`. -/
def feWETH9_block_180_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 180. -/
theorem feWETH9_block_180_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 190) (feWETH9_block_180_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 190)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_180_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 190) (feWETH9_block_180_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_180_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 190. -/
theorem feWETH9_block_190 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 190) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.WETH9.feWETH9Bytecode g s0 (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (((UInt256.ofNat 1).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.caller (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r20 := r19.calldataload (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sstore r22 hperm (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.pushConst (UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := RD.genLog3 r28 (by native_decide) hperm (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push0 (by native_decide) (by evm_ov)
  have r32 := RD.genMstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r34 := r33.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r34 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 272. -/
theorem feWETH9_block_272_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_272_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_272_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 272. -/
theorem feWETH9_block_272_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 277) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 277)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_272_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 272) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 277) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_272_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 277: unsupported_47 (0x47). No RD transition is asserted. Summaries resume at pc 278 from a fresh symbolic RD state. -/

/-- Static-mode twin of `feWETH9_block_190`: its steps up to the state change, which halts when
    `ee.perm = false`. -/
theorem feWETH9_block_190_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 190) (x0 :: R) mem aw rdata σ k C)
    : RDstatic FeProofs.WETH9.feWETH9Bytecode g s0 := by
  let r0 := h
  have r1 := r0.caller (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r20 := r19.calldataload (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r22 hperm (by native_decide) (by evm_ov)

end feWETH9Blocks
