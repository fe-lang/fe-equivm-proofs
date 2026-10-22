import Reasoning.Reach
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9Blocks

/-- Final stack for bytecode block summary `feWETH9_block_924`. -/
def feWETH9_block_924_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `feWETH9_block_924`. -/
def feWETH9_block_924_memory {mem : ByteArray} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 924. -/
theorem feWETH9_block_924 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 924) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 975) (feWETH9_block_924_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feWETH9_block_924_memory (mem := mem) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 975) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 975)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_934`. -/
def feWETH9_block_934_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x3 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 934. -/
theorem feWETH9_block_934 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 934) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 975) (feWETH9_block_934_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw rdata σ (k + 9) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 975) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 975)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_945`. -/
def feWETH9_block_945_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 32) (x5.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)) :: x1 :: x2 :: x3 :: x0 :: R)

/-- Final memory for bytecode block summary `feWETH9_block_945`. -/
def feWETH9_block_945_memory {mem : ByteArray} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 945. -/
theorem feWETH9_block_945 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 945) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 963) (feWETH9_block_945_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feWETH9_block_945_memory (mem := mem) (x5 := x5)) (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) rdata σ (k + 15) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) + (30 + 6 * (((UInt256.ofNat 32).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := RD.genKeccak256 r6 (by native_decide) (by evm_ov)
  have r8 := r7.swap4 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := r10.swap4 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.swap3 (by native_decide) (by evm_ov)
  have r15 := r14.swap4 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 963)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 963. -/
theorem feWETH9_block_963_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 985) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 963) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 985) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 985) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 985)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 963. -/
theorem feWETH9_block_963_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 963) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 971) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 985) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 971)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_971`. -/
def feWETH9_block_971_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 971. -/
theorem feWETH9_block_971 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 971) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 975) (feWETH9_block_971_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((9))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 975)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 975. -/
theorem feWETH9_block_975_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1039) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 975) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1039) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1039) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1039)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 975. -/
theorem feWETH9_block_975_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 975) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 981) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1039) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 981)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 981. -/
theorem feWETH9_block_981 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1080) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 981) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1080) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1080) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1080)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_985_taken`. -/
def feWETH9_block_985_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + x0) (⟨0⟩ : UInt256))) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 985. -/
theorem feWETH9_block_985_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1021) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 985) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1021) (feWETH9_block_985_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup1 (by native_decide) (by evm_ov)
  have r10 := r9.dup8 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.lt (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1021) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1021)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Final stack for bytecode block summary `feWETH9_block_985_fallthrough`. -/
def feWETH9_block_985_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + x0) (⟨0⟩ : UInt256))) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 985. -/
theorem feWETH9_block_985_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 985) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1006) (feWETH9_block_985_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup1 (by native_decide) (by evm_ov)
  have r10 := r9.dup8 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.lt (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1021) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1006)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Final stack for bytecode block summary `feWETH9_block_1006`. -/
def feWETH9_block_1006_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x2 (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x0 (UInt256.ofNat 3))))) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1006. -/
theorem feWETH9_block_1006 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1024) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1006) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1024) (feWETH9_block_1006_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r2 := r1.shl (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.not (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1024) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1024)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_1021`. -/
def feWETH9_block_1021_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1021. -/
theorem feWETH9_block_1021 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1024) (feWETH9_block_1021_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 3) (C + ((6))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1024)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_1024`. -/
def feWETH9_block_1024_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `feWETH9_block_1024`. -/
def feWETH9_block_1024_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x7 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x7 + ((UInt256.ofNat 32) + x1)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1024. -/
theorem feWETH9_block_1024 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 963) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1024) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 963) (feWETH9_block_1024_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (feWETH9_block_1024_memory (mem := mem) (x0 := x0) (x1 := x1) (x7 := x7)) (M aw (x7 + ((UInt256.ofNat 32) + x1)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (x7 + ((UInt256.ofNat 32) + x1)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 963) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 963)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_1039_fallthrough`. -/
def feWETH9_block_1039_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.shiftRight (UInt256.sub x1 (UInt256.ofNat 1)) (UInt256.ofNat 5)) + (UInt256.ofNat 1)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1039. -/
theorem feWETH9_block_1039_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt ((UInt256.shiftRight (UInt256.sub x1 (UInt256.ofNat 1)) (UInt256.ofNat 5)) + (UInt256.ofNat 1)) (UInt256.shiftRight (UInt256.sub x1 (UInt256.ofNat 1)) (UInt256.ofNat 5))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1039) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1058) (feWETH9_block_1039_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.lt (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 1073) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1058)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feWETH9_block_1058_taken`. -/
def feWETH9_block_1058_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1058. -/
theorem feWETH9_block_1058_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.shiftRight (UInt256.shiftLeft x0 (UInt256.ofNat 5)) (UInt256.ofNat 5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1082) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1058) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1082) (feWETH9_block_1058_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.eq (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1082) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1082)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

end feWETH9Blocks
