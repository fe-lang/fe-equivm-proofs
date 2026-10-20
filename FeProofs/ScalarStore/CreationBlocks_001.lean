import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.ScalarStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feScalarStoreCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.ScalarStore.feScalarStoreCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.ScalarStore.feScalarStoreCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feScalarStoreCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ScalarStore.feScalarStoreCreationBytecode 0).contains (UInt256.ofNat 9) = true)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ (k + 4) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 9) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feScalarStoreCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5) R mem aw rdata σ (k + 4) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 5. -/
theorem feScalarStoreCreation_block_5 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5) R mem aw rdata σ k C)
    : RDrev (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_9_fallthrough`. -/
def feScalarStoreCreation_block_9_fallthrough_stack {tail : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).size) :: (UInt256.ofNat 140) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9. -/
theorem feScalarStoreCreation_block_9_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).size) (UInt256.ofNat 140)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19) (feScalarStoreCreation_block_9_fallthrough_stack (tail := tail) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 140) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.codesize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_19_fallthrough`. -/
def feScalarStoreCreation_block_19_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 x1) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 19. -/
theorem feScalarStoreCreation_block_19_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 95)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 32) (feScalarStoreCreation_block_19_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((37) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 95) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 35) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 32)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_32`. -/
def feScalarStoreCreation_block_32_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 32. -/
theorem feScalarStoreCreation_block_32 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 32) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 35) (feScalarStoreCreation_block_32_stack (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 35)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_35_fallthrough`. -/
def feScalarStoreCreation_block_35_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Final memory for bytecode block summary `feScalarStoreCreation_block_35_fallthrough`. -/
def feScalarStoreCreation_block_35_fallthrough_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).write x2.toNat mem x0.toNat x1.toNat)

/-- Automatically generated RD summary for bytecode block at pc 35. -/
theorem feScalarStoreCreation_block_35_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) x1) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 35) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 47) (feScalarStoreCreation_block_35_fallthrough_stack (x0 := x0) (R := R)) (feScalarStoreCreation_block_35_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw x0 x1) rdata σ (k + 10) (C + ((32) + (memExpansionCost aw x0 x1) + (3 + 3 * ((x1.toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genCodecopy r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 47)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 47. -/
theorem feScalarStoreCreation_block_47 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (memLoad x0 mem)) (((FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).write (UInt256.ofNat 60).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 80).toNat).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 80).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 140 := by native_decide
  have r1 := RD.genMload r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 60) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 80) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genCodecopy r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end feScalarStoreCreationBlocks
