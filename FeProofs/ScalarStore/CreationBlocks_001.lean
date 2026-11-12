import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.ScalarStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feScalarStoreCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.ScalarStore.feScalarStoreCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.ScalarStore.feScalarStoreCreationBytecode

/- Shared branch prefix at pc 0. -/
private def feScalarStoreCreation_block_0_shared {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact r6

/-- Final memory for bytecode block summary `feScalarStoreCreation_block_0_taken`. -/
def feScalarStoreCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feScalarStoreCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ScalarStore.feScalarStoreCreationBytecode 0).contains (UInt256.ofNat 14) = true)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) R (feScalarStoreCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r6 := feScalarStoreCreation_block_0_shared hstack hcreationCodeSize h
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final memory for bytecode block summary `feScalarStoreCreation_block_0_fallthrough`. -/
def feScalarStoreCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feScalarStoreCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) R (feScalarStoreCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r6 := feScalarStoreCreation_block_0_shared hstack hcreationCodeSize h
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 10. -/
theorem feScalarStoreCreation_block_10 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) R mem aw rdata σ k C)
    : RDrev (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_14_fallthrough`. -/
def feScalarStoreCreation_block_14_fallthrough_stack {tail : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).size) :: (UInt256.ofNat 133) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14. -/
theorem feScalarStoreCreation_block_14_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).size) (UInt256.ofNat 133)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) R mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 24) (feScalarStoreCreation_block_14_fallthrough_stack (tail := tail) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 133) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.codesize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 10) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feScalarStoreCreation_block_24_fallthrough`. -/
def feScalarStoreCreation_block_24_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `feScalarStoreCreation_block_24_fallthrough`. -/
def feScalarStoreCreation_block_24_fallthrough_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).write x1.toNat mem (UInt256.ofNat 96).toNat (UInt256.sub x0 x1).toNat)

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feScalarStoreCreation_block_24_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x0 x1)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 24) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 38) (feScalarStoreCreation_block_24_fallthrough_stack (R := R)) (feScalarStoreCreation_block_24_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 96) (UInt256.sub x0 x1)) rdata σ (k + 11) (C + ((37) + (memExpansionCost aw (UInt256.ofNat 96) (UInt256.sub x0 x1)) + (3 + 3 * (((UInt256.sub x0 x1).toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r1 := r0.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 10) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 38)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 38. -/
theorem feScalarStoreCreation_block_38 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 38) R mem aw rdata σ k C)
    : RDret (FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (memLoad (UInt256.ofNat 96) mem)) (((FeProofs.ScalarStore.feScalarStoreCreationBytecode ++ tail).write (UInt256.ofNat 53).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 80).toNat).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 80).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.ScalarStore.feScalarStoreCreationBytecode.size = 133 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 53) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 80) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genCodecopy r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end feScalarStoreCreationBlocks
