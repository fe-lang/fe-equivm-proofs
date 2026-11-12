import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.CodeScalar.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feCodeScalarCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.CodeScalar.feCodeScalarCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.CodeScalar.feCodeScalarCreationBytecode

/- Shared branch prefix at pc 0. -/
private def feCodeScalarCreation_block_0_shared {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162)
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact r6

/-- Final memory for bytecode block summary `feCodeScalarCreation_block_0_taken`. -/
def feCodeScalarCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feCodeScalarCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.CodeScalar.feCodeScalarCreationBytecode 0).contains (UInt256.ofNat 14) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) R (feCodeScalarCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r6 := feCodeScalarCreation_block_0_shared hstack hcreationCodeSize h
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final memory for bytecode block summary `feCodeScalarCreation_block_0_fallthrough`. -/
def feCodeScalarCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feCodeScalarCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) R (feCodeScalarCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r6 := feCodeScalarCreation_block_0_shared hstack hcreationCodeSize h
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 10. -/
theorem feCodeScalarCreation_block_10 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) R mem aw rdata σ k C)
    : RDrev (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feCodeScalarCreation_block_14_fallthrough`. -/
def feCodeScalarCreation_block_14_fallthrough_stack {tail : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail).size) :: (UInt256.ofNat 162) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14. -/
theorem feCodeScalarCreation_block_14_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail).size) (UInt256.ofNat 162)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 24) (feCodeScalarCreation_block_14_fallthrough_stack (tail := tail) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 162) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.codesize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 10) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feCodeScalarCreation_block_24_fallthrough`. -/
def feCodeScalarCreation_block_24_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `feCodeScalarCreation_block_24_fallthrough`. -/
def feCodeScalarCreation_block_24_fallthrough_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail).write x1.toNat mem (UInt256.ofNat 96).toNat (UInt256.sub x0 x1).toNat)

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feCodeScalarCreation_block_24_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x0 x1)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 24) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 38) (feCodeScalarCreation_block_24_fallthrough_stack (R := R)) (feCodeScalarCreation_block_24_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 96) (UInt256.sub x0 x1)) rdata σ (k + 11) (C + ((37) + (memExpansionCost aw (UInt256.ofNat 96) (UInt256.sub x0 x1)) + (3 + 3 * (((UInt256.sub x0 x1).toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
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

/-- Final stack for bytecode block summary `feCodeScalarCreation_block_38_taken`. -/
def feCodeScalarCreation_block_38_taken_stack {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 55) + (UInt256.ofNat 32)) :: (UInt256.ofNat 55) :: (UInt256.ofNat 107) :: R)

/-- Final memory for bytecode block summary `feCodeScalarCreation_block_38_taken`. -/
def feCodeScalarCreation_block_38_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 38. -/
theorem feCodeScalarCreation_block_38_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((UInt256.ofNat 55) + (UInt256.ofNat 32)) (UInt256.ofNat 55))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.CodeScalar.feCodeScalarCreationBytecode 0).contains (UInt256.ofNat 87) = true)
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 38) R mem aw rdata σ k C)
    : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 87) (feCodeScalarCreation_block_38_taken_stack (R := R)) (feCodeScalarCreation_block_38_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((69) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 107) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 55) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 87) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 87) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 87)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 87. -/
theorem feCodeScalarCreation_block_87 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 87) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail) g s0 σ ((((FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail).write x2.toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x1.toNat).write (UInt256.ofNat 96).toNat ((FeProofs.CodeScalar.feCodeScalarCreationBytecode ++ tail).write x2.toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x1.toNat) ((memLoad (UInt256.ofNat 64) mem) + x1).toNat (UInt256.ofNat 32).toNat).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat x0.toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.CodeScalar.feCodeScalarCreationBytecode.size = 162 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genCodecopy r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMcopy r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end feCodeScalarCreationBlocks
