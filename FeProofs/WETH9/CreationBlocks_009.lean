import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.WETH9.feWETH9CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.WETH9.feWETH9CreationBytecode

/-- Final stack for bytecode block summary `feWETH9Creation_block_1308_fallthrough`. -/
def feWETH9Creation_block_1308_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1308. -/
theorem feWETH9Creation_block_1308_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1308) R mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1320) (feWETH9Creation_block_1308_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 223) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 853) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1320)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1308_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1308) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1320) (feWETH9Creation_block_1308_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1308_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1320`. -/
def feWETH9Creation_block_1320_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 224) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1320. -/
theorem feWETH9Creation_block_1320 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1320) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (feWETH9Creation_block_1320_stack (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1323)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1320_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1320) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (feWETH9Creation_block_1320_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1320 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9Creation_block_1323_taken`. -/
def feWETH9Creation_block_1323_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1323. -/
theorem feWETH9Creation_block_1323_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 945) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 945) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9Creation_block_1323_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 945) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 945) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 945)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1323_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 945) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 945) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9Creation_block_1323_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1323_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9Creation_block_1323_fallthrough`. -/
def feWETH9Creation_block_1323_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1323. -/
theorem feWETH9Creation_block_1323_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9Creation_block_1323_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 945) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1348)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1323_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1323) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9Creation_block_1323_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1323_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1348. -/
theorem feWETH9Creation_block_1348_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 934) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 934) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 934) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 934) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 934)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1348_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 934) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 934) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1348_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1348. -/
theorem feWETH9Creation_block_1348_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 934) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1354)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1348_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1348) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1348_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1354. -/
theorem feWETH9Creation_block_1354_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1354_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1354_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1354. -/
theorem feWETH9Creation_block_1354_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1363)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1354_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1354) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1354_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1363`. -/
def feWETH9Creation_block_1363_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x4 (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3))))) :: x1 :: x3 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1363. -/
theorem feWETH9Creation_block_1363 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 924) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 924) (feWETH9Creation_block_1363_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 21) (C + ((65))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 924) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 924) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 924)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1363_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 924) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 924) (feWETH9Creation_block_1363_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1363 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1387`. -/
def feWETH9Creation_block_1387_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x1 :: x3 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1387. -/
theorem feWETH9Creation_block_1387 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1387) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1394) (feWETH9Creation_block_1387_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 7) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1394)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1387_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1387) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1394) (feWETH9Creation_block_1387_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1387 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1394`. -/
def feWETH9Creation_block_1394_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `feWETH9Creation_block_1394`. -/
def feWETH9Creation_block_1394_memory {mem : ByteArray} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1394. -/
theorem feWETH9Creation_block_1394 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1394) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 975) (feWETH9Creation_block_1394_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feWETH9Creation_block_1394_memory (mem := mem) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 975) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 975)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1394_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1394) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 975) (feWETH9Creation_block_1394_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feWETH9Creation_block_1394_memory (mem := mem) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1394 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1404`. -/
def feWETH9Creation_block_1404_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x3 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1404. -/
theorem feWETH9Creation_block_1404 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1404) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 975) (feWETH9Creation_block_1404_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw rdata σ (k + 9) (C + ((27))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 975) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 975)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1404_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 975) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1404) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 975) (feWETH9Creation_block_1404_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1404 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1415`. -/
def feWETH9Creation_block_1415_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 32) (x5.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)) :: x1 :: x2 :: x3 :: x0 :: R)

/-- Final memory for bytecode block summary `feWETH9Creation_block_1415`. -/
def feWETH9Creation_block_1415_memory {mem : ByteArray} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1415. -/
theorem feWETH9Creation_block_1415 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (feWETH9Creation_block_1415_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feWETH9Creation_block_1415_memory (mem := mem) (x5 := x5)) (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) rdata σ (k + 15) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) + (30 + 6 * (((UInt256.ofNat 32).toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genKeccak256 r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1433)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1415_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (feWETH9Creation_block_1415_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feWETH9Creation_block_1415_memory (mem := mem) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1415 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1433. -/
theorem feWETH9Creation_block_1433_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 985) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 985) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 985) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 985) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 985)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1433_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 985) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 985) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1433_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1433. -/
theorem feWETH9Creation_block_1433_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1441) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 985) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1441)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1433_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1433) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1441) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1433_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1441`. -/
def feWETH9Creation_block_1441_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1441. -/
theorem feWETH9Creation_block_1441 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1441) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (feWETH9Creation_block_1441_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((9))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1445)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1441_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1441) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (feWETH9Creation_block_1441_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1441 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1445. -/
theorem feWETH9Creation_block_1445_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1039) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1039) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1039) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1039) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1039)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1445_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1039) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1039) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1445_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1445. -/
theorem feWETH9Creation_block_1445_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1451) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1039) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1451)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1445_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1445) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1451) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1445_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1451. -/
theorem feWETH9Creation_block_1451 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1080) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1451) R mem aw rdata σ k C)
    : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1080) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 1080) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 1080) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1080)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1451_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1080) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1451) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1080) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9Creation_block_1451 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9Creation_block_1455_taken`. -/
def feWETH9Creation_block_1455_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + x0) (⟨0⟩ : UInt256))) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1455. -/
theorem feWETH9Creation_block_1455_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1021) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1455) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1021) (feWETH9Creation_block_1455_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : FeProofs.WETH9.feWETH9CreationBytecode.size = 2060 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1021) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1021) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1021)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9Creation_block_1455_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub x4 (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9CreationBytecode 0).contains (UInt256.ofNat 1021) = true)
    (h : RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1455) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.WETH9.feWETH9CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1021) (feWETH9Creation_block_1455_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9Creation_block_1455_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end feWETH9CreationBlocks
