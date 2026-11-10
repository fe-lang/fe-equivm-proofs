import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.NarrowAbi.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feNarrowAbiCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.NarrowAbi.feNarrowAbiCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.NarrowAbi.feNarrowAbiCreationBytecode

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_201_taken`. -/
def feNarrowAbiCreation_block_201_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 201. -/
theorem feNarrowAbiCreation_block_201_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_201_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_201_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_201_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_201_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_201_fallthrough`. -/
def feNarrowAbiCreation_block_201_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 201. -/
theorem feNarrowAbiCreation_block_201_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 208) (feNarrowAbiCreation_block_201_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 208)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_201_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 208) (feNarrowAbiCreation_block_201_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_201_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_208`. -/
def feNarrowAbiCreation_block_208_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 208. -/
theorem feNarrowAbiCreation_block_208 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 197) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 208) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 197) (feNarrowAbiCreation_block_208_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 197) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 197) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 197)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_208_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 197) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 208) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 197) (feNarrowAbiCreation_block_208_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_208 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_213`. -/
def feNarrowAbiCreation_block_213_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 213. -/
theorem feNarrowAbiCreation_block_213 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 213) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 216) (feNarrowAbiCreation_block_213_stack (R := R)) mem aw rdata σ (k + 3) (C + ((5))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 216)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_213_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 213) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 216) (feNarrowAbiCreation_block_213_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_213 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 216. -/
theorem feNarrowAbiCreation_block_216 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 216) (x0 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) g s0 σ ((x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_223_taken`. -/
def feNarrowAbiCreation_block_223_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 223. -/
theorem feNarrowAbiCreation_block_223_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 223) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_223_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_223_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 223) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_223_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_223_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_223_fallthrough`. -/
def feNarrowAbiCreation_block_223_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 223. -/
theorem feNarrowAbiCreation_block_223_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 223) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) (feNarrowAbiCreation_block_223_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 229)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_223_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 223) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) (feNarrowAbiCreation_block_223_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_223_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 229. -/
theorem feNarrowAbiCreation_block_229_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_229_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_229_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 229. -/
theorem feNarrowAbiCreation_block_229_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 241)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_229_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 229) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_229_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_241_taken`. -/
def feNarrowAbiCreation_block_241_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 241. -/
theorem feNarrowAbiCreation_block_241_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_241_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_241_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_241_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_241_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_241_fallthrough`. -/
def feNarrowAbiCreation_block_241_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 241. -/
theorem feNarrowAbiCreation_block_241_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 251) (feNarrowAbiCreation_block_241_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 251)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_241_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 241) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 251) (feNarrowAbiCreation_block_241_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_241_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 251. -/
theorem feNarrowAbiCreation_block_251 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) g s0 σ ((x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end feNarrowAbiCreationBlocks
