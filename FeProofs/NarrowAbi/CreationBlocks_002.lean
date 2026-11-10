import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.NarrowAbi.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feNarrowAbiCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.NarrowAbi.feNarrowAbiCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.NarrowAbi.feNarrowAbiCreationBytecode

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_93_fallthrough`. -/
def feNarrowAbiCreation_block_93_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 93. -/
theorem feNarrowAbiCreation_block_93_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) (UInt256.ofNat 128))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (feNarrowAbiCreation_block_93_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 102) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 108)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_93_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) (UInt256.ofNat 128))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (feNarrowAbiCreation_block_93_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_93_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_108_taken`. -/
def feNarrowAbiCreation_block_108_taken_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 108. -/
theorem feNarrowAbiCreation_block_108_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 109) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 109) (feNarrowAbiCreation_block_108_taken_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 109) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 109) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 109)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_108_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 109) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 109) (feNarrowAbiCreation_block_108_taken_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_108_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_108_fallthrough`. -/
def feNarrowAbiCreation_block_108_fallthrough_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 108. -/
theorem feNarrowAbiCreation_block_108_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 117) (feNarrowAbiCreation_block_108_fallthrough_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 109) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 117)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_108_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 108) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 117) (feNarrowAbiCreation_block_108_fallthrough_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_108_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 117. -/
theorem feNarrowAbiCreation_block_117 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 117) R mem aw rdata σ k C)
    : RDrev (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_121_taken`. -/
def feNarrowAbiCreation_block_121_taken_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 121. -/
theorem feNarrowAbiCreation_block_121_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 121) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_121_taken_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_121_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 121) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_121_taken_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_121_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_121_fallthrough`. -/
def feNarrowAbiCreation_block_121_fallthrough_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 121. -/
theorem feNarrowAbiCreation_block_121_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 121) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 128) (feNarrowAbiCreation_block_121_fallthrough_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 128)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_121_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 x0)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 121) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 128) (feNarrowAbiCreation_block_121_fallthrough_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_121_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 128. -/
theorem feNarrowAbiCreation_block_128 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 128) (x0 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) g s0 σ (((UInt256.sar (UInt256.ofNat 248) (UInt256.shiftLeft x0 (UInt256.ofNat 248))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 248) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 248) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.sar (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_141_taken`. -/
def feNarrowAbiCreation_block_141_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 141. -/
theorem feNarrowAbiCreation_block_141_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_141_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
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
theorem feNarrowAbiCreation_block_141_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_141_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_141_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_141_fallthrough`. -/
def feNarrowAbiCreation_block_141_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 141. -/
theorem feNarrowAbiCreation_block_141_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) (feNarrowAbiCreation_block_141_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 147)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_141_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) (feNarrowAbiCreation_block_141_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_141_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 147. -/
theorem feNarrowAbiCreation_block_147_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
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
theorem feNarrowAbiCreation_block_147_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_147_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 147. -/
theorem feNarrowAbiCreation_block_147_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw rdata σ (k + 9) (C + ((33))) := by
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 159)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_147_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 147) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_147_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_159_taken`. -/
def feNarrowAbiCreation_block_159_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 159. -/
theorem feNarrowAbiCreation_block_159_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_159_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 98) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_159_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_159_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_159_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_159_fallthrough`. -/
def feNarrowAbiCreation_block_159_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 159. -/
theorem feNarrowAbiCreation_block_159_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 169) (feNarrowAbiCreation_block_159_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 169)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_159_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 169) (feNarrowAbiCreation_block_159_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_159_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 169. -/
theorem feNarrowAbiCreation_block_169 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 169) (x0 :: R) mem aw rdata σ k C)
    : RDret (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) g s0 σ ((x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_175_taken`. -/
def feNarrowAbiCreation_block_175_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 175. -/
theorem feNarrowAbiCreation_block_175_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 175) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_175_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
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
theorem feNarrowAbiCreation_block_175_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 175) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (feNarrowAbiCreation_block_175_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_175_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_175_fallthrough`. -/
def feNarrowAbiCreation_block_175_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 175. -/
theorem feNarrowAbiCreation_block_175_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 175) (x0 :: R) mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) (feNarrowAbiCreation_block_175_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 181)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_175_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 175) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) (feNarrowAbiCreation_block_175_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_175_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 181. -/
theorem feNarrowAbiCreation_block_181_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
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
theorem feNarrowAbiCreation_block_181_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 98) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_181_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 181. -/
theorem feNarrowAbiCreation_block_181_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw rdata σ (k + 9) (C + ((33))) := by
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 193)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_181_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_181_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_193_taken`. -/
def feNarrowAbiCreation_block_193_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 193. -/
theorem feNarrowAbiCreation_block_193_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 194) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 194) (feNarrowAbiCreation_block_193_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 194) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 194) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 194)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_193_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiCreationBytecode 0).contains (UInt256.ofNat 194) = true)
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 194) (feNarrowAbiCreation_block_193_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_193_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feNarrowAbiCreation_block_193_fallthrough`. -/
def feNarrowAbiCreation_block_193_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 193. -/
theorem feNarrowAbiCreation_block_193_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (feNarrowAbiCreation_block_193_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.NarrowAbi.feNarrowAbiCreationBytecode.size = 257 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 194) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 201)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feNarrowAbiCreation_block_193_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.NarrowAbi.feNarrowAbiCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 201) (feNarrowAbiCreation_block_193_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feNarrowAbiCreation_block_193_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end feNarrowAbiCreationBlocks
