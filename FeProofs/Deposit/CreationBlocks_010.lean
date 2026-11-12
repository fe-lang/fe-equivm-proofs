import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.Deposit.feDepositCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.Deposit.feDepositCreationBytecode

/-- Final stack for bytecode block summary `feDepositCreation_block_2197_fallthrough`. -/
def feDepositCreation_block_2197_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2197. -/
theorem feDepositCreation_block_2197_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2197) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (feDepositCreation_block_2197_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2204)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2197_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2197) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (feDepositCreation_block_2197_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2197_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2204. -/
theorem feDepositCreation_block_2204_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2199) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551552) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2199) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2204_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2199) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2204_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2204. -/
theorem feDepositCreation_block_2204_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551552) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2219)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2204_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2204) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2204_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDepositCreation_block_2219_taken`. -/
def feDepositCreation_block_2219_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x1) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `feDepositCreation_block_2219_taken`. -/
def feDepositCreation_block_2219_taken_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) ((UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2219. -/
theorem feDepositCreation_block_2219_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2187) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2187) (feDepositCreation_block_2219_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (feDepositCreation_block_2219_taken_memory (mem := mem) (x1 := x1)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((97) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 63) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 2187) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2187) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2187)) r30 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2219_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2187) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2187) (feDepositCreation_block_2219_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (feDepositCreation_block_2219_taken_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2219_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDepositCreation_block_2219_fallthrough`. -/
def feDepositCreation_block_2219_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x1) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `feDepositCreation_block_2219_fallthrough`. -/
def feDepositCreation_block_2219_fallthrough_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) ((UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2219. -/
theorem feDepositCreation_block_2219_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2260) (feDepositCreation_block_2219_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (feDepositCreation_block_2219_fallthrough_memory (mem := mem) (x1 := x1)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((97) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 63) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 2187) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2260)) r30 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2219_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2219) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2260) (feDepositCreation_block_2219_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (feDepositCreation_block_2219_fallthrough_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2219_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDepositCreation_block_2260`. -/
def feDepositCreation_block_2260_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 17) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2260. -/
theorem feDepositCreation_block_2260 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2243) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2260) R mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2243) (feDepositCreation_block_2260_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 17) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2243) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2243) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2243)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2260_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains (UInt256.ofNat 2243) = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2260) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2243) (feDepositCreation_block_2260_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2260 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDepositCreation_block_2267`. -/
def feDepositCreation_block_2267_stack {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x5 :: x3 :: R)

/-- Final memory for bytecode block summary `feDepositCreation_block_2267`. -/
def feDepositCreation_block_2267_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} : ByteArray :=
  (ee.calldata.write x4.toNat ((⟨0⟩ : UInt256).toByteArray.write 0 mem (x2 + x0).toNat 32) x2.toNat x1.toNat)

/-- Automatically generated RD summary for bytecode block at pc 2267. -/
theorem feDepositCreation_block_2267 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains x6 = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2267) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 x6 (feDepositCreation_block_2267_stack (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feDepositCreation_block_2267_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) (M (M aw (x2 + x0) (⟨32⟩ : UInt256)) x2 x1) rdata σ (k + 12) (C + ((35) + (memExpansionCost aw (x2 + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + x0) (⟨32⟩ : UInt256)) x2 x1) + (3 + 3 * ((x1.toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genCalldatacopy r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x6 hvalid) (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDepositCreation_block_2267_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositCreationBytecode 0).contains x6 = true)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2267) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 x6 (feDepositCreation_block_2267_stack (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feDepositCreation_block_2267_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDepositCreation_block_2267 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2279. -/
theorem feDepositCreation_block_2279 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2279) R mem aw rdata σ k C)
    : RDrev (FeProofs.Deposit.feDepositCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 2283. -/
theorem feDepositCreation_block_2283 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2283) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDrev (FeProofs.Deposit.feDepositCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 288) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 320) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := RD.genMstore r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 352) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMstore r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 384) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 132) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r20 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 2323. -/
theorem feDepositCreation_block_2323 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (FeProofs.Deposit.feDepositCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2323) (x0 :: R) mem aw rdata σ k C)
    : RDrev (FeProofs.Deposit.feDepositCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : FeProofs.Deposit.feDepositCreationBytecode.size = 2341 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1313373041) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end feDepositCreationBlocks
