import Reasoning.Reach
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositBlocks

/-- Final stack for bytecode block summary `feDeposit_block_698_fallthrough`. -/
def feDeposit_block_698_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 698. -/
theorem feDeposit_block_698_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 698) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) (feDeposit_block_698_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 705)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_698_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 698) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) (feDeposit_block_698_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_698_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 705. -/
theorem feDeposit_block_705_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_705_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_705_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 705. -/
theorem feDeposit_block_705_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 715) R mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 715)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_705_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 705) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 715) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_705_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_715`. -/
def feDeposit_block_715_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((160) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (x5 + (UInt256.ofNat 32)) :: (UInt256.ofNat 64) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 32) :: (x5 + (UInt256.ofNat 32)) :: ((g.subNat (C + ((160) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft (UInt256.lor (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32)) (UInt256.shiftLeft (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32))) (UInt256.ofNat 192)) :: (memLoad x0 mem) :: (memLoad (x7 + (UInt256.ofNat 32)) mem) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_715`. -/
def feDeposit_block_715_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 715. -/
theorem feDeposit_block_715 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 715) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 821) (feDeposit_block_715_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (feDeposit_block_715_memory (mem := mem)) (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((189) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup9 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 71777214294589695) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r13 := r12.shr (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 71777214294589695) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 281470681808895) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r23 := r22.shl (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r26 := r25.shr (by native_decide) (by evm_ov)
  have r27 := r26.pushConst (UInt256.ofNat 281470681808895) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.or (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r35 := r34.shr (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r38 := r37.shl (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r45 := RD.genMstore r44 (by native_decide) (by evm_ov)
  have r46 := r45.push0 (by native_decide) (by evm_ov)
  have r47 := r46.dup2 (by native_decide) (by evm_ov)
  have r48 := RD.genMstore r47 (by native_decide) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r50 := r49.dup2 (by native_decide) (by evm_ov)
  have r51 := r50.add (by native_decide) (by evm_ov)
  have r52 := r51.push0 (by native_decide) (by evm_ov)
  have r53 := r52.dup2 (by native_decide) (by evm_ov)
  have r54 := RD.genMstore r53 (by native_decide) (by evm_ov)
  have r55 := RD.genGas (RD.normalizeCounters (k' := k + 54) (C' := C + ((160) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) r54 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r57 := r56.dup11 (by native_decide) (by evm_ov)
  have r58 := r57.add (by native_decide) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r60 := r59.dup5 (by native_decide) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r62 := r61.dup4 (by native_decide) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r64 := r63.dup7 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 821)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_715_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 715) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 821) (feDeposit_block_715_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (feDeposit_block_715_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_715 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 821: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 822 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_822_taken`. -/
def feDeposit_block_822_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 822. -/
theorem feDeposit_block_822_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_822_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_822_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_822_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_822_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_822_fallthrough`. -/
def feDeposit_block_822_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 822. -/
theorem feDeposit_block_822_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (feDeposit_block_822_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 827)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_822_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (feDeposit_block_822_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_822_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_827_taken`. -/
def feDeposit_block_827_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 827. -/
theorem feDeposit_block_827_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_827_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.returndatasize (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.lt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_827_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_827_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_827_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_827_fallthrough`. -/
def feDeposit_block_827_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 827. -/
theorem feDeposit_block_827_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 838) (feDeposit_block_827_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.returndatasize (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.lt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 838)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_827_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 838) (feDeposit_block_827_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_838`. -/
def feDeposit_block_838_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((24) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: x2 :: (UInt256.ofNat 64) :: x2 :: (UInt256.ofNat 32) :: ((g.subNat (C + ((24) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad x2 mem) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_838`. -/
def feDeposit_block_838_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 64) + x0) mem).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 838. -/
theorem feDeposit_block_838 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 838) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 857) (feDeposit_block_838_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_838_memory (mem := mem) (x0 := x0) (x2 := x2)) (M (M (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((44) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := RD.genGas (RD.normalizeCounters (k' := k + 8) (C' := C + ((24) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)))) r8 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 857)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_838_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 838) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 857) (feDeposit_block_838_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_838_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_838 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 857: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 858 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_858_taken`. -/
def feDeposit_block_858_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 858. -/
theorem feDeposit_block_858_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 858) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_858_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_858_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 858) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_858_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_858_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_858_fallthrough`. -/
def feDeposit_block_858_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 858. -/
theorem feDeposit_block_858_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 858) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) (feDeposit_block_858_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 865)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_858_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 858) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) (feDeposit_block_858_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_858_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 865. -/
theorem feDeposit_block_865_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_865_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_865_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 865. -/
theorem feDeposit_block_865_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 874) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 874)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_865_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 865) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 874) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_865_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_874`. -/
def feDeposit_block_874_stack {g : Sat256} {aw : UInt256} {C : ℕ} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((21) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: x2 :: (UInt256.ofNat 64) :: x2 :: (UInt256.ofNat 32) :: ((g.subNat (C + ((21) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x2 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_874`. -/
def feDeposit_block_874_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((memLoad x2 mem).toByteArray.write 0 (x0.toByteArray.write 0 mem x2.toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 874. -/
theorem feDeposit_block_874 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 874) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 891) (feDeposit_block_874_stack (g := g) (aw := aw) (C := C) (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_874_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((41) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := RD.genGas (RD.normalizeCounters (k' := k + 7) (C' := C + ((21) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) r7 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r14 := r13.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 891)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_874_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 874) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 891) (feDeposit_block_874_stack (g := g) (aw := aw) (C := C) (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_874_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_874 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 891: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 892 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_892_taken`. -/
def feDeposit_block_892_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 892. -/
theorem feDeposit_block_892_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 892) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_892_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_892_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 892) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_892_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_892_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_892_fallthrough`. -/
def feDeposit_block_892_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 892. -/
theorem feDeposit_block_892_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 892) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) (feDeposit_block_892_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 899)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_892_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 892) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) (feDeposit_block_892_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_892_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 899. -/
theorem feDeposit_block_899_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_899_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_899_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 899. -/
theorem feDeposit_block_899_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 908) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 908)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_899_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 908) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_899_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_908`. -/
def feDeposit_block_908_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((51) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 64) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((51) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad x0 mem) :: x1 :: (memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `feDeposit_block_908`. -/
def feDeposit_block_908_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x2.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 908. -/
theorem feDeposit_block_908 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 908) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 939) (feDeposit_block_908_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (R := R)) (feDeposit_block_908_memory (mem := mem) (x2 := x2) (x3 := x3)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((71) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.swap3 (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.swap4 (by native_decide) (by evm_ov)
  have r16 := r15.dup5 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := RD.genGas (RD.normalizeCounters (k' := k + 17) (C' := C + ((51) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) r17 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := r19.dup5 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r24 := r23.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 939)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_908_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 908) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 939) (feDeposit_block_908_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (R := R)) (feDeposit_block_908_memory (mem := mem) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_908 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 939: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 940 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_940_taken`. -/
def feDeposit_block_940_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 940. -/
theorem feDeposit_block_940_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 940) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_940_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_940_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 940) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_940_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_940_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end feDepositBlocks
