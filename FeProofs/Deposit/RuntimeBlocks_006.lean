import Reasoning.Reach
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositBlocks

/-- Final stack for bytecode block summary `feDeposit_block_1338_taken`. -/
def feDeposit_block_1338_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1338_taken`. -/
def feDeposit_block_1338_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x0.toNat)

/-- Automatically generated RD summary for bytecode block at pc 1338. -/
theorem feDeposit_block_1338_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.ofNat 160) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1363) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1338) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (feDeposit_block_1338_taken_stack (mem := mem) (x0 := x0) (R := R)) (feDeposit_block_1338_taken_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x0) rdata σ (k + 14) (C + ((43) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x0) + (3 + 3 * ((x0.toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := RD.genCalldatacopy r7 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 1363) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1363)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1338_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.ofNat 160) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1363) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1338) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (feDeposit_block_1338_taken_stack (mem := mem) (x0 := x0) (R := R)) (feDeposit_block_1338_taken_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1338_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1338_fallthrough`. -/
def feDeposit_block_1338_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1338_fallthrough`. -/
def feDeposit_block_1338_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x0.toNat)

/-- Automatically generated RD summary for bytecode block at pc 1338. -/
theorem feDeposit_block_1338_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.ofNat 160) x0)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1338) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1338_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (feDeposit_block_1338_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x0) rdata σ (k + 14) (C + ((43) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x0) + (3 + 3 * ((x0.toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := RD.genCalldatacopy r7 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 1363) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1338_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.ofNat 160) x0)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1338) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1338_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (feDeposit_block_1338_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1338_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1356`. -/
def feDeposit_block_1356_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 50) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1356. -/
theorem feDeposit_block_1356 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2289) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2289) (feDeposit_block_1356_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 50) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2289) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2289)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1356_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2289) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2289) (feDeposit_block_1356_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1356 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1363_taken`. -/
def feDeposit_block_1363_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x1 (UInt256.ofNat 160)) :: (x0 + (UInt256.ofNat 160)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1363_taken`. -/
def feDeposit_block_1363_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x1 (UInt256.ofNat 160))).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1363. -/
theorem feDeposit_block_1363_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.gt x10 (UInt256.sub x1 (UInt256.ofNat 160))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1363_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1363_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup14 (by native_decide) (by evm_ov)
  have r15 := r14.gt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1363_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.gt x10 (UInt256.sub x1 (UInt256.ofNat 160))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1363_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1363_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1363_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1363_fallthrough`. -/
def feDeposit_block_1363_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x1 (UInt256.ofNat 160)) :: (x0 + (UInt256.ofNat 160)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1363_fallthrough`. -/
def feDeposit_block_1363_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x1 (UInt256.ofNat 160))).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1363. -/
theorem feDeposit_block_1363_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.gt x10 (UInt256.sub x1 (UInt256.ofNat 160))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (feDeposit_block_1363_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1363_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup14 (by native_decide) (by evm_ov)
  have r15 := r14.gt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1384)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1363_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.gt x10 (UInt256.sub x1 (UInt256.ofNat 160))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1363) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (feDeposit_block_1363_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1363_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1363_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1384_taken`. -/
def feDeposit_block_1384_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 x12) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: (x12 + x1) :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1384_taken`. -/
def feDeposit_block_1384_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x10 : UInt256} {x12 : UInt256} : ByteArray :=
  ((UInt256.sub x3 (UInt256.sub x0 x12)).toByteArray.write 0 (mem.write x10.toNat mem x1.toNat x12.toNat) (x2 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1384. -/
theorem feDeposit_block_1384_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt x9 (UInt256.sub x0 x12)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1384_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1384_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x10 := x10) (x12 := x12)) (M (Mmcopy aw x1 x10 x12) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((70) + (mcopyExpansionCost aw x1 x10 x12) + (3 + 3 * ((x12.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x1 x10 x12) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup13 (by native_decide) (by evm_ov)
  have r2 := r1.dup12 (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.dup13 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap12 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r15 := r14.dup4 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  have r19 := r18.dup10 (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1384_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt x9 (UInt256.sub x0 x12)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1384_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1384_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x10 := x10) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1384_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1384_fallthrough`. -/
def feDeposit_block_1384_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 x12) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: (x12 + x1) :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1384_fallthrough`. -/
def feDeposit_block_1384_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x10 : UInt256} {x12 : UInt256} : ByteArray :=
  ((UInt256.sub x3 (UInt256.sub x0 x12)).toByteArray.write 0 (mem.write x10.toNat mem x1.toNat x12.toNat) (x2 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1384. -/
theorem feDeposit_block_1384_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt x9 (UInt256.sub x0 x12)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (feDeposit_block_1384_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1384_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x10 := x10) (x12 := x12)) (M (Mmcopy aw x1 x10 x12) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((70) + (mcopyExpansionCost aw x1 x10 x12) + (3 + 3 * ((x12.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x1 x10 x12) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup13 (by native_decide) (by evm_ov)
  have r2 := r1.dup12 (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.dup13 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap12 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r15 := r14.dup4 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  have r19 := r18.dup10 (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1409)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1384_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt x9 (UInt256.sub x0 x12)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1384) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (feDeposit_block_1384_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1384_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x10 := x10) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1384_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1409_taken`. -/
def feDeposit_block_1409_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 x8) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: (x8 + x11) :: x9 :: x10 :: x1 :: x12 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1409_taken`. -/
def feDeposit_block_1409_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x8 : UInt256} {x11 : UInt256} {x12 : UInt256} : ByteArray :=
  ((UInt256.sub x2 (UInt256.sub x0 x8)).toByteArray.write 0 (mem.write x12.toNat mem x11.toNat x8.toNat) (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1409. -/
theorem feDeposit_block_1409_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x8)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1409_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1409_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x8 := x8) (x11 := x11) (x12 := x12)) (M (Mmcopy aw x11 x12 x8) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((73) + (mcopyExpansionCost aw x11 x12 x8) + (3 + 3 * ((x8.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x11 x12 x8) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup9 (by native_decide) (by evm_ov)
  have r2 := r1.dup14 (by native_decide) (by evm_ov)
  have r3 := r2.dup14 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap11 (by native_decide) (by evm_ov)
  have r6 := r5.dup9 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap8 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap11 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.dup13 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1409_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x8)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1409_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1409_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x8 := x8) (x11 := x11) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1409_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1409_fallthrough`. -/
def feDeposit_block_1409_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 x8) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: (x8 + x11) :: x9 :: x10 :: x1 :: x12 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1409_fallthrough`. -/
def feDeposit_block_1409_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x8 : UInt256} {x11 : UInt256} {x12 : UInt256} : ByteArray :=
  ((UInt256.sub x2 (UInt256.sub x0 x8)).toByteArray.write 0 (mem.write x12.toNat mem x11.toNat x8.toNat) (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1409. -/
theorem feDeposit_block_1409_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x8)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (feDeposit_block_1409_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1409_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x8 := x8) (x11 := x11) (x12 := x12)) (M (Mmcopy aw x11 x12 x8) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((73) + (mcopyExpansionCost aw x11 x12 x8) + (3 + 3 * ((x8.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x11 x12 x8) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup9 (by native_decide) (by evm_ov)
  have r2 := r1.dup14 (by native_decide) (by evm_ov)
  have r3 := r2.dup14 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap11 (by native_decide) (by evm_ov)
  have r6 := r5.dup9 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap8 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap11 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.dup13 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1436)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1409_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x8)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1409) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (feDeposit_block_1409_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (feDeposit_block_1409_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x8 := x8) (x11 := x11) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1409_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1436_taken`. -/
def feDeposit_block_1436_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 (UInt256.ofNat 64)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ((UInt256.ofNat 64) + x7) :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1436_taken`. -/
def feDeposit_block_1436_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x5 : UInt256} {x7 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x0 (UInt256.ofNat 64))).toByteArray.write 0 (mem.write x5.toNat mem x7.toNat (UInt256.ofNat 64).toNat) (x10 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1436. -/
theorem feDeposit_block_1436_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt x6 (UInt256.sub x0 (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1436_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1436_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5) (x7 := x7) (x10 := x10)) (M (Mmcopy aw x7 x5 (UInt256.ofNat 64)) (x10 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((73) + (mcopyExpansionCost aw x7 x5 (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x7 x5 (UInt256.ofNat 64)) (x10 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.dup7 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap7 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap8 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r16 := r15.dup13 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.dup8 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1436_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt x6 (UInt256.sub x0 (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1436_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1436_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5) (x7 := x7) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1436_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1436_fallthrough`. -/
def feDeposit_block_1436_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x0 (UInt256.ofNat 64)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ((UInt256.ofNat 64) + x7) :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1436_fallthrough`. -/
def feDeposit_block_1436_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x5 : UInt256} {x7 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x0 (UInt256.ofNat 64))).toByteArray.write 0 (mem.write x5.toNat mem x7.toNat (UInt256.ofNat 64).toNat) (x10 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1436. -/
theorem feDeposit_block_1436_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt x6 (UInt256.sub x0 (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (feDeposit_block_1436_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1436_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5) (x7 := x7) (x10 := x10)) (M (Mmcopy aw x7 x5 (UInt256.ofNat 64)) (x10 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((73) + (mcopyExpansionCost aw x7 x5 (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x7 x5 (UInt256.ofNat 64)) (x10 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.dup7 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap7 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap8 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r16 := r15.dup13 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.dup8 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1465)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1436_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt x6 (UInt256.sub x0 (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1436) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (feDeposit_block_1436_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1436_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5) (x7 := x7) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1436_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1465_taken`. -/
def feDeposit_block_1465_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: (x6 + x7) :: x1 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1465_taken`. -/
def feDeposit_block_1465_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x6 : UInt256} {x7 : UInt256} {x9 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x0 x6)).toByteArray.write 0 (mem.write x9.toNat mem x7.toNat x6.toNat) (x10 + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1465. -/
theorem feDeposit_block_1465_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x6)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1465_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1465_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10)) (M (Mmcopy aw x7 x9 x6) (x10 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((70) + (mcopyExpansionCost aw x7 x9 x6) + (3 + 3 * ((x6.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x7 x9 x6) (x10 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup7 (by native_decide) (by evm_ov)
  have r2 := r1.dup11 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap7 (by native_decide) (by evm_ov)
  have r6 := r5.dup7 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap6 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap7 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup8 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r16 := r15.dup12 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1356)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1465_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x6)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1356) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1356) (feDeposit_block_1465_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1465_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1465_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1465_fallthrough`. -/
def feDeposit_block_1465_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: (x6 + x7) :: x1 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1465_fallthrough`. -/
def feDeposit_block_1465_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x6 : UInt256} {x7 : UInt256} {x9 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.sub x1 (UInt256.sub x0 x6)).toByteArray.write 0 (mem.write x9.toNat mem x7.toNat x6.toNat) (x10 + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1465. -/
theorem feDeposit_block_1465_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x6)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (feDeposit_block_1465_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1465_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10)) (M (Mmcopy aw x7 x9 x6) (x10 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((70) + (mcopyExpansionCost aw x7 x9 x6) + (3 + 3 * ((x6.toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x7 x9 x6) (x10 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup7 (by native_decide) (by evm_ov)
  have r2 := r1.dup11 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap7 (by native_decide) (by evm_ov)
  have r6 := r5.dup7 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap6 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap7 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup8 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r16 := r15.dup12 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1356) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1491)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1465_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.sub x0 x6)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1465) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (feDeposit_block_1465_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (feDeposit_block_1465_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1465_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1491_taken`. -/
def feDeposit_block_1491_taken_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1491_taken`. -/
def feDeposit_block_1491_taken_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (mem.write x0.toNat mem x4.toNat (UInt256.ofNat 64).toNat)

/-- Automatically generated RD summary for bytecode block at pc 1491. -/
theorem feDeposit_block_1491_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt x1 (UInt256.ofNat 4294967295)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1592) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1592) (feDeposit_block_1491_taken_stack (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_1491_taken_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (Mmcopy aw x4 x0 (UInt256.ofNat 64)) x8 x5) rdata σ (k + 19) (C + ((55) + (mcopyExpansionCost aw x4 x0 (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x4 x0 (UInt256.ofNat 64)) x8 x5) + (375 + 8 * x5.toNat + 1 * 375))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap5 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 45506446345753628416285423056165511379837572639148407563471291220684748896453) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.swap6 (by native_decide) (by evm_ov)
  have r11 := RD.genLog1 r10 (by native_decide) hperm (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.lt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1592) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1592)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1491_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt x1 (UInt256.ofNat 4294967295)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1592) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1592) (feDeposit_block_1491_taken_stack (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_1491_taken_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1491_taken hstack hperm hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1491_fallthrough`. -/
def feDeposit_block_1491_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_1491_fallthrough`. -/
def feDeposit_block_1491_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (mem.write x0.toNat mem x4.toNat (UInt256.ofNat 64).toNat)

/-- Automatically generated RD summary for bytecode block at pc 1491. -/
theorem feDeposit_block_1491_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt x1 (UInt256.ofNat 4294967295)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1549) (feDeposit_block_1491_fallthrough_stack (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_1491_fallthrough_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (Mmcopy aw x4 x0 (UInt256.ofNat 64)) x8 x5) rdata σ (k + 19) (C + ((55) + (mcopyExpansionCost aw x4 x0 (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw x4 x0 (UInt256.ofNat 64)) x8 x5) + (375 + 8 * x5.toNat + 1 * 375))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap5 (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 45506446345753628416285423056165511379837572639148407563471291220684748896453) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.swap6 (by native_decide) (by evm_ov)
  have r11 := RD.genLog1 r10 (by native_decide) hperm (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.lt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1592) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1549)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1491_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt x1 (UInt256.ofNat 4294967295)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1549) (feDeposit_block_1491_fallthrough_stack (x1 := x1) (x2 := x2) (R := R)) (feDeposit_block_1491_fallthrough_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1491_fallthrough hstack hperm hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1549`. -/
def feDeposit_block_1549_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 896881205516154504303356323187679926572073778874356643889081023096165) :: (UInt256.shiftLeft (UInt256.ofNat 34789481243) (UInt256.ofNat 218)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1549. -/
theorem feDeposit_block_1549 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2249) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1549) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2249) (feDeposit_block_1549_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 34789481243) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 218) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 896881205516154504303356323187679926572073778874356643889081023096165) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2249) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2249)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1549_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2249) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1549) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2249) (feDeposit_block_1549_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1549 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_1592`. -/
def feDeposit_block_1592_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: ((UInt256.ofNat 1) + x1) :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1592. -/
theorem feDeposit_block_1592 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1592) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (feDeposit_block_1592_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 32) ((UInt256.ofNat 1) + x1)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sstore r6 hperm (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.swap3 (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1605)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1592_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1592) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (feDeposit_block_1592_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 32) ((UInt256.ofNat 1) + x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := feDeposit_block_1592 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1605. -/
theorem feDeposit_block_1605_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1688) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1688) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1688) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1688)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1605_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1688) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1688) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1605_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1605. -/
theorem feDeposit_block_1605_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1615) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1688) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1615)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1605_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1605) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1615) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1605_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1615. -/
theorem feDeposit_block_1615_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1634) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1615) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1634) (x0 :: x1 :: R) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1634) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1634)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_1615_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 1634) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1615) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 1634) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_1615_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end feDepositBlocks
