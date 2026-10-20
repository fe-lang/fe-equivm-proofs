import Reasoning.Reach
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositBlocks

/-- Automatically generated RD summary for bytecode block at pc 2101. -/
theorem feDeposit_block_2101 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2101) R mem aw rdata σ k C)
    : RDret FeProofs.Deposit.feDepositBytecode g s0 σ (((memLoad (UInt256.ofNat 160) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r6 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 2110. -/
theorem feDeposit_block_2110_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2110) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2110_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2110) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2110_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2110. -/
theorem feDeposit_block_2110_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2110) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2118)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2110_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2110) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2110_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2118. -/
theorem feDeposit_block_2118_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x1 x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.sub (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2118_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x1 x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2118_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2118. -/
theorem feDeposit_block_2118_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x1 x0)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.sub (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2128)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2118_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.sub x1 x0)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2118) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2118_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2128_taken`. -/
def feDeposit_block_2128_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2128. -/
theorem feDeposit_block_2128_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2226) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2128_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.lt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2226) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2226)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2128_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2226) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2128_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2128_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2128_fallthrough`. -/
def feDeposit_block_2128_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2128. -/
theorem feDeposit_block_2128_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (feDeposit_block_2128_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.lt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2226) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2141)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2128_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2128) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (feDeposit_block_2128_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2128_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2141_taken`. -/
def feDeposit_block_2141_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: (UInt256.sub x3 x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2141. -/
theorem feDeposit_block_2141_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x3 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2226) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2141_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.sub (by native_decide) (by evm_ov)
  have r4 := r3.swap4 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2226) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2226)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2141_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x3 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2226) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2141_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2141_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2141_fallthrough`. -/
def feDeposit_block_2141_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: (UInt256.sub x3 x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2141. -/
theorem feDeposit_block_2141_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x3 x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (feDeposit_block_2141_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.sub (by native_decide) (by evm_ov)
  have r4 := r3.swap4 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2226) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2150)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2141_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt x3 x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2141) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (feDeposit_block_2141_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2141_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2150_taken`. -/
def feDeposit_block_2150_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2150. -/
theorem feDeposit_block_2150_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_2150_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2150_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (feDeposit_block_2150_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2150_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2150_fallthrough`. -/
def feDeposit_block_2150_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2150. -/
theorem feDeposit_block_2150_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (feDeposit_block_2150_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2157)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2150_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2150) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (feDeposit_block_2150_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2150_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2157. -/
theorem feDeposit_block_2157_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551552) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2245)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2157_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2245) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2157_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2157. -/
theorem feDeposit_block_2157_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551552) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2245) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2172)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2157_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat 18446744073709551552)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2157) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2157_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2172_taken`. -/
def feDeposit_block_2172_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2172. -/
theorem feDeposit_block_2172_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2195) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (feDeposit_block_2172_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2195) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2195)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2172_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2195) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (feDeposit_block_2172_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2172_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2172_fallthrough`. -/
def feDeposit_block_2172_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 63))) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2172. -/
theorem feDeposit_block_2172_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2191) (feDeposit_block_2172_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2195) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2191)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2172_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2191) (feDeposit_block_2172_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2172_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2191`. -/
def feDeposit_block_2191_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2191. -/
theorem feDeposit_block_2191 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2191) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (feDeposit_block_2191_stack (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2195)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2191_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2191) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (feDeposit_block_2191_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2191 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2195_taken`. -/
def feDeposit_block_2195_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x1 (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x3) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_2195_taken`. -/
def feDeposit_block_2195_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2195. -/
theorem feDeposit_block_2195_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2233) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2233) (feDeposit_block_2195_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feDeposit_block_2195_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r19 := r18.dup5 (by native_decide) (by evm_ov)
  have r20 := r19.lt (by native_decide) (by evm_ov)
  have r21 := r20.iszero (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2233) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2233)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2195_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2233) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2233) (feDeposit_block_2195_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feDeposit_block_2195_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2195_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2195_fallthrough`. -/
def feDeposit_block_2195_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub x1 (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x3) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_2195_fallthrough`. -/
def feDeposit_block_2195_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2195. -/
theorem feDeposit_block_2195_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2195_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feDeposit_block_2195_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r19 := r18.dup5 (by native_decide) (by evm_ov)
  have r20 := r19.lt (by native_decide) (by evm_ov)
  have r21 := r20.iszero (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2233) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2226)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2195_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2195) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) (feDeposit_block_2195_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feDeposit_block_2195_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2195_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2226`. -/
def feDeposit_block_2226_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 17) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2226. -/
theorem feDeposit_block_2226 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2289) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2289) (feDeposit_block_2226_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 17) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2289) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2289)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2226_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2289) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2226) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2289) (feDeposit_block_2226_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2226 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feDeposit_block_2233`. -/
def feDeposit_block_2233_stack {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x5 :: x3 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_2233`. -/
def feDeposit_block_2233_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} : ByteArray :=
  (ee.calldata.write x4.toNat ((⟨0⟩ : UInt256).toByteArray.write 0 mem (x2 + x0).toNat 32) x2.toNat x1.toNat)

/-- Automatically generated RD summary for bytecode block at pc 2233. -/
theorem feDeposit_block_2233 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains x6 = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2233) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 x6 (feDeposit_block_2233_stack (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feDeposit_block_2233_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) (M (M aw (x2 + x0) (⟨32⟩ : UInt256)) x2 x1) rdata σ (k + 12) (C + ((35) + (memExpansionCost aw (x2 + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + x0) (⟨32⟩ : UInt256)) x2 x1) + (3 + 3 * ((x1.toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := RD.genCalldatacopy r9 (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feDeposit_block_2233_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains x6 = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2233) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.Deposit.feDepositBytecode ee g s0 x6 (feDeposit_block_2233_stack (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (feDeposit_block_2233_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feDeposit_block_2233 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end feDepositBlocks
