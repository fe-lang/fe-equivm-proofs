import Reasoning.Reach
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositBlocks

/-- Final stack for bytecode block summary `feDeposit_block_797_taken`. -/
def feDeposit_block_797_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 797. -/
theorem feDeposit_block_797_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 797) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_797_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_797_fallthrough`. -/
def feDeposit_block_797_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 797. -/
theorem feDeposit_block_797_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 797) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 802) (feDeposit_block_797_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 802)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Shared branch prefix at pc 802. -/
private def feDeposit_block_802_shared {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 802) (x0 :: x1 :: R) mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.returndatasize (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.lt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  exact r7

/-- Final stack for bytecode block summary `feDeposit_block_802_taken`. -/
def feDeposit_block_802_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 802. -/
theorem feDeposit_block_802_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 802) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_802_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  have r7 := feDeposit_block_802_shared hstack h
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_802_fallthrough`. -/
def feDeposit_block_802_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 802. -/
theorem feDeposit_block_802_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 802) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 813) (feDeposit_block_802_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  have r7 := feDeposit_block_802_shared hstack h
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 813)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_813`. -/
def feDeposit_block_813_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (UInt256.ofNat 320) :: (UInt256.ofNat 64) :: (UInt256.ofNat 320) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (UInt256.ofNat 320) mem) :: R)

/-- Final memory for bytecode block summary `feDeposit_block_813`. -/
def feDeposit_block_813_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 64) + x0) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 813. -/
theorem feDeposit_block_813 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 813) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 838) (feDeposit_block_813_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (R := R)) (feDeposit_block_813_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := RD.genGas (RD.normalizeCounters (k' := k + 8) (C' := C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) r8 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 838)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 838: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 839 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_839_taken`. -/
def feDeposit_block_839_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 839. -/
theorem feDeposit_block_839_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 839) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_839_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_839_fallthrough`. -/
def feDeposit_block_839_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 839. -/
theorem feDeposit_block_839_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 839) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 846) (feDeposit_block_839_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 846)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 846. -/
theorem feDeposit_block_846_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 846) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 846. -/
theorem feDeposit_block_846_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 846) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 855) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 855)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_855`. -/
def feDeposit_block_855_stack {g : Sat256} {aw : UInt256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((21) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (UInt256.ofNat 320) :: (UInt256.ofNat 64) :: (UInt256.ofNat 320) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((21) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: R)

/-- Final memory for bytecode block summary `feDeposit_block_855`. -/
def feDeposit_block_855_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 855. -/
theorem feDeposit_block_855 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 855) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 880) (feDeposit_block_855_stack (g := g) (aw := aw) (C := C) (R := R)) (feDeposit_block_855_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((41) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := RD.genGas (RD.normalizeCounters (k' := k + 7) (C' := C + ((21) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) r7 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r14 := r13.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 880)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 880: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 881 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_881_taken`. -/
def feDeposit_block_881_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 881. -/
theorem feDeposit_block_881_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 881) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_881_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_881_fallthrough`. -/
def feDeposit_block_881_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 881. -/
theorem feDeposit_block_881_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 881) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 888) (feDeposit_block_881_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 888)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 888. -/
theorem feDeposit_block_888_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 888) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 888. -/
theorem feDeposit_block_888_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 888) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 897) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 897)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_897`. -/
def feDeposit_block_897_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (UInt256.ofNat 384) :: (UInt256.ofNat 64) :: (UInt256.ofNat 384) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (UInt256.ofNat 320) mem) :: x0 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_897`. -/
def feDeposit_block_897_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 897. -/
theorem feDeposit_block_897 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 897) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 923) (feDeposit_block_897_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (R := R)) (feDeposit_block_897_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := RD.genGas (RD.normalizeCounters (k' := k + 8) (C' := C + ((24) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) r8 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 923)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 923: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 924 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_924_taken`. -/
def feDeposit_block_924_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 924. -/
theorem feDeposit_block_924_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 924) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_924_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_924_fallthrough`. -/
def feDeposit_block_924_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 924. -/
theorem feDeposit_block_924_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 924) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 931) (feDeposit_block_924_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 931)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 931. -/
theorem feDeposit_block_931_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 931) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 931. -/
theorem feDeposit_block_931_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 931) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 940) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 940)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_940`. -/
def feDeposit_block_940_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (UInt256.ofNat 384) :: (UInt256.ofNat 64) :: (UInt256.ofNat 384) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((24) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (UInt256.ofNat 384) mem) :: x1 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_940`. -/
def feDeposit_block_940_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 940. -/
theorem feDeposit_block_940 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 940) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 966) (feDeposit_block_940_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (R := R)) (feDeposit_block_940_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := RD.genGas (RD.normalizeCounters (k' := k + 8) (C' := C + ((24) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) r8 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 966)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 966: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 967 from a fresh symbolic RD state. -/

end feDepositBlocks
