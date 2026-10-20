import Reasoning.Reach
import FeProofs.NarrowAbi.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feNarrowAbiBlocks

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feNarrowAbi_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 99) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feNarrowAbi_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_8_taken`. -/
def feNarrowAbi_block_8_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feNarrowAbi_block_8_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1192718507)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 56) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 56) (feNarrowAbi_block_8_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1192718507) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 56) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 56)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_8_fallthrough`. -/
def feNarrowAbi_block_8_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feNarrowAbi_block_8_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1192718507)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 23) (feNarrowAbi_block_8_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1192718507) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 56) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 23. -/
theorem feNarrowAbi_block_23_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3048534363)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 124) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 23) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 124) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3048534363) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 124) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 124)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 23. -/
theorem feNarrowAbi_block_23_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3048534363)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 23) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3048534363) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 124) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 33)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 33. -/
theorem feNarrowAbi_block_33_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3438394775)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 180) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 180) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3438394775) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 180) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 180)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 33. -/
theorem feNarrowAbi_block_33_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3438394775)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3438394775) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 180) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 43)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem feNarrowAbi_block_43_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3525076283)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 242) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 242) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3525076283) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 242) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 242)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem feNarrowAbi_block_43_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3525076283)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 53) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3525076283) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 242) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 53)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 53. -/
theorem feNarrowAbi_block_53 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 99) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 53) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_56_taken`. -/
def feNarrowAbi_block_56_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 56. -/
theorem feNarrowAbi_block_56_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 99) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) (feNarrowAbi_block_56_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_56_fallthrough`. -/
def feNarrowAbi_block_56_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 56. -/
theorem feNarrowAbi_block_56_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 56) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 62) (feNarrowAbi_block_56_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 62. -/
theorem feNarrowAbi_block_62_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 99) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 62. -/
theorem feNarrowAbi_block_62_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 74) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 99) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 74)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_74_taken`. -/
def feNarrowAbi_block_74_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 74. -/
theorem feNarrowAbi_block_74_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) (UInt256.ofNat 128))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 103) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 74) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 103) (feNarrowAbi_block_74_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 103) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 103)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_74_fallthrough`. -/
def feNarrowAbi_block_74_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 74. -/
theorem feNarrowAbi_block_74_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 255)) (UInt256.ofNat 128))) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 74) R mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 89) (feNarrowAbi_block_74_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 103) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 89)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_89_taken`. -/
def feNarrowAbi_block_89_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 89. -/
theorem feNarrowAbi_block_89_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.NarrowAbi.feNarrowAbiBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 89) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 111) (feNarrowAbi_block_89_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r2 := r1.not (by native_decide) (by evm_ov)
  have r3 := r2.or (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feNarrowAbi_block_89_fallthrough`. -/
def feNarrowAbi_block_89_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 89. -/
theorem feNarrowAbi_block_89_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.lor (UInt256.lnot (UInt256.ofNat 255)) x0) x1) = (UInt256.ofNat 0))
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 89) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) (feNarrowAbi_block_89_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r2 := r1.not (by native_decide) (by evm_ov)
  have r3 := r2.or (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 99. -/
theorem feNarrowAbi_block_99 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.NarrowAbi.feNarrowAbiBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : RDrev FeProofs.NarrowAbi.feNarrowAbiBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r3 (by native_decide) (by evm_ov)

end feNarrowAbiBlocks
