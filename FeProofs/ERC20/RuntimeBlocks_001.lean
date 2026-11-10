import Reasoning.Reach
import FeProofs.ERC20.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feERC20Blocks

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feERC20_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 65) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feERC20_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_8_taken`. -/
def feERC20_block_8_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feERC20_block_8_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1889567281)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 400) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 400) (feERC20_block_8_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 400) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 400)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_8_fallthrough`. -/
def feERC20_block_8_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feERC20_block_8_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 1889567281)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 24) (feERC20_block_8_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 400) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feERC20_block_24_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 58) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 58) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 58)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem feERC20_block_24_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1889567281)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1889567281) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 58) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 34)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 34. -/
theorem feERC20_block_34_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 109) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 109) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2835717307) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 109) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 109)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 34. -/
theorem feERC20_block_34_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2835717307)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 34) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2835717307) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 109) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 44)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem feERC20_block_44_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 333) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 333) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3714247998) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 333) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 333)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem feERC20_block_44_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 3714247998)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 55) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3714247998) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 333) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 55)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 55. -/
theorem feERC20_block_55 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 65) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 55) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_58_taken`. -/
def feERC20_block_58_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem feERC20_block_58_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 69) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 69) (feERC20_block_58_taken_stack (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 69) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 69)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_58_fallthrough`. -/
def feERC20_block_58_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem feERC20_block_58_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) (feERC20_block_58_fallthrough_stack (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 69) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem feERC20_block_65 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ k C)
    : RDrev FeProofs.ERC20.feERC20Bytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r3 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 69. -/
theorem feERC20_block_69_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 65) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 69) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 69. -/
theorem feERC20_block_69_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 69) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 82) R mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 82)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_82_taken`. -/
def feERC20_block_82_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 82. -/
theorem feERC20_block_82_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 65) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 82) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) (feERC20_block_82_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feERC20_block_82_fallthrough`. -/
def feERC20_block_82_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 82. -/
theorem feERC20_block_82_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 82) R mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 92) (feERC20_block_82_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 92)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 92. -/
theorem feERC20_block_92 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 92) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.ERC20.feERC20Bytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genKeccak256 r7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r13 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feERC20_block_109_taken`. -/
def feERC20_block_109_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 109. -/
theorem feERC20_block_109_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.ERC20.feERC20Bytecode 0).contains (UInt256.ofNat 65) = true)
    (h : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 109) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.ERC20.feERC20Bytecode ee g s0 (UInt256.ofNat 65) (feERC20_block_109_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 65) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

end feERC20Blocks
