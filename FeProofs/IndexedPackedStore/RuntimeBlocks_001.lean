import Reasoning.Reach
import FeProofs.IndexedPackedStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feIndexedPackedStoreBlocks

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feIndexedPackedStore_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem feIndexedPackedStore_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_8_taken`. -/
def feIndexedPackedStore_block_8_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feIndexedPackedStore_block_8_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 447770341)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 47) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 47) (feIndexedPackedStore_block_8_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 447770341) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 47) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 47)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_8_fallthrough`. -/
def feIndexedPackedStore_block_8_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8. -/
theorem feIndexedPackedStore_block_8_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 447770341)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 8) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 23) (feIndexedPackedStore_block_8_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 447770341) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 47) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 23. -/
theorem feIndexedPackedStore_block_23_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1659099261)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 153) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 23) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 153) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1659099261) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 153) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 153)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 23. -/
theorem feIndexedPackedStore_block_23_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 1659099261)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 23) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1659099261) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 153) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 33)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 33. -/
theorem feIndexedPackedStore_block_33_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2500318106)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 336) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 336) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2500318106) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 336) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 336)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 33. -/
theorem feIndexedPackedStore_block_33_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2500318106)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 33) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2500318106) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 336) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 44)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem feIndexedPackedStore_block_44 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 44) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_47_taken`. -/
def feIndexedPackedStore_block_47_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 47. -/
theorem feIndexedPackedStore_block_47_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_47_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_47_fallthrough`. -/
def feIndexedPackedStore_block_47_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 47. -/
theorem feIndexedPackedStore_block_47_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 53) (feIndexedPackedStore_block_47_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 53)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 53. -/
theorem feIndexedPackedStore_block_53_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 53) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 53. -/
theorem feIndexedPackedStore_block_53_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 53) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_65_taken`. -/
def feIndexedPackedStore_block_65_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem feIndexedPackedStore_block_65_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 79) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 79) (feIndexedPackedStore_block_65_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 79) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 79)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_65_fallthrough`. -/
def feIndexedPackedStore_block_65_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem feIndexedPackedStore_block_65_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 65) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_65_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 79) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 75. -/
theorem feIndexedPackedStore_block_75 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ k C)
    : RDrev FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r3 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 79. -/
theorem feIndexedPackedStore_block_79 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 79) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) (mem.readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := r18.not (by native_decide) (by evm_ov)
  have r20 := r19.xor (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r25 := r24.calldataload (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.shl (by native_decide) (by evm_ov)
  have r31 := r30.or (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sstore r32 hperm (by native_decide) (by evm_ov)
  have r34 := r33.push0 (by native_decide) (by evm_ov)
  have r35 := r34.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r35 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_153_taken`. -/
def feIndexedPackedStore_block_153_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 153. -/
theorem feIndexedPackedStore_block_153_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 153) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_153_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_153_fallthrough`. -/
def feIndexedPackedStore_block_153_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 153. -/
theorem feIndexedPackedStore_block_153_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 153) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 159) (feIndexedPackedStore_block_153_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 159)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 159. -/
theorem feIndexedPackedStore_block_159_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

end feIndexedPackedStoreBlocks
