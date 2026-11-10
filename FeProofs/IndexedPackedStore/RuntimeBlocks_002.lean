import Reasoning.Reach
import FeProofs.IndexedPackedStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feIndexedPackedStoreBlocks

/-- Automatically generated RD summary for bytecode block at pc 142. -/
theorem feIndexedPackedStore_block_142_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 54) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 142) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 54) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 54)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 142. -/
theorem feIndexedPackedStore_block_142_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 142) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 154) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 154)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_154_taken`. -/
def feIndexedPackedStore_block_154_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 154. -/
theorem feIndexedPackedStore_block_154_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 81) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 154) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 81) (feIndexedPackedStore_block_154_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 81)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_154_fallthrough`. -/
def feIndexedPackedStore_block_154_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 154. -/
theorem feIndexedPackedStore_block_154_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 154) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 165) (feIndexedPackedStore_block_154_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 165)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_165_taken`. -/
def feIndexedPackedStore_block_165_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `feIndexedPackedStore_block_165_taken`. -/
def feIndexedPackedStore_block_165_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 165. -/
theorem feIndexedPackedStore_block_165_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 81) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 165) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 81) (feIndexedPackedStore_block_165_taken_stack (ee := ee) (R := R)) (feIndexedPackedStore_block_165_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r11 := r10.shr (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.xor (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.swap3 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r30 := r29.calldataload (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r38⟩ := RD.sstore r37 hperm (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r40 := r39.calldataload (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.lt (by native_decide) (by evm_ov)
  have r44 := r43.iszero (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r46 := r45.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 81)) r46 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_165_fallthrough`. -/
def feIndexedPackedStore_block_165_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `feIndexedPackedStore_block_165_fallthrough`. -/
def feIndexedPackedStore_block_165_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 165. -/
theorem feIndexedPackedStore_block_165_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 165) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 222) (feIndexedPackedStore_block_165_fallthrough_stack (ee := ee) (R := R)) (feIndexedPackedStore_block_165_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r11 := r10.shr (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.xor (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.swap3 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r30 := r29.calldataload (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r38⟩ := RD.sstore r37 hperm (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r40 := r39.calldataload (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.lt (by native_decide) (by evm_ov)
  have r44 := r43.iszero (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r46 := r45.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 222)) r46 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Automatically generated RD summary for bytecode block at pc 222. -/
theorem feIndexedPackedStore_block_222 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 222) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) (((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r11 := r10.shr (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.xor (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.swap3 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r30 := r29.calldataload (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r38⟩ := RD.sstore r37 hperm (by native_decide) (by evm_ov)
  have r39 := r38.push0 (by native_decide) (by evm_ov)
  have r40 := r39.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r40 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_271_taken`. -/
def feIndexedPackedStore_block_271_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 271. -/
theorem feIndexedPackedStore_block_271_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 54) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 271) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 54) (feIndexedPackedStore_block_271_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 54)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_271_fallthrough`. -/
def feIndexedPackedStore_block_271_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 271. -/
theorem feIndexedPackedStore_block_271_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 271) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 277) (feIndexedPackedStore_block_271_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 277)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 277. -/
theorem feIndexedPackedStore_block_277_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 54) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 277) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 54) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 54)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 277. -/
theorem feIndexedPackedStore_block_277_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 277) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 289) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 54) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 289)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_289_taken`. -/
def feIndexedPackedStore_block_289_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem feIndexedPackedStore_block_289_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 81) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 289) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 81) (feIndexedPackedStore_block_289_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 81)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_289_fallthrough`. -/
def feIndexedPackedStore_block_289_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem feIndexedPackedStore_block_289_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 289) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 300) (feIndexedPackedStore_block_289_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 300)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 300. -/
theorem feIndexedPackedStore_block_300 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 300) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 σ (((UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3)))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.shiftRight x0 (UInt256.ofNat 5)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shr (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.shr (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r25 := r24.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r25 (by native_decide) (by evm_ov)

/-- Static-mode twin of `feIndexedPackedStore_block_165_taken`: its steps up to the state change, which halts when
    `ee.perm = false`. -/
theorem feIndexedPackedStore_block_165_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 165) (x0 :: R) mem aw rdata σ k C)
    : RDstatic FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r11 := r10.shr (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.xor (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.swap3 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r30 := r29.calldataload (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r37 hperm (by native_decide) (by evm_ov)

end feIndexedPackedStoreBlocks
