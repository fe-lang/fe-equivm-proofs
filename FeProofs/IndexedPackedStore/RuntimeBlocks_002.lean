import Reasoning.Reach
import FeProofs.IndexedPackedStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feIndexedPackedStoreBlocks

/-- Automatically generated RD summary for bytecode block at pc 159. -/
theorem feIndexedPackedStore_block_159_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 159) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 171) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 171)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_171_taken`. -/
def feIndexedPackedStore_block_171_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 171. -/
theorem feIndexedPackedStore_block_171_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 171) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_171_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_171_fallthrough`. -/
def feIndexedPackedStore_block_171_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 171. -/
theorem feIndexedPackedStore_block_171_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 171) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 182) (feIndexedPackedStore_block_171_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 182)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_182_taken`. -/
def feIndexedPackedStore_block_182_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 182. -/
theorem feIndexedPackedStore_block_182_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 182) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_182_taken_stack (ee := ee) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) k' C' := by
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
  have r12 := r11.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.xor (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.swap3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r24 := r23.calldataload (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.or (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sstore r31 hperm (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r34 := r33.calldataload (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r36 := r35.dup2 (by native_decide) (by evm_ov)
  have r37 := r36.lt (by native_decide) (by evm_ov)
  have r38 := r37.iszero (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r40 := r39.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r40 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_182_fallthrough`. -/
def feIndexedPackedStore_block_182_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 182. -/
theorem feIndexedPackedStore_block_182_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 182) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 263) (feIndexedPackedStore_block_182_fallthrough_stack (ee := ee) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) k' C' := by
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
  have r12 := r11.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.xor (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.swap3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r24 := r23.calldataload (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.or (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sstore r31 hperm (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r34 := r33.calldataload (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r36 := r35.dup2 (by native_decide) (by evm_ov)
  have r37 := r36.lt (by native_decide) (by evm_ov)
  have r38 := r37.iszero (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r40 := r39.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 263)) r40 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Automatically generated RD summary for bytecode block at pc 263. -/
theorem feIndexedPackedStore_block_263 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 263) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (⟨0⟩ : UInt256))) (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3))))))) (mem.readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
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
  have r12 := r11.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.xor (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.swap3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r24 := r23.calldataload (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.or (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sstore r31 hperm (by native_decide) (by evm_ov)
  have r33 := r32.push0 (by native_decide) (by evm_ov)
  have r34 := r33.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r34 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_336_taken`. -/
def feIndexedPackedStore_block_336_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 336. -/
theorem feIndexedPackedStore_block_336_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 336) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_336_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_336_fallthrough`. -/
def feIndexedPackedStore_block_336_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 336. -/
theorem feIndexedPackedStore_block_336_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 336) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 342) (feIndexedPackedStore_block_336_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 342)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 342. -/
theorem feIndexedPackedStore_block_342_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 342) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 342. -/
theorem feIndexedPackedStore_block_342_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 342) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 354) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 354)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_354_taken`. -/
def feIndexedPackedStore_block_354_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 354. -/
theorem feIndexedPackedStore_block_354_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode 0).contains (UInt256.ofNat 75) = true)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 354) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 75) (feIndexedPackedStore_block_354_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 75)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feIndexedPackedStore_block_354_fallthrough`. -/
def feIndexedPackedStore_block_354_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 354. -/
theorem feIndexedPackedStore_block_354_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 354) R mem aw rdata σ k C)
    : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 365) (feIndexedPackedStore_block_354_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 75) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 365)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 365. -/
theorem feIndexedPackedStore_block_365 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode ee g s0 (UInt256.ofNat 365) (x0 :: R) mem aw rdata σ k C)
    : RDret FeProofs.IndexedPackedStore.feIndexedPackedStoreBytecode g s0 σ (((UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) + (UInt256.shiftRight x0 (UInt256.ofNat 5))) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 31)) (UInt256.ofNat 3)))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shr (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.shr (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r19 (by native_decide) (by evm_ov)

end feIndexedPackedStoreBlocks
