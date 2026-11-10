import Reasoning.Reach
import FeProofs.PackedStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace fePackedStoreBlocks

/-- Automatically generated RD summary for bytecode block at pc 143. -/
theorem fePackedStore_block_143_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 143) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 155) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 155)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 155. -/
theorem fePackedStore_block_155 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 155) R mem aw rdata σ k C)
    : RDret FeProofs.PackedStore.fePackedStoreBytecode g s0 (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.ofNat 8)) (UInt256.land (UInt256.lnot (UInt256.ofNat 65280)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 65280) (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.or (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sstore r22 hperm (by native_decide) (by evm_ov)
  have r24 := r23.push0 (by native_decide) (by evm_ov)
  have r25 := r24.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r25 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 188. -/
theorem fePackedStore_block_188_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 62) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 188) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 188. -/
theorem fePackedStore_block_188_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 188) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 193) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 193)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 193. -/
theorem fePackedStore_block_193_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 62) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 193. -/
theorem fePackedStore_block_193_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 193) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 205) R mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.calldatasize (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 205)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 205. -/
theorem fePackedStore_block_205 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 205) R mem aw rdata σ k C)
    : RDret FeProofs.PackedStore.fePackedStoreBytecode g s0 (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 255) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sstore r20 hperm (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r23 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 234. -/
theorem fePackedStore_block_234_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 88873589)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 260) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 234) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 260) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 88873589) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 260)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 234. -/
theorem fePackedStore_block_234_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 88873589)) = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 234) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 246) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 88873589) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 246)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 246. -/
theorem fePackedStore_block_246_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2428205892)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 289) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 246) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 289) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2428205892) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 289) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 289)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 246. -/
theorem fePackedStore_block_246_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.ofNat 2428205892)) = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 246) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 257) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2428205892) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 289) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 257)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 257. -/
theorem fePackedStore_block_257 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 62) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 257) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 260. -/
theorem fePackedStore_block_260_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 62) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 260) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 260. -/
theorem fePackedStore_block_260_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 260) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 265) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 265)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 265. -/
theorem fePackedStore_block_265 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 265) R mem aw rdata σ k C)
    : RDret FeProofs.PackedStore.fePackedStoreBytecode g s0 σ (((UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 8))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r18 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem fePackedStore_block_289_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.PackedStore.fePackedStoreBytecode 0).contains (UInt256.ofNat 62) = true)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 289) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 62) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 62)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem fePackedStore_block_289_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 289) R mem aw rdata σ k C)
    : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 294) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 62) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 294)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 294. -/
theorem fePackedStore_block_294 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 294) R mem aw rdata σ k C)
    : RDret FeProofs.PackedStore.fePackedStoreBytecode g s0 σ (((UInt256.land (UInt256.ofNat 255) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r16 (by native_decide) (by evm_ov)

/-- Static-mode twin of `fePackedStore_block_155`: its steps up to the state change, which halts when
    `ee.perm = false`. -/
theorem fePackedStore_block_155_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 155) R mem aw rdata σ k C)
    : RDstatic FeProofs.PackedStore.fePackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 65280) (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.or (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r22 hperm (by native_decide) (by evm_ov)

/-- Static-mode twin of `fePackedStore_block_205`: its steps up to the state change, which halts when
    `ee.perm = false`. -/
theorem fePackedStore_block_205_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 205) R mem aw rdata σ k C)
    : RDstatic FeProofs.PackedStore.fePackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r20 hperm (by native_decide) (by evm_ov)

end fePackedStoreBlocks
