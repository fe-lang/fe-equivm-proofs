import FeProofs.PackedStore.Common
import FeProofs.PackedStore.RuntimeBlocks_001
import FeProofs.PackedStore.RuntimeBlocks_002

/-! Static-mode twins of the generated setter summaries: the same steps up to the first
    `SSTORE`, which halts under `ee.perm = false`. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

theorem fePackedStore_block_190_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 190) R mem aw rdata σ k C)
    (hperm : ee.perm = false)
    : RDstatic FeProofs.PackedStore.fePackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.or (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 65280) (by native_decide) (by evm_ov)
  have r12 := r11.not (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r15 := r14.calldataload (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.or (by native_decide) (by evm_ov)
  have r21 := r20.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r21 hperm (by native_decide) (by evm_ov)

theorem fePackedStore_block_304_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 304) R mem aw rdata σ k C)
    (hperm : ee.perm = false)
    : RDstatic FeProofs.PackedStore.fePackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65280) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r13 hperm (by native_decide) (by evm_ov)

theorem fePackedStore_block_407_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.PackedStore.fePackedStoreBytecode ee g s0 (UInt256.ofNat 407) R mem aw rdata σ k C)
    (hperm : ee.perm = false)
    : RDstatic FeProofs.PackedStore.fePackedStoreBytecode g s0 := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.or (by native_decide) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r11 hperm (by native_decide) (by evm_ov)

end FeProofs.PackedStore
