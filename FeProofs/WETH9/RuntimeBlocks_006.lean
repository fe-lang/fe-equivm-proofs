import Reasoning.Reach
import FeProofs.WETH9.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feWETH9Blocks

/-- Final stack for bytecode block summary `feWETH9_block_670_fallthrough`. -/
def feWETH9_block_670_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 670. -/
theorem feWETH9_block_670_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 670) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) (feWETH9_block_670_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 680)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_670_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 670) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) (feWETH9_block_670_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_670_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_680_taken`. -/
def feWETH9_block_680_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 680. -/
theorem feWETH9_block_680_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_680_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 143)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_680_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 143) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 143) (feWETH9_block_680_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_680_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_680_fallthrough`. -/
def feWETH9_block_680_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 680. -/
theorem feWETH9_block_680_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 690) (feWETH9_block_680_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 143) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 690)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_680_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 680) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 690) (feWETH9_block_680_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_680_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 690. -/
theorem feWETH9_block_690 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 690) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret FeProofs.WETH9.feWETH9Bytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r22 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feWETH9_block_723`. -/
def feWETH9_block_723_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 731) :: R)

/-- Automatically generated RD summary for bytecode block at pc 723. -/
theorem feWETH9_block_723 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 735) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 735) (feWETH9_block_723_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 731) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 735) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 735)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_723_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 735) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 723) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 735) (feWETH9_block_723_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_723 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 731. -/
theorem feWETH9_block_731 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 731) R mem aw rdata σ k C)
    : RDret FeProofs.WETH9.feWETH9Bytecode g s0 σ (mem.readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  exact RD.genRet r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `feWETH9_block_735`. -/
def feWETH9_block_735_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `feWETH9_block_735`. -/
def feWETH9_block_735_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  (ee.weiValue.toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 735. -/
theorem feWETH9_block_735 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains x0 = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 735) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 x0 (feWETH9_block_735_stack (R := R)) (feWETH9_block_735_memory (ee := ee) (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 64)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (ee.weiValue + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sstore r17 hperm (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.pushConst (UInt256.ofNat 102222681472383059465863322013072701928378550215632170212813623808969952268444) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := RD.genLog2 r23 (by native_decide) hperm (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r25⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_735_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains x0 = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 735) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 x0 (feWETH9_block_735_stack (R := R)) (feWETH9_block_735_memory (ee := ee) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (ee.weiValue + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 160) (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_735 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_800`. -/
def feWETH9_block_800_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))) :: (UInt256.ofNat 812) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 800. -/
theorem feWETH9_block_800 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1115) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 800) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1115) (feWETH9_block_800_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 812) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1115) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1115)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_800_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1115) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 800) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1115) (feWETH9_block_800_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := feWETH9_block_800 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_812_taken`. -/
def feWETH9_block_812_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) :: (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 812. -/
theorem feWETH9_block_812_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt ((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1565) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 812) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1565) (feWETH9_block_812_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 19) (C + ((61))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r15 := r14.shr (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1565) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1565)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_812_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt ((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 1565) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 812) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 1565) (feWETH9_block_812_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_812_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_812_fallthrough`. -/
def feWETH9_block_812_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) :: (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 812. -/
theorem feWETH9_block_812_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt ((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 812) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) (feWETH9_block_812_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 19) (C + ((61))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r15 := r14.shr (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1565) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 838)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_812_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt ((UInt256.ofNat 32) + (UInt256.shiftLeft (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) (UInt256.ofNat 5))) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 812) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) (feWETH9_block_812_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_812_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_838_taken`. -/
def feWETH9_block_838_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 838. -/
theorem feWETH9_block_838_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 853) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (feWETH9_block_838_taken_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 223) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 853) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 853)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_838_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 853) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (feWETH9_block_838_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_838_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_838_fallthrough`. -/
def feWETH9_block_838_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 838. -/
theorem feWETH9_block_838_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) R mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 850) (feWETH9_block_838_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 223) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 853) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 850)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_838_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 838) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 850) (feWETH9_block_838_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_838_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_850`. -/
def feWETH9_block_850_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 224) :: R)

/-- Automatically generated RD summary for bytecode block at pc 850. -/
theorem feWETH9_block_850 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 850) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (feWETH9_block_850_stack (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 853)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_850_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 850) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (feWETH9_block_850_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_850 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_853_taken`. -/
def feWETH9_block_853_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 853. -/
theorem feWETH9_block_853_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 945) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 945) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9_block_853_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
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
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.dup6 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 945) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 945)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_853_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 945) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 945) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9_block_853_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_853_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `feWETH9_block_853_fallthrough`. -/
def feWETH9_block_853_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 ((x0 + (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (x1 + (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 853. -/
theorem feWETH9_block_853_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9_block_853_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
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
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.dup6 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 945) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 878)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_853_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 853) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: x4 :: R) (feWETH9_block_853_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_853_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 878. -/
theorem feWETH9_block_878_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 934) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 934) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup4 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 934) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 934)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_878_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 934) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 934) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_878_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 878. -/
theorem feWETH9_block_878_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup4 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 934) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 884)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_878_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 878) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_878_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 884. -/
theorem feWETH9_block_884_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 917) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 917) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_884_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 917) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_884_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 884. -/
theorem feWETH9_block_884_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 893) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 917) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 893)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_884_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x3 (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 884) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 893) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_884_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `feWETH9_block_893`. -/
def feWETH9_block_893_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x4 (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3))))) :: x1 :: x3 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 893. -/
theorem feWETH9_block_893 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 924) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 893) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 924) (feWETH9_block_893_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 21) (C + ((65))) := by
  let r0 := h
  have r1 := r0.dup4 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap5 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.swap4 (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap3 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 924) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 924)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem feWETH9_block_893_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J FeProofs.WETH9.feWETH9Bytecode 0).contains (UInt256.ofNat 924) = true)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 893) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 924) (feWETH9_block_893_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (feWETH9_block_893 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Static-mode twin of `feWETH9_block_735`: its steps up to the state change, which halts when
    `ee.perm = false`. -/
theorem feWETH9_block_735_static {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD FeProofs.WETH9.feWETH9Bytecode ee g s0 (UInt256.ofNat 735) (x0 :: R) mem aw rdata σ k C)
    : RDstatic FeProofs.WETH9.feWETH9Bytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  exact RD.sstoreStatic r17 hperm (by native_decide) (by evm_ov)

end feWETH9Blocks
