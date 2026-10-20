import FeProofs.Deposit.Dispatch

/-!
# FeDeposit `bytes` decoder routine (pc 2110)

Fe's dynamic `bytes` decoder, called once per `bytes` argument of `deposit` with stack
`[p, CALLDATASIZE, ret, …]` where `p = 4 + offset` is the argument's absolute position.  It
reverts unless `p ≤ size`, a length word fits, and the payload fits (and its length is at most
`2^64 - 64`); otherwise it allocates `(len + 63) & ~31` bytes at the free pointer
(`max(mload 0x40, 0x100)`), bumps the free pointer, zeroes the last allocated word, copies the
length word and payload there with `CALLDATACOPY`, and returns `[fp, len, alloc, …]` to `ret`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The length word of the `bytes` argument at absolute position `p`. -/
abbrev rLen (ee : ExecutionEnv) (p : UInt256) : UInt256 :=
  uInt256OfByteArray (ee.calldata.readBytes p.toNat 32)

/-- The allocation size `(len + 63) & ~31`. -/
abbrev rAlloc (ee : ExecutionEnv) (p : UInt256) : UInt256 :=
  UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rLen ee p + UInt256.ofNat 63)

/-- The free pointer the decoder allocates at: `max(mload 0x40, 0x100)`. -/
abbrev rFp (mem : ByteArray) : UInt256 :=
  if UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255) = UInt256.ofNat 0 then
    UInt256.ofNat 256 else memLoad (UInt256.ofNat 64) mem

/-- Memory after the decoder allocating at `F`: free-pointer bump, last-word clear, then the copy. -/
abbrev rMemAt (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) : ByteArray :=
  ee.calldata.write p.toNat
    ((⟨0⟩ : UInt256).toByteArray.write 0
      ((F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray.write
        0 mem (UInt256.ofNat 64).toNat 32)
      (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat 32)
    F.toNat (UInt256.ofNat 32 + rLen ee p).toNat

/-- Every check of the decoder passes for the argument at `p`. -/
def rOk (ee : ExecutionEnv) (p cds : UInt256) : Prop :=
  UInt256.gt p cds = UInt256.ofNat 0 ∧
  UInt256.gt (UInt256.ofNat 32) (UInt256.sub cds p) = UInt256.ofNat 0 ∧
  UInt256.lt (p + UInt256.ofNat 32) p = UInt256.ofNat 0 ∧
  UInt256.lt cds (p + UInt256.ofNat 32) = UInt256.ofNat 0 ∧
  UInt256.gt (rLen ee p) (UInt256.sub cds (p + UInt256.ofNat 32)) = UInt256.ofNat 0 ∧
  UInt256.gt (rLen ee p) (UInt256.ofNat 18446744073709551552) = UInt256.ofNat 0 ∧
  UInt256.isZero (UInt256.lt (rAlloc ee p) (UInt256.ofNat 32)) ≠ UInt256.ofNat 0

set_option maxHeartbeats 1000000 in
theorem decodeBytesRoutine_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {p cds ret : UInt256}
    {R : List UInt256} (hR : R.length + 9 ≤ 1024)
    (h1 : UInt256.gt p cds = UInt256.ofNat 0)
    (h2 : UInt256.gt (UInt256.ofNat 32) (UInt256.sub cds p) = UInt256.ofNat 0)
    (h3 : UInt256.lt (p + UInt256.ofNat 32) p = UInt256.ofNat 0)
    (h4 : UInt256.lt cds (p + UInt256.ofNat 32) = UInt256.ofNat 0)
    (h5 : UInt256.gt (rLen ee p) (UInt256.sub cds (p + UInt256.ofNat 32)) = UInt256.ofNat 0)
    (h6 : UInt256.gt (rLen ee p) (UInt256.ofNat 18446744073709551552) = UInt256.ofNat 0)
    (h7 : UInt256.isZero (UInt256.lt (rAlloc ee p) (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hret : (D_J feDepositBytecode 0).contains ret = true)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 2110) (p :: cds :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD feDepositBytecode ee g s0 ret (rFp mem :: rLen ee p :: rAlloc ee p :: R)
      (rMemAt ee mem p (rFp mem)) aw' rdata σ k' C' := by
  have r1 := feDepositBlocks.feDeposit_block_2110_fallthrough (by simp; omega) h1 h
  have r2 := feDepositBlocks.feDeposit_block_2118_fallthrough (by simp; omega) h2 r1
  have r3 := feDepositBlocks.feDeposit_block_2128_fallthrough (by simp; omega) h3 r2
  simp only [feDepositBlocks.feDeposit_block_2128_fallthrough_stack] at r3
  have r4 := feDepositBlocks.feDeposit_block_2141_fallthrough (by simp; omega) h4 r3
  simp only [feDepositBlocks.feDeposit_block_2141_fallthrough_stack] at r4
  have r5 := feDepositBlocks.feDeposit_block_2150_fallthrough (by simp; omega) h5 r4
  simp only [feDepositBlocks.feDeposit_block_2150_fallthrough_stack] at r5
  have r6 := feDepositBlocks.feDeposit_block_2157_fallthrough (by simp; omega) h6 r5
  by_cases hfp : UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255) = UInt256.ofNat 0
  · have r7 := feDepositBlocks.feDeposit_block_2172_fallthrough (by simp; omega) hfp r6
    simp only [feDepositBlocks.feDeposit_block_2172_fallthrough_stack] at r7
    have r8 := feDepositBlocks.feDeposit_block_2191 (by simp; omega) r7
    simp only [feDepositBlocks.feDeposit_block_2191_stack] at r8
    have r9 := feDepositBlocks.feDeposit_block_2195_taken (by simp; omega) h7 (by jump_dest) r8
    simp only [feDepositBlocks.feDeposit_block_2195_taken_stack,
      feDepositBlocks.feDeposit_block_2195_taken_memory] at r9
    have r10 := feDepositBlocks.feDeposit_block_2233 (by simp; omega) hret r9
    simp only [feDepositBlocks.feDeposit_block_2233_stack,
      feDepositBlocks.feDeposit_block_2233_memory] at r10
    have hF : rFp mem = UInt256.ofNat 256 := if_pos hfp
    rw [hF]
    exact ⟨_, _, _, r10⟩
  · have r7 := feDepositBlocks.feDeposit_block_2172_taken (by simp; omega) hfp (by jump_dest) r6
    simp only [feDepositBlocks.feDeposit_block_2172_taken_stack] at r7
    have r9 := feDepositBlocks.feDeposit_block_2195_taken (by simp; omega) h7 (by jump_dest) r7
    simp only [feDepositBlocks.feDeposit_block_2195_taken_stack,
      feDepositBlocks.feDeposit_block_2195_taken_memory] at r9
    have r10 := feDepositBlocks.feDeposit_block_2233 (by simp; omega) hret r9
    simp only [feDepositBlocks.feDeposit_block_2233_stack,
      feDepositBlocks.feDeposit_block_2233_memory] at r10
    have hF : rFp mem = memLoad (UInt256.ofNat 64) mem := if_neg hfp
    rw [hF]
    exact ⟨_, _, _, r10⟩

/-- A panic path through pc 2226 (`Panic(0x11)`) reverts. -/
theorem decodeBytesPanic {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hR : R.length + 3 ≤ 1024)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 2226) R mem aw rdata σ k C) :
    RDrev feDepositBytecode g s0 := by
  have r1 := feDepositBlocks.feDeposit_block_2226 (by omega) (by jump_dest) h
  exact feDepositBlocks.feDeposit_block_2289 (by simp [feDepositBlocks.feDeposit_block_2226_stack]; omega) r1

set_option maxHeartbeats 1000000 in
/-- Any failing check of the `bytes` decoder reverts (the overflow and allocation checks panic). -/
theorem decodeBytesRoutine_rev {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {p cds ret : UInt256}
    {R : List UInt256} (hR : R.length + 10 ≤ 1024)
    (hbad : ¬ (UInt256.gt p cds = UInt256.ofNat 0 ∧
      UInt256.gt (UInt256.ofNat 32) (UInt256.sub cds p) = UInt256.ofNat 0 ∧
      UInt256.lt (p + UInt256.ofNat 32) p = UInt256.ofNat 0 ∧
      UInt256.lt cds (p + UInt256.ofNat 32) = UInt256.ofNat 0 ∧
      UInt256.gt (rLen ee p) (UInt256.sub cds (p + UInt256.ofNat 32)) = UInt256.ofNat 0 ∧
      UInt256.gt (rLen ee p) (UInt256.ofNat 18446744073709551552) = UInt256.ofNat 0 ∧
      UInt256.isZero (UInt256.lt (rAlloc ee p) (UInt256.ofNat 32)) ≠ UInt256.ofNat 0))
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 2110) (p :: cds :: ret :: R) mem aw rdata σ k C) :
    RDrev feDepositBytecode g s0 := by
  by_cases h1 : UInt256.gt p cds = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp; omega)
      (feDepositBlocks.feDeposit_block_2110_taken (by simp; omega) h1 (by jump_dest) h)
  have r1 := feDepositBlocks.feDeposit_block_2110_fallthrough (by simp; omega) h1 h
  by_cases h2 : UInt256.gt (UInt256.ofNat 32) (UInt256.sub cds p) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp; omega)
      (feDepositBlocks.feDeposit_block_2118_taken (by simp; omega) h2 (by jump_dest) r1)
  have r2 := feDepositBlocks.feDeposit_block_2118_fallthrough (by simp; omega) h2 r1
  by_cases h3 : UInt256.lt (p + UInt256.ofNat 32) p = UInt256.ofNat 0
  swap
  · exact decodeBytesPanic (R := feDepositBlocks.feDeposit_block_2128_taken_stack (ee := ee)
      (x0 := p) (R := cds :: ret :: R)) (by simp [feDepositBlocks.feDeposit_block_2128_fallthrough_stack, feDepositBlocks.feDeposit_block_2141_fallthrough_stack, feDepositBlocks.feDeposit_block_2150_fallthrough_stack, feDepositBlocks.feDeposit_block_2172_taken_stack, feDepositBlocks.feDeposit_block_2172_fallthrough_stack, feDepositBlocks.feDeposit_block_2191_stack, feDepositBlocks.feDeposit_block_2195_fallthrough_stack, feDepositBlocks.feDeposit_block_2128_taken_stack, feDepositBlocks.feDeposit_block_2150_taken_stack, feDepositBlocks.feDeposit_block_2141_taken_stack, feDepositBlocks.feDeposit_block_2226_stack]; omega)
      (feDepositBlocks.feDeposit_block_2128_taken (by simp; omega) h3 (by jump_dest) r2)
  have r3 := feDepositBlocks.feDeposit_block_2128_fallthrough (by simp; omega) h3 r2
  simp only [feDepositBlocks.feDeposit_block_2128_fallthrough_stack] at r3
  by_cases h4 : UInt256.lt cds (p + UInt256.ofNat 32) = UInt256.ofNat 0
  swap
  · exact decodeBytesPanic (by simp [feDepositBlocks.feDeposit_block_2128_fallthrough_stack, feDepositBlocks.feDeposit_block_2141_fallthrough_stack, feDepositBlocks.feDeposit_block_2150_fallthrough_stack, feDepositBlocks.feDeposit_block_2172_taken_stack, feDepositBlocks.feDeposit_block_2172_fallthrough_stack, feDepositBlocks.feDeposit_block_2191_stack, feDepositBlocks.feDeposit_block_2195_fallthrough_stack, feDepositBlocks.feDeposit_block_2128_taken_stack, feDepositBlocks.feDeposit_block_2150_taken_stack, feDepositBlocks.feDeposit_block_2141_taken_stack, feDepositBlocks.feDeposit_block_2226_stack]; omega)
      (feDepositBlocks.feDeposit_block_2141_taken (by simp; omega) h4 (by jump_dest) r3)
  have r4 := feDepositBlocks.feDeposit_block_2141_fallthrough (by simp; omega) h4 r3
  simp only [feDepositBlocks.feDeposit_block_2141_fallthrough_stack] at r4
  by_cases h5 : UInt256.gt (rLen ee p) (UInt256.sub cds (p + UInt256.ofNat 32)) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_2128_fallthrough_stack, feDepositBlocks.feDeposit_block_2141_fallthrough_stack, feDepositBlocks.feDeposit_block_2150_fallthrough_stack, feDepositBlocks.feDeposit_block_2172_taken_stack, feDepositBlocks.feDeposit_block_2172_fallthrough_stack, feDepositBlocks.feDeposit_block_2191_stack, feDepositBlocks.feDeposit_block_2195_fallthrough_stack, feDepositBlocks.feDeposit_block_2128_taken_stack, feDepositBlocks.feDeposit_block_2150_taken_stack, feDepositBlocks.feDeposit_block_2141_taken_stack, feDepositBlocks.feDeposit_block_2226_stack]; omega)
      (feDepositBlocks.feDeposit_block_2150_taken (by simp; omega) h5 (by jump_dest) r4)
  have r5 := feDepositBlocks.feDeposit_block_2150_fallthrough (by simp; omega) h5 r4
  simp only [feDepositBlocks.feDeposit_block_2150_fallthrough_stack] at r5
  by_cases h6 : UInt256.gt (rLen ee p) (UInt256.ofNat 18446744073709551552) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_2128_fallthrough_stack, feDepositBlocks.feDeposit_block_2141_fallthrough_stack, feDepositBlocks.feDeposit_block_2150_fallthrough_stack, feDepositBlocks.feDeposit_block_2172_taken_stack, feDepositBlocks.feDeposit_block_2172_fallthrough_stack, feDepositBlocks.feDeposit_block_2191_stack, feDepositBlocks.feDeposit_block_2195_fallthrough_stack, feDepositBlocks.feDeposit_block_2128_taken_stack, feDepositBlocks.feDeposit_block_2150_taken_stack, feDepositBlocks.feDeposit_block_2141_taken_stack, feDepositBlocks.feDeposit_block_2226_stack]; omega)
      (feDepositBlocks.feDeposit_block_2157_taken (by simp; omega) h6 (by jump_dest) r5)
  have r6 := feDepositBlocks.feDeposit_block_2157_fallthrough (by simp; omega) h6 r5
  have h7 : ¬ UInt256.isZero (UInt256.lt (rAlloc ee p) (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 :=
    fun h7 => hbad ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have h7' : UInt256.isZero (UInt256.lt (rAlloc ee p) (UInt256.ofNat 32)) = UInt256.ofNat 0 :=
    by simpa using h7
  by_cases hfp : UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255) = UInt256.ofNat 0
  · have r7 := feDepositBlocks.feDeposit_block_2172_fallthrough (by simp; omega) hfp r6
    simp only [feDepositBlocks.feDeposit_block_2172_fallthrough_stack] at r7
    have r8 := feDepositBlocks.feDeposit_block_2191 (by simp; omega) r7
    simp only [feDepositBlocks.feDeposit_block_2191_stack] at r8
    have r9 := feDepositBlocks.feDeposit_block_2195_fallthrough (by simp; omega) h7' r8
    simp only [feDepositBlocks.feDeposit_block_2195_fallthrough_stack] at r9
    exact decodeBytesPanic (by simp; omega) r9
  · have r7 := feDepositBlocks.feDeposit_block_2172_taken (by simp; omega) hfp (by jump_dest) r6
    simp only [feDepositBlocks.feDeposit_block_2172_taken_stack] at r7
    have r9 := feDepositBlocks.feDeposit_block_2195_fallthrough (by simp; omega) h7' r7
    simp only [feDepositBlocks.feDeposit_block_2195_fallthrough_stack] at r9
    exact decodeBytesPanic (by simp; omega) r9

theorem decodeBytesRoutine_ok' {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {p cds ret : UInt256}
    {R : List UInt256} (hR : R.length + 9 ≤ 1024) (hok : rOk ee p cds)
    (hret : (D_J feDepositBytecode 0).contains ret = true)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 2110) (p :: cds :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD feDepositBytecode ee g s0 ret (rFp mem :: rLen ee p :: rAlloc ee p :: R)
      (rMemAt ee mem p (rFp mem)) aw' rdata σ k' C' :=
  decodeBytesRoutine_ok hR hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
    hok.2.2.2.2.2.2 hret h

end FeProofs.Deposit
