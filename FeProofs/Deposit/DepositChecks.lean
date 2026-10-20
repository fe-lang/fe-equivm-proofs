import FeProofs.Deposit.Dispatch

/-!
# FeDeposit `deposit` length and value checks (EVM side, pc 242 → 650)

The decoded lengths must be 48, 32 and 96; the call value must be at least one ether, a whole
number of gwei, and at most `2^64 - 1` gwei.  Every failure reverts with an `Error(string)` payload
(pc 2249).  On success pc 650 holds the gwei amount on top of the remaining decoded values.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The length and value checks pass. -/
def cOk (ee : ExecutionEnv) (len0 len1 len2 : UInt256) : Prop :=
  UInt256.eq (UInt256.ofNat 48) len0 ≠ UInt256.ofNat 0 ∧
  UInt256.eq (UInt256.ofNat 32) len1 ≠ UInt256.ofNat 0 ∧
  UInt256.eq (UInt256.ofNat 96) len2 ≠ UInt256.ofNat 0 ∧
  UInt256.isZero (UInt256.lt ee.weiValue (UInt256.ofNat 1000000000000000000)) ≠ UInt256.ofNat 0 ∧
  UInt256.isZero (UInt256.mod ee.weiValue (UInt256.ofNat 1000000000)) ≠ UInt256.ofNat 0 ∧
  UInt256.isZero (UInt256.gt (UInt256.div ee.weiValue (UInt256.ofNat 1000000000))
    (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ UInt256.ofNat 0

set_option maxHeartbeats 1000000 in
theorem depositChecks_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {fp2 len2 alloc2 len1 alloc1 fp0 len0 alloc0 fp1 : UInt256}
    (hok : cOk ee len0 len1 len2)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 242)
      [fp2, len2, alloc2, len1, alloc1, fp0, len0, alloc0, fp1] mem aw rdata σ k C) :
    ∃ k' C', RD feDepositBytecode ee g s0 (UInt256.ofNat 650)
      [UInt256.div ee.weiValue (UInt256.ofNat 1000000000), alloc2, alloc1, fp0, fp2, alloc0, fp1]
      mem aw rdata σ k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hok
  have r1 := feDepositBlocks.feDeposit_block_242_taken (by simp) h0 (by jump_dest) h
  simp only [feDepositBlocks.feDeposit_block_242_taken_stack] at r1
  have r2 := feDepositBlocks.feDeposit_block_299_taken (by simp) h1 (by jump_dest) r1
  simp only [feDepositBlocks.feDeposit_block_299_taken_stack] at r2
  have r3 := feDepositBlocks.feDeposit_block_375_taken (by simp) h2 (by jump_dest) r2
  simp only [feDepositBlocks.feDeposit_block_375_taken_stack] at r3
  have r4 := feDepositBlocks.feDeposit_block_435_taken (by simp) h3 (by jump_dest) r3
  simp only [feDepositBlocks.feDeposit_block_435_taken_stack] at r4
  have r5 := feDepositBlocks.feDeposit_block_501_taken (by simp) h4 (by jump_dest) r4
  have r6 := feDepositBlocks.feDeposit_block_581_taken (by simp) h5 (by jump_dest) r5
  simp only [feDepositBlocks.feDeposit_block_581_taken_stack] at r6
  exact ⟨_, _, r6⟩

set_option maxHeartbeats 1000000 in
theorem depositChecks_rev {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {fp2 len2 alloc2 len1 alloc1 fp0 len0 alloc0 fp1 : UInt256}
    (hbad : ¬ cOk ee len0 len1 len2)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 242)
      [fp2, len2, alloc2, len1, alloc1, fp0, len0, alloc0, fp1] mem aw rdata σ k C) :
    RDrev feDepositBytecode g s0 := by
  unfold cOk at hbad
  by_cases h0 : UInt256.eq (UInt256.ofNat 48) len0 ≠ UInt256.ofNat 0
  swap
  · have r := feDepositBlocks.feDeposit_block_242_fallthrough (by simp) (by simpa using h0) h
    exact feDepositBlocks.feDeposit_block_2249 (by simp [feDepositBlocks.feDeposit_block_242_fallthrough_stack])
      (feDepositBlocks.feDeposit_block_251 (by simp [feDepositBlocks.feDeposit_block_242_fallthrough_stack]) (by jump_dest) r)
  have r1 := feDepositBlocks.feDeposit_block_242_taken (by simp) h0 (by jump_dest) h
  simp only [feDepositBlocks.feDeposit_block_242_taken_stack] at r1
  by_cases h1 : UInt256.eq (UInt256.ofNat 32) len1 ≠ UInt256.ofNat 0
  swap
  · have r := feDepositBlocks.feDeposit_block_299_fallthrough (by simp) (by simpa using h1) r1
    exact feDepositBlocks.feDeposit_block_2249 (by simp [feDepositBlocks.feDeposit_block_299_fallthrough_stack])
      (feDepositBlocks.feDeposit_block_308 (by simp [feDepositBlocks.feDeposit_block_299_fallthrough_stack]) (by jump_dest) r)
  have r2 := feDepositBlocks.feDeposit_block_299_taken (by simp) h1 (by jump_dest) r1
  simp only [feDepositBlocks.feDeposit_block_299_taken_stack] at r2
  by_cases h2 : UInt256.eq (UInt256.ofNat 96) len2 ≠ UInt256.ofNat 0
  swap
  · have r := feDepositBlocks.feDeposit_block_375_fallthrough (by simp) (by simpa using h2) r2
    exact feDepositBlocks.feDeposit_block_2249 (by simp [feDepositBlocks.feDeposit_block_375_fallthrough_stack])
      (feDepositBlocks.feDeposit_block_384 (by simp [feDepositBlocks.feDeposit_block_375_fallthrough_stack]) (by jump_dest) r)
  have r3 := feDepositBlocks.feDeposit_block_375_taken (by simp) h2 (by jump_dest) r2
  simp only [feDepositBlocks.feDeposit_block_375_taken_stack] at r3
  by_cases h3 : UInt256.isZero (UInt256.lt ee.weiValue (UInt256.ofNat 1000000000000000000)) ≠
      UInt256.ofNat 0
  swap
  · have r := feDepositBlocks.feDeposit_block_435_fallthrough (by simp) (by simpa using h3) r3
    exact feDepositBlocks.feDeposit_block_2249 (by simp [feDepositBlocks.feDeposit_block_435_fallthrough_stack])
      (feDepositBlocks.feDeposit_block_453 (by simp [feDepositBlocks.feDeposit_block_435_fallthrough_stack]) (by jump_dest) r)
  have r4 := feDepositBlocks.feDeposit_block_435_taken (by simp) h3 (by jump_dest) r3
  simp only [feDepositBlocks.feDeposit_block_435_taken_stack] at r4
  by_cases h4 : UInt256.isZero (UInt256.mod ee.weiValue (UInt256.ofNat 1000000000)) ≠ UInt256.ofNat 0
  swap
  · have r := feDepositBlocks.feDeposit_block_501_fallthrough (by simp) (by simpa using h4) r4
    exact feDepositBlocks.feDeposit_block_2249 (by simp)
      (feDepositBlocks.feDeposit_block_514 (by simp) (by jump_dest) r)
  have r5 := feDepositBlocks.feDeposit_block_501_taken (by simp) h4 (by jump_dest) r4
  have h5 : ¬ UInt256.isZero (UInt256.gt (UInt256.div ee.weiValue (UInt256.ofNat 1000000000))
      (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) ≠ UInt256.ofNat 0 :=
    fun h5 => hbad ⟨h0, h1, h2, h3, h4, h5⟩
  have r := feDepositBlocks.feDeposit_block_581_fallthrough (by simp) (by simpa using h5) r5
  exact feDepositBlocks.feDeposit_block_2249 (by simp [feDepositBlocks.feDeposit_block_581_fallthrough_stack])
    (feDepositBlocks.feDeposit_block_601 (by simp [feDepositBlocks.feDeposit_block_581_fallthrough_stack]) (by jump_dest) r)

end FeProofs.Deposit
