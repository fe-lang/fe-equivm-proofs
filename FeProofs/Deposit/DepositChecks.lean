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
  rd_run h to 650 using [h0, h1, h2, h3, h4, h5]
  exact ⟨_, _, h⟩

theorem depositChecks_rev {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {fp2 len2 alloc2 len1 alloc1 fp0 len0 alloc0 fp1 : UInt256}
    (hbad : ¬ cOk ee len0 len1 len2)
    (h : RD feDepositBytecode ee g s0 (UInt256.ofNat 242)
      [fp2, len2, alloc2, len1, alloc1, fp0, len0, alloc0, fp1] mem aw rdata σ k C) :
    RDrev feDepositBytecode g s0 := by
  unfold cOk at hbad
  by_cases h0 : UInt256.eq (UInt256.ofNat 48) len0 = UInt256.ofNat 0
  · rd_run h using [h0]; exact h
  by_cases h1 : UInt256.eq (UInt256.ofNat 32) len1 = UInt256.ofNat 0
  · rd_run h using [h0, h1]; exact h
  by_cases h2 : UInt256.eq (UInt256.ofNat 96) len2 = UInt256.ofNat 0
  · rd_run h using [h0, h1, h2]; exact h
  by_cases h3 : UInt256.isZero (UInt256.lt ee.weiValue (UInt256.ofNat 1000000000000000000)) =
      UInt256.ofNat 0
  · rd_run h using [h0, h1, h2, h3]; exact h
  by_cases h4 : UInt256.isZero (UInt256.mod ee.weiValue (UInt256.ofNat 1000000000)) = UInt256.ofNat 0
  · rd_run h using [h0, h1, h2, h3, h4]; exact h
  have h5 : UInt256.isZero (UInt256.gt (UInt256.div ee.weiValue (UInt256.ofNat 1000000000))
      (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192))) = UInt256.ofNat 0 := by
    simpa using fun h5 => hbad ⟨h0, h1, h2, h3, h4, h5⟩
  rd_run h using [h0, h1, h2, h3, h4, h5]
  exact h

end FeProofs.Deposit
