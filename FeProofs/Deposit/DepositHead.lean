import FeProofs.Deposit.DepositRoutine

/-!
# FeDeposit `deposit` argument decoding (EVM side, pc 154 → 242)

After the call-value-free arm entry (`deposit` is payable), the head check
`SLT(CALLDATASIZE - 4, 0x80)`, then for each `bytes` argument the head word `w` must satisfy
`w ≤ 2^256 - 5` and the decoder routine runs at `p = 4 + w`.  The three decoded arguments arrive at
pc 242 as `(fp, len, alloc)` triples.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The head word of argument `i`. -/
abbrev hWord (ee : ExecutionEnv) (i : Nat) : UInt256 :=
  uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat (4 + 32 * i)).toNat 32)

abbrev hCds (ee : ExecutionEnv) : UInt256 := UInt256.ofNat ee.calldata.size

abbrev hPos (ee : ExecutionEnv) (i : Nat) : UInt256 := UInt256.ofNat 4 + hWord ee i

abbrev hMem1 (ee : ExecutionEnv) : ByteArray :=
  rMemAt ee ByteArray.empty (hPos ee 0) (rFp ByteArray.empty)
abbrev hMem2 (ee : ExecutionEnv) : ByteArray := rMemAt ee (hMem1 ee) (hPos ee 1) (rFp (hMem1 ee))
abbrev hMem3 (ee : ExecutionEnv) : ByteArray := rMemAt ee (hMem2 ee) (hPos ee 2) (rFp (hMem2 ee))

/-- Every argument check of the `deposit` decoder passes. -/
def hOk (ee : ExecutionEnv) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128) =
      UInt256.ofNat 0 ∧
  UInt256.gt (hWord ee 0) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 ∧ rOk ee (hPos ee 0) (hCds ee) ∧
  UInt256.gt (hWord ee 1) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 ∧ rOk ee (hPos ee 1) (hCds ee) ∧
  UInt256.gt (hWord ee 2) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 ∧ rOk ee (hPos ee 2) (hCds ee)

/-- The decoded stack at pc 242. -/
abbrev hStack (ee : ExecutionEnv) : List UInt256 :=
  [rFp (hMem2 ee), rLen ee (hPos ee 2), rAlloc ee (hPos ee 2),
   rLen ee (hPos ee 1), rAlloc ee (hPos ee 1),
   rFp ByteArray.empty, rLen ee (hPos ee 0), rAlloc ee (hPos ee 0),
   rFp (hMem1 ee)]

set_option maxHeartbeats 2000000 in
theorem depositHead_ok {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap} {k C : ℕ}
    {sel : UInt256} (hok : hOk I)
    (h : RD feDepositBytecode I g s0 (UInt256.ofNat 154) [sel] ByteArray.empty (UInt256.ofNat 0)
      ByteArray.empty σ k C) :
    ∃ aw' k' C', RD feDepositBytecode I g s0 (UInt256.ofNat 242) (hStack I) (hMem3 I) aw'
      ByteArray.empty σ k' C' := by
  obtain ⟨hh, hw0, hr0, hw1, hr1, hw2, hr2⟩ := hok
  have r1 := feDepositBlocks.feDeposit_block_154_fallthrough (by simp) hh h
  simp only [feDepositBlocks.feDeposit_block_154_fallthrough_stack] at r1
  have r2 := feDepositBlocks.feDeposit_block_169_fallthrough (by simp) hw0 r1
  simp only [feDepositBlocks.feDeposit_block_169_fallthrough_stack] at r2
  have r3 := feDepositBlocks.feDeposit_block_182 (by simp) (by jump_dest) r2
  simp only [feDepositBlocks.feDeposit_block_182_stack] at r3
  obtain ⟨_, _, _, r4⟩ := decodeBytesRoutine_ok' (by simp) hr0 (by jump_dest) r3
  have r5 := feDepositBlocks.feDeposit_block_193_fallthrough (by simp) hw1 r4
  simp only [feDepositBlocks.feDeposit_block_193_fallthrough_stack] at r5
  have r6 := feDepositBlocks.feDeposit_block_206 (by simp) (by jump_dest) r5
  simp only [feDepositBlocks.feDeposit_block_206_stack] at r6
  obtain ⟨_, _, _, r7⟩ := decodeBytesRoutine_ok' (by simp) hr1 (by jump_dest) r6
  have r8 := feDepositBlocks.feDeposit_block_217_fallthrough (by simp) hw2 r7
  simp only [feDepositBlocks.feDeposit_block_217_fallthrough_stack] at r8
  have r9 := feDepositBlocks.feDeposit_block_230 (by simp) (by jump_dest) r8
  simp only [feDepositBlocks.feDeposit_block_230_stack] at r9
  obtain ⟨_, _, _, r10⟩ := decodeBytesRoutine_ok' (by simp) hr2 (by jump_dest) r9
  exact ⟨_, _, _, r10⟩

set_option maxHeartbeats 2000000 in
/-- Any failing argument check reverts. -/
theorem depositHead_rev {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap} {k C : ℕ}
    {sel : UInt256} (hbad : ¬ hOk I)
    (h : RD feDepositBytecode I g s0 (UInt256.ofNat 154) [sel] ByteArray.empty (UInt256.ofNat 0)
      ByteArray.empty σ k C) :
    RDrev feDepositBytecode g s0 := by
  unfold hOk at hbad
  by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
      (UInt256.ofNat 128) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_154_taken_stack])
      (feDepositBlocks.feDeposit_block_154_taken (by simp) hh (by jump_dest) h)
  have r1 := feDepositBlocks.feDeposit_block_154_fallthrough (by simp) hh h
  simp only [feDepositBlocks.feDeposit_block_154_fallthrough_stack] at r1
  by_cases hw0 : UInt256.gt (hWord I 0) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_169_taken_stack])
      (feDepositBlocks.feDeposit_block_169_taken (by simp) hw0 (by jump_dest) r1)
  have r2 := feDepositBlocks.feDeposit_block_169_fallthrough (by simp) hw0 r1
  simp only [feDepositBlocks.feDeposit_block_169_fallthrough_stack] at r2
  have r3 := feDepositBlocks.feDeposit_block_182 (by simp) (by jump_dest) r2
  simp only [feDepositBlocks.feDeposit_block_182_stack] at r3
  by_cases hr0 : rOk I (hPos I 0) (hCds I)
  swap
  · exact decodeBytesRoutine_rev (by simp) hr0 r3
  obtain ⟨_, _, _, r4⟩ := decodeBytesRoutine_ok' (by simp) hr0 (by jump_dest) r3
  by_cases hw1 : UInt256.gt (hWord I 1) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_193_taken_stack])
      (feDepositBlocks.feDeposit_block_193_taken (by simp) hw1 (by jump_dest) r4)
  have r5 := feDepositBlocks.feDeposit_block_193_fallthrough (by simp) hw1 r4
  simp only [feDepositBlocks.feDeposit_block_193_fallthrough_stack] at r5
  have r6 := feDepositBlocks.feDeposit_block_206 (by simp) (by jump_dest) r5
  simp only [feDepositBlocks.feDeposit_block_206_stack] at r6
  by_cases hr1 : rOk I (hPos I 1) (hCds I)
  swap
  · exact decodeBytesRoutine_rev (by simp) hr1 r6
  obtain ⟨_, _, _, r7⟩ := decodeBytesRoutine_ok' (by simp) hr1 (by jump_dest) r6
  by_cases hw2 : UInt256.gt (hWord I 2) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0
  swap
  · exact feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_217_taken_stack])
      (feDepositBlocks.feDeposit_block_217_taken (by simp) hw2 (by jump_dest) r7)
  have r8 := feDepositBlocks.feDeposit_block_217_fallthrough (by simp) hw2 r7
  simp only [feDepositBlocks.feDeposit_block_217_fallthrough_stack] at r8
  have r9 := feDepositBlocks.feDeposit_block_230 (by simp) (by jump_dest) r8
  simp only [feDepositBlocks.feDeposit_block_230_stack] at r9
  have hr2 : ¬ rOk I (hPos I 2) (hCds I) := fun hr2 => hbad ⟨hh, hw0, hr0, hw1, hr1, hw2, hr2⟩
  exact decodeBytesRoutine_rev (by simp) hr2 r9

end FeProofs.Deposit
