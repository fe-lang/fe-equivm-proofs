import FeProofs.Deposit.DepositCompose
import FeProofs.Deposit.DepositLoop

/-!
# FeDeposit `deposit`: chaining the segments

Adapters from each segment's conclusion to `OutAt`, so `feDepositDepositBody` is assembled by
transporting outcomes back to statement 9 with `OutAt.mono`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The Merkle-insertion tail (`depositTail`, pc 1592 / statement 23 on) as an `OutAt`. -/
theorem tailOut {σ σ₀ A I} {g : UInt256} (hperm : I.perm = true)
    {node count x2 : UInt256} {L : Store} {evm : EVM.State} {σ' : AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 1592) (node :: count :: x2 :: R) mem aw rdata σ' k C)
    (hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm)
    (hcount : solcSlotWord σ' I (UInt256.ofNat 32) = count)
    (hlt : count.toNat < 2 ^ 32 - 1)
    (hn : L.get? "node" = some (.int (Int.ofNat node.toNat)))
    (hb : L.get? "branch" = none) (hdc : L.get? "deposit_count" = none) :
    OutAt σ σ₀ A I g (ExecBlock config (pFrame L) evm (depositTransition.body.drop 22)) := by
  rw [show depositTransition.body.drop 22 = depositTailStmts from depositTailStmts_eq]
  rcases depositTail hperm hR rd hs hcount hlt hn hb hdc with
    ⟨σf, frf, evmf, hr, he, ha⟩ | ⟨hr, he⟩
  · exact Or.inl ⟨σf, frf, evmf, hr, he, ha.symm⟩
  · exact OutAt.rev hr he

end FeProofs.Deposit
