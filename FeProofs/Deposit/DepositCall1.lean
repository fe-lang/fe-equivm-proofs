import FeProofs.Deposit.DepositMemory
import FeProofs.Deposit.DepositFront
import FeProofs.Deposit.DepositLoop

/-!
# FeDeposit `deposit`: the pubkey root (pc 637 → 695, statement 8)

The bytecode stores `mload(pubkey + 32)` and the high half of `mload(pubkey + 64)` at the scratch
pair `0x100`/`0x120` and `STATICCALL`s precompile 2 over those 64 bytes, writing the digest back
to `0x100`; `pubkey_root = sha256_64(abi.encodePacked(pubkey, bytes16(0)))` makes the same call.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The memory block 637 leaves: the two pubkey words at `0x100` and `0x120`. -/
abbrev c1Mem (I : ExecutionEnv) : ByteArray :=
  feDepositBlocks.feDeposit_block_637_memory (mem := hMem3 I) (x3 := rFp entryMem)

/-- The 64 bytes block 637 hands to the `STATICCALL` are the pubkey followed by 16 zero bytes. -/
theorem c1Payload {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96) :
    (c1Mem I).readWithPadding (UInt256.ofNat 256).toNat (UInt256.ofNat 64).toNat =
      dPayload I.calldata (dWord I.calldata 0) ++ ByteArray.zeroes 16 := by
  obtain ⟨_, _, _, hsz3, hpk, _, _⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  unfold c1Mem feDepositBlocks.feDeposit_block_637_memory
  rw [mFp0, show (UInt256.ofNat 256).toNat = 256 from rfl,
    show (UInt256.ofNat 288).toNat = 256 + 32 from rfl,
    show (UInt256.ofNat 64).toNat = 64 from rfl, pairWords_read _ _ _ 256 (256 + 32) 64 rfl rfl (by decide),
    show UInt256.ofNat 448 + UInt256.ofNat 32 = UInt256.ofNat 480 by decide,
    show UInt256.ofNat 480 + UInt256.ofNat 32 = UInt256.ofNat (480 + 32) by decide]
  exact pubkeyWords_eq (hMem3 I) _ (by omega) (by decide) hpk

/-- Statement 8: `pubkey_root = sha256_64(abi.encodePacked(bytes(pubkey), bytes16(0)))`. -/
abbrev c1Stmt : Stmt :=
  .internalCall "sha256_64" [.abiEncodePacked [(.bytes, .var "pubkey"),
    (.elem (.bytes 15), .fixedBytesLit 15 (List.replicate 16 0))]] "pubkey_root"

/-- **Call 1.**  From pc 637, either both sides revert (failed call or short return data) or the
    EVM reaches pc 695 with the digest at `0x100` while `pubkey_root` binds it. -/
theorem call1 {σ σ₀ A I} {g : UInt256} {σ1 : AccountMap} {evm : EVM.State} {L : Store}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    (hpk : L.get? "pubkey" = some (.bytes (dPayload I.calldata (dWord I.calldata 0))))
    (hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ1 evm)
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 637) (fStack I) (hMem3 I) aw rdata σ1 k C) :
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecStmt config (pFrame L) evm c1Stmt .reverted) ∨
    (∃ (evm' : EVM.State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 695) (fStack I)
        (callOutputMem (c1Mem I) out (UInt256.ofNat 256) (UInt256.ofNat 32))
        aw' out σ' k' C' ∧
      ExecStmt config (pFrame L) evm c1Stmt
        (.ok (pFrame (L.insert "pubkey_root" (shaDigest out))) evm')) := by
  have he := evalPubkeyPayload (cfg := config) (stele := pFrame L) (evm := evm) hpk
  have r1 := feDepositBlocks.feDeposit_block_637 (by simp) rd
  obtain ⟨evm', σ', z, out, aw', k', C', hcall, hs', r2, hob⟩ :=
    staticCallBridge r1 hs (by native_decide) (by simp)
  rw [c1Payload hok hargs hl0 hl1 hl2, ← precompile2_eq] at hcall
  rd_checked r2 z out as hrev hsz to 695
  · exact Or.inl ⟨hrev, sha64Call_revert rfl he hcall hsz⟩
  · exact Or.inr ⟨evm', σ', out, aw', _, _, hsz, hob, hs', r2, sha64Call_ok rfl he hcall hsz⟩

end FeProofs.Deposit
