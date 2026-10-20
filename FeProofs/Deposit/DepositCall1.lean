import FeProofs.Deposit.DepositMemory
import FeProofs.Deposit.DepositFront
import FeProofs.Deposit.DepositLoop

/-!
# FeDeposit `deposit`: the pubkey root (pc 650 → 715, statement 8)

The bytecode stores `mload(pubkey + 32)` and the high half of `mload(pubkey + 64)` at the free
pointer `0x220` and `STATICCALL`s precompile 2 over those 64 bytes, writing the digest back to
`0x220`; `pubkey_root = sha256_64(abi.encodePacked(pubkey, bytes16(0)))` makes the same call.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- Two adjacent stored words read back as the 64-byte payload. -/
theorem pairWords_read (mem : ByteArray) (b n : UInt256) (o : Nat) (ho : o + 32 < 2 ^ 32) :
    (n.toByteArray.write 0 (b.toByteArray.write 0 mem o 32) (o + 32) 32).readWithPadding o 64 =
      b.toByteArray ++ n.toByteArray := by
  have h0 := toByteArray_write_size_ge_off_add32 b mem o (small_gap mem o (by omega))
  have h1 := toByteArray_write_size_ge_off_add32 n (b.toByteArray.write 0 mem o 32) (o + 32)
    (small_gap _ (o + 32) ho)
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ o 32 32 (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega),
    toByteArray_write_read_below_of_gap n _ (o + 32) o (by omega) (by omega)
      (small_gap _ (o + 32) ho),
    toByteArray_write_read_back_of_gap b mem o (small_gap mem o (by omega)),
    toByteArray_write_read_back_of_gap n _ (o + 32) (small_gap _ (o + 32) ho)]

/-- The memory block 650 leaves (free-pointer bump, then the two pubkey words at the free
    pointer). -/
abbrev c1Mem (I : ExecutionEnv) : ByteArray :=
  feDepositBlocks.feDeposit_block_650_memory (mem := hMem3 I) (x3 := rFp ByteArray.empty)

set_option maxHeartbeats 1000000 in
/-- The 64 bytes block 650 hands to the `STATICCALL` are the pubkey followed by 16 zero bytes. -/
theorem c1Payload {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96) :
    (c1Mem I).readWithPadding (memLoad (UInt256.ofNat 64) (hMem3 I)).toNat (UInt256.ofNat 64).toNat =
      dPayload I.calldata (dWord I.calldata 0) ++ ByteArray.zeroes 16 := by
  obtain ⟨_, _, hload3, hsz3, hpk, _, _⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  unfold c1Mem feDepositBlocks.feDeposit_block_650_memory
  rw [hload3, mFp0, show (UInt256.ofNat 544).toNat = 544 from rfl,
    show (UInt256.ofNat 544 + UInt256.ofNat 32).toNat = 544 + 32 by decide,
    show (UInt256.ofNat 64).toNat = 64 from rfl, pairWords_read _ _ _ 544 (by decide),
    show UInt256.ofNat 256 + UInt256.ofNat 32 = UInt256.ofNat 288 by decide,
    show UInt256.ofNat 288 + UInt256.ofNat 32 = UInt256.ofNat (288 + 32) by decide]
  exact pubkeyWords_eq (hMem3 I) _ (by omega) (by decide) hpk

/-- Statement 8: `pubkey_root = sha256_64(abi.encodePacked(bytes(pubkey), bytes16(0)))`. -/
abbrev c1Stmt : Stmt :=
  .internalCall "sha256_64" [.abiEncodePacked [(.bytes, .var "pubkey"),
    (.elem (.bytes 15), .fixedBytesLit 15 (List.replicate 16 0))]] "pubkey_root"

set_option maxHeartbeats 2000000 in
/-- **Call 1.**  From pc 650, either both sides revert (failed call or short return data) or the
    EVM reaches pc 715 with the digest at the free pointer while `pubkey_root` binds it. -/
theorem call1 {σ σ₀ A I} {g : UInt256} {σ1 : AccountMap} {evm : EVM.State} {L : Store}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    (hpk : L.get? "pubkey" = some (.bytes (dPayload I.calldata (dWord I.calldata 0))))
    (hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ1 evm)
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 650) (fStack I) (hMem3 I) aw rdata σ1 k C) :
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecStmt config (pFrame L) evm c1Stmt .reverted) ∨
    (∃ (evm' : EVM.State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 715) (memLoad (UInt256.ofNat 64) (hMem3 I) :: fStack I)
        (callOutputMem (c1Mem I) out (memLoad (UInt256.ofNat 64) (hMem3 I)) (UInt256.ofNat 32))
        aw' out σ' k' C' ∧
      ExecStmt config (pFrame L) evm c1Stmt
        (.ok (pFrame (L.insert "pubkey_root" (shaDigest out))) evm')) := by
  have he := evalPubkeyPayload (cfg := config) (stele := pFrame L) (evm := evm) hpk
  have r1 := feDepositBlocks.feDeposit_block_650 (by simp) rd
  obtain ⟨evm', σ', z, out, aw', k', C', hcall, hs', r2, hob⟩ :=
    staticCallBridge r1 hs (by native_decide) (by simp)
  rw [c1Payload hok hargs hl0 hl1 hl2, ← precompile2_eq] at hcall
  rd_checked r2 z out as hrev hsz to 715
  · exact Or.inl ⟨hrev, sha64Call_revert rfl he hcall hsz⟩
  · exact Or.inr ⟨evm', σ', out, aw', _, _, hsz, hob, hs', r2, sha64Call_ok rfl he hcall hsz⟩

end FeProofs.Deposit
