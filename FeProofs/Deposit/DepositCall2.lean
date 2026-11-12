import FeProofs.Deposit.DepositCall1

/-!
# FeDeposit `deposit`: the first signature call (pc 695 → 813, statement 9)

Block 695 loads the pubkey digest and the withdrawal credentials word, byte-swaps the gwei
amount, zeroes the scratch pair `0x140`/`0x160` and hashes the signature's first 64 bytes where
the decoder put them.  Every write after the decoder lies below the decoded arguments
(`ArgsKept`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- Block 637's two scratch words keep the decoded arguments. -/
theorem c1Mem_kept {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96) :
    ArgsKept I (c1Mem I) := by
  obtain ⟨_, _, _, hsz3, _, _, _⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  have h0 : ArgsKept I (hMem3 I) := ⟨hsz3, fun _ _ _ _ _ => rfl⟩
  exact (h0.word _ (d := (UInt256.ofNat 256).toNat) (by decide)).word _
    (d := (UInt256.ofNat 288).toNat) (by decide)

/-- Memory after call 1's digest is copied to `0x100`. -/
abbrev c2Base (I : ExecutionEnv) (out1 : ByteArray) : ByteArray :=
  callOutputMem (c1Mem I) out1 (UInt256.ofNat 256) (UInt256.ofNat 32)

/-- Memory after block 695 zeroes the scratch pair at `0x140`. -/
abbrev c2Mem (I : ExecutionEnv) (out1 : ByteArray) : ByteArray :=
  feDepositBlocks.feDeposit_block_695_memory (mem := c2Base I out1)

theorem c2_facts {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    {out1 : ByteArray} (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size) :
    ArgsKept I (c2Base I out1) ∧ ArgsKept I (c2Mem I out1) ∧
    (c2Mem I out1).extract 352 384 = ByteArray.zeroes 32 := by
  have hb : ArgsKept I (c2Base I out1) :=
    (c1Mem_kept hok hargs hl0 hl1 hl2).out hob hsz (by decide)
  have hm : ArgsKept I (c2Mem I out1) :=
    (hb.word _ (d := (UInt256.ofNat 320).toNat) (by decide)).word _
      (d := (UInt256.ofNat 352).toNat) (by decide)
  refine ⟨hb, hm, ?_⟩
  have hs := hm.1
  unfold c2Mem feDepositBlocks.feDeposit_block_695_memory at hs ⊢
  rw [show (UInt256.ofNat 352).toNat = 352 from rfl] at hs ⊢
  rw [show (384 : ℕ) = 352 + 32 from rfl, ← readWithPadding_eq_extract _ 352 (by omega),
    toByteArray_write_read_back_of_gap _ _ 352 (small_gap _ _ (by decide)),
    zero_toByteArray_eq_zeroes32]

/-- The bytecode's SSZ chunk of the gwei amount (block 695's byte swap), on its own operand order. -/
abbrev c2Chunk (x1 : UInt256) : UInt256 :=
  (UInt256.shiftLeft (UInt256.lor (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32)) (UInt256.shiftLeft (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32))) (UInt256.ofNat 192))

/-- Statement 9: `signature_left = sha256_64(signature[0:64])`. -/
abbrev c2Stmt : Stmt :=
  .internalCall "sha256_64" [.bytesSlice (.var "signature") (.intLit 0) (.intLit 64)] "signature_left"

/-- The stack at pc 813 (after call 2's checks). -/
abbrev c2Stack (I : ExecutionEnv) (out1 : ByteArray) : List UInt256 :=
  [rFp (hMem2 I) + UInt256.ofNat 32, c2Chunk (UInt256.div I.weiValue (UInt256.ofNat 1000000000)),
   memLoad (UInt256.ofNat 256) (c2Base I out1), memLoad (rFp (hMem1 I) + UInt256.ofNat 32) (c2Base I out1),
   rAlloc I (hPos I 2), rAlloc I (hPos I 1), rFp entryMem, rFp (hMem2 I), rAlloc I (hPos I 0),
   rFp (hMem1 I)]

theorem c2Chunk_eq (x : UInt256) : c2Chunk x = u64ChunkWord x := by
  unfold c2Chunk
  rw [u256_lor_comm (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 71777214294589695))
    (UInt256.ofNat 8))]
  exact evmChunk_eq x

/-- The 64 bytes block 695 hands to call 2 are the signature's first two words. -/
theorem c2Payload {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    {out1 : ByteArray} (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size) :
    (c2Mem I out1).readWithPadding (rFp (hMem2 I) + UInt256.ofNat 32).toNat (UInt256.ofNat 64).toNat =
      (dPayload I.calldata (dWord I.calldata 64)).extract 0 64 := by
  obtain ⟨_, hfp2, _, _, _, _, hsig⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  obtain ⟨_, ⟨ms, mx⟩, _⟩ := c2_facts hok hargs hl0 hl1 hl2 hob hsz
  rw [hfp2, show (UInt256.ofNat 608 + UInt256.ofNat 32).toNat = 640 by decide,
    show (UInt256.ofNat 64).toNat = 64 from rfl,
    readWithPadding_eq_extract' _ 640 64 (by decide) (by decide) (by omega),
    show 640 + 64 = 704 from rfl, mx 640 704 (by decide) (by decide) (by decide), ← hsig, extract_extract_BA]
  rfl

/-- **Call 2.**  From pc 695 (after call 1), both sides revert or the EVM reaches pc 813 with the
    digest at `0x140` while `signature_left` binds it. -/
theorem call2 {σ σ₀ A I} {g : UInt256} {σ1 : AccountMap} {evm : EVM.State} {L : Store}
    {aw : UInt256} {out1 : ByteArray} {k C : Nat}
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size)
    (hsig : L.get? "signature" = some (.bytes (dPayload I.calldata (dWord I.calldata 64))))
    (hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ1 evm)
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 695) (fStack I) (c2Base I out1) aw out1 σ1 k C) :
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecStmt config (pFrame L) evm c2Stmt .reverted) ∨
    (∃ (evm' : EVM.State) (σ' : AccountMap) (out2 : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out2.size ∧ out2.size < UInt256.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 813) (c2Stack I out1)
        (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 320) (UInt256.ofNat 32))
        aw' out2 σ' k' C' ∧
      ExecStmt config (pFrame L) evm c2Stmt
        (.ok (pFrame (L.insert "signature_left" (shaDigest out2))) evm')) := by
  have hs96 : (dPayload I.calldata (dWord I.calldata 64)).size = 96 := by
    rw [dPayload_size _ _ hargs.2.2.2.2]; exact hl2
  have he := evalSigLeftPayload (cfg := config) (stele := pFrame L) (evm := evm) hsig hs96
  have r1 := feDepositBlocks.feDeposit_block_695 (by simp) rd
  obtain ⟨evm', σ', z, out, aw', k', C', hcall, hs', r2, hob2⟩ :=
    staticCallBridge r1 hs (by native_decide) (by simp)
  rw [c2Payload hok hargs hl0 hl1 hl2 hob hsz, ← precompile2_eq] at hcall
  rd_checked r2 z out as hrev hsz2 to 813
  · exact Or.inl ⟨hrev, sha64Call_revert rfl he hcall hsz2⟩
  · exact Or.inr ⟨evm', σ', out, aw', _, _, hsz2, hob2, hs', r2, sha64Call_ok rfl he hcall hsz2⟩

end FeProofs.Deposit
