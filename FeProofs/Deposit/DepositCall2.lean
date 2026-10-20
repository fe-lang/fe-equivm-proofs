import FeProofs.Deposit.DepositCall1

/-!
# FeDeposit `deposit`: the signature calls (pc 715 → 874, statements 9 and 10)

Memory bookkeeping for the signature hashes: every write after the decoder lies outside the
signature payload window `[0x1c0, 0x220)`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- A 32-byte word write leaves a window it does not overlap unchanged. -/
theorem wordWrite_extract (w : UInt256) (base : ByteArray) {dest i j : Nat} (hij : i ≤ j)
    (hj : j ≤ base.size) (hd : j ≤ dest ∨ (dest + 32 ≤ i ∧ dest ≤ base.size))
    (hgap : dest < 2 ^ 32) :
    (w.toByteArray.write 0 base dest 32).extract i j = base.extract i j := by
  rcases hd with hd | ⟨hd, hb⟩
  · exact write_extract_below _ _ (by decide) (by rw [toByteArray_size]) (small_gap _ _ hgap) hij hj hd
  · exact write_extract_preserved _ _ (by decide) (by rw [toByteArray_size]) hb hij hj (Or.inr hd)

theorem wordWrite_size (w : UInt256) (base : ByteArray) {dest : Nat} (hgap : dest < 2 ^ 32) :
    base.size ≤ (w.toByteArray.write 0 base dest 32).size :=
  write_size_ge _ _ (by decide) (by rw [toByteArray_size]) (small_gap _ _ hgap)

theorem out32_len (out : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size) :
    (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = 32 := by
  have h := callOutputLen32 hob
  rw [Nat.min_eq_left hsz] at h
  exact h

/-- A returned word copied to `off` leaves a window it does not overlap unchanged. -/
theorem out32_extract (out base : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size)
    {off : UInt256} {i j : Nat} (hij : i ≤ j) (hj : j ≤ base.size)
    (hd : j ≤ off.toNat ∨ (off.toNat + 32 ≤ i ∧ off.toNat ≤ base.size)) (hgap : off.toNat < 2 ^ 32) :
    (callOutputMem base out off (UInt256.ofNat 32)).extract i j = base.extract i j := by
  unfold callOutputMem
  rw [out32_len out hob hsz]
  rcases hd with hd | ⟨hd, hb⟩
  · exact write_extract_below _ _ (by decide) (by omega) (small_gap _ _ hgap) hij hj hd
  · exact write_extract_preserved _ _ (by decide) (by omega) hb hij hj (Or.inr hd)

theorem out32_size (out base : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size)
    {off : UInt256} (hgap : off.toNat < 2 ^ 32) :
    base.size ≤ (callOutputMem base out off (UInt256.ofNat 32)).size := by
  unfold callOutputMem
  rw [out32_len out hob hsz]
  exact write_size_ge _ _ (by decide) (by omega) (small_gap _ _ hgap)

set_option maxHeartbeats 2000000 in
/-- After block 650's writes: extent, the untouched signature window, and the bumped free
    pointer `0x260`. -/
theorem c1Mem_facts {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96) :
    608 ≤ (c1Mem I).size ∧
      (∀ i j, 96 ≤ i → i ≤ j → j ≤ 544 → (c1Mem I).extract i j = (hMem3 I).extract i j) ∧
      (c1Mem I).extract 64 96 = (UInt256.ofNat 608).toByteArray := by
  obtain ⟨_, _, hload3, hsz3, _, _, _⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  unfold c1Mem feDepositBlocks.feDeposit_block_650_memory
  rw [hload3, show (UInt256.ofNat 544).toNat = 544 from rfl,
    show (UInt256.ofNat 544 + UInt256.ofNat 32).toNat = 576 by decide]
  have s0 := wordWrite_size (UInt256.ofNat 544 + UInt256.ofNat 64) (hMem3 I)
    (dest := (UInt256.ofNat 64).toNat) (by decide)
  have s1 := toByteArray_write_size_ge_off_add32 (memLoad (rFp ByteArray.empty + UInt256.ofNat 32) (hMem3 I))
    ((UInt256.ofNat 544 + UInt256.ofNat 64).toByteArray.write 0 (hMem3 I) (UInt256.ofNat 64).toNat 32) 544
    (small_gap _ _ (by decide))
  have s2 := toByteArray_write_size_ge_off_add32
    (UInt256.shiftLeft (UInt256.shiftRight (memLoad ((rFp ByteArray.empty + UInt256.ofNat 32) +
      UInt256.ofNat 32) (hMem3 I)) (UInt256.ofNat 128)) (UInt256.ofNat 128))
    ((memLoad (rFp ByteArray.empty + UInt256.ofNat 32) (hMem3 I)).toByteArray.write 0
      ((UInt256.ofNat 544 + UInt256.ofNat 64).toByteArray.write 0 (hMem3 I) (UInt256.ofNat 64).toNat 32)
      544 32) 576 (small_gap _ _ (by decide))
  refine ⟨by omega, fun i j hi hij hj => ?_, ?_⟩
  · rw [wordWrite_extract _ _ hij (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ hij (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ hij (by omega) (Or.inr ⟨by show 96 ≤ i; omega, by
        show 64 ≤ (hMem3 I).size; omega⟩) (by decide)]
  · rw [wordWrite_extract _ _ (by omega) (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ (by omega) (by omega) (Or.inl (by omega)) (by decide),
      fpWord_extract]
    rfl

/-- Memory after call 1's digest is copied to `0x220`. -/
abbrev c2Base (I : ExecutionEnv) (out1 : ByteArray) : ByteArray :=
  callOutputMem (c1Mem I) out1 (UInt256.ofNat 544) (UInt256.ofNat 32)

/-- Memory after block 715's scratch allocation at `0x260`. -/
abbrev c2Mem (I : ExecutionEnv) (out1 : ByteArray) : ByteArray :=
  feDepositBlocks.feDeposit_block_715_memory (mem := c2Base I out1)

set_option maxHeartbeats 2000000 in
theorem c2_facts {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    {out1 : ByteArray} (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size) :
    memLoad (UInt256.ofNat 64) (c2Base I out1) = UInt256.ofNat 608 ∧
    672 ≤ (c2Mem I out1).size ∧
    (∀ i j, 96 ≤ i → i ≤ j → j ≤ 544 → (c2Mem I out1).extract i j = (hMem3 I).extract i j) ∧
    (c2Mem I out1).extract 64 96 = (UInt256.ofNat 672).toByteArray ∧
    (c2Mem I out1).extract 640 672 = ByteArray.zeroes 32 := by
  obtain ⟨cs, cx, cf⟩ := c1Mem_facts hok hargs hl0 hl1 hl2
  have bs0 := out32_size out1 (c1Mem I) hob hsz (off := UInt256.ofNat 544) (by decide)
  have bs : 608 ≤ (c2Base I out1).size := le_trans cs bs0
  have bx : ∀ i j, i ≤ j → j ≤ 544 → (c2Base I out1).extract i j = (c1Mem I).extract i j :=
    fun i j hij hj => out32_extract out1 (c1Mem I) hob hsz hij (by omega) (Or.inl (by
      show j ≤ 544; omega)) (by decide)
  have bf : (c2Base I out1).extract 64 96 = (UInt256.ofNat 608).toByteArray := by
    rw [out32_extract out1 (c1Mem I) hob hsz (by omega) (by omega) (Or.inl (by decide)) (by decide), cf]
  have bl : memLoad (UInt256.ofNat 64) (c2Base I out1) = UInt256.ofNat 608 := by
    refine Reasoning.VyperCalls.memLoad_of_read _ 64 _ (by decide) (by omega) ?_
    rw [readWithPadding_eq_extract _ 64 (by omega), bf]
  refine ⟨bl, ?_⟩
  unfold c2Mem feDepositBlocks.feDeposit_block_715_memory
  rw [bl, show (UInt256.ofNat 608).toNat = 608 from rfl,
    show (UInt256.ofNat 608 + UInt256.ofNat 32).toNat = 640 by decide]
  have m0 := wordWrite_size (UInt256.ofNat 608 + UInt256.ofNat 64) (c2Base I out1)
    (dest := (UInt256.ofNat 64).toNat) (by decide)
  have m1 := toByteArray_write_size_ge_off_add32 (⟨0⟩ : UInt256)
    ((UInt256.ofNat 608 + UInt256.ofNat 64).toByteArray.write 0 (c2Base I out1) (UInt256.ofNat 64).toNat 32)
    608 (small_gap _ _ (by decide))
  have m2 := toByteArray_write_size_ge_off_add32 (⟨0⟩ : UInt256)
    ((⟨0⟩ : UInt256).toByteArray.write 0
      ((UInt256.ofNat 608 + UInt256.ofNat 64).toByteArray.write 0 (c2Base I out1) (UInt256.ofNat 64).toNat 32)
      608 32) 640 (small_gap _ _ (by decide))
  refine ⟨by omega, fun i j hi hij hj => ?_, ?_, ?_⟩
  · rw [wordWrite_extract _ _ hij (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ hij (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ hij (by omega) (Or.inr ⟨by show 96 ≤ i; omega, by
        show 64 ≤ (c2Base I out1).size; omega⟩) (by decide), bx i j hij hj, cx i j hi hij hj]
  · rw [wordWrite_extract _ _ (by omega) (by omega) (Or.inl (by omega)) (by decide),
      wordWrite_extract _ _ (by omega) (by omega) (Or.inl (by omega)) (by decide),
      fpWord_extract]
    rfl
  · rw [show (672 : ℕ) = 640 + 32 from rfl, ← readWithPadding_eq_extract _ 640 m2,
      toByteArray_write_read_back_of_gap _ _ 640 (small_gap _ _ (by decide)),
      zero_toByteArray_eq_zeroes32]

/-- The bytecode's SSZ chunk of the gwei amount (block 715's byte swap), on its own operand order. -/
abbrev c2Chunk (x1 : UInt256) : UInt256 :=
  (UInt256.shiftLeft (UInt256.lor (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32)) (UInt256.shiftLeft (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x1 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x1 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32))) (UInt256.ofNat 192))

/-- Statement 9: `signature_left = sha256_64(signature[0:64])`. -/
abbrev c2Stmt : Stmt :=
  .internalCall "sha256_64" [.bytesSlice (.var "signature") (.intLit 0) (.intLit 64)] "signature_left"

/-- The stack at pc 838 (after call 2's checks). -/
abbrev c2Stack (I : ExecutionEnv) (out1 : ByteArray) : List UInt256 :=
  [rFp (hMem2 I) + UInt256.ofNat 32, memLoad (UInt256.ofNat 64) (c2Base I out1) + UInt256.ofNat 32,
   memLoad (UInt256.ofNat 64) (c2Base I out1), c2Chunk (UInt256.div I.weiValue (UInt256.ofNat 1000000000)),
   memLoad (UInt256.ofNat 544) (c2Base I out1), memLoad (rFp (hMem1 I) + UInt256.ofNat 32) (c2Base I out1),
   rAlloc I (hPos I 2), rAlloc I (hPos I 1), rFp ByteArray.empty, rFp (hMem2 I), rAlloc I (hPos I 0),
   rFp (hMem1 I)]

theorem c2Chunk_eq (x : UInt256) : c2Chunk x = u64ChunkWord x := by
  unfold c2Chunk
  rw [u256_lor_comm (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 71777214294589695))
    (UInt256.ofNat 8))]
  exact evmChunk_eq x

set_option maxHeartbeats 2000000 in
/-- The 64 bytes block 715 hands to call 2 are the signature's first two words. -/
theorem c2Payload {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    {out1 : ByteArray} (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size) :
    (c2Mem I out1).readWithPadding (rFp (hMem2 I) + UInt256.ofNat 32).toNat (UInt256.ofNat 64).toNat =
      (dPayload I.calldata (dWord I.calldata 64)).extract 0 64 := by
  obtain ⟨_, hfp2, _, _, _, _, hsig⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  obtain ⟨_, ms, mx, _⟩ := c2_facts hok hargs hl0 hl1 hl2 hob hsz
  rw [hfp2, show (UInt256.ofNat 416 + UInt256.ofNat 32).toNat = 448 by decide,
    show (UInt256.ofNat 64).toNat = 64 from rfl,
    readWithPadding_eq_extract' _ 448 64 (by decide) (by decide) (by omega),
    show 448 + 64 = 512 from rfl, mx 448 512 (by decide) (by decide) (by decide), ← hsig, extract_extract_BA]
  rfl

set_option maxHeartbeats 4000000 in
/-- **Call 2.**  From pc 715 (after call 1), both sides revert or the EVM reaches pc 838 with the
    digest at the scratch pair while `signature_left` binds it. -/
theorem call2 {σ σ₀ A I} {g : UInt256} {σ1 : AccountMap} {evm : EVM.State} {L : Store}
    {aw : UInt256} {out1 : ByteArray} {k C : Nat}
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)
    (hob : out1.size < UInt256.size) (hsz : 32 ≤ out1.size)
    (hsig : L.get? "signature" = some (.bytes (dPayload I.calldata (dWord I.calldata 64))))
    (hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ1 evm)
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 715) (memLoad (UInt256.ofNat 64) (hMem3 I) :: fStack I)
      (callOutputMem (c1Mem I) out1 (memLoad (UInt256.ofNat 64) (hMem3 I)) (UInt256.ofNat 32))
      aw out1 σ1 k C) :
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecStmt config (pFrame L) evm c2Stmt .reverted) ∨
    (∃ (evm' : EVM.State) (σ' : AccountMap) (out2 : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out2.size ∧ out2.size < UInt256.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 838) (c2Stack I out1)
        (callOutputMem (c2Mem I out1) out2 (memLoad (UInt256.ofNat 64) (c2Base I out1)) (UInt256.ofNat 32))
        aw' out2 σ' k' C' ∧
      ExecStmt config (pFrame L) evm c2Stmt
        (.ok (pFrame (L.insert "signature_left" (shaDigest out2))) evm')) := by
  obtain ⟨_, _, hload3, _, _, _, _⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  rw [hload3] at rd
  have hs96 : (dPayload I.calldata (dWord I.calldata 64)).size = 96 := by
    rw [dPayload_size _ _ hargs.2.2.2.2]; exact hl2
  have he := evalSigLeftPayload (cfg := config) (stele := pFrame L) (evm := evm) hsig hs96
  have r1 := feDepositBlocks.feDeposit_block_715 (by simp) rd
  obtain ⟨evm', σ', z, out, aw', k', C', hcall, hs', r2, hob2⟩ :=
    staticCallBridge r1 hs (by native_decide) (by simp)
  rw [c2Payload hok hargs hl0 hl1 hl2 hob hsz, ← precompile2_eq] at hcall
  cases z with
  | false =>
    have r3 := feDepositBlocks.feDeposit_block_822_taken (by simp) (by decide) (by jump_dest) r2
    exact Or.inl ⟨feDepositBlocks.feDeposit_block_2245
      (by simp [feDepositBlocks.feDeposit_block_822_taken_stack]) r3,
      sha64Call_revert rfl he hcall (by simp)⟩
  | true =>
    have r3 := feDepositBlocks.feDeposit_block_822_fallthrough (by simp) (by decide) r2
    simp only [feDepositBlocks.feDeposit_block_822_fallthrough_stack] at r3
    by_cases hsz2 : 32 ≤ out.size
    · have r4 := feDepositBlocks.feDeposit_block_827_fallthrough (by simp)
        (ult_zero (by rw [ulit_toNat' _ hob2, ulit_toNat' 32 (by decide)]; exact hsz2)) r3
      simp only [feDepositBlocks.feDeposit_block_827_fallthrough_stack] at r4
      exact Or.inr ⟨evm', σ', out, aw', _, _, hsz2, hob2, hs', r4, sha64Call_ok rfl he hcall hsz2⟩
    · have r4 := feDepositBlocks.feDeposit_block_827_taken (by simp)
        (by rw [ult_one (by rw [ulit_toNat' _ hob2, ulit_toNat' 32 (by decide)]; omega)]; decide)
        (by jump_dest) r3
      exact Or.inl ⟨feDepositBlocks.feDeposit_block_2245
        (by simp [feDepositBlocks.feDeposit_block_827_taken_stack]) r4,
        sha64Call_revert rfl he hcall (by simp; omega)⟩

end FeProofs.Deposit
