import FeProofs.Deposit.DepositHashStele
import FeProofs.Deposit.DepositLayout
import FeProofs.Deposit.DepositPrefix
import FeProofs.Deposit.CtorLoop

/-!
# FeDeposit `deposit()` hashing, calls 4–7 (pc 874 → 1026)

From the second signature hash on, every digest is a `sha256_pair` over a 64-byte scratch pair:
the signature pair at `0x260` (call 4: `left ‖ right`) and the merkleization pair at `0x2a0`
(calls 5–7).  Each call writes its digest over the pair's first word, which the next block reads.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## Scratch-pair memory -/

/-- Two stores at `s` and `s + 32` make `[s, s + 64)` the pair payload. -/
theorem pairAt_read (a b : UInt256) (mem : ByteArray) (s t : UInt256)
    (ht : t.toNat = s.toNat + 32) (hs : s.toNat ≤ mem.size) :
    (b.toByteArray.write 0 (a.toByteArray.write 0 mem s.toNat 32) t.toNat 32).readWithPadding
      s.toNat (UInt256.ofNat 64).toNat = pairPayload a b := by
  have hw : 32 ≤ a.toByteArray.size := by rw [toByteArray_size]
  have hwb : 32 ≤ b.toByteArray.size := by rw [toByteArray_size]
  rw [ht, show (UInt256.ofNat 64).toNat = 64 from rfl]
  have hAsz := write32_size_ge a.toByteArray mem s.toNat hw hs
  have hA0 : (a.toByteArray.write 0 mem s.toNat 32).extract s.toNat (s.toNat + 32) =
      a.toByteArray := by
    rw [← readWithPadding_eq_extract _ s.toNat hAsz, write32_read_back _ _ s.toNat hw hs,
      toByteArray_extract_all]
  generalize a.toByteArray.write 0 mem s.toNat 32 = A at hAsz hA0
  have hB := write32_size_ge b.toByteArray A (s.toNat + 32) hwb hAsz
  have hX : (A.extract 0 (s.toNat + 32)).size = s.toNat + 32 := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract' _ s.toNat 64 (by decide) (by decide) (by omega),
    write32_eq _ _ (s.toNat + 32) hwb hAsz,
    extract_append_left _ _ s.toNat (s.toNat + 64) (by
      rw [ByteArray.size_append, hX, ByteArray.size_extract, toByteArray_size]; omega),
    extract_append_span _ _ s.toNat (s.toNat + 64) (by rw [hX]; omega) (by rw [hX]; omega), hX,
    extract_extract_BA, show 0 + s.toNat = s.toNat from Nat.zero_add _,
    show min (0 + (s.toNat + 32)) (s.toNat + 32) = s.toNat + 32 by omega,
    show s.toNat + 64 - (s.toNat + 32) = 32 by omega, hA0, pairPayload_eq]
  simp only [toByteArray_extract_all]

theorem pairAt_size (a b : UInt256) (mem : ByteArray) (s t : UInt256)
    (ht : t.toNat = s.toNat + 32) (hs : s.toNat ≤ mem.size) :
    s.toNat + 64 ≤ (b.toByteArray.write 0 (a.toByteArray.write 0 mem s.toNat 32) t.toNat 32).size := by
  have hw : 32 ≤ a.toByteArray.size := by rw [toByteArray_size]
  have hwb : 32 ≤ b.toByteArray.size := by rw [toByteArray_size]
  have hAsz := write32_size_ge a.toByteArray mem s.toNat hw hs
  rw [ht]
  have := write32_size_ge b.toByteArray (a.toByteArray.write 0 mem s.toNat 32) (s.toNat + 32) hwb hAsz
  omega

/-! ## The segment -/

abbrev hL12 (L : Store) (o4 : ByteArray) : Store := L.insert "signature_root" (shaDigest o4)
abbrev hL13 (L : Store) (o4 wc : ByteArray) : Store :=
  (hL12 L o4).insert "credentials" (.int (Int.ofNat (calldataWord wc 0).toNat))
abbrev hL14 (L : Store) (o4 wc : ByteArray) (m : UInt256) : Store :=
  (hL13 L o4 wc).insert "amount_chunk" (.int (Int.ofNat (u64ChunkWord m).toNat))
abbrev hL15 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 : ByteArray) : Store :=
  (hL14 L o4 wc m).insert "left" (shaDigest o5)
abbrev hL16 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 o6 : ByteArray) : Store :=
  (hL15 L o4 wc m o5).insert "right" (shaDigest o6)
abbrev hL17 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 o6 o7 : ByteArray) : Store :=
  (hL16 L o4 wc m o5 o6).insert "node" (shaDigest o7)

/-- Memory after call 4 (its digest over the signature pair at `0x260`). -/
abbrev hM4 (mem : ByteArray) (l r : UInt256) (o4 : ByteArray) : ByteArray :=
  callOutputMem (r.toByteArray.write 0 (l.toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32)
    (UInt256.ofNat 640).toNat 32) o4 (UInt256.ofNat 608) (UInt256.ofNat 32)

/-- The merkleization pair's allocation: `0x40 := 0x2e0`. -/
abbrev hBase5 (M4 : ByteArray) : ByteArray :=
  (UInt256.ofNat 672 + UInt256.ofNat 64).toByteArray.write 0 M4 (UInt256.ofNat 64).toNat 32

theorem depositBody_drop11 :
    depositTransition.body.drop 11 =
      .internalCall "sha256_pair" [.var "signature_left", .var "signature_right"] "signature_root" ::
      .letDecl "credentials" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.abiDecode (.elem (.int (.uint ⟨256, by decide⟩))) (.var "withdrawal_credentials")) ::
      .internalCall "u64_chunk" [.var "amount"] "amount_chunk" ::
      .internalCall "sha256_pair" [.var "pubkey_root", .var "credentials"] "left" ::
      .internalCall "sha256_pair" [.var "amount_chunk", .var "signature_root"] "right" ::
      .internalCall "sha256_pair" [.var "left", .var "right"] "node" ::
      depositTransition.body.drop 17 := rfl

/-- **Calls 4–7.**  From the signature pair at `0x260` (holding `signature_left ‖ ·`, with
    `signature_right` at its first word) to the node at pc 1026: the EVM either reverts, or reaches
    pc 1026 with the node pointer `0x2a0` on top while the spec has run statements 11–16. -/
theorem depositHash_874 {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {evm : EVM.State} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {L : Store} {o1 o2 o3 wc : ByteArray} {m : UInt256} (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 874)
      (calldataWord o2 0 :: UInt256.ofNat 640 :: UInt256.ofNat 608 :: u64ChunkWord m ::
        calldataWord o1 0 :: calldataWord wc 0 :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hright : memLoad (UInt256.ofNat 608) mem = calldataWord o3 0)
    (hfp : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 672) (hsize : 672 ≤ mem.size)
    (hsl : L.get? "signature_left" = some (shaDigest o2))
    (hsr : L.get? "signature_right" = some (shaDigest o3))
    (hpk : L.get? "pubkey_root" = some (shaDigest o1))
    (hwc : L.get? "withdrawal_credentials" = some (.bytes wc)) (hwcsz : wc.size = 32)
    (ham : L.get? "amount" = some (.int (Int.ofNat m.toNat))) :
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o4 o5 o6 o7 mem' rdata' : ByteArray) (aw' : UInt256)
        (k' C' : ℕ),
      RD feDepositBytecode I g s0 (UInt256.ofNat 1026) (UInt256.ofNat 672 :: u64ChunkWord m :: R)
        mem' aw' rdata' σ' k' C' ∧
      memLoad (UInt256.ofNat 672) mem' = calldataWord o7 0 ∧
      SourceState s0 I σ' evm' ∧
      ∀ res, ExecBlock config (pFrame (hL17 L o4 wc m o5 o6 o7)) evm' (depositTransition.body.drop 17) res →
        ExecBlock config (pFrame L) evm (depositTransition.body.drop 11) res) ∨
    (RDrev feDepositBytecode g s0 ∧
      ExecBlock config (pFrame L) evm (depositTransition.body.drop 11) .reverted) := by
  rw [depositBody_drop11]
  -- call 4: signature_root = sha256(signature_left ‖ signature_right) over the pair at 0x260
  have h608 : (UInt256.ofNat 608).toNat = 608 := rfl
  have h640 : (UInt256.ofNat 640).toNat = 640 := rfl
  have h672 : (UInt256.ofNat 672).toNat = 672 := rfl
  have r891 := feDepositBlocks.feDeposit_block_874 (by simp; omega) rd
  simp only [feDepositBlocks.feDeposit_block_874_stack, feDepositBlocks.feDeposit_block_874_memory, hright] at r891
  have hp4 := pairAt_size (calldataWord o2 0) (calldataWord o3 0) mem (UInt256.ofNat 608)
    (UInt256.ofNat 640) (by decide) (by omega)
  have hfp4 := memLoad64_write (calldataWord o3 0).toByteArray
    ((calldataWord o2 0).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32)
    (srcOff := 0) (dest := (UInt256.ofNat 640).toNat) (len := 32) (by decide)
    (by rw [toByteArray_size]) (gapSmall (by decide)) (by decide)
    (le_trans (by omega) (write_size_ge _ mem (dest := (UInt256.ofNat 608).toNat)
      (by decide) (by rw [toByteArray_size]) (gapSmall (by decide))))
  rw [memLoad64_write _ mem (by decide) (by rw [toByteArray_size]) (gapSmall (by decide)) (by decide)
    (by omega), hfp] at hfp4
  obtain ⟨ev4, σ4, z4, o4, aw4, k4, C4, hc4, hs4, r892, hb4⟩ :=
    staticCallBridge r891 hs (by native_decide) (by simp; omega)
  rw [pairAt_read _ _ mem (UInt256.ofNat 608) (UInt256.ofNat 640) (by decide)
    (by omega), ← precompile2_eq] at hc4
  rd_checked r892 z4 o4 as hrev hout4 to 908
  · exact Or.inr ⟨hrev, ExecBlock.consRevert (shaPairCall_revert (caller := pFrame L) rfl (ret := "signature_root")
      (evalVarF hsl) (evalVarF hsr) hc4 hout4)⟩
  have hl4 := callOutput_loadAt ((calldataWord o3 0).toByteArray.write 0
    ((calldataWord o2 0).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32) (UInt256.ofNat 640).toNat 32) o4 (UInt256.ofNat 608) hb4 hout4 (by omega)
  have hf4 := callOutput_memLoad64 ((calldataWord o3 0).toByteArray.write 0
    ((calldataWord o2 0).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32) (UInt256.ofNat 640).toNat 32) o4 (UInt256.ofNat 608) hb4 hout4 (by decide) (by omega)
  rw [hfp4] at hf4
  have hsz4 := callOutput_sizeAt ((calldataWord o3 0).toByteArray.write 0
    ((calldataWord o2 0).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32) (UInt256.ofNat 640).toNat 32) o4 (UInt256.ofNat 608) hb4 (by omega)
  have hs11 := shaPairCall_ok (caller := pFrame L) rfl (ret := "signature_root") (evalVarF hsl)
    (evalVarF hsr) hc4 hout4
  have hs12 := ExecStmt.letDecl (cfg := config) (stele := pFrame (hL12 L o4)) (evm := ev4)
    (name := "credentials") (ty := some (.elem (.int (.uint ⟨256, by decide⟩))))
    (evalCredentials (by store_get; exact hwc) hwcsz)
  have hs13 := u64ChunkCall (caller := pFrame (hL13 L o4 wc)) (evm := ev4) rfl
    (by store_get; exact ham)
  -- call 5: left = sha256(pubkey_root ‖ credentials) over the merkleization pair at 0x2a0
  have r939 := feDepositBlocks.feDeposit_block_908 (by simp; omega) r892
  simp only [feDepositBlocks.feDeposit_block_908_stack, feDepositBlocks.feDeposit_block_908_memory, hl4, hf4] at r939
  have hb5base : (hM4 mem (calldataWord o2 0) (calldataWord o3 0) o4).size ≤
      (hBase5 (hM4 mem (calldataWord o2 0) (calldataWord o3 0) o4)).size :=
    write_size_ge (UInt256.ofNat 672 + UInt256.ofNat 64).toByteArray
    (callOutputMem ((calldataWord o3 0).toByteArray.write 0
    ((calldataWord o2 0).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32) (UInt256.ofNat 640).toNat 32)
    o4 (UInt256.ofNat 608) (UInt256.ofNat 32)) (srcOff := 0) (dest := (UInt256.ofNat 64).toNat) (len := 32) (by decide)
    (by rw [toByteArray_size]) (gapSmall (by decide))
  have hbase5 : (UInt256.ofNat 672).toNat ≤
      (hBase5 (hM4 mem (calldataWord o2 0) (calldataWord o3 0) o4)).size := by
    have : (hM4 mem (calldataWord o2 0) (calldataWord o3 0) o4).size = _ := hsz4
    omega
  have hp5 := pairAt_size (calldataWord o1 0) (calldataWord wc 0) _ (UInt256.ofNat 672)
    (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide) hbase5
  obtain ⟨ev5, σ5, z5, o5, aw5, k5, C5, hc5, hs5, r940, hb5⟩ :=
    staticCallBridge r939 hs4 (by native_decide) (by simp; omega)
  rw [pairAt_read _ _ _ (UInt256.ofNat 672) (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide)
    hbase5, ← precompile2_eq] at hc5
  have hs14rev := fun (hbad : ¬ (z5 = true ∧ 32 ≤ o5.size)) =>
    shaPairCall_revert (caller := pFrame (hL14 L o4 wc m)) (evm := ev4) rfl (ret := "left")
      (ea := .var "pubkey_root") (eb := .var "credentials") (a := calldataWord o1 0) (b := calldataWord wc 0)
      (evalVarF (by store_get; exact hpk))
      (evalVarF (by store_get)) hc5 hbad
  rd_checked r940 z5 o5 as hrev hout5 to 956
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consRevert (hs14rev hout5)⟩
  have hs14 := shaPairCall_ok (caller := pFrame (hL14 L o4 wc m)) (evm := ev4) rfl (ret := "left")
    (ea := .var "pubkey_root") (eb := .var "credentials") (a := calldataWord o1 0) (b := calldataWord wc 0)
    (evalVarF (by store_get; exact hpk))
    (evalVarF (by store_get)) hc5 hout5
  have hin5 := le_trans (Nat.add_le_add_left (show 32 ≤ 64 by decide) _) hp5
  have hl5 := callOutput_loadAt _ o5 (UInt256.ofNat 672) hb5 hout5 hin5
  have hsz5 := callOutput_sizeAt _ o5 (UInt256.ofNat 672) hb5 hin5
  -- call 6: right = sha256(amount_chunk ‖ signature_root)
  have r974 := feDepositBlocks.feDeposit_block_956 (by simp; omega) r940
  simp only [feDepositBlocks.feDeposit_block_956_stack, feDepositBlocks.feDeposit_block_956_memory, hl5] at r974
  have hbase6 := le_of_le_of_eq (le_trans (Nat.le_add_right _ 64) hp5) hsz5.symm
  have hp6 := pairAt_size (u64ChunkWord m) (calldataWord o4 0) _ (UInt256.ofNat 672)
    (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide) hbase6
  obtain ⟨ev6, σ6, z6, o6, aw6, k6, C6, hc6, hs6, r975, hb6⟩ :=
    staticCallBridge r974 hs5 (by native_decide) (by simp; omega)
  rw [pairAt_read _ _ _ (UInt256.ofNat 672) (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide)
    hbase6, ← precompile2_eq] at hc6
  have hs15rev := fun (hbad : ¬ (z6 = true ∧ 32 ≤ o6.size)) =>
    shaPairCall_revert (caller := pFrame (hL15 L o4 wc m o5)) (evm := ev5) rfl (ret := "right")
      (ea := .var "amount_chunk") (eb := .var "signature_root") (a := u64ChunkWord m) (b := calldataWord o4 0)
      (evalVarF (by store_get))
      (evalVarF (by store_get)) hc6 hbad
  rd_checked r975 z6 o6 as hrev hout6 to 991
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consRevert (hs15rev hout6)⟩
  have hs15 := shaPairCall_ok (caller := pFrame (hL15 L o4 wc m o5)) (evm := ev5) rfl (ret := "right")
    (ea := .var "amount_chunk") (eb := .var "signature_root") (a := u64ChunkWord m) (b := calldataWord o4 0)
    (evalVarF (by store_get))
    (evalVarF (by store_get)) hc6 hout6
  have hin6 := le_trans (Nat.add_le_add_left (show 32 ≤ 64 by decide) _) hp6
  have hl6 := callOutput_loadAt _ o6 (UInt256.ofNat 672) hb6 hout6 hin6
  have hsz6 := callOutput_sizeAt _ o6 (UInt256.ofNat 672) hb6 hin6
  -- call 7: node = sha256(left ‖ right)
  have r1009 := feDepositBlocks.feDeposit_block_991 (by simp; omega) r975
  simp only [feDepositBlocks.feDeposit_block_991_stack, feDepositBlocks.feDeposit_block_991_memory, hl6] at r1009
  have hbase7 := le_of_le_of_eq (le_trans (Nat.le_add_right _ 64) hp6) hsz6.symm
  have hp7 := pairAt_size (calldataWord o5 0) (calldataWord o6 0) _ (UInt256.ofNat 672)
    (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide) hbase7
  obtain ⟨ev7, σ7, z7, o7, aw7, k7, C7, hc7, hs7, r1010, hb7⟩ :=
    staticCallBridge r1009 hs6 (by native_decide) (by simp; omega)
  rw [pairAt_read _ _ _ (UInt256.ofNat 672) (UInt256.ofNat 672 + UInt256.ofNat 32) (by decide)
    hbase7, ← precompile2_eq] at hc7
  have hs16rev := fun (hbad : ¬ (z7 = true ∧ 32 ≤ o7.size)) =>
    shaPairCall_revert (caller := pFrame (hL16 L o4 wc m o5 o6)) (evm := ev6) rfl (ret := "node")
      (ea := .var "left") (eb := .var "right") (a := calldataWord o5 0) (b := calldataWord o6 0)
      (evalVarF (by store_get))
      (evalVarF (store_get_self _ _ _)) hc7 hbad
  rd_checked r1010 z7 o7 as hrev hout7 to 1026
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consNormal hs15 <|
      ExecBlock.consRevert (hs16rev hout7)⟩
  have hs16 := shaPairCall_ok (caller := pFrame (hL16 L o4 wc m o5 o6)) (evm := ev6) rfl (ret := "node")
    (ea := .var "left") (eb := .var "right") (a := calldataWord o5 0) (b := calldataWord o6 0)
    (evalVarF (by store_get))
    (evalVarF (store_get_self _ _ _)) hc7 hout7
  have hin7 := le_trans (Nat.add_le_add_left (show 32 ≤ 64 by decide) _) hp7
  have hl7 := callOutput_loadAt _ o7 (UInt256.ofNat 672) hb7 hout7 hin7
  exact Or.inl ⟨σ7, ev7, o4, o5, o6, o7, _, _, _, _, _, r1010, hl7, hs7, fun res h =>
    ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consNormal hs15 <| ExecBlock.consNormal hs16 h⟩

end FeProofs.Deposit
