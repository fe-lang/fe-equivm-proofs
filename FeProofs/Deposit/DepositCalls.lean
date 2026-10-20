import FeProofs.Deposit.DepositCall2
import FeProofs.Deposit.DepositCall3

/-!
# FeDeposit `deposit`: calls 1–3 (pc 650 → 874, statements 8–10)

Chains `call1`, `call2` and `depositCall3` from the state `depositFront` leaves at pc 650 to the
`depositHash_874` entry state.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

theorem depositBody_drop8 :
    depositTransition.body.drop 8 = c1Stmt :: c2Stmt :: depositTransition.body.drop 10 := rfl

/-- The decoder's words below the hashing operands, unchanged from pc 650 to pc 1026. -/
abbrev c3Rest (I : ExecutionEnv) : List UInt256 :=
  [rAlloc I (hPos I 2), rAlloc I (hPos I 1), rFp ByteArray.empty, rFp (hMem2 I), rAlloc I (hPos I 0),
   rFp (hMem1 I)]

/-- The locals after statements 8–10. -/
abbrev c3Locals (cd : ByteArray) (evm : EVM.State) (o1 o2 o3 : ByteArray) : Store :=
  (((pLocals cd evm).insert "pubkey_root" (shaDigest o1)).insert "signature_left"
    (shaDigest o2)).insert "signature_right" (shaDigest o3)

set_option maxHeartbeats 4000000 in
/-- **Calls 1–3.**  From pc 650, both sides revert or the EVM reaches the `depositHash_874` entry
    state while statements 8–10 bind `pubkey_root`, `signature_left` and `signature_right`. -/
theorem calls123 {σ σ₀ A I} {g : UInt256} {aw : UInt256} {k C : Nat}
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hp : pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 650) (fStack I) (hMem3 I) aw ByteArray.empty σ k C) :
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) .reverted) ∨
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o1 o2 o3 mem : ByteArray) (aw' : UInt256) (k' C' : Nat),
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 874)
        (calldataWord o2 0 :: UInt256.ofNat 640 :: UInt256.ofNat 608 ::
          u64ChunkWord (UInt256.div I.weiValue (UInt256.ofNat 1000000000)) :: calldataWord o1 0 ::
          calldataWord (dPayload I.calldata (dWord I.calldata 32)) 0 :: c3Rest I) mem aw' o3 σ' k' C' ∧
      memLoad (UInt256.ofNat 608) mem = calldataWord o3 0 ∧
      memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 672 ∧ 672 ≤ mem.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      ∀ res, ExecBlock config
          (pFrame (c3Locals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3)) evm'
          (depositTransition.body.drop 11) res →
        ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) res) := by
  obtain ⟨hl0, hl1, hl2, -, -, -⟩ := hp
  obtain ⟨hfp1, hfp2, -, -, -, hwcL, hsigL⟩ := hMem3_layout hok hargs hl0 hl1 hl2
  have hpk : (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)).get? "pubkey" =
      some (.bytes (dPayload I.calldata (dWord I.calldata 0))) := by
    rw [store_get_ne2 _ _ _ (by decide) (by decide)]; exact dStore_pubkey _
  rcases call1 hok hargs hl0 hl1 hl2 hpk SourceState.init rd with
    ⟨hrev, hst⟩ | ⟨evm1, σ1, out1, aw1, k1, C1, hsz1, hob1, hs1, rd1, hst1⟩
  · exact Or.inl ⟨hrev, by rw [depositBody_drop8]; exact ExecBlock.consRevert hst⟩
  have hsig1 : ((pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)).insert "pubkey_root"
      (shaDigest out1)).get? "signature" = some (.bytes (dPayload I.calldata (dWord I.calldata 64))) := by
    rw [store_get_ne _ _ (by decide), store_get_ne2 _ _ _ (by decide) (by decide)]; exact dStore_sig _
  rcases call2 hok hargs hl0 hl1 hl2 hob1 hsz1 hsig1 hs1 rd1 with
    ⟨hrev, hst⟩ | ⟨evm2, σ2, out2, aw2, k2, C2, hsz2, hob2, hs2, rd2, hst2⟩
  · exact Or.inl ⟨hrev, by rw [depositBody_drop8]; exact ExecBlock.consNormal hst1 (ExecBlock.consRevert hst)⟩
  obtain ⟨bl, ms, mx, mf, mz⟩ := c2_facts hok hargs hl0 hl1 hl2 hob1 hsz1
  obtain ⟨cs, cx, -⟩ := c1Mem_facts hok hargs hl0 hl1 hl2
  have h608 : (UInt256.ofNat 608).toNat = 608 := rfl
  have bs : 608 ≤ (c2Base I out1).size :=
    le_trans cs (out32_size out1 (c1Mem I) hob1 hsz1 (off := UInt256.ofNat 544) (by decide))
  have hwcsz : (dPayload I.calldata (dWord I.calldata 32)).size = 32 := by
    rw [dPayload_size _ _ hargs.2.2.1.2]; exact hl1
  have hsigsz : (dPayload I.calldata (dWord I.calldata 64)).size = 96 := by
    rw [dPayload_size _ _ hargs.2.2.2.2]; exact hl2
  have h448 : rFp (hMem2 I) + UInt256.ofNat 32 = UInt256.ofNat 448 := by rw [hfp2]; decide
  have h640 : memLoad (UInt256.ofNat 64) (c2Base I out1) + UInt256.ofNat 32 = UInt256.ofNat 640 := by
    rw [bl]; decide
  have h544 : memLoad (UInt256.ofNat 544) (c2Base I out1) = calldataWord out1 0 :=
    callOutput_load (c1Mem I) out1 (UInt256.ofNat 544) hob1 hsz1 (by
      rw [show (UInt256.ofNat 544).toNat = 544 from rfl]; omega)
  have hwc : memLoad (rFp (hMem1 I) + UInt256.ofNat 32) (c2Base I out1) =
      calldataWord (dPayload I.calldata (dWord I.calldata 32)) 0 := by
    rw [hfp1, show UInt256.ofNat 352 + UInt256.ofNat 32 = UInt256.ofNat 384 by decide]
    refine Reasoning.VyperCalls.memLoad_of_read _ 384 _ (by decide) (by omega) ?_
    rw [readWithPadding_eq_extract _ 384 (by omega),
      calldataWord_bytes (out := dPayload I.calldata (dWord I.calldata 32)) (by omega), ← hwcL,
      out32_extract out1 (c1Mem I) hob1 hsz1 (by omega) (by omega) (Or.inl (by decide)) (by decide),
      cx 384 (384 + 32) (by omega) (by omega) (by omega), extract_extract_BA]
    rfl
  unfold c2Stack at rd2
  rw [h448, h640, bl, c2Chunk_eq, h544, hwc] at rd2
  have m3s : 672 ≤ (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 608) (UInt256.ofNat 32)).size :=
    le_trans ms (out32_size out2 (c2Mem I out1) hob2 hsz2 (off := UInt256.ofNat 608) (by decide))
  have hleft : memLoad (UInt256.ofNat 608)
      (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 608) (UInt256.ofNat 32)) = calldataWord out2 0 :=
    callOutput_load (c2Mem I out1) out2 (UInt256.ofNat 608) hob2 hsz2 (by omega)
  have hsigM : (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 608) (UInt256.ofNat 32)).extract 448 544 =
      dPayload I.calldata (dWord I.calldata 64) := by
    rw [out32_extract out2 (c2Mem I out1) hob2 hsz2 (by omega) (by omega) (Or.inl (by decide)) (by decide),
      mx 448 544 (by omega) (by omega) (by omega), hsigL]
  have hfp : memLoad (UInt256.ofNat 64)
      (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 608) (UInt256.ofNat 32)) = UInt256.ofNat 672 := by
    refine Reasoning.VyperCalls.memLoad_of_read _ 64 _ (by decide) (by omega) ?_
    rw [readWithPadding_eq_extract _ 64 (by omega),
      out32_extract out2 (c2Mem I out1) hob2 hsz2 (by omega) (by omega) (Or.inl (by decide)) (by decide), mf]
  have hzero : (callOutputMem (c2Mem I out1) out2 (UInt256.ofNat 608) (UInt256.ofNat 32)).extract 640 672 =
      ByteArray.zeroes 32 := by
    rw [out32_extract out2 (c2Mem I out1) hob2 hsz2 (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩)
      (by decide), mz]
  have hsig2 : (((pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)).insert "pubkey_root"
      (shaDigest out1)).insert "signature_left" (shaDigest out2)).get? "signature" =
      some (.bytes (dPayload I.calldata (dWord I.calldata 64))) := by
    rw [store_get_ne _ _ (by decide)]; exact hsig1
  rcases depositCall3 (by simp) rd2 hs2 hleft hsigM hfp m3s hzero hsig2 hsigsz with
    ⟨σ3, evm3, o3, M3, aw3, k3, C3, rd3, hr3, hf3, hs3, hss3, hrun⟩ | ⟨hrev, hblk⟩
  · exact Or.inr ⟨σ3, evm3, out1, out2, o3, M3, aw3, k3, C3, rd3, hr3, hf3, hs3, hss3, fun res h => by
      rw [depositBody_drop8]; exact ExecBlock.consNormal hst1 (ExecBlock.consNormal hst2 (hrun res h))⟩
  · exact Or.inl ⟨hrev, by
      rw [depositBody_drop8]; exact ExecBlock.consNormal hst1 (ExecBlock.consNormal hst2 hblk)⟩

end FeProofs.Deposit
