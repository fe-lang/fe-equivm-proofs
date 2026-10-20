import FeProofs.Deposit.DepositHash

/-!
# FeDeposit `deposit()` hashing, call 3 (pc 838 → 874)

`signature_right = sha256_64(signature[64:96] ‖ bytes32(0))`.  The bytecode stores the
signature's last word over the first word of the signature pair at `0x260`, whose second word
is still the zero `alloc_pair(0, 0)` left there, and hashes the pair in place.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- One store at `s` over memory holding `[s + 32, s + 64)`. -/
theorem wordThenRest_read (w : UInt256) (M : ByteArray) {s : ℕ} (hs : s + 64 ≤ M.size) :
    (w.toByteArray.write 0 M s 32).readWithPadding s 64 = w.toByteArray ++ M.extract (s + 32) (s + 64) := by
  have hw : 32 ≤ w.toByteArray.size := by rw [toByteArray_size]
  have hA : (M.extract 0 s).size = s := by rw [ByteArray.size_extract]; omega
  have hW : (w.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hsz := write_size_ge w.toByteArray M (srcOff := 0) (dest := s) (len := 32) (by decide)
    (by rw [toByteArray_size]) (by have := USize.le_size; omega)
  rw [readWithPadding_eq_extract' _ s 64 (by decide) (by decide) (by omega),
    write32_eq _ _ s hw (by omega),
    extract_append_span _ _ s (s + 64) (by rw [ByteArray.size_append, hA, hW]; omega)
      (by rw [ByteArray.size_append, hA, hW]; omega),
    ByteArray.size_append, hA, hW,
    extract_append_right' _ _ s (s + 32) hA.symm (by rw [hA, hW]),
    extract_extract_BA, extract_word_all,
    show s + 32 + 0 = s + 32 by omega,
    show min (s + 32 + (s + 64 - (s + 32))) M.size = s + 64 by omega]

theorem depositBody_drop10 :
    depositTransition.body.drop 10 =
      .internalCall "sha256_64"
        [.abiEncodePacked [(.bytes, .bytesSlice (.var "signature") (.intLit 64) (.intLit 96)),
          (.elem (.bytes 31), .fixedBytesLit 31 (List.replicate 32 0))]] "signature_right" ::
      depositTransition.body.drop 11 := rfl

set_option maxHeartbeats 4000000 in
/-- **Call 3.**  From pc 838 (signature payload at `0x1c0`, signature pair at `0x260` holding
    `signature_left ‖ 0`) to the `depositHash_874` entry state. -/
theorem depositCall3 {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {evm : EVM.State} {M : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {L : Store} {o1 o2 wc sig : ByteArray} {m : UInt256} (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 838)
      (UInt256.ofNat 448 :: UInt256.ofNat 640 :: UInt256.ofNat 608 :: u64ChunkWord m ::
        calldataWord o1 0 :: calldataWord wc 0 :: R) M aw o2 σ k C)
    (hs : SourceState s0 I σ evm)
    (hleft : memLoad (UInt256.ofNat 608) M = calldataWord o2 0)
    (hsigM : M.extract 448 544 = sig)
    (hfp : memLoad (UInt256.ofNat 64) M = UInt256.ofNat 672) (hsize : 672 ≤ M.size)
    (hzero : M.extract 640 672 = ByteArray.zeroes 32)
    (hsig : L.get? "signature" = some (.bytes sig)) (hsigsz : sig.size = 96) :
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o3 M' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      RD feDepositBytecode I g s0 (UInt256.ofNat 874)
        (calldataWord o2 0 :: UInt256.ofNat 640 :: UInt256.ofNat 608 :: u64ChunkWord m ::
          calldataWord o1 0 :: calldataWord wc 0 :: R) M' aw' o3 σ' k' C' ∧
      memLoad (UInt256.ofNat 608) M' = calldataWord o3 0 ∧
      memLoad (UInt256.ofNat 64) M' = UInt256.ofNat 672 ∧ 672 ≤ M'.size ∧
      SourceState s0 I σ' evm' ∧
      ∀ res, ExecBlock config (pFrame (L.insert "signature_right" (shaDigest o3))) evm'
          (depositTransition.body.drop 11) res →
        ExecBlock config (pFrame L) evm (depositTransition.body.drop 10) res) ∨
    (RDrev feDepositBytecode g s0 ∧
      ExecBlock config (pFrame L) evm (depositTransition.body.drop 10) .reverted) := by
  rw [depositBody_drop10]
  have h608 : (UInt256.ofNat 608).toNat = 608 := rfl
  have h512 : UInt256.ofNat 64 + UInt256.ofNat 448 = UInt256.ofNat (448 + 64) := by decide
  have r857 := feDepositBlocks.feDeposit_block_838 (by simp; omega) rd
  simp only [feDepositBlocks.feDeposit_block_838_stack, feDepositBlocks.feDeposit_block_838_memory,
    h512, hleft] at r857
  have hpay : ((memLoad (UInt256.ofNat (448 + 64)) M).toByteArray.write 0 M
      (UInt256.ofNat 608).toNat 32).readWithPadding (UInt256.ofNat 608).toNat (UInt256.ofNat 64).toNat =
      sig.extract 64 96 ++ ByteArray.zeroes 32 := by
    rw [h608, show (UInt256.ofNat 64).toNat = 64 from rfl, wordThenRest_read _ M (by omega),
      show 608 + 32 = 640 from rfl, show 608 + 64 = 672 from rfl, hzero]
    exact sigTailWord_eq M sig (q := 448) (by omega) (by decide) hsigM
  have hP := write32_size_ge (memLoad (UInt256.ofNat (448 + 64)) M).toByteArray M 608
    (by rw [toByteArray_size]) (by omega)
  have hfpP := memLoad64_write (memLoad (UInt256.ofNat (448 + 64)) M).toByteArray M
    (srcOff := 0) (dest := (UInt256.ofNat 608).toNat) (len := 32) (by decide)
    (by rw [toByteArray_size]) (gapSmall (by decide)) (by decide) (by omega)
  rw [hfp] at hfpP
  obtain ⟨ev3, σ3, z3, o3, aw3, k3, C3, hc3, hs3, r858, hb3⟩ :=
    staticCallBridge r857 hs (by native_decide) (by simp; omega)
  rw [hpay, ← precompile2_eq] at hc3
  have r858' := RD.normalizePC (pc' := UInt256.ofNat 858) r858 (by decide)
  have hpl := evalSigRightPayload (cfg := config) (stele := pFrame L) (evm := evm) hsig hsigsz
  by_cases hok3 : z3 = true ∧ 32 ≤ o3.size
  swap
  · have hrev : RDrev feDepositBytecode g s0 := by
      cases z3 with
      | false =>
        exact feDepositBlocks.feDeposit_block_2245
          (by simp [feDepositBlocks.feDeposit_block_858_taken_stack]; omega)
          (feDepositBlocks.feDeposit_block_858_taken (by simp; omega) (by decide) (by jump_dest) r858')
      | true =>
        have hshort : o3.size < 32 := by
          by_contra hge
          exact hok3 ⟨rfl, by omega⟩
        exact feDepositBlocks.feDeposit_block_2245
          (by simp [feDepositBlocks.feDeposit_block_858_fallthrough_stack]; omega)
          (feDepositBlocks.feDeposit_block_865_taken
            (by simp [feDepositBlocks.feDeposit_block_858_fallthrough_stack]; omega)
            (lt32_size_word_ne hshort) (by jump_dest)
            (feDepositBlocks.feDeposit_block_858_fallthrough (by simp; omega) (by decide) r858'))
    exact Or.inr ⟨hrev, ExecBlock.consRevert
      (sha64Call_revert (caller := pFrame L) rfl (ret := "signature_right") hpl hc3 hok3)⟩
  obtain ⟨rfl, hout3⟩ := hok3
  have r874 := feDepositBlocks.feDeposit_block_865_fallthrough
    (by simp [feDepositBlocks.feDeposit_block_858_fallthrough_stack]; omega)
    (lt32_size_word hout3 hb3)
    (feDepositBlocks.feDeposit_block_858_fallthrough (by simp; omega) (by decide) r858')
  simp only [feDepositBlocks.feDeposit_block_858_fallthrough_stack] at r874
  have hin : (UInt256.ofNat 608).toNat + 32 ≤
      ((memLoad (UInt256.ofNat (448 + 64)) M).toByteArray.write 0 M (UInt256.ofNat 608).toNat 32).size := by
    rw [h608]; omega
  have hl3 := callOutput_loadAt _ o3 (UInt256.ofNat 608) hb3 hout3 hin
  have hf3 := callOutput_memLoad64 _ o3 (UInt256.ofNat 608) hb3 hout3 (by decide) hin
  rw [hfpP] at hf3
  have hsz3 := callOutput_sizeAt _ o3 (UInt256.ofNat 608) hb3 hin
  have hs10 := sha64Call_ok (caller := pFrame L) rfl (ret := "signature_right") hpl hc3 hout3
  have hP2 := write_size_ge (memLoad (UInt256.ofNat (448 + 64)) M).toByteArray M (srcOff := 0)
    (dest := (UInt256.ofNat 608).toNat) (len := 32) (by decide) (by rw [toByteArray_size])
    (gapSmall (by decide))
  exact Or.inl ⟨σ3, ev3, o3, _, _, _, _, r874, hl3, hf3, by rw [hsz3]; omega, hs3,
    fun res h => ExecBlock.consNormal hs10 h⟩

end FeProofs.Deposit
