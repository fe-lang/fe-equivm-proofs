import FeProofs.Deposit.DepositHash

/-!
# FeDeposit `deposit()` hashing, call 3 (pc 813 → 855)

`signature_right = sha256_64(signature[64:96] ‖ bytes32(0))`.  The bytecode stores the
signature's last word over the first word of the scratch pair at `0x140`, whose second word
is still the zero block 695 left there, and hashes the pair in place.
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
    extract_extract_BA, toByteArray_extract_all,
    show s + 32 + 0 = s + 32 by omega,
    show min (s + 32 + (s + 64 - (s + 32))) M.size = s + 64 by omega]

theorem depositBody_drop10 :
    depositTransition.body.drop 10 =
      .internalCall "sha256_64"
        [.abiEncodePacked [(.bytes, .bytesSlice (.var "signature") (.intLit 64) (.intLit 96)),
          (.elem (.bytes 31), .fixedBytesLit 31 (List.replicate 32 0))]] "signature_right" ::
      depositTransition.body.drop 11 := rfl

/-- **Call 3.**  From pc 813 (signature payload at `0x280`, scratch pair at `0x140` holding
    `signature_left ‖ 0`) to the `depositHash_855` entry state. -/
theorem depositCall3 {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {evm : EVM.State} {M : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {L : Store} {o1 o2 wc sig : ByteArray} {m : UInt256} (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 813)
      (UInt256.ofNat 640 :: u64ChunkWord m :: calldataWord o1 0 :: calldataWord wc 0 :: R)
      M aw o2 σ k C)
    (hs : SourceState s0 I σ evm)
    (hleft : memLoad (UInt256.ofNat 320) M = calldataWord o2 0)
    (hsigM : M.extract 640 736 = sig) (hsize : 736 ≤ M.size)
    (hzero : M.extract 352 384 = ByteArray.zeroes 32)
    (hsig : L.get? "signature" = some (.bytes sig)) (hsigsz : sig.size = 96) :
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o3 M' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      RD feDepositBytecode I g s0 (UInt256.ofNat 855)
        (calldataWord o2 0 :: u64ChunkWord m :: calldataWord o1 0 :: calldataWord wc 0 :: R)
        M' aw' o3 σ' k' C' ∧
      memLoad (UInt256.ofNat 320) M' = calldataWord o3 0 ∧
      SourceState s0 I σ' evm' ∧
      ∀ res, ExecBlock config (pFrame (L.insert "signature_right" (shaDigest o3))) evm'
          (depositTransition.body.drop 11) res →
        ExecBlock config (pFrame L) evm (depositTransition.body.drop 10) res) ∨
    (RDrev feDepositBytecode g s0 ∧
      ExecBlock config (pFrame L) evm (depositTransition.body.drop 10) .reverted) := by
  rw [depositBody_drop10]
  have h320 : (UInt256.ofNat 320).toNat = 320 := rfl
  have h704 : UInt256.ofNat 64 + UInt256.ofNat 640 = UInt256.ofNat (640 + 64) := by decide
  have r838 := feDepositBlocks.feDeposit_block_813 (by simp; omega) rd
  simp only [feDepositBlocks.feDeposit_block_813_stack, feDepositBlocks.feDeposit_block_813_memory,
    h704, hleft] at r838
  have hpay : ((memLoad (UInt256.ofNat (640 + 64)) M).toByteArray.write 0 M
      (UInt256.ofNat 320).toNat 32).readWithPadding (UInt256.ofNat 320).toNat (UInt256.ofNat 64).toNat =
      sig.extract 64 96 ++ ByteArray.zeroes 32 := by
    rw [h320, show (UInt256.ofNat 64).toNat = 64 from rfl, wordThenRest_read _ M (by omega),
      show 320 + 32 = 352 from rfl, show 320 + 64 = 384 from rfl, hzero]
    exact sigTailWord_eq M sig (q := 640) (by omega) (by decide) hsigM
  have hP := write32_size_ge (memLoad (UInt256.ofNat (640 + 64)) M).toByteArray M 320
    (by rw [toByteArray_size]) (by omega)
  obtain ⟨ev3, σ3, z3, o3, aw3, k3, C3, hc3, hs3, r839, hb3⟩ :=
    staticCallBridge r838 hs (by native_decide) (by simp; omega)
  rw [hpay, ← precompile2_eq] at hc3
  have hpl := evalSigRightPayload (cfg := config) (stele := pFrame L) (evm := evm) hsig hsigsz
  rd_checked r839 z3 o3 as hrev hout3 to 855
  · exact Or.inr ⟨hrev, ExecBlock.consRevert
      (sha64Call_revert (caller := pFrame L) rfl (ret := "signature_right") hpl hc3 hout3)⟩
  have hin : (UInt256.ofNat 320).toNat + 32 ≤
      ((memLoad (UInt256.ofNat (640 + 64)) M).toByteArray.write 0 M (UInt256.ofNat 320).toNat 32).size := by
    rw [h320]; omega
  have hl3 := callOutput_loadAt _ o3 (UInt256.ofNat 320) hb3 hout3 hin
  have hs10 := sha64Call_ok (caller := pFrame L) rfl (ret := "signature_right") hpl hc3 hout3
  exact Or.inl ⟨σ3, ev3, o3, _, _, _, _, r839, hl3, hs3,
    fun res h => ExecBlock.consNormal hs10 h⟩

end FeProofs.Deposit
