import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_i8(int8)`

Arm entry pc 56: call-value check, head-size check (pc 62), then Solidity's canonical `int8`
check: the low byte's sign bit (pc 74) selects comparing the word with the low byte (pc 103) or
with the sign-extended low byte (pc 89); the canonical word is sign-extended again by
`SAR(248, SHL(248, x))` and returned (pc 111).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_i8Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 0) rfl hsel
  have hd := feNarrowAbiDispatch_echo_i8 hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_i8Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  have h128 : EVM.twoPow 7 = 128 := rfl
  have hmod : EVM.wordModulus - EVM.twoPow 7 = EVM.wordModulus - 128 := by rw [h128]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hlen : 36 ≤ I.calldata.size
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_word_none_short rfl (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckHuge_4_32 (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_word_none_huge rfl (by omega))
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hbody : ∀ v : Value, ExecTransitionBody config contract
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ((∅ : Store).insert "value" v)
      echo_i8Transition.body
      (.returned { contract := contract, locals := (∅ : Store).insert "value" v }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [v])) := fun v =>
    nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
      (evalLocalVar (store_get_self _ _ _))
  have hdecOk : i8Canonical (calldataWord I.calldata 4) →
      config.externalABI.decodeCalldata? (echo_i8Transition.params.map Param.name)
        (transitionSignature echo_i8Transition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (i8Value (calldataWord I.calldata 4))) := by
    intro hcanon
    show decodeCalldata ["value"] [int8Ty] I.calldata = _
    rw [decodeCalldata_word rfl hlen hhi, decodeWordI8_ok hcanon]
    rfl
  have hwlt : (calldataWord I.calldata 4).toNat < EVM.wordModulus :=
    (calldataWord I.calldata 4).val.isLt
  -- The argument word and the byte masks as the block summaries spell them.
  have hW : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
      calldataWord I.calldata 4 := rfl
  have hm255 : UInt256.ofNat 255 = ⟨255⟩ := rfl
  have hm128 : UInt256.ofNat 128 = ⟨128⟩ := rfl
  by_cases hpos : (calldataWord I.calldata 4).toNat < 128
  · -- Non-negative canonical word: the low byte is the word, and its sign bit is clear.
    have hlow : UInt256.land (calldataWord I.calldata 4) ⟨255⟩ = calldataWord I.calldata 4 :=
      lowByteClean (by omega)
    rd_run rd using [(by
      simp only [hW, hm255, hm128, hlow, byteSignBit_of_lt128 hpos, uInt256_eq_self]
      decide)]
    u256_lits at rd
    rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide), hm255, hlow,
      sarShiftLeft248_low_lt128 hpos] at rd
    have hcanon : i8Canonical (calldataWord I.calldata 4) := Or.inl (by rw [h128]; exact hpos)
    exact rd.reEquivExecution hcode hd (hdecOk hcanon) (hbody _)
      (returnEquiv_of_encode (int8ReturnEncoding hcanon))
  by_cases hneg : EVM.wordModulus - 128 ≤ (calldataWord I.calldata 4).toNat
  · -- Negative canonical word: the sign-extended low byte is the word.
    obtain ⟨_, hge, hlt⟩ := negativeLowByte hneg
    have hext := negativeCanonicalWord hneg
    rd_run rd using [(by
      simp only [hW, hm255, hm128, byteSignBit_of_ge128 hge hlt, hext, uInt256_eq_self]
      decide)]
    u256_lits at rd
    rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide), hm255, hext,
      sarShiftLeft248_negative hneg] at rd
    have hcanon : i8Canonical (calldataWord I.calldata 4) := Or.inr (by rw [hmod]; exact hneg)
    exact rd.reEquivExecution hcode hd (hdecOk hcanon) (hbody _)
      (returnEquiv_of_encode (int8ReturnEncoding hcanon))
  -- Non-canonical word: both comparisons fail and the call reverts.
  have hdec : config.externalABI.decodeCalldata? (echo_i8Transition.params.map Param.name)
      (transitionSignature echo_i8Transition).paramTypes I.calldata = none := by
    show decodeCalldata ["value"] [int8Ty] I.calldata = _
    rw [decodeCalldata_word rfl hlen hhi,
      decodeWordI8_none (by rw [h128]; omega) (by rw [hmod]; omega)]
    rfl
  have hlowLt := lowByte_lt256 (calldataWord I.calldata 4)
  by_cases hsign : UInt256.land (UInt256.land (calldataWord I.calldata 4) ⟨255⟩) ⟨128⟩ = ⟨0⟩
  · have hlowNe : UInt256.land (calldataWord I.calldata 4) ⟨255⟩ ≠ calldataWord I.calldata 4 := by
      intro heq
      have hsign128 := byteSignBit_of_ge128 (low := UInt256.land (calldataWord I.calldata 4)
        ⟨255⟩) (by rw [heq]; omega) hlowLt
      exact (by decide : (⟨128⟩ : UInt256) ≠ ⟨0⟩) (hsign128.symm.trans hsign)
    rd_run rd using [(by
      simp only [hW, hm255, hm128, hsign,
        uInt256_eq_zero_of_ne fun h => hlowNe (uInt256_eq_one_eq h)]
      decide)]
    exact RDrev.reEquivDecodingFailed hcode rd hd hdec
  have hlowGe : 128 ≤ (UInt256.land (calldataWord I.calldata 4) ⟨255⟩).toNat := by
    by_contra h
    exact hsign (byteSignBit_of_lt128 (by omega))
  have hextNe : UInt256.lor (UInt256.lnot ⟨255⟩)
      (UInt256.land (calldataWord I.calldata 4) ⟨255⟩) ≠ calldataWord I.calldata 4 := by
    intro heq
    have hge := signExtendedLow_toNat (calldataWord I.calldata 4)
    rw [heq] at hge
    omega
  rd_run rd using [isZero_eq_zero_of_ne hsign,
    uInt256_eq_zero_of_ne (fun h => hextNe (uInt256_eq_one_eq h))]
  exact RDrev.reEquivDecodingFailed hcode rd hd hdec

end FeProofs.NarrowAbi
