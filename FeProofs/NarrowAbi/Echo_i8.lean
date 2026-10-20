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
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_56_fallthrough (by simp) hwv rd
    simp only [feNarrowAbiBlocks.feNarrowAbi_block_56_fallthrough_stack] at rd1
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_62_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
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
        by_cases hpos : (calldataWord I.calldata 4).toNat < 128
        · -- Non-negative canonical word: the low byte is the word, and its sign bit is clear.
          have hlow : UInt256.land (calldataWord I.calldata 4) ⟨255⟩ = calldataWord I.calldata 4 :=
            lowByteClean (by omega)
          have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_74_taken (by simp)
            (by
              show UInt256.isZero (UInt256.land (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)
                ⟨128⟩) ≠ UInt256.ofNat 0
              rw [hlow, byteSignBit_of_lt128 hpos]; decide) (by jump_dest) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_74_taken_stack] at rd3
          have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_103_fallthrough (by simp)
            (by
              show UInt256.isZero (UInt256.eq (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)
                (calldataWord I.calldata 4)) = UInt256.ofNat 0
              rw [hlow, uInt256_eq_self]; decide) rd3
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_103_fallthrough_stack] at rd4
          have hsar : UInt256.sar (UInt256.ofNat 248) (UInt256.shiftLeft
              (UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255)) (UInt256.ofNat 248)) =
              calldataWord I.calldata 4 := by
            rw [show UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255) =
              calldataWord I.calldata 4 from hlow]
            exact sarShiftLeft248_low_lt128 hpos
          have rret : RDret feNarrowAbiBytecode _ _ σ (calldataWord I.calldata 4).toByteArray :=
            RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_111 (by simp) rd4)
              ((toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)).trans
                (congrArg UInt256.toByteArray hsar))
          have hcanon : i8Canonical (calldataWord I.calldata 4) := Or.inl (by rw [h128]; exact hpos)
          exact rret.reEquivExecution hcode hd (hdecOk hcanon) (hbody _)
            (returnEquiv_of_encode (int8ReturnEncoding hcanon))
        · by_cases hneg : EVM.wordModulus - 128 ≤ (calldataWord I.calldata 4).toNat
          · -- Negative canonical word: the sign-extended low byte is the word.
            obtain ⟨_, hge, hlt⟩ := negativeLowByte hneg
            have hext := negativeCanonicalWord hneg
            have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_74_fallthrough (by simp)
              (by
                show UInt256.isZero (UInt256.land (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)
                  ⟨128⟩) = UInt256.ofNat 0
                rw [byteSignBit_of_ge128 hge hlt]; decide) rd2
            simp only [feNarrowAbiBlocks.feNarrowAbi_block_74_fallthrough_stack] at rd3
            have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_89_taken (by simp)
              (by
                show UInt256.eq (UInt256.lor (UInt256.lnot ⟨255⟩)
                  (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)) (calldataWord I.calldata 4) ≠
                  UInt256.ofNat 0
                rw [hext, uInt256_eq_self]; decide) (by jump_dest) rd3
            simp only [feNarrowAbiBlocks.feNarrowAbi_block_89_taken_stack] at rd4
            have hsar : UInt256.sar (UInt256.ofNat 248) (UInt256.shiftLeft
                (UInt256.lor (UInt256.lnot (UInt256.ofNat 255))
                  (UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255)))
                (UInt256.ofNat 248)) = calldataWord I.calldata 4 := by
              rw [show UInt256.lor (UInt256.lnot (UInt256.ofNat 255))
                  (UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255)) =
                calldataWord I.calldata 4 from hext]
              exact sarShiftLeft248_negative hneg
            have rret : RDret feNarrowAbiBytecode _ _ σ (calldataWord I.calldata 4).toByteArray :=
              RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_111 (by simp) rd4)
                ((toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)).trans
                  (congrArg UInt256.toByteArray hsar))
            have hcanon : i8Canonical (calldataWord I.calldata 4) := Or.inr (by rw [hmod]; exact hneg)
            exact rret.reEquivExecution hcode hd (hdecOk hcanon) (hbody _)
              (returnEquiv_of_encode (int8ReturnEncoding hcanon))
          · -- Non-canonical word: both comparisons fail and the call reverts.
            have hdec : config.externalABI.decodeCalldata? (echo_i8Transition.params.map Param.name)
                (transitionSignature echo_i8Transition).paramTypes I.calldata = none := by
              show decodeCalldata ["value"] [int8Ty] I.calldata = _
              rw [decodeCalldata_word rfl hlen hhi,
                decodeWordI8_none (by rw [h128]; omega) (by rw [hmod]; omega)]
              rfl
            have hlowLt := lowByte_lt256 (calldataWord I.calldata 4)
            by_cases hsign : UInt256.land (UInt256.land (calldataWord I.calldata 4) ⟨255⟩) ⟨128⟩ = ⟨0⟩
            · have hlowNe : UInt256.land (calldataWord I.calldata 4) ⟨255⟩ ≠
                  calldataWord I.calldata 4 := by
                intro heq
                have hsign128 := byteSignBit_of_ge128 (low := UInt256.land (calldataWord I.calldata 4)
                  ⟨255⟩) (by rw [heq]; omega) hlowLt
                exact (by decide : (⟨128⟩ : UInt256) ≠ ⟨0⟩) (hsign128.symm.trans hsign)
              have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_74_taken (by simp)
                (by
                  show UInt256.isZero (UInt256.land (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)
                    ⟨128⟩) ≠ UInt256.ofNat 0
                  rw [hsign]; decide) (by jump_dest) rd2
              simp only [feNarrowAbiBlocks.feNarrowAbi_block_74_taken_stack] at rd3
              have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_103_taken (by simp)
                (by
                  show UInt256.isZero (UInt256.eq (UInt256.land (calldataWord I.calldata 4) ⟨255⟩)
                    (calldataWord I.calldata 4)) ≠ UInt256.ofNat 0
                  rw [uInt256_eq_zero_of_ne (fun h => hlowNe (uInt256_eq_one_eq h))]; decide)
                (by jump_dest) rd3
              exact RDrev.reEquivDecodingFailed hcode
                (feNarrowAbiBlocks.feNarrowAbi_block_99
                  (by simp [feNarrowAbiBlocks.feNarrowAbi_block_103_taken_stack]) rd4) hd hdec
            · have hlowGe : 128 ≤ (UInt256.land (calldataWord I.calldata 4) ⟨255⟩).toNat := by
                by_contra h
                exact hsign (byteSignBit_of_lt128 (by omega))
              have hextNe : UInt256.lor (UInt256.lnot ⟨255⟩)
                  (UInt256.land (calldataWord I.calldata 4) ⟨255⟩) ≠ calldataWord I.calldata 4 := by
                intro heq
                have hge := signExtendedLow_toNat (calldataWord I.calldata 4)
                rw [heq] at hge
                omega
              have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_74_fallthrough (by simp)
                (isZero_eq_zero_of_ne hsign) rd2
              simp only [feNarrowAbiBlocks.feNarrowAbi_block_74_fallthrough_stack] at rd3
              have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_89_fallthrough (by simp)
                (uInt256_eq_zero_of_ne (fun h => hextNe (uInt256_eq_one_eq h))) rd3
              exact RDrev.reEquivDecodingFailed hcode
                (feNarrowAbiBlocks.feNarrowAbi_block_99
                  (by simp [feNarrowAbiBlocks.feNarrowAbi_block_89_fallthrough_stack]) rd4) hd hdec
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_62_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        exact RDrev.reEquivDecodingFailed hcode
          (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
          (decodeCalldata_word_none_huge rfl hbig)
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_62_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode
        (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
        (decodeCalldata_word_none_short rfl hshort)
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_56_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feNarrowAbiBlocks.feNarrowAbi_block_99
        (by simp [feNarrowAbiBlocks.feNarrowAbi_block_56_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.NarrowAbi
