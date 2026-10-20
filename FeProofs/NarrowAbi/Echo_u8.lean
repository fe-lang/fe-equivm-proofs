import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_u8(uint8)`

Arm entry pc 124: call-value check, head-size check (pc 130), the canonical check
`GT(word, 255)` (pc 142), and `MSTORE(0, word); RETURN(0, 32)` (pc 172).  A dirty word takes the
`None` path (pc 158), whose tag check at pc 163 reverts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_u8Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 1) rfl hsel
  have hd := feNarrowAbiDispatch_echo_u8 (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_u8Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_124_fallthrough (by simp) hwv rd
    simp only [feNarrowAbiBlocks.feNarrowAbi_block_124_fallthrough_stack] at rd1
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_130_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.twoPow 8
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_142_fallthrough (by simp)
            (ugt_zero (a := calldataWord I.calldata 4) (b := UInt256.ofNat 255)
              (show (calldataWord I.calldata 4).toNat ≤ 255 by
                have : EVM.twoPow 8 = 256 := rfl
                omega)) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_142_fallthrough_stack] at rd3
          have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_152 (by simp) (by jump_dest) rd3
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_152_stack] at rd4
          have rd5 := feNarrowAbiBlocks.feNarrowAbi_block_163_fallthrough (by simp) (by decide) rd4
          have rret : RDret feNarrowAbiBytecode _ _ σ (calldataWord I.calldata 4).toByteArray :=
            RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_172 (by simp) rd5)
              (toByteArray_write32_read_back ByteArray.empty _ 0 (by decide))
          have hdec : config.externalABI.decodeCalldata? (echo_u8Transition.params.map Param.name)
              (transitionSignature echo_u8Transition).paramTypes I.calldata =
              some ((∅ : Store).insert "value"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) :=
            (decodeCalldata_uint_result _ hlen hhi).trans (if_pos hcanon)
          exact rret.reEquivExecution hcode hd hdec
            (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
              (evalLocalVar (store_get_self _ _ _)))
            (returnEquiv_of_encode (uint8ReturnEncoding _ hcanon))
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_142_taken (by simp)
            (by
              show UInt256.gt (calldataWord I.calldata 4) (UInt256.ofNat 255) ≠ UInt256.ofNat 0
              rw [ugt_one (a := calldataWord I.calldata 4) (b := UInt256.ofNat 255)
                (show 255 < (calldataWord I.calldata 4).toNat by
                  have : EVM.twoPow 8 = 256 := rfl
                  omega)]
              decide) (by jump_dest) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_142_taken_stack] at rd3
          have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_158 (by simp) rd3
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_158_stack] at rd4
          have rd5 := feNarrowAbiBlocks.feNarrowAbi_block_163_taken (by simp) (by decide)
            (by jump_dest) rd4
          have hdec : config.externalABI.decodeCalldata? (echo_u8Transition.params.map Param.name)
              (transitionSignature echo_u8Transition).paramTypes I.calldata = none :=
            (decodeCalldata_uint_result _ hlen hhi).trans (if_neg hcanon)
          exact RDrev.reEquivDecodingFailed hcode
            (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd5) hd hdec
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_130_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        exact RDrev.reEquivDecodingFailed hcode
          (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
          (decodeCalldata_uint_none_huge _ hbig)
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_130_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode
        (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
        (decodeCalldata_uint_none_short _ hshort)
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_124_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feNarrowAbiBlocks.feNarrowAbi_block_99
        (by simp [feNarrowAbiBlocks.feNarrowAbi_block_124_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.NarrowAbi
