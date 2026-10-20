import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_bool(bool)`

Arm entry pc 180: call-value check, head-size check (pc 186), the canonical check (zero at
pc 198, otherwise `EQ(1, word)` at pc 206), and the re-encoding of the decoded flag as `0`/`1`
(pcs 221–237).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_boolBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 2) rfl hsel
  have hd := feNarrowAbiDispatch_echo_bool
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_boolBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_180_fallthrough (by simp) hwv rd
    simp only [feNarrowAbiBlocks.feNarrowAbi_block_180_fallthrough_stack] at rd1
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_186_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        have hbody : ∀ b : Bool, ExecTransitionBody config contract
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ((∅ : Store).insert "value" (.bool b))
            echo_boolTransition.body
            (.returned { contract := contract, locals := (∅ : Store).insert "value" (.bool b) }
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [.bool b])) := fun b =>
          nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
            (evalLocalVar (store_get_self _ _ _))
        by_cases hw0 : calldataWord I.calldata 4 = ⟨0⟩
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_198_taken (by simp)
            (by
              show UInt256.isZero (calldataWord I.calldata 4) ≠ UInt256.ofNat 0
              rw [hw0]; decide) (by jump_dest) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_198_taken_stack] at rd3
          have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_218 (by simp) rd3
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_218_stack] at rd4
          have rd5 := feNarrowAbiBlocks.feNarrowAbi_block_221_taken (by simp) (by decide)
            (by jump_dest) rd4
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_221_taken_stack] at rd5
          have rd6 := feNarrowAbiBlocks.feNarrowAbi_block_233 (by simp) rd5
          have rret : RDret feNarrowAbiBytecode _ _ σ (UInt256.toByteArray ⟨0⟩) :=
            RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_237 (by simp) rd6)
              (toByteArray_write32_read_back ByteArray.empty _ 0 (by decide))
          have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
              (transitionSignature echo_boolTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "value" (.bool false)) := by
            show decodeCalldata ["value"] [.elem .bool] I.calldata = _
            rw [decodeCalldata_word rfl hlen hhi, hw0]
            rfl
          exact rret.reEquivExecution hcode hd hdec (hbody false)
            (returnEquiv_of_encode boolFalseReturnEncoding)
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_198_fallthrough (by simp)
            (isZero_eq_zero_of_ne hw0) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_198_fallthrough_stack] at rd3
          by_cases hw1 : calldataWord I.calldata 4 = ⟨1⟩
          · have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_206_fallthrough (by simp)
              (by
                show UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (calldataWord I.calldata 4)) =
                  UInt256.ofNat 0
                rw [hw1]; decide) rd3
            simp only [feNarrowAbiBlocks.feNarrowAbi_block_206_fallthrough_stack] at rd4
            have rd5 := feNarrowAbiBlocks.feNarrowAbi_block_213 (by simp) (by jump_dest) rd4
            simp only [feNarrowAbiBlocks.feNarrowAbi_block_213_stack] at rd5
            have rd6 := feNarrowAbiBlocks.feNarrowAbi_block_221_fallthrough (by simp) (by decide) rd5
            simp only [feNarrowAbiBlocks.feNarrowAbi_block_221_fallthrough_stack] at rd6
            have rd7 := feNarrowAbiBlocks.feNarrowAbi_block_226 (by simp) (by jump_dest) rd6
            have rret : RDret feNarrowAbiBytecode _ _ σ (UInt256.toByteArray ⟨1⟩) :=
              RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_237 (by simp) rd7)
                (toByteArray_write32_read_back ByteArray.empty _ 0 (by decide))
            have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
                (transitionSignature echo_boolTransition).paramTypes I.calldata =
                some ((∅ : Store).insert "value" (.bool true)) := by
              show decodeCalldata ["value"] [.elem .bool] I.calldata = _
              rw [decodeCalldata_word rfl hlen hhi, hw1]
              rfl
            exact rret.reEquivExecution hcode hd hdec (hbody true)
              (returnEquiv_of_encode boolTrueReturnEncoding)
          · have rd4 := feNarrowAbiBlocks.feNarrowAbi_block_206_taken (by simp)
              (by
                show UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (calldataWord I.calldata 4)) ≠
                  UInt256.ofNat 0
                rw [uInt256_eq_zero_of_ne (a := UInt256.ofNat 1) (fun h => hw1 (uInt256_eq_one_eq h).symm)]
                decide) (by jump_dest) rd3
            have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
                (transitionSignature echo_boolTransition).paramTypes I.calldata = none := by
              show decodeCalldata ["value"] [.elem .bool] I.calldata = _
              rw [decodeCalldata_word rfl hlen hhi]
              have hz : (↑(calldataWord I.calldata 4).val : Nat) ≠ 0 := fun h => hw0 (u256_inj h)
              have ho : (↑(calldataWord I.calldata 4).val : Nat) ≠ 1 := fun h => hw1 (u256_inj h)
              simp only [decodeABIWord?, if_neg hz, if_neg ho]
              rfl
            exact RDrev.reEquivDecodingFailed hcode
              (feNarrowAbiBlocks.feNarrowAbi_block_99
                (by simp [feNarrowAbiBlocks.feNarrowAbi_block_206_taken_stack]) rd4) hd hdec
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_186_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        exact RDrev.reEquivDecodingFailed hcode
          (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
          (decodeCalldata_word_none_huge rfl hbig)
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_186_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode
        (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd
        (decodeCalldata_word_none_short rfl hshort)
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_180_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feNarrowAbiBlocks.feNarrowAbi_block_99
        (by simp [feNarrowAbiBlocks.feNarrowAbi_block_180_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.NarrowAbi
