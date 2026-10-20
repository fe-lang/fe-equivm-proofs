import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_address(address)`

Arm entry pc 242: call-value check, head-size check (pc 248), the canonical-address check
`SHR(160, word) = 0` (pc 260), and `MSTORE(0, word); RETURN(0, 32)` (pc 270).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_addressBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 3) rfl hsel
  have hd := feNarrowAbiDispatch_echo_address
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_addressBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_242_fallthrough (by simp) hwv rd
    simp only [feNarrowAbiBlocks.feNarrowAbi_block_242_fallthrough_stack] at rd1
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_248_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        by_cases hcanon : (argWord I).toNat < EVM.addressModulus
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_260_fallthrough (by simp)
            (shiftRight160_eq_zero hcanon) rd2
          simp only [feNarrowAbiBlocks.feNarrowAbi_block_260_fallthrough_stack] at rd3
          have rret := RDret.of_output_eq (feNarrowAbiBlocks.feNarrowAbi_block_270 (by simp) rd3)
            (toByteArray_write32_read_back ByteArray.empty (argWord I) 0 (by decide))
          have hdec : config.externalABI.decodeCalldata? (echo_addressTransition.params.map Param.name)
              (transitionSignature echo_addressTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "value"
                (.address (AccountAddress.ofNat (argWord I).toNat))) :=
            decodeCalldata_address_ok hlen hhi hcanon
          exact rret.reEquivExecution hcode hd hdec
            (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
              (evalLocalVar (store_get_self _ _ _)))
            (returnEquiv_of_encode (addressReturnEncoding hcanon))
        · have rd3 := feNarrowAbiBlocks.feNarrowAbi_block_260_taken (by simp)
            (shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)) (by jump_dest) rd2
          refine RDrev.reEquivDecodingFailed hcode
            (feNarrowAbiBlocks.feNarrowAbi_block_99
              (by simp [feNarrowAbiBlocks.feNarrowAbi_block_260_taken_stack]) rd3) hd ?_
          show decodeCalldata ["value"] [.elem .address] I.calldata = _
          exact decodeCalldata_address_none_noncanon hlen hhi hcanon
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_248_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        refine RDrev.reEquivDecodingFailed hcode
          (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd ?_
        show decodeCalldata ["value"] [.elem .address] I.calldata = _
        exact decodeCalldata_address_none_huge hbig
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feNarrowAbiBlocks.feNarrowAbi_block_248_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      refine RDrev.reEquivDecodingFailed hcode
        (feNarrowAbiBlocks.feNarrowAbi_block_99 (by simp) rd2) hd ?_
      show decodeCalldata ["value"] [.elem .address] I.calldata = _
      exact decodeCalldata_address_none_short hsz hshort
  · have rd1 := feNarrowAbiBlocks.feNarrowAbi_block_242_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feNarrowAbiBlocks.feNarrowAbi_block_99
        (by simp [feNarrowAbiBlocks.feNarrowAbi_block_242_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.NarrowAbi
