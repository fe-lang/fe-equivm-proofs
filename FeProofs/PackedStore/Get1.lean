import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.Common.Basic

/-!
# FePackedStore `get1()`

Arm entry pc 68: call-value check, then `SLOAD(packedSlot)` and the lane extraction; the lane is
returned zero-extended to a word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreGet1Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 0) rfl hsel
  have hd := fePackedStoreDispatch_get1  hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachGet1Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  have hdec : config.externalABI.decodeCalldata? (get1Transition.params.map Param.name)
      (transitionSignature get1Transition).paramTypes I.calldata = some ∅ := by
    show decodeCalldata [] [] I.calldata = some ∅
    exact decodeCalldata_empty_ok hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := fePackedStoreBlocks.fePackedStore_block_68_taken (by simp) (by rw [hwv]; decide) (by jump_dest) rd
    have rret : RDret fePackedStoreBytecode _ _ σ
        (packedByte (codeOwnerStorageWord I σ packedSlot) 1).toByteArray :=
      RDret.of_output_eq (fePackedStoreBlocks.fePackedStore_block_78 (by simp) rd1)
        ((toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)).trans
          (congrArg UInt256.toByteArray (packedByte_lane1 _)))
    have hbody := nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
      (imms := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
      (by simp only [initState]; exact hwv)
      (evalLaneCast "lane1" 1 (by simp) rfl rfl)
    have hW : Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner packedSlot =
        codeOwnerStorageWord I σ packedSlot := codeOwnerStorageWord_initState packedSlot
    rw [hW] at hbody
    exact rret.reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := fePackedStoreBlocks.fePackedStore_block_68_fallthrough (by simp) (isZero_eq_zero_of_ne hwv) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (fePackedStoreBlocks.fePackedStore_block_74 (by simp) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.PackedStore
