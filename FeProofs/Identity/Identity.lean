import FeProofs.Identity.Dispatch
import FeProofs.Common.Basic
import Reasoning.SteleArithmetic

/-!
# FeIdentity `identity(uint256)`

Fe checks call value inside the selector arm (pc 26), then the Solidity-compatible head check
`SLT(CALLDATASIZE - 4, 32)` (pc 36), and finally stores the argument word at memory offset 0 and
returns it (pc 49).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Identity

set_option maxRecDepth 2000000

theorem feIdentityDecode_ok {I : ExecutionEnv} (hlen : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    config.externalABI.decodeCalldata? (identityTransition.params.map Param.name)
      (transitionSignature identityTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) := by
  show decodeCalldata ["value"] [abiUInt256] I.calldata = _
  exact decodeCalldata_uint256_ok hlen hhi

theorem feIdentityDecode_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (identityTransition.params.map Param.name)
      (transitionSignature identityTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [abiUInt256] I.calldata = _
  exact decodeCalldata_uint256_none_short hshort

theorem feIdentityDecode_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (identityTransition.params.map Param.name)
      (transitionSignature identityTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [abiUInt256] I.calldata = _
  exact decodeCalldata_uint256_none_huge hbig

/-- `identity(uint256)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem feIdentityIdentityBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feIdentityBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feIdentitySelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feIdentitySelBytes 0) rfl hsel
  have hd := feIdentityDispatch_identity hsel
  obtain ⟨k, C, rd⟩ := feIdentityReachIdentityBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feIdentityBlocks.feIdentity_block_26_taken (by simp) (by rw [hwv]; decide)
      (by jump_dest) rd
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feIdentityBlocks.feIdentity_block_36_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        have rret := feIdentityBlocks.feIdentity_block_49 (by simp) rd2
        have hout : ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write
            0 ByteArray.empty (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat
            (UInt256.ofNat 32).toNat = (calldataWord I.calldata 4).toByteArray :=
          toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)
        rw [hout] at rret
        exact rret.reEquivExecution hcode hd (feIdentityDecode_ok hlen hhi)
          (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
            (evalExpr_varUInt256 (store_get_self _ _ _)))
          (returnEquiv_of_encode (uint256ReturnEncoding (calldataWord I.calldata 4)))
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feIdentityBlocks.feIdentity_block_36_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        exact (feIdentityBlocks.feIdentity_block_32 (by simp) rd2).reEquivDecodingFailed hcode hd
          (feIdentityDecode_huge hbig)
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feIdentityBlocks.feIdentity_block_36_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      exact (feIdentityBlocks.feIdentity_block_32 (by simp) rd2).reEquivDecodingFailed hcode hd
        (feIdentityDecode_short hshort)
  · have rd1 := feIdentityBlocks.feIdentity_block_26_fallthrough (by simp)
      (isZero_eq_zero_of_ne hwv) rd
    exact (feIdentityBlocks.feIdentity_block_32 (by simp) rd1).reEquivDispatchedRevert hcode hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.Identity
