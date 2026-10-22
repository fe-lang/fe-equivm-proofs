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
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hlen : 36 ≤ I.calldata.size
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (feIdentityDecode_short (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckHuge_4_32 (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (feIdentityDecode_huge (by omega))
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
  exact rd.reEquivExecution hcode hd (feIdentityDecode_ok hlen hhi)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
      (evalExpr_varUInt256 (store_get_self _ _ _)))
    (returnEquiv_of_encode (uint256ReturnEncoding (calldataWord I.calldata 4)))

end FeProofs.Identity
