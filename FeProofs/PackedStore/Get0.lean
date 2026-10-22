import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.Common.Basic

/-!
# FePackedStore `get0()`

Arm entry pc 125: call-value check, then `SLOAD(packedSlot)` and the lane extraction; the lane is
returned zero-extended to a word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreGet0Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 1) rfl hsel
  have hd := fePackedStoreDispatch_get0 hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachGet0Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  have hdec : config.externalABI.decodeCalldata? (get0Transition.params.map Param.name)
      (transitionSignature get0Transition).paramTypes I.calldata = some ∅ := by
    show decodeCalldata [] [] I.calldata = some ∅
    exact decodeCalldata_empty_ok hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide), packedByte_lane0] at rd
  have hbody := nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (imms := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
    (by simp only [initState]; exact hwv)
    (evalLaneCast "lane0" 0 (by simp) rfl rfl)
  exact rd.reEquivExecution hcode hd hdec hbody
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.PackedStore
