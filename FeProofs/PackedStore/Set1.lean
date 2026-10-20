import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.Common.Basic

/-!
# FePackedStore `set1(uint256)`

Arm entry pc 287: call-value check, head-size check (pc 292), then one read-modify-write of word
`packedSlot` replacing lane 1 with the argument's low byte (pc 304).  Under `STATICCALL` the
`SSTORE` halts, matching Stele's static violation at the storage assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreSet1Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 3) rfl hsel
  have hd := fePackedStoreDispatch_set1 (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSet1Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (hbad.elim decodeCalldata_uint256_none_short decodeCalldata_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  rd_run rd to 304 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hdec : config.externalABI.decodeCalldata? (set1Transition.params.map Param.name)
      (transitionSignature set1Transition).paramTypes I.calldata = some (valueStore I) := by
    show decodeCalldata ["value"] [abiUInt256] I.calldata = _
    exact decodeCalldata_uint256_ok hlen hhi
  have hval := evalCast8 (stele := { contract := contract, locals := valueStore I })
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (store_get_self _ _ _)
  have hasg := assignLane (stele := { contract := contract, locals := valueStore I })
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) "lane1" 1 (calldataWord I.calldata 4)
    (by simp) rfl rfl
  have hreq := ExecStmt.requireTrue (cfg := config)
    (stele := { contract := contract, locals := valueStore I })
    (evalCallvalueEq_true (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv))
  by_cases hperm : I.perm = true
  · rd_step rd
    exact (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _)).reEquivExecutionGen hcode hd
      hdec (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by simp only [initState]; exact hperm)) hval hasg)
        ExecBlock.nil)))
      (by rw [storeLane_accountMap, setPackedByte_lane1]; try rfl)
      (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact RDstatic.reEquivStaticHalt hcode rd hd hdec
      (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consStatic
        (ExecStmt.assignStatic hval hasg (by simp only [initState]; exact hpf)))))

end FeProofs.PackedStore
