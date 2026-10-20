import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.PackedStore.Static
import FeProofs.Common.Basic

/-!
# FePackedStore `set0(uint256)`

Arm entry pc 390: call-value check, head-size check (pc 395), then one read-modify-write of word
`packedSlot` replacing lane 0 with the argument's low byte (pc 407).  Under `STATICCALL` the
`SSTORE` halts, matching Stele's static violation at the storage assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach FeProofs.Common

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreSet0Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 4) rfl hsel
  have hd := fePackedStoreDispatch_set0 (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSet0Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := fePackedStoreBlocks.fePackedStore_block_390_fallthrough (by simp) hwv rd
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := fePackedStoreBlocks.fePackedStore_block_395_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        have hdec : config.externalABI.decodeCalldata? (set0Transition.params.map Param.name)
            (transitionSignature set0Transition).paramTypes I.calldata =
            some (valueStore I) := by
          show decodeCalldata ["value"] [abiUInt256] I.calldata = _
          exact decodeCalldata_uint256_ok hlen hhi
        have hval := evalCast8 (stele := { contract := contract, locals := valueStore I })
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (store_get_self _ _ _)
        have hasg := assignLane (stele := { contract := contract, locals := valueStore I })
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) "lane0" 0 (calldataWord I.calldata 4)
          (by simp) rfl rfl
        have hreq := ExecStmt.requireTrue (cfg := config)
          (stele := { contract := contract, locals := valueStore I })
          (evalCallvalueEq_true (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (by simp only [initState]; exact hwv))
        by_cases hperm : I.perm = true
        · have rret := RDret.of_output_eq
            (fePackedStoreBlocks.fePackedStore_block_407 (by simp) hperm rd2)
            (byteArray_readWithPadding_zero _ _)
          exact rret.reEquivExecutionGen hcode hd hdec
            (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal
              (ExecStmt.assign (Or.inr (by simp only [initState]; exact hperm)) hval hasg)
              ExecBlock.nil)))
            (by rw [storeLane_accountMap, setPackedByte_lane0]; try rfl)
            (returnEquiv.fallthrough rfl rfl (by native_decide))
        · have hpf : I.perm = false := by simpa using hperm
          exact RDstatic.reEquivStaticHalt hcode
            (fePackedStore_block_407_static (by simp) rd2 hpf) hd hdec
            (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consStatic
              (ExecStmt.assignStatic hval hasg (by simp only [initState]; exact hpf)))))
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := fePackedStoreBlocks.fePackedStore_block_395_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        refine RDrev.reEquivDecodingFailed hcode
          (fePackedStoreBlocks.fePackedStore_block_74 (by simp) rd2) hd ?_
        show decodeCalldata ["value"] [abiUInt256] I.calldata = _
        exact decodeCalldata_uint256_none_huge hbig
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := fePackedStoreBlocks.fePackedStore_block_395_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      refine RDrev.reEquivDecodingFailed hcode
        (fePackedStoreBlocks.fePackedStore_block_74 (by simp) rd2) hd ?_
      show decodeCalldata ["value"] [abiUInt256] I.calldata = _
      exact decodeCalldata_uint256_none_short hshort
  · have rd1 := fePackedStoreBlocks.fePackedStore_block_390_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (fePackedStoreBlocks.fePackedStore_block_74 (by simp) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.PackedStore
