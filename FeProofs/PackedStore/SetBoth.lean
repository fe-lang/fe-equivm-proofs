import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.Common.Basic

/-!
# FePackedStore `setBoth(uint256,uint256)`

Arm entry pc 173: call-value check, the two-word head check (pc 178), then one read-modify-write of
word `packedSlot` replacing lane 0 with the first argument's low byte and lane 1 with the second's
(pc 190).  The compiler merges the spec's two lane writes into one `SSTORE`; `storeLanes_accountMap`
shows the account maps agree.  Under `STATICCALL` the `SSTORE` halts, matching Stele's static
violation at the first lane assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreSetBothBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 2) rfl hsel
  have hd := fePackedStoreDispatch_setBoth (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSetBothBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
        (UInt256.ofNat 64) = ⟨1⟩ := by
      rcases hbad with h | h
      · exact solcDecodeLenCheckShort_4_64 hsz h hsize
      · exact solcDecodeLenCheckHuge_4_64 h hsize
    rd_run rd using [hwv, hslt]
    exact RDrev.reEquivDecodingFailed hcode rd hd (hbad.elim
      decodeCalldata_uint256_uint256_none_short decodeCalldata_uint256_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  rd_run rd to 190 using [hwv, solcDecodeLenCheckOk_4_64 hlen hhi hsize]
  have hdec : config.externalABI.decodeCalldata? (setBothTransition.params.map Param.name)
      (transitionSignature setBothTransition).paramTypes I.calldata = some (bothStore I) := by
    show decodeCalldata ["first", "second"] [abiUInt256, abiUInt256] I.calldata = _
    exact decodeCalldata_uint256_uint256_ok hlen hhi
  set evm := initState σ σ₀ (Sat256.ofUInt256 g) A I with hevm
  have hreq := ExecStmt.requireTrue (cfg := config)
    (stele := { contract := contract, locals := bothStore I })
    (evalCallvalueEq_true (evm := evm) (by simp only [hevm, initState]; exact hwv))
  have hv0 := evalCast8 (stele := { contract := contract, locals := bothStore I }) (evm := evm)
    (x := "first") (v := calldataWord I.calldata 4)
    (by rw [store_get_ne _ _ (by decide), store_get_self])
  have ha0 := assignLane (stele := { contract := contract, locals := bothStore I }) (evm := evm)
    "lane0" 0 (calldataWord I.calldata 4) (by simp) rfl rfl
  set evm1 := Stele.EVM.storageStore evm evm.executionEnv.codeOwner packedSlot
    (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner packedSlot)
      (calldataWord I.calldata 4) 0) with hevm1
  have hv1 := evalCast8 (stele := { contract := contract, locals := bothStore I }) (evm := evm1)
    (x := "second") (v := calldataWord I.calldata 36) (store_get_self _ _ _)
  have ha1 := assignLane (stele := { contract := contract, locals := bothStore I }) (evm := evm1)
    "lane1" 1 (calldataWord I.calldata 36) (by simp) rfl rfl
  by_cases hperm : I.perm = true
  · rd_step rd
    have hp1 : evm1.executionEnv.perm = true := by
      rw [hevm1, storageStore_executionEnv]; simp only [hevm, initState]; exact hperm
    refine (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _)).reEquivExecutionGen hcode
      hd hdec (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by simp only [hevm, initState]; exact hperm)) hv0 ha0)
        (ExecBlock.consNormal (ExecStmt.assign (Or.inr hp1) hv1 ha1) ExecBlock.nil))))
      ?_ (returnEquiv.fallthrough rfl rfl (by native_decide))
    have h1 : evm.executionEnv.codeOwner = I.codeOwner := rfl
    have h2 : evm.accountMap = σ := rfl
    have h3 : Stele.EVM.storageLoad evm I.codeOwner packedSlot =
        codeOwnerStorageWord I σ packedSlot := codeOwnerStorageWord_initState packedSlot
    rw [storeLanes_accountMap (evm := evm), setPackedByte_lane0, setPackedByte_lane1, h1, h2, h3]
    rfl
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact RDstatic.reEquivStaticHalt hcode rd hd hdec
      (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consStatic
        (ExecStmt.assignStatic hv0 ha0 (by simp only [hevm, initState]; exact hpf)))))

end FeProofs.PackedStore
