import FeProofs.PackedStore.Dispatch
import FeProofs.PackedStore.Lanes
import FeProofs.Common.Basic
import Reasoning.ExternalCall

/-!
# FePackedStore `setBoth(uint256,uint256)`

Arm entry pc 56: call-value check, the two-word head check (pc 66), then two read-modify-writes of
word `packedSlot` (pc 79): lane 0 from the first argument's low byte, then lane 1 from the second's,
as the spec's two lane assignments do.  Under `STATICCALL` the first `SSTORE` halts, matching
Stele's static violation at the first lane assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

theorem fePackedStoreSetBothBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 2) rfl hsel
  have hd := fePackedStoreDispatch_setBoth hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSetBothBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd (hbad.elim
      decodeCalldata_uint256_uint256_none_short decodeCalldata_uint256_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  rd_run rd to 79 using [hwv, solcDecodeLenCheckOk_4_64 hlen hhi hsize]
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
    simp only [keccak_packedSlot] at rd
    have hp1 : evm1.executionEnv.perm = true := by
      rw [hevm1, storageStore_executionEnv]; simp only [hevm, initState]; exact hperm
    refine (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _)).reEquivExecutionGen hcode
      hd hdec (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by simp only [hevm, initState]; exact hperm)) hv0 ha0)
        (ExecBlock.consNormal (ExecStmt.assign (Or.inr hp1) hv1 ha1) ExecBlock.nil))))
      ?_ (returnEquiv.fallthrough rfl rfl (by native_decide))
    have hs0 : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
    set v0 := setPackedByte (solcSlotWord σ I packedSlot) (calldataWord I.calldata 4) 0
    have hs1 := hs0.storageWrite packedSlot v0
    have hevm1' : evm1 = Stele.EVM.storageStore evm I.codeOwner packedSlot v0 := by
      rw [hevm1, hs0.storageRead]
      rfl
    have hs2 := hs1.storageWrite packedSlot (setPackedByte
      (solcSlotWord (sstoreAccountMap I.codeOwner σ packedSlot v0) I packedSlot)
      (calldataWord I.calldata 36) 1)
    rw [← setPackedByte_lane0, ← setPackedByte_lane1]
    refine hs2.accounts.trans ?_
    have hload : Stele.EVM.storageLoad evm1 evm1.executionEnv.codeOwner packedSlot =
        solcSlotWord (sstoreAccountMap I.codeOwner σ packedSlot v0) I packedSlot := by
      rw [hevm1']; exact hs1.storageRead packedSlot
    have hco : evm1.executionEnv.codeOwner = I.codeOwner := by rw [hevm1', hs1.env]
    rw [hload, hco, ← hevm1']
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact RDstatic.reEquivStaticHalt hcode rd hd hdec
      (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consStatic
        (ExecStmt.assignStatic hv0 ha0 (by simp only [hevm, initState]; exact hpf)))))

end FeProofs.PackedStore
