import FeProofs.IndexedPackedStore.Dispatch
import FeProofs.IndexedPackedStore.Elems
import FeProofs.Common.Basic

/-!
# FeIndexedPackedStore `set(uint256,uint256)`

Arm entry pc 47: call-value check, head check (pc 53), the `index < 64` check (pc 65), then one
read-modify-write of word `keccak256(0) + index / 32` replacing byte `index % 32` with the value's
low byte (pc 79).  Under `STATICCALL` the `SSTORE` halts, matching Stele's static violation.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev setStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "index" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert "value"
    (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

theorem feIndexedPackedStoreSetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feIndexedPackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feIndexedPackedStoreSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feIndexedPackedStoreSelBytes 0) rfl hsel
  have hd := feIndexedPackedStoreDispatch_set hsel
  obtain ⟨k, C, rd⟩ := feIndexedPackedStoreReachSetBody (g := Sat256.ofUInt256 g) (σ := σ)
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
  rd_run rd to 65 using [hwv, solcDecodeLenCheckOk_4_64 hlen hhi hsize]
  have hdec : config.externalABI.decodeCalldata? (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = some (setStore I) := by
    show decodeCalldata ["index", "value"] [abiUInt256, abiUInt256] I.calldata = _
    exact decodeCalldata_uint256_uint256_ok hlen hhi
  set i := (calldataWord I.calldata 4).toNat with hi
  set evm := initState σ σ₀ (Sat256.ofUInt256 g) A I with hevm
  have hxi : (setStore I).get? "index" = some (.int (Int.ofNat i)) :=
    by rw [store_get_ne _ _ (by decide), store_get_self]
  have hreq := ExecStmt.requireTrue (cfg := config)
    (stele := { contract := contract, locals := setStore I })
    (evalCallvalueEq_true (evm := evm) (by simp only [hevm, initState]; exact hwv))
  by_cases hin : i < 64
  swap
  · rd_run rd using [(by rw [ult_zero (by exact Nat.le_of_not_lt hin)]; decide)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consRevert
        (ExecStmt.requireFalse (by rw [evalIndexLt hxi, decide_eq_false hin])))))
  rd_run rd to 79 using [(by rw [ult_one (by exact hin)]; decide)]
  have hval := evalCastU8 (evm := evm) (x := "value") (v := calldataWord I.calldata 36)
    (L := setStore I) (store_get_self _ _ _)
  have hasg := assignElem (evm := evm) hin hxi (by simp) (calldataWord I.calldata 36)
  have hreq2 := ExecStmt.requireTrue (cfg := config)
    (stele := { contract := contract, locals := setStore I }) (evm := evm)
    (by rw [evalIndexLt hxi, decide_eq_true hin])
  by_cases hperm : I.perm = true
  · rd_step rd
    refine (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _)).reEquivExecutionGen hcode
      hd hdec (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal hreq2
        (ExecBlock.consNormal
          (ExecStmt.assign (Or.inr (by simp only [hevm, initState]; exact hperm)) hval hasg)
          ExecBlock.nil))))
      ?_ (returnEquiv.fallthrough rfl rfl (by native_decide))
    rw [laneWrite_eq, shr5_eq, storageStore_accountMap]
    rfl
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact RDstatic.reEquivStaticHalt hcode rd
      hd hdec (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consNormal hreq2
        (ExecBlock.consStatic
          (ExecStmt.assignStatic hval hasg (by simp only [hevm, initState]; exact hpf))))))

end FeProofs.IndexedPackedStore
