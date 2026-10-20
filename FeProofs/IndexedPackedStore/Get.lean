import FeProofs.IndexedPackedStore.Dispatch
import FeProofs.IndexedPackedStore.Elems
import FeProofs.Common.Basic

/-!
# FeIndexedPackedStore `get(uint256)`

Arm entry pc 336: call-value check, head check (pc 342), the `index < 64` check (pc 354), then the
lane read of word `keccak256(0) + index / 32` and the 32-byte return (pc 365).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev indexStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "index" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

theorem feIndexedPackedStoreGetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feIndexedPackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feIndexedPackedStoreSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feIndexedPackedStoreSelBytes 2) rfl hsel
  have hd := feIndexedPackedStoreDispatch_get (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feIndexedPackedStoreReachGetBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
        (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hbad with h | h
      · exact solcDecodeLenCheckShort_4_32 hsz h hsize
      · exact solcDecodeLenCheckHuge_4_32 h hsize
    rd_run rd using [hwv, hslt]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (hbad.elim decodeCalldata_uint256_none_short decodeCalldata_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  rd_run rd to 354 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hdec : config.externalABI.decodeCalldata? (getTransition.params.map Param.name)
      (transitionSignature getTransition).paramTypes I.calldata = some (indexStore I) := by
    show decodeCalldata ["index"] [abiUInt256] I.calldata = _
    exact decodeCalldata_uint256_ok hlen hhi
  set i := (calldataWord I.calldata 4).toNat with hi
  have hxi : (indexStore I).get? "index" = some (.int (Int.ofNat i)) := store_get_self _ _ _
  have hreq := ExecStmt.requireTrue (cfg := config)
    (stele := { contract := contract, locals := indexStore I })
    (evalCallvalueEq_true (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv))
  by_cases hin : i < 64
  swap
  · rd_run rd using [(by rw [ult_zero (by exact Nat.le_of_not_lt hin)]; decide)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consRevert
        (ExecStmt.requireFalse (by rw [evalIndexLt hxi, decide_eq_false hin])))))
  rd_run rd using [(by rw [ult_one (by exact hin)]; decide)]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide), laneRead_eq, shr5_eq] at rd
  have hval := evalElemCast (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hin hxi (by simp)
  exact rd.reEquivExecution hcode hd hdec
    (ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq (ExecBlock.consNormal
      (ExecStmt.requireTrue (by rw [evalIndexLt hxi, decide_eq_true hin]))
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hval))))))
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.IndexedPackedStore
