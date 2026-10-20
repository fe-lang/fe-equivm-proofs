import FeProofs.ScalarStore.Dispatch
import FeProofs.ScalarStore.Storage
import FeProofs.Common.Basic
import Reasoning.SteleArithmetic

/-!
# FeScalarStore `set(uint256)`

Arm entry pc 36: the call-value check, the Solidity-compatible head check at pc 46, then
`SSTORE(0, CALLDATALOAD(4))` and an empty `RETURN` at pc 59.  Under `STATICCALL` the `SSTORE`
halts with a static-mode violation, matching the Stele storage assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ScalarStore

set_option maxRecDepth 2000000

/-- The argument store `set(uint256)` decodes. -/
abbrev setLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "value" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

theorem feScalarStoreSetDecode_ok {I : ExecutionEnv} (hlen : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    config.externalABI.decodeCalldata? (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) := by
  show decodeCalldata ["value"] [abiUInt256] I.calldata = _
  exact decodeCalldata_uint256_ok hlen hhi

theorem feScalarStoreSetDecode_none {I : ExecutionEnv}
    (h : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [abiUInt256] I.calldata = _
  rcases h with h | h
  · exact decodeCalldata_uint256_none_short h
  · exact decodeCalldata_uint256_none_huge h

/-- `set(uint256)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem feScalarStoreSetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 0) rfl hsel
  have hd := feScalarStoreDispatch_set hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachSetBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [isZero_eq_zero_of_ne hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd (feScalarStoreSetDecode_none hbad)
  obtain ⟨hlen, hhi⟩ := hok
  rd_run rd to 59 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hcv : evalExpr? config { contract := contract, locals := setLocals I }
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp only [initState]; exact hwv)
  have hval := evalExpr_varUInt256 (cfg := config) (contract := contract)
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (store_get_self ∅ "value"
      (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
  have hassign := stored_write (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (L := setLocals I) (by simp [setLocals]) (calldataWord I.calldata 4)
  by_cases hperm : I.perm = true
  · rd_step rd
    refine rd.reEquivExecutionGen hcode hd (feScalarStoreSetDecode_ok hlen hhi)
      (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hval hassign)
          ExecBlock.nil))) (by rw [storageStore_accountMap]; rfl)
      (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact RDstatic.reEquivStaticHalt hcode rd hd (feScalarStoreSetDecode_ok hlen hhi)
      (ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consStatic (ExecStmt.assignStatic hval hassign
          (by show I.perm = false; exact hpf)))))

end FeProofs.ScalarStore
