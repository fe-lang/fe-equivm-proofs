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
  · have rd1 := feScalarStoreBlocks.feScalarStore_block_36_taken (by simp) (by rw [hwv]; decide)
      (by jump_dest) rd
    by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨hlen, hhi⟩ := hok
      have rd2 := feScalarStoreBlocks.feScalarStore_block_46_fallthrough (by simp)
        (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
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
      · have rret := feScalarStoreBlocks.feScalarStore_block_59 (by simp) hperm rd2
        refine rret.reEquivExecutionGen hcode hd (feScalarStoreSetDecode_ok hlen hhi)
          (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hval hassign)
              ExecBlock.nil))) (by rw [storageStore_accountMap]; rfl)
          (returnEquiv.fallthrough rfl rfl (by native_decide))
      · have hpf : I.perm = false := by simpa using hperm
        have r1 := rd2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
        have r2 := r1.calldataload (by native_decide) (by evm_ov)
        have r3 := r2.push0 (by native_decide) (by evm_ov)
        have rs := r3.sstoreStatic hpf (by native_decide) (by evm_ov)
        exact RDstatic.reEquivStaticHalt hcode rs hd (feScalarStoreSetDecode_ok hlen hhi)
          (ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
            (ExecBlock.consStatic (ExecStmt.assignStatic hval hassign
              (by show I.perm = false; exact hpf)))))
    · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = ⟨1⟩ := by
        rcases hbad with h | h
        · exact solcDecodeLenCheckShort_4_32 hsz h hsize
        · exact solcDecodeLenCheckHuge_4_32 h hsize
      have rd2 := feScalarStoreBlocks.feScalarStore_block_46_taken (by simp)
        (by rw [hslt]; decide) (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode (feScalarStoreBlocks.feScalarStore_block_42 (by simp) rd2)
        hd (feScalarStoreSetDecode_none hbad)
  · have rd1 := feScalarStoreBlocks.feScalarStore_block_36_fallthrough (by simp)
      (isZero_eq_zero_of_ne hwv) rd
    exact RDrev.reEquivDispatchedRevert hcode (feScalarStoreBlocks.feScalarStore_block_42 (by simp) rd1)
      hd fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ScalarStore
