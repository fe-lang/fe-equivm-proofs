import FeProofs.WETH9.Dispatch
import FeProofs.WETH9.MapStorage
import FeProofs.Common.Basic

/-!
# FeWETH9 `approve(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 162; reach lemma `feWETH9ReachApproveBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- The argument store `approve(address,uint256)` decodes. -/
abbrev approveLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "guy" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "wad" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

/-- The Stele slot of `allowance[msg.sender][guy]`. -/
abbrev approveSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (calldataWord I.calldata 4) (mapSlot (UInt256.ofNat I.source.val) ⟨4⟩)

theorem feWETH9ApproveDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some (approveLocals I) := by
  show decodeCalldata ["guy", "wad"] [.elem .address, abiUInt256] I.calldata = _
  exact decodeCalldata_addr_uint256_ok hsz68 hbig hcanon

theorem feWETH9ApproveDecode_none {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (h : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size ∨
      (68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
        ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)) :
    config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["guy", "wad"] [.elem .address, abiUInt256] I.calldata = _
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact decodeCalldata_addr_uint256_none_short hsz4 h
  · exact decodeCalldata_addr_uint256_none_huge h
  · exact decodeCalldata_addr_uint256_none_noncanon h1 h2 h3

theorem approveEval_guy (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveLocals I } evm (.var "guy") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
  evalVarF ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))

theorem approveEval_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveLocals I } evm (.var "wad") =
      .ok (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) :=
  evalVarF (store_get_self _ _ _)

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := approveLocals I } evm .storage
        { base := "allowance", steps := [.mindex (.env .caller), .mindex (.var "guy")] }
        (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) =
      .ok ({ contract := contract, locals := approveLocals I },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot I)
          (calldataWord I.calldata 36)) := by
  have h := allowance_assign (by simp [approveLocals])
    (Reasoning.VyperDispatch.evalExpr_caller evm)
    (approveEval_guy evm I) (calldataWord I.calldata 36)
  rw [keyValueToWord_address_of_canonical _ hcanon, keyValueToWord_address, hsrc] at h
  exact h

/-- `approve(address,uint256)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem feWETH9ApproveBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 1) rfl hsel
  have hd := feWETH9Dispatch_approve hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachApproveBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (feWETH9ApproveDecode_none hsz (by omega))
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (feWETH9ApproveDecode_none hsz (Or.inr (Or.inr ⟨hlen, hhi, hcanon⟩)))
  rd_run rd to 190 using [hwv, hc, shiftRight160_eq_zero hcanon]
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hcv : evalExpr? config { contract := contract, locals := approveLocals I } evmS
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp only [evmS, initState]; exact hwv)
  have hval := approveEval_wad evmS I
  have hassign := approveAssign evmS I (by simp only [evmS, initState]) hcanon
  by_cases hperm : I.perm = true
  · rd_step rd
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
    have hbody : ExecTransitionBody config contract evmS (approveLocals I) approveTransition.body
        (.returned { contract := contract, locals := approveLocals I }
          (Stele.EVM.storageStore evmS evmS.executionEnv.codeOwner (approveSlot I)
            (calldataWord I.calldata 36)) (some [(.bool true)])) := by
      refine ExecFuncBody.execBlockRet ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hcv) ?_
      refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) hval hassign) ?_
      exact ExecBlock.consReturn
        (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))
    exact RDret.reEquivExecutionGenSel hcode rd hd (feWETH9ApproveDecode_ok hlen hhi hcanon) hbody
      (by rw [storageStore_accountMap]; rfl)
      (returnEquiv_of_encode boolTrueReturnEncoding)
  -- static mode: the `SSTORE` of block 190 halts
  have hpf : I.perm = false := by simpa using hperm
  rd_step rd
  exact RDstatic.reEquivStaticHaltSel hcode rd hd (feWETH9ApproveDecode_ok hlen hhi hcanon)
    (ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consStatic (ExecStmt.assignStatic hval hassign
        (by show I.perm = false; exact hpf)))))

end FeProofs.WETH9
