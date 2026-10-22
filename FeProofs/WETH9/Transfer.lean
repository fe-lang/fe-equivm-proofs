import FeProofs.WETH9.TransferFrom

/-!
# FeWETH9 `transfer(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 592; reach lemma `feWETH9ReachTransferBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- The argument store `transfer(address,uint256)` decodes. -/
abbrev transferLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "dst" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "wad" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

/-- The locals `transferFrom(msg.sender, dst, wad)` runs with. -/
abbrev transferCalleeLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "wad" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))).insert "dst"
    (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "src" (.address I.source)

theorem feWETH9TransferDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferLocals I) := by
  show decodeCalldata ["dst", "wad"] [.elem .address, abiUInt256] I.calldata = _
  exact decodeCalldata_addr_uint256_ok hsz68 hbig hcanon

theorem feWETH9TransferDecode_none {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (h : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size ∨
      (68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
        ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)) :
    config.externalABI.decodeCalldata? (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["dst", "wad"] [.elem .address, abiUInt256] I.calldata = _
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact decodeCalldata_addr_uint256_none_short hsz4 h
  · exact decodeCalldata_addr_uint256_none_huge h
  · exact decodeCalldata_addr_uint256_none_noncanon h1 h2 h3

section
variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}

/-- The internal call's arguments `msg.sender, dst, wad`. -/
theorem transfer_args :
    evalExprs? config { contract := contract, locals := transferLocals I } (initState σ σ₀ g A I)
        [.env .caller, .var "dst", .var "wad"] =
      .ok [.address I.source, .address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat),
        .int (Int.ofNat (calldataWord I.calldata 36).toNat)] := by
  have hdst := evalVarF (cfg := config) (stele := { contract := contract, locals := transferLocals I })
    (evm := initState σ σ₀ g A I)
    (show (transferLocals I).get? "dst" =
      some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) by store_get)
  have hwad := evalVarF (cfg := config) (stele := { contract := contract, locals := transferLocals I })
    (evm := initState σ σ₀ g A I)
    (show (transferLocals I).get? "wad" =
      some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) by store_get)
  simp only [evalExprs?, Reasoning.VyperDispatch.evalExpr_caller, hdst, hwad, EvalResult.bind, bind,
    pure]
  rfl

theorem transfer_lookup : lookupCallable? contract "transferFrom" = some transferFromTransition.toCallable :=
  rfl

theorem transfer_bind :
    bindParams? transferFromTransition.toCallable.params
        [.address I.source, .address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat),
          .int (Int.ofNat (calldataWord I.calldata 36).toNat)] = some (transferCalleeLocals I) :=
  rfl

variable (hwv : I.weiValue = ⟨0⟩)
include hwv

theorem transferBody_reverts
    (hcallee : ExecTransitionBody config contract (initState σ σ₀ g A I) (transferCalleeLocals I)
      transferFromTransition.body .reverted) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consRevert (internalCallTransitionRevert
      (caller := { contract := contract, locals := transferLocals I })
      transfer_args transfer_lookup transfer_bind hcallee)))

theorem transferBody_static
    (hcallee : ExecTransitionBody config contract (initState σ σ₀ g A I) (transferCalleeLocals I)
      transferFromTransition.body .staticViolation) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consStatic (ExecStmt.internalCallStatic transfer_args transfer_lookup
      transfer_bind hcallee)))

theorem transferBody_returns {e' : EVM.State}
    (hcallee : ExecTransitionBody config contract (initState σ σ₀ g A I) (transferCalleeLocals I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferCalleeLocals I } e' (some [.bool true]))) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body
      (.returned { contract := contract, locals := (transferLocals I).insert "_ok" (.bool true) } e'
        (some [.bool true])) :=
  ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (internalCallTransitionReturn
      (caller := { contract := contract, locals := transferLocals I })
      transfer_args transfer_lookup transfer_bind hcallee)
      (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure])))))

end

/-- `transfer(address,uint256)`: the theorem `Correct.lean` routes selector 8 to. -/
theorem feWETH9TransferBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 8)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 8) rfl hsel
  have hd := feWETH9Dispatch_transfer
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachTransferBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
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
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (feWETH9TransferDecode_none hsz (by omega))
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (feWETH9TransferDecode_none hsz (Or.inr (Or.inr ⟨hlen, hhi, hcanon⟩)))
  have hdec := feWETH9TransferDecode_ok hlen hhi hcanon
  rd_run rd to 1305 using [hwv, hc, shiftRight160_eq_zero hcanon]
  have hsrcL : (transferCalleeLocals I).get? "src" = some (.address I.source) := by store_get
  have hdstL : (transferCalleeLocals I).get? "dst" =
      some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) := by store_get
  have hwadL : (transferCalleeLocals I).get? "wad" =
      some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) := by store_get
  have hbo : (transferCalleeLocals I).get? "balanceOf" = none := by store_get
  have hal : (transferCalleeLocals I).get? "allowance" = none := by store_get
  by_cases hbal : (calldataWord I.calldata 36).toNat ≤
      (solcSlotWord σ I (mapSlot (addrWord I.source) ⟨3⟩)).toNat
  swap
  · have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevertSel hcode rd hd hdec (transferBody_reverts hwv
      (tfBody_balance (hcv := hwv) (hbo := hbo) (hsrc := hsrcL) (hwad := hwadL)
        (by rw [loadAt_initState]; exact hlt)))
  have hbalS : (calldataWord I.calldata 36).toNat ≤
      (loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I) (balSlot I.source)).toNat := by
    rw [loadAt_initState]; exact hbal
  rd_run rd to 1450 using [slot_hint (ult_zero hbal), u256_eq_refl (addrWord I.source)]
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    exact RDstatic.reEquivStaticHaltSel hcode (tfTailStatic hpf rd) hd hdec (transferBody_static hwv
      (tfBody_skipStatic (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hwad := hwadL)
        (hbal := hbalS) (Or.inl rfl) hpf))
  obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write_read_back_of_gap _ mem' 224 (small_gap mem' 224 (by decide))] at rd
  refine RDret.reEquivExecutionGenSel hcode rd hd hdec (transferBody_returns hwv
    (tfBody_skipReturns (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hdst := hdstL)
      (hwad := hwadL) (hbal := hbalS) (Or.inl rfl) hperm)) ?_
    (returnEquiv_of_encode boolTrueReturnEncoding)
  rw [tfMove_accountMap (I := I) rfl, addrWord_ofNat hcanon]
  rfl

end FeProofs.WETH9
