import FeProofs.Deposit.Common
import Reasoning.ExternalCall
import Reasoning.SteleBody
import Reasoning.HeapMemory

/-!
# FeDeposit SHA-256 calls

Every SHA-256 in the deposit contract is a `STATICCALL` to precompile 2 over a 64-byte buffer,
reverting unless the call succeeds and returns at least 32 bytes, and then using the first returned
word.  The spec's `sha256_64`/`sha256_pair` helpers make the same opaque `Θ` call
(`lowLevelCall … (perm := false)`), so the two sides coincide whenever the payload bytes agree.

* `staticCallBridge` — the EVM `STATICCALL` step and the matching Stele `callViaEVM`, from any
  Stele state tracking the EVM accounts (`SourceState`).
* `shaPairCall_ok` / `shaPairCall_revert` — the `sha256_pair(a, b)` internal call over a call
  result.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## EVM side -/

-- GENERALIZES Benchmarks.Safe.V3_77901a5.rawStaticCallTraceFrom — phrased over `SourceState`
-- (LIBRARY CANDIDATE: `Reasoning/ExternalCall.lean`, beside `callBridge`).
/-! ## Stele side -/

abbrev sha64Fn : FunctionDecl := contract.functions[0]!
abbrev shaPairFn : FunctionDecl := contract.functions[1]!

theorem sha64Fn_lookup : lookupCallable? contract "sha256_64" = some sha64Fn.toCallable := by
  rfl

theorem shaPairFn_lookup : lookupCallable? contract "sha256_pair" = some shaPairFn.toCallable := by
  rfl

/-- The `sha256_64` frame after binding `payload`. -/
abbrev sha64Locals (payload : ByteArray) : Store := (∅ : Store).insert "payload" (.bytes payload)

/-- The `sha256_64` frame after the call. -/
abbrev sha64CallLocals (payload out : ByteArray) (z : Bool) : Store :=
  (((sha64Locals payload).insert "precompile" (.address precompile2)).insert "ok" (.bool z)).insert
    "result" (.bytes out)

theorem sha64_eval_precompile {fr : Frame} {evm : EVM.State} :
    evalExpr? config fr evm (.cast (.intLit 2) (.elem .address)) = .ok (.address precompile2) := by
  simp [evalExpr?, castValue?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem sha64_eval_zero {fr : Frame} {evm : EVM.State} :
    evalExpr? config fr evm (.intLit 0) = .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem sha64_eval_len {caller : Frame} {evm : EVM.State} {payload out : ByteArray} {z : Bool} :
    evalExpr? config { caller with locals := sha64CallLocals payload out z } evm
      (.binary .ge (.arrayLength .localVar { base := "result", steps := [] }) (.intLit 32)) =
      .ok (.bool (decide ((32 : Int) ≤ Int.ofNat out.size))) := by
  simp [evalExpr?, readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem sha64_eval_ok {caller : Frame} {evm : EVM.State} {payload out : ByteArray} {z : Bool} :
    evalExpr? config { caller with locals := sha64CallLocals payload out z } evm (.var "ok") =
      .ok (.bool z) :=
  evalVarF (by store_get)

theorem sha64_eval_ret {caller : Frame} {evm : EVM.State} {payload out : ByteArray} {z : Bool}
    (hout : 32 ≤ out.size) :
    evalExpr? config { caller with locals := sha64CallLocals payload out z } evm
      (.abiDecode (.elem (.int (.uint ⟨256, by decide⟩)))
        (.bytesSlice (.var "result") (.intLit 0) (.intLit 32))) =
      .ok (.int (Int.ofNat (calldataWord out 0).toNat)) := by
  have hdv : config.externalABI.decodeValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (out.extract 0 32) = some (.int (Int.ofNat (calldataWord out 0).toNat)) :=
    decodeReturnUint_extract (by omega) hout (by norm_num)
  have hres := evalVarF (evm := evm)
    (cfg := config) (stele := { caller with locals := sha64CallLocals payload out z }) (name := "result")
    (v := .bytes out) (store_get_self _ _ _)
  have hslice : sliceBytes? out 0 32 = .ok (.bytes (out.extract 0 32)) := by
    simp only [sliceBytes?]
    rw [if_neg (by decide), if_neg (by simp; omega)]
    rfl
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind, hres, sha64_eval_zero]
  rw [show evalExpr? config { caller with locals := sha64CallLocals payload out z } evm (.intLit 32) =
      .ok (.int 32) by simp [evalExpr?, pure]]
  simp only [hslice, hdv, pure]

theorem sha64_eval_receiver {caller : Frame} {evm : EVM.State} {payload : ByteArray} :
    evalExpr? config
      { caller with locals := (sha64Locals payload).insert "precompile" (.address precompile2) } evm
      (.var "precompile") = .ok (.address precompile2) :=
  evalVarF (store_get_self _ _ _)

theorem sha64_eval_payload {caller : Frame} {evm : EVM.State} {payload : ByteArray} :
    evalExpr? config
      { caller with locals := (sha64Locals payload).insert "precompile" (.address precompile2) } evm
      (.var "payload") = .ok (.bytes payload) :=
  evalVarF (by
    rw [store_get_ne (sha64Locals payload) (k := "precompile") (a := "payload") _ (by decide),
      store_get_self])

theorem sha64Body_ok {caller : Frame} {evm evm' : EVM.State} {payload out : ByteArray}
    (hcall : callViaEVM evm (EVM.address precompile2) 0 payload (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecFuncBody config { caller with locals := sha64Locals payload } evm sha64Fn.body
      (.returned { caller with locals := sha64CallLocals payload out true } evm'
        (some [.int (Int.ofNat (calldataWord out 0).toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl sha64_eval_precompile) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess (Or.inl rfl) sha64_eval_receiver sha64_eval_zero
      sha64_eval_payload hcall) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue sha64_eval_ok) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by
    rw [sha64_eval_len, decide_eq_true (by rw [Int.ofNat_eq_natCast]; exact_mod_cast hout)])) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (sha64_eval_ret hout)))

theorem sha64Body_revert {caller : Frame} {evm evm' : EVM.State} {payload out : ByteArray} {z : Bool}
    (hcall : callViaEVM evm (EVM.address precompile2) 0 payload (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecFuncBody config { caller with locals := sha64Locals payload } evm sha64Fn.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl sha64_eval_precompile) ?_
  cases z with
  | false =>
      refine ExecBlock.consNormal
        (ExecStmt.lowLevelCallFailure (Or.inl rfl) sha64_eval_receiver sha64_eval_zero
          sha64_eval_payload hcall) ?_
      exact ExecBlock.consRevert (ExecStmt.requireFalse sha64_eval_ok)
  | true =>
      have hshort : out.size < 32 := by
        by_contra h
        exact hbad ⟨rfl, by omega⟩
      refine ExecBlock.consNormal
        (ExecStmt.lowLevelCallSuccess (Or.inl rfl) sha64_eval_receiver sha64_eval_zero
          sha64_eval_payload hcall) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue sha64_eval_ok) ?_
      exact ExecBlock.consRevert (ExecStmt.requireFalse (by
        rw [sha64_eval_len, decide_eq_false (by rw [Int.ofNat_eq_natCast]; omega)]))

/-! ## `sha256_pair` -/

/-- `sha256_pair`'s frame after binding `left` and `right`. -/
abbrev pairLocals (a b : UInt256) : Store :=
  ((∅ : Store).insert "right" (.int (Int.ofNat b.toNat))).insert "left" (.int (Int.ofNat a.toNat))

/-- The digest a successful call returns. -/
abbrev shaDigest (out : ByteArray) : Value := .int (Int.ofNat (calldataWord out 0).toNat)

theorem pair_eval_args {fr : Frame} {evm : EVM.State} {a b : UInt256}
    (hl : fr.locals.get? "left" = some (.int (Int.ofNat a.toNat)))
    (hr : fr.locals.get? "right" = some (.int (Int.ofNat b.toNat))) :
    evalExprs? config fr evm
      [.abiEncodePacked [(.elem (.int (.uint ⟨256, by decide⟩)), .var "left"),
        (.elem (.int (.uint ⟨256, by decide⟩)), .var "right")]] = .ok [.bytes (pairPayload a b)] := by
  apply evalExprs?_singleton
  have hpk : evalPackedArgs? config fr evm
      [(.elem (.int (.uint ⟨256, by decide⟩)), .var "left"),
        (.elem (.int (.uint ⟨256, by decide⟩)), .var "right")] =
      .ok (EVM.Word.toBytesBE a ++ EVM.Word.toBytesBE b) :=
    evalPackedArgs_cons (evalVarF hl) (encodePacked_uint256 a)
      (evalPackedArgs_single (evalVarF hr) (encodePacked_uint256 b))
  rw [evalExpr?]
  simp only [hpk, EvalResult.bind, bind, pure]

theorem shaPairBody_ok {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {a b : UInt256} {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address precompile2) 0 (pairPayload a b) (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecFuncBody config { caller with locals := pairLocals a b } evm shaPairFn.body
      (.returned { caller with locals := (pairLocals a b).insert "digest" (shaDigest out) } evm'
        (some [shaDigest out])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (internalCallFunctionReturn
    (pair_eval_args (by simp [pairLocals])
      (by store_get))
    (by rw [hc]; exact sha64Fn_lookup) rfl (sha64Body_ok hcall hout)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (evalVarF
    (by simp [resumeAfterInternalCall, collapseReturns]))))

theorem shaPairBody_revert {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {a b : UInt256} {out : ByteArray} {z : Bool}
    (hcall : callViaEVM evm (EVM.address precompile2) 0 (pairPayload a b) (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecFuncBody config { caller with locals := pairLocals a b } evm shaPairFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (pair_eval_args (by simp [pairLocals])
      (by store_get))
    (by rw [hc]; exact sha64Fn_lookup) rfl (sha64Body_revert hcall hbad))

/-- **`sha256_pair(ea, eb)` over a successful call** binds the first returned word. -/
theorem shaPairCall_ok {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {ea eb : Expr} {ret : Ident} {a b : UInt256} {out : ByteArray}
    (ha : evalExpr? config caller evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config caller evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hcall : callViaEVM evm (EVM.address precompile2) 0 (pairPayload a b) (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecStmt config caller evm (.internalCall "sha256_pair" [ea, eb] ret)
      (.ok { caller with locals := caller.locals.insert ret (shaDigest out) } evm') := by
  exact internalCallFunctionReturn (retVar := ret)
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)])
    (by simp [evalExprs?, ha, hb, EvalResult.bind, bind, pure])
    (by rw [hc]; exact shaPairFn_lookup) rfl (shaPairBody_ok hc hcall hout)

/-- **`sha256_pair(ea, eb)` reverts** when the call fails or returns less than a word. -/
theorem shaPairCall_revert {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {ea eb : Expr} {ret : Ident} {a b : UInt256} {out : ByteArray} {z : Bool}
    (ha : evalExpr? config caller evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config caller evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hcall : callViaEVM evm (EVM.address precompile2) 0 (pairPayload a b) (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecStmt config caller evm (.internalCall "sha256_pair" [ea, eb] ret) .reverted :=
  internalCallFunctionRevert (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)])
    (by simp [evalExprs?, ha, hb, EvalResult.bind, bind, pure])
    (by rw [hc]; exact shaPairFn_lookup) rfl (shaPairBody_revert hc hcall hbad)

end FeProofs.Deposit
