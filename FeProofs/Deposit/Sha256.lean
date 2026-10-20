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
theorem staticCallBridge {σ : AccountMap} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {evm : EVM.State} {code mem rdata : ByteArray}
    {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.STATICCALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.solcStaticcallDepthLimit h hdec hd hov
    refine ⟨{ evm with substate :=
        (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
      σ, false, ByteArray.empty, _, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩, hr, by decide⟩
    exact callViaEVM.callNotMade rfl rfl
      (fun hgood ↦ hgood.2 (by simpa only [hs.env] using hd))
  · have hdl : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, AIn, gasCall, k', C', ⟨gasLeft, A', hΘ⟩, hr, hout⟩ :=
      RD.solcStaticcall h hdec hdl hov
    refine ⟨{ evm with accountMap := σ', substate := A' },
      σ', z, out, _, k', C', ?_, ⟨hs.world, hs.env, rfl⟩, hr, hout⟩
    apply callViaEVM.callMade (perm := false) (g' := gasLeft) wordOfInt_zero.symm
      ⟨gasCall, AIn, ?_⟩ rfl (Fin.zero_le _) (by simpa only [hs.env] using hd)
    simpa only [hs.env, ← hs.accounts, hs.world, accountAddress_roundtrip, Bool.false_and] using hΘ

/-- After a call returning at least a word into `[off, off + 32)` of memory that already covers
    that window, `MLOAD(off)` is the first returned word. -/
theorem callOutput_load (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (callOutputMem mem out off ⟨32⟩) = calldataWord out 0 := by
  have hsize := callOutput32_size mem out off hb hin
  unfold memLoad
  rw [if_neg (by rw [hsize]; omega), callOutput32_read_word mem out off hb hs (by omega),
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-! ## Stele side -/

/-- `address(2)` as the spec evaluates it. -/
abbrev precompile2 : AccountAddress := .ofNat 2

theorem precompile2_eq : EVM.address precompile2 = AccountAddress.ofUInt256 (UInt256.ofNat 2) := by
  decide

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

theorem sha64_eval_var {fr : Frame} {evm : EVM.State} {x : Ident} {v : Value}
    (h : fr.locals.get? x = some v) : evalExpr? config fr evm (.var x) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (fr.locals.get? x) = .ok v
  rw [h]
  rfl

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
  sha64_eval_var (by store_get)

theorem sha64_eval_ret {caller : Frame} {evm : EVM.State} {payload out : ByteArray} {z : Bool}
    (hout : 32 ≤ out.size) :
    evalExpr? config { caller with locals := sha64CallLocals payload out z } evm
      (.abiDecode (.elem (.int (.uint ⟨256, by decide⟩)))
        (.bytesSlice (.var "result") (.intLit 0) (.intLit 32))) =
      .ok (.int (Int.ofNat (calldataWord out 0).toNat)) := by
  have hdv : config.externalABI.decodeValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (out.extract 0 32) = some (.int (Int.ofNat (calldataWord out 0).toNat)) :=
    decodeReturnUint_extract (by omega) hout (by norm_num)
  have hres := sha64_eval_var (evm := evm)
    (fr := { caller with locals := sha64CallLocals payload out z }) (x := "result")
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
  sha64_eval_var (store_get_self _ _ _)

theorem sha64_eval_payload {caller : Frame} {evm : EVM.State} {payload : ByteArray} :
    evalExpr? config
      { caller with locals := (sha64Locals payload).insert "precompile" (.address precompile2) } evm
      (.var "payload") = .ok (.bytes payload) :=
  sha64_eval_var (by
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
    rw [sha64_eval_len, decide_eq_true (by rw [Int.ofNat_eq_coe]; exact_mod_cast hout)])) ?_
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
        rw [sha64_eval_len, decide_eq_false (by rw [Int.ofNat_eq_coe]; omega)]))

/-! ## `sha256_pair` -/

/-- The 64-byte payload `abi.encodePacked(uint256(a), uint256(b))`. -/
abbrev pairPayload (a b : UInt256) : ByteArray :=
  ByteArray.mk (EVM.Word.toBytesBE a ++ EVM.Word.toBytesBE b).toArray

theorem pairPayload_eq (a b : UInt256) : pairPayload a b = a.toByteArray ++ b.toByteArray := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray a, ← word_toBytesBE_toByteArray_eq_toByteArray b,
    ← List.toByteArray_append]
  apply ByteArray.ext
  simp

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
    evalPackedArgs_cons (sha64_eval_var hl) (encodePacked_uint256 a)
      (evalPackedArgs_single (sha64_eval_var hr) (encodePacked_uint256 b))
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
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (sha64_eval_var
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
