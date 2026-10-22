import FeProofs.WETH9.Deposit

/-!
# FeWETH9 `withdraw(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 340; reach lemma `feWETH9ReachWithdrawBody`.

The arm checks the call value (revert block 143) and the one-word head (pc 346).  Pc 358 reads
`balanceOf[caller]` (`SLOAD(keccak256(caller ‖ 3))` over memory `0xa0..0xe0`) and jumps to the
`assert!` panic at 1539 when it is below `wad`; pc 384 hashes the slot again, stores the debit
(the `SSTORE` halts in static mode, matching the Stele storage assignment) and branches on
`wad == 0` for the gas stipend (`2300` at pc 416, `0` at pc 411).  Pc 420 to 452 bump the free
pointer for the empty call buffers and push the arguments of the `CALL` at pc 453, which sends
`wad` to the caller with no input and no output copy.  `callBridge` couples it with Stele's
`callViaEVM` for the same opaque `Θ` result, whether the call is made or not (call depth,
insufficient balance), with the callee free to change any account.  Pc 454 asserts `success`
(panic at 1539) and pc 461 logs `Withdrawal` and returns nothing, leaving the post-call accounts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- The argument store `withdraw(uint256)` decodes. -/
abbrev withdrawLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "wad" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

/-- The frame `withdraw`'s body starts in. -/
abbrev withdrawFrame (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := withdrawLocals I }

/-- The frame after the transfer, with `success` and `_data` bound. -/
abbrev withdrawCallFrame (I : ExecutionEnv) (z : Bool) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := ((withdrawLocals I).insert "success" (.bool z)).insert "_data" (.bytes out) }

/-- The `wad` argument. -/
abbrev withdrawWad (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

/-- `balanceOf[msg.sender]` before the call. -/
abbrev withdrawBal (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (callerBalanceSlot I)

/-- The account map after the debit. -/
abbrev withdrawDebited (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (callerBalanceSlot I)
    (UInt256.sub (withdrawBal σ I) (withdrawWad I))

/-- The Stele state after the debit. -/
abbrev withdrawDebitState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) :
    EVM.State :=
  Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (callerBalanceSlot I)
    (UInt256.sub (withdrawBal σ I) (withdrawWad I))

/-- `balanceOf[msg.sender]`. -/
abbrev withdrawBalRef : StorageRef := { base := "balanceOf", steps := [.mindex (.env .caller)] }

theorem feWETH9WithdrawDecode_ok {I : ExecutionEnv} (hlen : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    config.externalABI.decodeCalldata? (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some (withdrawLocals I) := by
  show decodeCalldata ["wad"] [abiUInt256] I.calldata = _
  exact decodeCalldata_uint256_ok hlen hhi

theorem feWETH9WithdrawDecode_none {I : ExecutionEnv}
    (hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["wad"] [abiUInt256] I.calldata = _
  exact hbad.elim decodeCalldata_uint256_none_short decodeCalldata_uint256_none_huge

section
variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}

theorem withdraw_wad (evm : EVM.State) :
    evalExpr? config (withdrawFrame I) evm (.var "wad") =
      .ok (.int (Int.ofNat (withdrawWad I).toNat)) :=
  evalVarF (by store_get)

theorem withdraw_bal : evalExpr? config (withdrawFrame I) (initState σ σ₀ g A I)
    (.storage withdrawBalRef) = .ok (.int (Int.ofNat (withdrawBal σ I).toNat)) := by
  rw [balanceOf_read (by store_get) (Reasoning.VyperDispatch.evalExpr_caller _),
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address,
    codeOwnerStorageWord_initState]

theorem withdraw_check : evalExpr? config (withdrawFrame I) (initState σ σ₀ g A I)
    (.binary .ge (.storage withdrawBalRef) (.var "wad")) =
      .ok (.bool (decide ((withdrawWad I).toNat ≤ (withdrawBal σ I).toNat))) :=
  evalBin (by decide) (by decide) withdraw_bal (withdraw_wad _) (evalBinaryOp_ge_word _ _)

theorem withdraw_debitEval (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat) :
    evalExpr? config (withdrawFrame I) (initState σ σ₀ g A I)
      (.binary .sub (.storage withdrawBalRef) (.var "wad")) =
      .ok (.int (Int.ofNat (UInt256.sub (withdrawBal σ I) (withdrawWad I)).toNat)) :=
  evalBin (by decide) (by decide) withdraw_bal (withdraw_wad _) (evalBinaryOp_sub_word henough)

theorem withdraw_debitAssign :
    assignStorageRef? config (withdrawFrame I) (initState σ σ₀ g A I) .storage withdrawBalRef
      (.int (Int.ofNat (UInt256.sub (withdrawBal σ I) (withdrawWad I)).toNat)) =
      .ok (withdrawFrame I, withdrawDebitState σ σ₀ g A I) := by
  rw [balanceOf_assign (by store_get) (Reasoning.VyperDispatch.evalExpr_caller _),
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address]

/-- The transfer `(success, _data) = msg.sender.call{value: wad}(new bytes(0))`. -/
theorem withdraw_call {z : Bool} {evm' : EVM.State} {out : ByteArray} (hperm : I.perm = true)
    (hcall : callViaEVM (withdrawDebitState σ σ₀ g A I) I.source
      (Int.ofNat (withdrawWad I).toNat) ByteArray.empty (z, evm', out)) :
    ExecStmt config (withdrawFrame I) (withdrawDebitState σ σ₀ g A I)
      (.lowLevelCall (.env .caller) (.var "wad") (.newBytes (.intLit 0)) "success" "_data")
      (.ok (withdrawCallFrame I z out) evm') :=
  lowLevelCallSource (target := I.source)
    ((Reasoning.VyperDispatch.evalExpr_caller _).trans (by rw [storageStore_executionEnv]; rfl))
    (withdraw_wad _) (Reasoning.VyperDispatch.evalExpr_newBytes_zero _) hcall
    (Or.inr (by rw [storageStore_executionEnv]; exact hperm))

theorem withdraw_success (evm : EVM.State) (z : Bool) (out : ByteArray) :
    evalExpr? config (withdrawCallFrame I z out) evm (.var "success") = .ok (.bool z) :=
  evalVarF (by store_get)

theorem withdrawBody_insufficient (hwv : I.weiValue = ⟨0⟩)
    (hlt : (withdrawBal σ I).toNat < (withdrawWad I).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (withdrawLocals I)
      withdrawTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consRevert (ExecStmt.requireFalse (withdraw_check.trans (by simp [hlt])))))

theorem withdrawBody_static (hwv : I.weiValue = ⟨0⟩)
    (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat) (hpf : I.perm = false) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (withdrawLocals I)
      withdrawTransition.body .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.requireTrue (withdraw_check.trans (by simp [henough])))
      (ExecBlock.consStatic (ExecStmt.assignStatic (withdraw_debitEval henough) withdraw_debitAssign
        hpf))))

/-- The body up to and including the transfer; `require(success)` remains. -/
theorem withdrawBody_prefix {z : Bool} {evm' : EVM.State} {out : ByteArray} {res : ExecResult}
    (hwv : I.weiValue = ⟨0⟩) (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat)
    (hperm : I.perm = true)
    (hcall : callViaEVM (withdrawDebitState σ σ₀ g A I) I.source
      (Int.ofNat (withdrawWad I).toNat) ByteArray.empty (z, evm', out))
    (htail : ExecBlock config (withdrawCallFrame I z out) evm' [.require (.var "success")] res) :
    ExecBlock config (withdrawFrame I) (initState σ σ₀ g A I) withdrawTransition.body res :=
  ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.requireTrue (withdraw_check.trans (by simp [henough])))
      (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (withdraw_debitEval henough)
        withdraw_debitAssign)
        (ExecBlock.consNormal (withdraw_call hperm hcall) htail)))

theorem withdrawBody_failed {evm' : EVM.State} {out : ByteArray} (hwv : I.weiValue = ⟨0⟩)
    (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat) (hperm : I.perm = true)
    (hcall : callViaEVM (withdrawDebitState σ σ₀ g A I) I.source
      (Int.ofNat (withdrawWad I).toNat) ByteArray.empty (false, evm', out)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (withdrawLocals I)
      withdrawTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (withdrawBody_prefix hwv henough hperm hcall
    (ExecBlock.consRevert (ExecStmt.requireFalse (withdraw_success _ _ _))))

theorem withdrawBody_returns {evm' : EVM.State} {out : ByteArray} (hwv : I.weiValue = ⟨0⟩)
    (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat) (hperm : I.perm = true)
    (hcall : callViaEVM (withdrawDebitState σ σ₀ g A I) I.source
      (Int.ofNat (withdrawWad I).toNat) ByteArray.empty (true, evm', out)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (withdrawLocals I)
      withdrawTransition.body (.returned (withdrawCallFrame I true out) evm' none) :=
  ExecFuncBody.execBlockOK (withdrawBody_prefix hwv henough hperm hcall
    (ExecBlock.consNormal (ExecStmt.requireTrue (withdraw_success _ _ _)) ExecBlock.nil))

end

/-- From pc 420, with the debit stored and the gas stipend on the stack: the call buffers, the
transfer `CALL`, `assert!(success)`, the `Withdrawal` log and the empty return. -/
theorem withdrawFrom420 {σ σ₀ A I} {g gas aw : UInt256} {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = feWETH9Bytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat)
    (hd : selectorDispatchMsg contract I.calldata = some withdrawTransition)
    (hdec : config.externalABI.decodeCalldata? (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some (withdrawLocals I))
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 420) [gas, withdrawWad I, UInt256.ofNat I.source.val] mem aw ByteArray.empty
      (withdrawDebited σ I) k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  -- the call buffers: whichever free pointer `MLOAD(0x40)` gives, both are empty
  obtain ⟨q, aw, k, C, rd⟩ : ∃ q aw k C, RD feWETH9Bytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 435)
      [q, gas, withdrawWad I, UInt256.ofNat I.source.val] mem aw ByteArray.empty
      (withdrawDebited σ I) k C := by
    by_cases hq : UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223) = UInt256.ofNat 0
    · rd_run rd to 435 using [hq]
      exact ⟨_, _, _, _, rd⟩
    · rd_run rd to 435 using [hq]
      exact ⟨_, _, _, _, rd⟩
  rd_step rd
  obtain ⟨evm', σ', z, out, _, _, hcall, hs', rd, _⟩ := callBridge rd
    (SourceState.init.storageWrite (callerBalanceSlot I)
      (UInt256.sub (withdrawBal σ I) (withdrawWad I)))
    hperm (by native_decide) (byteArray_readWithPadding_zero _ _)
    (by show ByteArray.empty.size ≤ _; exact Nat.zero_le _) (by simp)
  rw [accountAddress_roundtrip] at hcall
  cases z
  · rd_run rd
    exact RDrev.reEquivExecutionRevertSel hcode rd hd hdec
      (withdrawBody_failed hwv henough hperm hcall)
  · rd_run rd
    u256_lits at rd
    rw [byteArray_readWithPadding_zero] at rd
    exact RDret.reEquivExecutionGenSel hcode rd hd hdec
      (withdrawBody_returns hwv henough hperm hcall) hs'.accounts
      (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))

/-- `withdraw(uint256)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem feWETH9WithdrawBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 4) rfl hsel
  have hd := feWETH9Dispatch_withdraw hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachWithdrawBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (feWETH9WithdrawDecode_none hbad)
  obtain ⟨hlen, hhi⟩ := hok
  have hdec := feWETH9WithdrawDecode_ok hlen hhi
  rd_run rd to 358 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  by_cases henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat
  swap
  · -- `balanceOf[caller] < wad`: `assert!` panics
    have hlt := Nat.lt_of_not_le henough
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevertSel hcode rd hd hdec (withdrawBody_insufficient hwv hlt)
  have hge := ult_zero henough
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the debit's `SSTORE` halts
    have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint hge]
    exact RDstatic.reEquivStaticHaltSel hcode rd hd hdec (withdrawBody_static hwv henough hpf)
  rd_run rd to 384 using [slot_hint hge]
  -- the gas stipend: `2300` when `wad == 0`, else `0`
  by_cases hz : UInt256.isZero (withdrawWad I) = UInt256.ofNat 0 <;>
  · rd_run rd to 420 using [hz]
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide)] at rd
    exact withdrawFrom420 hcode hperm hwv henough hd hdec rd

end FeProofs.WETH9
