import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `transfer(address,uint256)`

Arm entry pc 585: the call-value check (revert block 86), the two-word head check at pc 591 and
the `to` canonicality check at pc 603.  Pc 613 compares `balanceOf[caller]`
(`SLOAD(keccak256(caller ‖ 0))`) with `value` and jumps to the `Error(string)` revert at 336/810
when it is short; pc 636 is Fe's checked subtraction, the same comparison, so its panic is
unreachable.  Pc 660 stores the debit and adds `value` to `balanceOf[to]`, read after the debit
(an overflow jumps to the panic at 520), and pc 684 stores the credit, logs `Transfer` and returns
`true`.  Under `STATICCALL` the debit's `SSTORE` halts with a static-mode violation, matching the
Stele storage assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The argument store `transfer(address,uint256)` decodes. -/
abbrev transferLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "to" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "value" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

/-- The caller's balance before the call. -/
abbrev transferBal (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  balanceWord σ I (UInt256.ofNat I.source.val)

/-- The account map after the caller's debit. -/
abbrev transferDebited (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (mapSlot (UInt256.ofNat I.source.val) ⟨0⟩)
    (UInt256.sub (transferBal σ I) (calldataWord I.calldata 36))

/-- `balanceOf[to]` after the debit. -/
abbrev transferToBal (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  balanceWord (transferDebited σ I) I (calldataWord I.calldata 4)

/-- The frame `transfer`'s body starts in. -/
abbrev transferFrame (I : ExecutionEnv) : Frame := { contract := contract, locals := transferLocals I }

/-- `balanceOf[msg.sender]`. -/
abbrev balanceOfCaller : StorageRef := { base := "balanceOf", steps := [.mindex (.env .caller)] }

/-- The Stele state after the caller's debit. -/
abbrev transferDebitState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) :
    EVM.State :=
  Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (mapSlot (UInt256.ofNat I.source.val) ⟨0⟩)
    (UInt256.sub (transferBal σ I) (calldataWord I.calldata 36))

section
variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}

theorem transfer_to (evm : EVM.State) :
    evalExpr? config (transferFrame I) evm (.var "to") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
  evalVarF (by store_get)

theorem transfer_value (evm : EVM.State) :
    evalExpr? config (transferFrame I) evm (.var "value") =
      .ok (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) :=
  evalVarF (by store_get)

theorem transfer_bal : evalExpr? config (transferFrame I) (initState σ σ₀ g A I)
    (.storage balanceOfCaller) = .ok (.int (Int.ofNat (transferBal σ I).toNat)) := by
  rw [balanceOf_read (by store_get) (Reasoning.VyperDispatch.evalExpr_caller _),
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address,
    codeOwnerStorageWord_initState]

theorem transfer_check : evalExpr? config (transferFrame I) (initState σ σ₀ g A I)
    (.binary .ge (.storage balanceOfCaller) (.var "value")) =
      .ok (.bool (decide ((calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat))) :=
  evalBin (by decide) (by decide) transfer_bal (transfer_value _) (evalBinaryOp_ge_word _ _)

theorem transfer_debitEval (henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat) :
    evalExpr? config (transferFrame I) (initState σ σ₀ g A I)
      (.binary .sub (.storage balanceOfCaller) (.var "value")) =
      .ok (.int (Int.ofNat (UInt256.sub (transferBal σ I) (calldataWord I.calldata 36)).toNat)) :=
  evalBin (by decide) (by decide) transfer_bal (transfer_value _) (evalBinaryOp_sub_word henough)

theorem transfer_debitAssign (w : UInt256) :
    assignStorageRef? config (transferFrame I) (initState σ σ₀ g A I) .storage balanceOfCaller
      (.int (Int.ofNat w.toNat)) =
      .ok (transferFrame I, Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner
        (mapSlot (UInt256.ofNat I.source.val) ⟨0⟩) w) := by
  rw [balanceOf_assign (by store_get) (Reasoning.VyperDispatch.evalExpr_caller _),
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address]

theorem transfer_toBal (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFrame I) (transferDebitState σ σ₀ g A I) (.storage balanceOfTo) =
      .ok (.int (Int.ofNat (transferToBal σ I).toNat)) := by
  rw [balanceOf_read (by store_get) (transfer_to _), keyValueToWord_address_of_canonical _ hcanon,
    storageStore_executionEnv, show (initState σ σ₀ g A I).executionEnv = I from rfl,
    storageLoad_after_initState_store]
  rfl

theorem transfer_credit (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFrame I) (transferDebitState σ σ₀ g A I)
      (.binary .add (.storage balanceOfTo) (.var "value")) =
      .ok (.int (Int.ofNat ((transferToBal σ I).toNat + (calldataWord I.calldata 36).toNat))) :=
  evalBin (by decide) (by decide) (transfer_toBal hcanon) (transfer_value _)
    (evalBinaryOp_add_word _ _)

theorem transfer_creditAssign (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (w : UInt256) :
    assignStorageRef? config (transferFrame I) (transferDebitState σ σ₀ g A I) .storage balanceOfTo
      (.int (Int.ofNat w.toNat)) =
      .ok (transferFrame I, Stele.EVM.storageStore (transferDebitState σ σ₀ g A I) I.codeOwner
        (mapSlot (calldataWord I.calldata 4) ⟨0⟩) w) := by
  rw [balanceOf_assign (by store_get) (transfer_to _), keyValueToWord_address_of_canonical _ hcanon,
    storageStore_executionEnv]
  rfl

theorem transfer_event (evm : EVM.State) :
    evalExprs? config (transferFrame I) evm [.env .caller, .var "to", .var "value"] =
      .ok [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat),
        .int (Int.ofNat (calldataWord I.calldata 36).toNat)] := by
  simp only [evalExprs?, transfer_to, transfer_value, Reasoning.VyperDispatch.evalExpr_caller,
    EvalResult.bind, bind, pure]

theorem transferBody_insufficient (hwv : I.weiValue = ⟨0⟩)
    (hlt : (transferBal σ I).toNat < (calldataWord I.calldata 36).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consRevert (ExecStmt.requireFalse (transfer_check.trans (by simp [hlt])))))

theorem transferBody_static (hwv : I.weiValue = ⟨0⟩)
    (henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat) (hpf : I.perm = false) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.requireTrue (transfer_check.trans (by simp [henough])))
      (ExecBlock.consStatic (ExecStmt.assignStatic (transfer_debitEval henough)
        (transfer_debitAssign _) hpf))))

theorem transferBody_overflow (hwv : I.weiValue = ⟨0⟩)
    (henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat) (hperm : I.perm = true)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hover : UInt256.size ≤ (transferToBal σ I).toNat + (calldataWord I.calldata 36).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.requireTrue (transfer_check.trans (by simp [henough])))
      (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (transfer_debitEval henough)
        (transfer_debitAssign _))
        (ExecBlock.consRevert (ExecStmt.assignExprRevert
          (evalInRange256_add_revert (transfer_credit hcanon) hover))))))

theorem transferBody_returns (hwv : I.weiValue = ⟨0⟩)
    (henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat) (hperm : I.perm = true)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hfit : (transferToBal σ I).toNat + (calldataWord I.calldata 36).toNat < UInt256.size) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferLocals I)
      transferTransition.body
      (.returned (transferFrame I) (Stele.EVM.storageStore (transferDebitState σ σ₀ g A I)
        I.codeOwner (mapSlot (calldataWord I.calldata 4) ⟨0⟩)
        (transferToBal σ I + calldataWord I.calldata 36)) (some [.bool true])) := by
  have hperm1 : (transferDebitState σ σ₀ g A I).executionEnv.perm = true := by
    rw [storageStore_executionEnv]; exact hperm
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_)
  refine ExecBlock.consNormal (ExecStmt.requireTrue (transfer_check.trans (by simp [henough]))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (transfer_debitEval henough)
    (transfer_debitAssign _)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm1)
    (evalInRange256_add (transfer_credit hcanon) hfit) (transfer_creditAssign hcanon _)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit (by rw [storageStore_executionEnv]; exact hperm1)
    (transfer_event _)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

end

/-- `transfer(address,uint256)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem feERC20TransferBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 4) rfl hsel
  have hd := feERC20Dispatch_transfer hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTransferBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd (hbad.elim
      (decodeCalldata_addr_uint256_none_short hsz) decodeCalldata_addr_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (decodeCalldata_addr_uint256_none_noncanon hlen hhi hcanon)
  have hdec : config.externalABI.decodeCalldata? (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferLocals I) :=
    decodeCalldata_addr_uint256_ok hlen hhi hcanon
  rd_run rd to 613 using [hwv, hc, shiftRight160_eq_zero hcanon]
  by_cases henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat
  swap
  · -- short balance: `Error(string)` revert
    have hlt := Nat.lt_of_not_le henough
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec (transferBody_insufficient hwv hlt)
  have hge := ult_zero henough
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the debit's `SSTORE` halts
    have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint hge]
    exact RDstatic.reEquivStaticHalt hcode rd hd hdec (transferBody_static hwv henough hpf)
  by_cases hfit : (transferToBal σ I).toNat + (calldataWord I.calldata 36).toNat < UInt256.size
  swap
  · -- `balanceOf[to] + value` overflows: Fe's panic
    have hover := Nat.le_of_not_lt hfit
    rd_run rd using [slot_hint hge, slot_hint (addCarry_ne_zero hover)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (transferBody_overflow hwv henough hperm hcanon hover)
  rd_run rd using [slot_hint hge, slot_hint (addCarry_eq_zero hfit)]
  simp only [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact rd.reEquivExecutionGen hcode hd hdec (transferBody_returns hwv henough hperm hcanon hfit)
    (by rw [storageStore_accountMap, storageStore_accountMap]; rfl)
    (returnEquiv_of_encode boolTrueReturnEncoding)

end FeProofs.ERC20
