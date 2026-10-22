import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `transferFrom(address,address,uint256)`

Arm entry pc 203: the call-value check (revert block 86), the three-word head check at pc 209 and
the canonicality checks of `from` (pc 221) and `to` (pc 231).  Pc 241 compares
`allowance[from][caller]` with `value` (short: `Error(string)` revert at 276/810) and pc 315
compares `balanceOf[from]` (short: revert at 336/810).  Pc 372 stores the reduced allowance and
re-reads `balanceOf[from]` for Fe's checked subtraction (panic at 520); pc 426 stores the debit
and adds `value` to `balanceOf[to]` (an overflow panics at 520); pc 460 stores the credit, logs
`Transfer` and returns `true`.  Each read after a store sees that store, as in the Stele body, so
the proof needs no disjointness of the slots.  Under `STATICCALL` the allowance `SSTORE` halts,
as the Stele allowance assignment does.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The argument store `transferFrom(address,address,uint256)` decodes. -/
abbrev transferFromLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "to" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert
    "value" (.int (Int.ofNat (calldataWord I.calldata 68).toNat))

/-- The slot of `allowance[from][msg.sender]`. -/
abbrev transferFromAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (UInt256.ofNat I.source.val) (mapSlot (calldataWord I.calldata 4) ⟨1⟩)

/-- `allowance[from][msg.sender]` in `σ`. -/
abbrev transferFromAllowance (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (transferFromAllowanceSlot I)

/-- `balanceOf[from]` in `σ`. -/
abbrev transferFromBal (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  balanceWord σ I (calldataWord I.calldata 4)

/-- The account map after the allowance store. -/
abbrev transferFromSpent (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlot I)
    (UInt256.sub (transferFromAllowance σ I) (calldataWord I.calldata 68))

/-- The account map after the debit of `from`. -/
abbrev transferFromDebited (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (transferFromSpent σ I) (mapSlot (calldataWord I.calldata 4) ⟨0⟩)
    (UInt256.sub (transferFromBal (transferFromSpent σ I) I) (calldataWord I.calldata 68))

/-- `balanceOf[to]` after the debit. -/
abbrev transferFromToBal (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  balanceWord (transferFromDebited σ I) I (calldataWord I.calldata 36)

/-- The frame after `currentAllowance` is bound. -/
abbrev transferFromFrame (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := (transferFromLocals I).insert "currentAllowance"
      (.int (Int.ofNat (transferFromAllowance σ I).toNat)) }

/-- `balanceOf[from]`. -/
abbrev balanceOfFrom : StorageRef := { base := "balanceOf", steps := [.mindex (.var "from")] }

/-- `allowance[from][msg.sender]`. -/
abbrev allowanceFromCaller : StorageRef :=
  { base := "allowance", steps := [.mindex (.var "from"), .mindex (.env .caller)] }

/-- The Stele state after the allowance store. -/
abbrev transferFromSpentState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) :
    EVM.State :=
  Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (transferFromAllowanceSlot I)
    (UInt256.sub (transferFromAllowance σ I) (calldataWord I.calldata 68))

/-- The Stele state after the debit of `from`. -/
abbrev transferFromDebitState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) :
    EVM.State :=
  Stele.EVM.storageStore (transferFromSpentState σ σ₀ g A I) I.codeOwner
    (mapSlot (calldataWord I.calldata 4) ⟨0⟩)
    (UInt256.sub (transferFromBal (transferFromSpent σ I) I) (calldataWord I.calldata 68))

section
variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}

theorem transferFrom_fromVar (evm : EVM.State) :
    evalExpr? config (transferFromFrame σ I) evm (.var "from") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
  evalVarF (by store_get)

theorem transferFrom_toVar (evm : EVM.State) :
    evalExpr? config (transferFromFrame σ I) evm (.var "to") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) :=
  evalVarF (by store_get)

theorem transferFrom_value (evm : EVM.State) :
    evalExpr? config (transferFromFrame σ I) evm (.var "value") =
      .ok (.int (Int.ofNat (calldataWord I.calldata 68).toNat)) :=
  evalVarF (by store_get)

theorem transferFrom_currentAllowance (evm : EVM.State) :
    evalExpr? config (transferFromFrame σ I) evm (.var "currentAllowance") =
      .ok (.int (Int.ofNat (transferFromAllowance σ I).toNat)) :=
  evalVarF (by store_get)

theorem transferFrom_fromArg (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := transferFromLocals I } evm (.var "from") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
  evalVarF (by store_get)

theorem transferFrom_allowance (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := transferFromLocals I } (initState σ σ₀ g A I)
      (.storage allowanceFromCaller) = .ok (.int (Int.ofNat (transferFromAllowance σ I).toNat)) := by
  rw [allowance_read (by store_get) (transferFrom_fromArg _)
      (Reasoning.VyperDispatch.evalExpr_caller _), keyValueToWord_address_of_canonical _ hc0,
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address,
    codeOwnerStorageWord_initState]

theorem transferFrom_allowanceCheck :
    evalExpr? config (transferFromFrame σ I) (initState σ σ₀ g A I)
      (.binary .ge (.var "currentAllowance") (.var "value")) =
      .ok (.bool (decide ((calldataWord I.calldata 68).toNat ≤ (transferFromAllowance σ I).toNat))) :=
  evalBin (by decide) (by decide) (transferFrom_currentAllowance _) (transferFrom_value _)
    (evalBinaryOp_ge_word _ _)

theorem transferFrom_bal (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (initState σ σ₀ g A I) (.storage balanceOfFrom) =
      .ok (.int (Int.ofNat (transferFromBal σ I).toNat)) := by
  rw [balanceOf_read (by store_get) (transferFrom_fromVar _),
    keyValueToWord_address_of_canonical _ hc0, show (initState σ σ₀ g A I).executionEnv = I from rfl,
    codeOwnerStorageWord_initState]

theorem transferFrom_balCheck (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (initState σ σ₀ g A I)
      (.binary .ge (.storage balanceOfFrom) (.var "value")) =
      .ok (.bool (decide ((calldataWord I.calldata 68).toNat ≤ (transferFromBal σ I).toNat))) :=
  evalBin (by decide) (by decide) (transferFrom_bal hc0) (transferFrom_value _)
    (evalBinaryOp_ge_word _ _)

theorem transferFrom_spend
    (h : (calldataWord I.calldata 68).toNat ≤ (transferFromAllowance σ I).toNat) :
    evalExpr? config (transferFromFrame σ I) (initState σ σ₀ g A I)
      (.binary .sub (.var "currentAllowance") (.var "value")) =
      .ok (.int (Int.ofNat
        (UInt256.sub (transferFromAllowance σ I) (calldataWord I.calldata 68)).toNat)) :=
  evalBin (by decide) (by decide) (transferFrom_currentAllowance _) (transferFrom_value _)
    (evalBinaryOp_sub_word h)

theorem transferFrom_spendAssign (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (w : UInt256) :
    assignStorageRef? config (transferFromFrame σ I) (initState σ σ₀ g A I) .storage
      allowanceFromCaller (.int (Int.ofNat w.toNat)) =
      .ok (transferFromFrame σ I, Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner
        (transferFromAllowanceSlot I) w) := by
  rw [allowance_assign (by store_get) (transferFrom_fromVar _)
      (Reasoning.VyperDispatch.evalExpr_caller _), keyValueToWord_address_of_canonical _ hc0,
    show (initState σ σ₀ g A I).executionEnv = I from rfl, keyValueToWord_address]

theorem transferFrom_bal1 (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (transferFromSpentState σ σ₀ g A I)
      (.storage balanceOfFrom) = .ok (.int (Int.ofNat (transferFromBal (transferFromSpent σ I) I).toNat)) := by
  rw [balanceOf_read (by store_get) (transferFrom_fromVar _),
    keyValueToWord_address_of_canonical _ hc0, storageStore_executionEnv,
    show (initState σ σ₀ g A I).executionEnv = I from rfl, storageLoad_after_initState_store]
  rfl

theorem transferFrom_debit (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (transferFromSpentState σ σ₀ g A I)
      (.binary .sub (.storage balanceOfFrom) (.var "value")) =
      .ok (.int (Int.ofNat (transferFromBal (transferFromSpent σ I) I).toNat -
        Int.ofNat (calldataWord I.calldata 68).toNat)) :=
  evalBin (by decide) (by decide) (transferFrom_bal1 hc0) (transferFrom_value _) rfl

theorem transferFrom_debitAssign (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (w : UInt256) :
    assignStorageRef? config (transferFromFrame σ I) (transferFromSpentState σ σ₀ g A I) .storage
      balanceOfFrom (.int (Int.ofNat w.toNat)) =
      .ok (transferFromFrame σ I, Stele.EVM.storageStore (transferFromSpentState σ σ₀ g A I)
        I.codeOwner (mapSlot (calldataWord I.calldata 4) ⟨0⟩) w) := by
  rw [balanceOf_assign (by store_get) (transferFrom_fromVar _),
    keyValueToWord_address_of_canonical _ hc0, storageStore_executionEnv]
  rfl

theorem transferFrom_toBal (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (transferFromDebitState σ σ₀ g A I)
      (.storage balanceOfTo) = .ok (.int (Int.ofNat (transferFromToBal σ I).toNat)) := by
  rw [balanceOf_read (by store_get) (transferFrom_toVar _),
    keyValueToWord_address_of_canonical _ hc1, storageStore_executionEnv, storageStore_executionEnv,
    show (initState σ σ₀ g A I).executionEnv = I from rfl, storageLoad_eq_solcSlotWord,
    storageStore_accountMap, storageStore_accountMap]
  rfl

theorem transferFrom_credit (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    evalExpr? config (transferFromFrame σ I) (transferFromDebitState σ σ₀ g A I)
      (.binary .add (.storage balanceOfTo) (.var "value")) =
      .ok (.int (Int.ofNat ((transferFromToBal σ I).toNat + (calldataWord I.calldata 68).toNat))) :=
  evalBin (by decide) (by decide) (transferFrom_toBal hc1) (transferFrom_value _)
    (evalBinaryOp_add_word _ _)

theorem transferFrom_creditAssign (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (w : UInt256) :
    assignStorageRef? config (transferFromFrame σ I) (transferFromDebitState σ σ₀ g A I) .storage
      balanceOfTo (.int (Int.ofNat w.toNat)) =
      .ok (transferFromFrame σ I, Stele.EVM.storageStore (transferFromDebitState σ σ₀ g A I)
        I.codeOwner (mapSlot (calldataWord I.calldata 36) ⟨0⟩) w) := by
  rw [balanceOf_assign (by store_get) (transferFrom_toVar _),
    keyValueToWord_address_of_canonical _ hc1, storageStore_executionEnv, storageStore_executionEnv]
  rfl

theorem transferFrom_event (evm : EVM.State) :
    evalExprs? config (transferFromFrame σ I) evm [.var "from", .var "to", .var "value"] =
      .ok [.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat),
        .address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat),
        .int (Int.ofNat (calldataWord I.calldata 68).toNat)] := by
  simp only [evalExprs?, transferFrom_fromVar, transferFrom_toVar, transferFrom_value,
    EvalResult.bind, bind, pure]

end

section
variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
  (hwv : I.weiValue = ⟨0⟩) (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)

include hwv hc0

theorem transferFromBody_allowance
    (hlt : (transferFromAllowance σ I).toNat < (calldataWord I.calldata 68).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0))
      (ExecBlock.consRevert (ExecStmt.requireFalse (transferFrom_allowanceCheck.trans
        (by simp [hlt]))))))

variable (hallow : (calldataWord I.calldata 68).toNat ≤ (transferFromAllowance σ I).toNat)
include hallow

theorem transferFromBody_balance
    (hlt : (transferFromBal σ I).toNat < (calldataWord I.calldata 68).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0))
      (ExecBlock.consNormal (ExecStmt.requireTrue (transferFrom_allowanceCheck.trans
        (by simp [hallow])))
        (ExecBlock.consRevert (ExecStmt.requireFalse ((transferFrom_balCheck hc0).trans
          (by simp [hlt])))))))

variable (hbal : (calldataWord I.calldata 68).toNat ≤ (transferFromBal σ I).toNat)
include hbal

theorem transferFromBody_static (hpf : I.perm = false) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0))
      (ExecBlock.consNormal (ExecStmt.requireTrue (transferFrom_allowanceCheck.trans
        (by simp [hallow])))
        (ExecBlock.consNormal (ExecStmt.requireTrue ((transferFrom_balCheck hc0).trans
          (by simp [hbal])))
          (ExecBlock.consStatic (ExecStmt.assignStatic (transferFrom_spend hallow)
            (transferFrom_spendAssign hc0 _) hpf))))))

variable (hperm : I.perm = true)
include hperm

theorem transferFromBody_underflow
    (hlt : (transferFromBal (transferFromSpent σ I) I).toNat < (calldataWord I.calldata 68).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0))
      (ExecBlock.consNormal (ExecStmt.requireTrue (transferFrom_allowanceCheck.trans
        (by simp [hallow])))
        (ExecBlock.consNormal (ExecStmt.requireTrue ((transferFrom_balCheck hc0).trans
          (by simp [hbal])))
          (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (transferFrom_spend hallow)
            (transferFrom_spendAssign hc0 _))
            (ExecBlock.consRevert (ExecStmt.assignExprRevert
              (evalInRange256_sub_revert (transferFrom_debit hc0) hlt))))))))

variable (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
  (hsub : (calldataWord I.calldata 68).toNat ≤ (transferFromBal (transferFromSpent σ I) I).toNat)
include hc1 hsub

theorem transferFromBody_overflow
    (hover : UInt256.size ≤ (transferFromToBal σ I).toNat + (calldataWord I.calldata 68).toNat) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
    (ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0))
      (ExecBlock.consNormal (ExecStmt.requireTrue (transferFrom_allowanceCheck.trans
        (by simp [hallow])))
        (ExecBlock.consNormal (ExecStmt.requireTrue ((transferFrom_balCheck hc0).trans
          (by simp [hbal])))
          (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (transferFrom_spend hallow)
            (transferFrom_spendAssign hc0 _))
            (ExecBlock.consNormal (ExecStmt.assign
              (Or.inr (by rw [storageStore_executionEnv]; exact hperm))
              (evalInRange256_sub (transferFrom_debit hc0) hsub) (transferFrom_debitAssign hc0 _))
              (ExecBlock.consRevert (ExecStmt.assignExprRevert
                (evalInRange256_add_revert (transferFrom_credit hc1) hover)))))))))

theorem transferFromBody_returns
    (hfit : (transferFromToBal σ I).toNat + (calldataWord I.calldata 68).toNat < UInt256.size) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (transferFromLocals I)
      transferFromTransition.body
      (.returned (transferFromFrame σ I) (Stele.EVM.storageStore (transferFromDebitState σ σ₀ g A I)
        I.codeOwner (mapSlot (calldataWord I.calldata 36) ⟨0⟩)
        (transferFromToBal σ I + calldataWord I.calldata 68)) (some [.bool true])) := by
  have hperm1 : (transferFromSpentState σ σ₀ g A I).executionEnv.perm = true := by
    rw [storageStore_executionEnv]; exact hperm
  have hperm2 : (transferFromDebitState σ σ₀ g A I).executionEnv.perm = true := by
    rw [storageStore_executionEnv]; exact hperm1
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (transferFrom_allowance hc0)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (transferFrom_allowanceCheck.trans
    (by simp [hallow]))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ((transferFrom_balCheck hc0).trans
    (by simp [hbal]))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (transferFrom_spend hallow)
    (transferFrom_spendAssign hc0 _)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm1)
    (evalInRange256_sub (transferFrom_debit hc0) hsub) (transferFrom_debitAssign hc0 _)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm2)
    (evalInRange256_add (transferFrom_credit hc1) hfit) (transferFrom_creditAssign hc1 _)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit (by rw [storageStore_executionEnv]; exact hperm2)
    (transferFrom_event _)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

end

/-- `transferFrom(address,address,uint256)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem feERC20TransferFromBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 2) rfl hsel
  have hd := feERC20Dispatch_transferFrom hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTransferFromBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 100 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 100 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 3 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd (hbad.elim
      (decodeCalldata_address_address_uint256_none_short hsz)
      decodeCalldata_address_address_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcCalldataStaticLenCheckOk (words := 3) hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (decodeCalldata_address_address_uint256_none_noncanon0 hlen hhi hc0)
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (decodeCalldata_address_address_uint256_none_noncanon1 hlen hhi hc0 hc1)
  have hdec : config.externalABI.decodeCalldata? (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromLocals I) :=
    decodeCalldata_address_address_uint256_ok hlen hhi hc0 hc1
  rd_run rd to 241 using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  by_cases hallow : (calldataWord I.calldata 68).toNat ≤ (transferFromAllowance σ I).toNat
  swap
  · -- short allowance: `Error(string)` revert
    have hlt := Nat.lt_of_not_le hallow
    rd_run rd using [slot_hint (isZero_lt_eq_zero hlt)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec (transferFromBody_allowance hwv hc0 hlt)
  by_cases hbal : (calldataWord I.calldata 68).toNat ≤ (transferFromBal σ I).toNat
  swap
  · -- short balance: `Error(string)` revert
    have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (isZero_lt_eq_zero hlt)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (transferFromBody_balance hwv hc0 hallow hlt)
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the allowance `SSTORE` halts
    have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (isZero_lt_ne_zero hbal)]
    exact RDstatic.reEquivStaticHalt hcode rd hd hdec
      (transferFromBody_static hwv hc0 hallow hbal hpf)
  by_cases hsub : (calldataWord I.calldata 68).toNat ≤
      (transferFromBal (transferFromSpent σ I) I).toNat
  swap
  · -- `balanceOf[from]`, re-read after the allowance store, is short: Fe's panic
    have hlt := Nat.lt_of_not_le hsub
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (isZero_lt_ne_zero hbal),
      slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (transferFromBody_underflow hwv hc0 hallow hbal hperm hlt)
  by_cases hfit : (transferFromToBal σ I).toNat + (calldataWord I.calldata 68).toNat < UInt256.size
  swap
  · -- `balanceOf[to] + value` overflows: Fe's panic
    have hover := Nat.le_of_not_lt hfit
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (isZero_lt_ne_zero hbal),
      slot_hint (ult_zero hsub), slot_hint (addCarry_ne_zero hover)]
    exact RDrev.reEquivExecutionRevert hcode rd hd hdec
      (transferFromBody_overflow hwv hc0 hallow hbal hperm hc1 hsub hover)
  rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (isZero_lt_ne_zero hbal),
    slot_hint (ult_zero hsub), slot_hint (addCarry_eq_zero hfit)]
  simp only [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact rd.reEquivExecutionGen hcode hd hdec
    (transferFromBody_returns hwv hc0 hallow hbal hperm hc1 hsub hfit)
    (by rw [storageStore_accountMap, storageStore_accountMap, storageStore_accountMap]; rfl)
    (returnEquiv_of_encode boolTrueReturnEncoding)

end FeProofs.ERC20
