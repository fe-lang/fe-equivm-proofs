import FeProofs.WETH9.MapStorage
import FeProofs.Common.Basic

/-!
# FeWETH9 `transferFrom` body, Stele side

The body of `transferFrom(src, dst, wad)` run in any frame binding `src`, `dst` and `wad`: the
`transferFrom` arm binds its decoded arguments, and `transfer` binds `msg.sender`, `dst` and `wad`
through its internal call.  It reverts on a short balance, skips the allowance when `src` is the
caller or the allowance is the maximum, otherwise reverts on a short allowance or spends it, then
moves the balance (`tfMove`).  Each storage read sees the writes before it, as in the bytecode, so no
slot disjointness is needed.  Arithmetic wraps on store, like Solidity 0.5 and the unchecked Fe code.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- The slot of `balanceOf[a]`. -/
abbrev balSlot (a : AccountAddress) : UInt256 := mapSlot (addrWord a) ⟨3⟩

/-- The slot of `allowance[o][sp]`. -/
abbrev allowSlot (o sp : AccountAddress) : UInt256 := mapSlot (addrWord sp) (mapSlot (addrWord o) ⟨4⟩)

/-- The largest `uint256`, `type(uint256).max`. -/
abbrev maxUInt : Int := 115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- `balanceOf[x]`. -/
abbrev balanceOfVar (x : Ident) : StorageRef := { base := "balanceOf", steps := [.mindex (.var x)] }

/-- `allowance[src][msg.sender]`. -/
abbrev allowanceSrcCaller : StorageRef :=
  { base := "allowance", steps := [.mindex (.var "src"), .mindex (.env .caller)] }

/-- A word read from storage in `e`. -/
abbrev loadAt (e : EVM.State) (slot : UInt256) : UInt256 :=
  Stele.EVM.storageLoad e e.executionEnv.codeOwner slot

/-- `balanceOf[s] -= w; balanceOf[d] += w`, each read after the write before it. -/
def tfMove (e : EVM.State) (s d : AccountAddress) (w : UInt256) : EVM.State :=
  let e2 := Stele.EVM.storageStore e e.executionEnv.codeOwner (balSlot s)
    (UInt256.sub (loadAt e (balSlot s)) w)
  Stele.EVM.storageStore e2 e2.executionEnv.codeOwner (balSlot d)
    (UInt256.add (loadAt e2 (balSlot d)) w)

/-- The allowance spent: `allowance[s][caller] -= w`. -/
def tfSpend (e : EVM.State) (s : AccountAddress) (w : UInt256) : EVM.State :=
  Stele.EVM.storageStore e e.executionEnv.codeOwner (allowSlot s e.executionEnv.source)
    (UInt256.sub (loadAt e (allowSlot s e.executionEnv.source)) w)

/-- A storage read in the initial state. -/
theorem loadAt_initState {σ σ₀ : AccountMap} {g : Sat256} {A : Substate} {I : ExecutionEnv}
    (slot : UInt256) : loadAt (initState σ σ₀ g A I) slot = solcSlotWord σ I slot :=
  storageLoad_eq_solcSlotWord (initState σ σ₀ g A I) I slot

/-- The accounts after the debit `balanceOf[sw] -= w` and the credit `balanceOf[dw] += w`, each read
after the write before it, as the bytecode computes them. -/
abbrev tfMoveMap (σ1 : AccountMap) (I : ExecutionEnv) (sw dw w : UInt256) : AccountMap :=
  let σ2 := sstoreAccountMap I.codeOwner σ1 (mapSlot sw ⟨3⟩)
    (UInt256.sub (solcSlotWord σ1 I (mapSlot sw ⟨3⟩)) w)
  sstoreAccountMap I.codeOwner σ2 (mapSlot dw ⟨3⟩) (UInt256.add (solcSlotWord σ2 I (mapSlot dw ⟨3⟩)) w)

theorem tfMove_accountMap {e : EVM.State} {I : ExecutionEnv} (he : e.executionEnv = I)
    (s d : AccountAddress) (w : UInt256) :
    (tfMove e s d w).accountMap = tfMoveMap e.accountMap I (addrWord s) (addrWord d) w := by
  simp only [tfMove, loadAt, storageStore_accountMap, storageStore_executionEnv, he,
    storageLoad_eq_solcSlotWord]

theorem tfSpend_accountMap {e : EVM.State} {I : ExecutionEnv} (he : e.executionEnv = I)
    (s : AccountAddress) (w : UInt256) :
    (tfSpend e s w).accountMap = sstoreAccountMap I.codeOwner e.accountMap (allowSlot s I.source)
      (UInt256.sub (solcSlotWord e.accountMap I (allowSlot s I.source)) w) := by
  simp only [tfSpend, loadAt, storageStore_accountMap, he, storageLoad_eq_solcSlotWord]

theorem tfSpend_executionEnv (e : EVM.State) (s : AccountAddress) (w : UInt256) :
    (tfSpend e s w).executionEnv = e.executionEnv := storageStore_executionEnv _ _ _ _

section
variable {L : Store} {s d : AccountAddress} {w : UInt256} {e : EVM.State}

theorem tf_bal {a : AccountAddress} {x : Ident} (hbo : L.get? "balanceOf" = none)
    (hx : L.get? x = some (.address a)) :
    evalExpr? config { contract := contract, locals := L } e (.storage (balanceOfVar x)) =
      .ok (.int (Int.ofNat (loadAt e (balSlot a)).toNat)) := by
  rw [balanceOf_read hbo (evalVarF hx), keyValueToWord_address]

theorem tf_balAssign {a : AccountAddress} {x : Ident} (hbo : L.get? "balanceOf" = none)
    (hx : L.get? x = some (.address a)) (n : Int) :
    assignStorageRef? config { contract := contract, locals := L } e .storage (balanceOfVar x) (.int n) = .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore e e.executionEnv.codeOwner (balSlot a)
        (EVM.wordOfInt n)) := by
  rw [balanceOf_assign_int hbo (evalVarF hx), keyValueToWord_address]

theorem tf_allow (hal : L.get? "allowance" = none) (hsrc : L.get? "src" = some (.address s)) :
    evalExpr? config { contract := contract, locals := L } e (.storage allowanceSrcCaller) =
      .ok (.int (Int.ofNat (loadAt e (allowSlot s e.executionEnv.source)).toNat)) := by
  rw [allowance_read hal (evalVarF hsrc) (Reasoning.VyperDispatch.evalExpr_caller e),
    keyValueToWord_address, keyValueToWord_address]

theorem tf_allowAssign (hal : L.get? "allowance" = none) (hsrc : L.get? "src" = some (.address s))
    (n : Int) :
    assignStorageRef? config { contract := contract, locals := L } e .storage allowanceSrcCaller
      (.int n) =
      .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore e e.executionEnv.codeOwner (allowSlot s e.executionEnv.source)
        (EVM.wordOfInt n)) := by
  rw [allowance_assign_int hal (evalVarF hsrc) (Reasoning.VyperDispatch.evalExpr_caller e),
    keyValueToWord_address, keyValueToWord_address]

/-- `x - wad` for a word `x` read from storage. -/
theorem tf_sub {r : Expr} {x : UInt256} (hwad : L.get? "wad" = some (.int (Int.ofNat w.toNat)))
    (hr : evalExpr? config { contract := contract, locals := L } e r = .ok (.int (Int.ofNat x.toNat))) :
    evalExpr? config { contract := contract, locals := L } e (.binary .sub r (.var "wad")) =
      .ok (.int (Int.ofNat x.toNat - Int.ofNat w.toNat)) :=
  evalBin (by decide) (by decide) hr (evalVarF hwad) rfl

/-- `x + wad` for a word `x` read from storage. -/
theorem tf_add {r : Expr} {x : UInt256} (hwad : L.get? "wad" = some (.int (Int.ofNat w.toNat)))
    (hr : evalExpr? config { contract := contract, locals := L } e r = .ok (.int (Int.ofNat x.toNat))) :
    evalExpr? config { contract := contract, locals := L } e (.binary .add r (.var "wad")) =
      .ok (.int (Int.ofNat x.toNat + Int.ofNat w.toNat)) :=
  evalBin (by decide) (by decide) hr (evalVarF hwad) rfl

/-- `x >= wad` for a word `x` read from storage. -/
theorem tf_ge {r : Expr} {x : UInt256} (hwad : L.get? "wad" = some (.int (Int.ofNat w.toNat)))
    (hr : evalExpr? config { contract := contract, locals := L } e r = .ok (.int (Int.ofNat x.toNat))) :
    evalExpr? config { contract := contract, locals := L } e (.binary .ge r (.var "wad")) = .ok (.bool (decide (w.toNat ≤ x.toNat))) :=
  evalBin (by decide) (by decide) hr (evalVarF hwad) (evalBinaryOp_ge_word _ _)

/-- The spend condition `src != msg.sender && allowance[src][msg.sender] != type(uint256).max`. -/
abbrev tfCond : Expr :=
  .binary .and (.binary .ne (.var "src") (.env .caller))
    (.binary .ne (.storage allowanceSrcCaller) (.intLit maxUInt))

theorem tf_cond (hal : L.get? "allowance" = none) (hsrc : L.get? "src" = some (.address s)) :
    evalExpr? config { contract := contract, locals := L } e tfCond = .ok (.bool (decide (s ≠ e.executionEnv.source ∧
      (loadAt e (allowSlot s e.executionEnv.source)).toNat ≠ 2 ^ 256 - 1))) := by
  have hne : evalExpr? config { contract := contract, locals := L } e (.binary .ne (.var "src") (.env .caller)) =
      .ok (.bool (decide (s ≠ e.executionEnv.source))) :=
    evalBin (by decide) (by decide) (evalVarF hsrc) (Reasoning.VyperDispatch.evalExpr_caller e)
      (by simp only [evalBinaryOp?, Reasoning.VyperDispatch.value_address_beq]; simp)
  have hmax : evalExpr? config { contract := contract, locals := L } e
      (.binary .ne (.storage allowanceSrcCaller) (.intLit maxUInt)) =
      .ok (.bool (decide ((loadAt e (allowSlot s e.executionEnv.source)).toNat ≠ 2 ^ 256 - 1))) :=
    evalBin (by decide) (by decide) (tf_allow hal hsrc) (evalLit _)
      (by simp only [evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq, maxUInt]; simp; omega)
  simp only [tfCond, evalExpr?, hne, hmax, EvalResult.bind, bind, pure]
  by_cases h : s = e.executionEnv.source <;> simp [h]

/-- The debit and the credit, then `return true`. -/
theorem tf_tail (hbo : L.get? "balanceOf" = none) (hsrc : L.get? "src" = some (.address s))
    (hdst : L.get? "dst" = some (.address d)) (hwad : L.get? "wad" = some (.int (Int.ofNat w.toNat)))
    (hperm : e.executionEnv.perm = true) :
    ExecBlock config { contract := contract, locals := L } e (transferFromTransition.body.drop 3)
      (.returned { contract := contract, locals := L } (tfMove e s d w) (some [.bool true])) := by
  let e2 := Stele.EVM.storageStore e e.executionEnv.codeOwner (balSlot s)
    (UInt256.sub (loadAt e (balSlot s)) w)
  have hdebit := tf_balAssign (e := e) hbo hsrc (Int.ofNat (loadAt e (balSlot s)).toNat -
    Int.ofNat w.toNat)
  rw [wordOfInt_sub_natCasts] at hdebit
  have hcredit := tf_balAssign (e := e2) hbo hdst (Int.ofNat (loadAt e2 (balSlot d)).toNat +
    Int.ofNat w.toNat)
  rw [wordOfInt_add_words] at hcredit
  have hperm2 : e2.executionEnv.perm = true := by
    simp only [e2, storageStore_executionEnv]; exact hperm
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (tf_sub hwad (tf_bal hbo hsrc))
    hdebit) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm2) (tf_add hwad (tf_bal hbo hdst))
    hcredit) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind,
    bind, pure]))

end

/-! ## The body's outcomes -/

section
variable {L : Store} {s d : AccountAddress} {w : UInt256} {e : EVM.State}
  (hcv : e.executionEnv.weiValue = ⟨0⟩) (hbo : L.get? "balanceOf" = none)
  (hal : L.get? "allowance" = none) (hsrc : L.get? "src" = some (.address s))
  (hdst : L.get? "dst" = some (.address d)) (hwad : L.get? "wad" = some (.int (Int.ofNat w.toNat)))

include hcv hbo hwad hsrc

theorem tfBody_balance (hlt : (loadAt e (balSlot s)).toNat < w.toNat) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
    (ExecBlock.consRevert (ExecStmt.requireFalse ((tf_ge hwad (tf_bal hbo hsrc)).trans
      (by simp [hlt])))))

variable (hbal : w.toNat ≤ (loadAt e (balSlot s)).toNat)
include hbal hal

theorem tfBody_allowance (hne : s ≠ e.executionEnv.source)
    (hmax : (loadAt e (allowSlot s e.executionEnv.source)).toNat ≠ 2 ^ 256 - 1)
    (hlt : (loadAt e (allowSlot s e.executionEnv.source)).toNat < w.toNat) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
    (ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_bal hbo hsrc)).trans
      (by simp [hbal])))
      (ExecBlock.consRevert (ExecStmt.iteTrue ((tf_cond hal hsrc).trans (by simp [hne]; exact hmax))
        (ExecBlock.consRevert (ExecStmt.requireFalse ((tf_ge hwad (tf_allow hal hsrc)).trans
          (by simp [hlt]))))))))

theorem tfBody_spendStatic (hne : s ≠ e.executionEnv.source)
    (hmax : (loadAt e (allowSlot s e.executionEnv.source)).toNat ≠ 2 ^ 256 - 1)
    (hallow : w.toNat ≤ (loadAt e (allowSlot s e.executionEnv.source)).toNat)
    (hpf : e.executionEnv.perm = false) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
    (ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_bal hbo hsrc)).trans
      (by simp [hbal])))
      (ExecBlock.consStatic (ExecStmt.iteTrue ((tf_cond hal hsrc).trans (by simp [hne]; exact hmax))
        (ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_allow hal hsrc)).trans
          (by simp [hallow])))
          (ExecBlock.consStatic (ExecStmt.assignStatic (tf_sub hwad (tf_allow hal hsrc))
            (tf_allowAssign hal hsrc _) hpf)))))))

theorem tfBody_skipStatic
    (hskip : s = e.executionEnv.source ∨
      (loadAt e (allowSlot s e.executionEnv.source)).toNat = 2 ^ 256 - 1)
    (hpf : e.executionEnv.perm = false) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      .staticViolation :=
  ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
    (ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_bal hbo hsrc)).trans
      (by simp [hbal])))
      (ExecBlock.consNormal (ExecStmt.iteFalse ((tf_cond hal hsrc).trans
        (by rcases hskip with h | h <;> simp [h])) ExecBlock.nil)
        (ExecBlock.consStatic (ExecStmt.assignStatic (tf_sub hwad (tf_bal hbo hsrc))
          (tf_balAssign hbo hsrc _) hpf)))))

include hdst

theorem tfBody_spendReturns (hne : s ≠ e.executionEnv.source)
    (hmax : (loadAt e (allowSlot s e.executionEnv.source)).toNat ≠ 2 ^ 256 - 1)
    (hallow : w.toNat ≤ (loadAt e (allowSlot s e.executionEnv.source)).toNat)
    (hperm : e.executionEnv.perm = true) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      (.returned { contract := contract, locals := L } (tfMove (tfSpend e s w) s d w)
        (some [.bool true])) := by
  have hassign := tf_allowAssign (e := e) hal hsrc
    (Int.ofNat (loadAt e (allowSlot s e.executionEnv.source)).toNat - Int.ofNat w.toNat)
  rw [wordOfInt_sub_natCasts] at hassign
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hcv)) ?_)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_bal hbo hsrc)).trans
    (by simp [hbal]))) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue ((tf_cond hal hsrc).trans (by simp [hne]; exact hmax))
    (ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_allow hal hsrc)).trans
      (by simp [hallow])))
      (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (tf_sub hwad (tf_allow hal hsrc))
        hassign) ExecBlock.nil))) ?_
  exact tf_tail hbo hsrc hdst hwad (by simp only [storageStore_executionEnv]; exact hperm)

theorem tfBody_skipReturns
    (hskip : s = e.executionEnv.source ∨
      (loadAt e (allowSlot s e.executionEnv.source)).toNat = 2 ^ 256 - 1)
    (hperm : e.executionEnv.perm = true) :
    ExecFuncBody config { contract := contract, locals := L } e transferFromTransition.body
      (.returned { contract := contract, locals := L } (tfMove e s d w) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hcv)) ?_)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ((tf_ge hwad (tf_bal hbo hsrc)).trans
    (by simp [hbal]))) ?_
  refine ExecBlock.consNormal (ExecStmt.iteFalse ((tf_cond hal hsrc).trans
    (by rcases hskip with h | h <;> simp [h])) ExecBlock.nil) ?_
  exact tf_tail hbo hsrc hdst hwad hperm

end

end FeProofs.WETH9
