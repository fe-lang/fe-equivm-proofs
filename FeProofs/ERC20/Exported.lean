import FeProofs.ERC20.Model

/-!
# FeERC20: exported arms

The definitions under "Exported definitions" are the output of `fe-lean-export` on `FeERC20.fe`, pasted
unchanged (Fe branch `lean-export`, golden file `tests/golden/erc20.lean`).  Arms are numbered in
the order of the `msg` declaration.

The exporter does not yet print an event's encoding.  It prints a call to `emit<Event>`, which
this file defines by hand.

Each theorem shows that an exported arm runs exactly as the hand-written model arm does, so the
certificate for the model covers the exported code.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20.Exported

/-- `log.emit(Transfer { from, to, value })` -/
def emitTransfer (src dst value : UInt256) : FeM Unit :=
  emit #[Model.transferTopic, src, dst] value.toByteArray

/-- `log.emit(Approval { owner, spender, value })` -/
def emitApproval (owner spender value : UInt256) : FeM Unit :=
  emit #[Model.approvalTopic, owner, spender] value.toByteArray

/-! ## Exported definitions -/

def init (v0 : UInt256) : FeM Unit := do
  let v2 ← caller
  let v3 := v2
  let v4 := v0
  sstore (mapSlot v3 (UInt256.ofNat 0)) v4
  let v5 := ()
  let v6 := v0
  sstore (UInt256.ofNat 2) v6
  let v7 := ()
  let v8 := UInt256.ofNat 0
  let v9 := v0
  let v12 ← emitTransfer v8 v3 v9
  return ()

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM Bool := do
  let v3 ← caller
  let v4 := v3
  let v5 ← sload (mapSlot v4 (UInt256.ofNat 0))
  let v6 := decide (v1.toNat ≤ v5.toNat)
  if v6 then
    let v7 := ()
    let v8 ← sload (mapSlot v4 (UInt256.ofNat 0))
    let v9 ← checkedSub v8 v1
    sstore (mapSlot v4 (UInt256.ofNat 0)) v9
    let v10 := ()
    let v11 ← sload (mapSlot v0 (UInt256.ofNat 0))
    let v12 ← checkedAdd v11 v1
    sstore (mapSlot v0 (UInt256.ofNat 0)) v12
    let v13 := ()
    let v16 ← emitTransfer v4 v0 v1
    let v17 := true
    return v17
  else
    M.revert (assertData "ERC20: insufficient balance")

def recv0_arm1 (v0 : UInt256) (v1 : UInt256) : FeM Bool := do
  let v3 ← caller
  let v4 := v3
  sstore (mapSlot v0 (mapSlot v4 (UInt256.ofNat 1))) v1
  let v5 := ()
  let v8 ← emitApproval v4 v0 v1
  let v9 := true
  return v9

def recv0_arm2 (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) : FeM Bool := do
  let v4 ← caller
  let v5 := v4
  let v6 ← sload (mapSlot v5 (mapSlot v0 (UInt256.ofNat 1)))
  let v7 := v6
  let v8 := decide (v2.toNat ≤ v7.toNat)
  if v8 then
    let v9 := ()
    let v10 ← sload (mapSlot v0 (UInt256.ofNat 0))
    let v11 := decide (v2.toNat ≤ v10.toNat)
    if v11 then
      let v12 := ()
      let v13 ← checkedSub v7 v2
      sstore (mapSlot v5 (mapSlot v0 (UInt256.ofNat 1))) v13
      let v14 := ()
      let v15 ← sload (mapSlot v0 (UInt256.ofNat 0))
      let v16 ← checkedSub v15 v2
      sstore (mapSlot v0 (UInt256.ofNat 0)) v16
      let v17 := ()
      let v18 ← sload (mapSlot v1 (UInt256.ofNat 0))
      let v19 ← checkedAdd v18 v2
      sstore (mapSlot v1 (UInt256.ofNat 0)) v19
      let v20 := ()
      let v23 ← emitTransfer v0 v1 v2
      let v24 := true
      return v24
    else
      M.revert (assertData "ERC20: insufficient balance")
  else
    M.revert (assertData "ERC20: insufficient allowance")

def recv0_arm3 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← sload (mapSlot v0 (UInt256.ofNat 0))
  return v1

def recv0_arm4 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← sload (mapSlot v1 (mapSlot v0 (UInt256.ofNat 1)))
  return v2

def recv0_arm5 : FeM UInt256 := do
  let v0 ← sload (UInt256.ofNat 2)
  return v0

/-! ## Agreement with the model -/

variable (I : ExecutionEnv) (w : World)

theorem ofNat0 : UInt256.ofNat 0 = ⟨0⟩ := rfl
theorem ofNat1 : UInt256.ofNat 1 = ⟨1⟩ := rfl
theorem ofNat2 : UInt256.ofNat 2 = ⟨2⟩ := rfl

/-- Close an agreement goal after unfolding: split every branch of both runs, and discharge each
    case by reflexivity, by contradictory bounds, or by simplification. -/
macro "agree" : tactic =>
  `(tactic| repeat' first
    | rfl
    | (exfalso; omega)
    | split
    | simp_all [checkedSub, checkedAdd, exec_sstore, exec_emit])

theorem init_exec (initialSupply : UInt256) :
    (init initialSupply).exec I w = (Model.initBody initialSupply).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, init, Model.initBody, Model.balanceSlot, Model.balancesRoot, Model.totalSupplySlot,
    emitTransfer, exec_sstore, exec_emit]
  agree

theorem transfer_exec (dst value : UInt256) :
    (recv0_arm0 dst value).exec I w = (Model.transfer dst value).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm0, Model.transfer, Model.balanceSlot, Model.balancesRoot, emitTransfer,
    checkedSub, checkedAdd, exec_sstore, exec_emit]
  agree

theorem approve_exec (spender value : UInt256) :
    (recv0_arm1 spender value).exec I w = (Model.approve spender value).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm1, Model.approve, Model.allowanceSlot, Model.allowancesRoot, emitApproval,
    exec_sstore, exec_emit]
  agree

theorem transferFrom_exec (src dst value : UInt256) :
    (recv0_arm2 src dst value).exec I w = (Model.transferFrom src dst value).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm2, Model.transferFrom, Model.balanceSlot, Model.balancesRoot,
    Model.allowanceSlot, Model.allowancesRoot, emitTransfer, checkedSub, checkedAdd, exec_sstore,
    exec_emit]
  agree

theorem balanceOf_exec (owner : UInt256) :
    (recv0_arm3 owner).exec I w = (Model.balanceOf owner).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm3, Model.balanceOf, Model.balanceSlot, Model.balancesRoot]

theorem allowance_exec (owner spender : UInt256) :
    (recv0_arm4 owner spender).exec I w = (Model.allowance owner spender).exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm4, Model.allowance, Model.allowanceSlot, Model.allowancesRoot]

theorem totalSupply_exec : recv0_arm5.exec I w = Model.totalSupply.exec I w := by
  simp [ofNat0, ofNat1, ofNat2, recv0_arm5, Model.totalSupply, Model.totalSupplySlot]

end FeProofs.ERC20.Exported
