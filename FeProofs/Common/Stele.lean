import Reasoning.SteleBody
import Reasoning.SteleArithmetic
import Reasoning.VyperDispatch -- `evalExpr_caller`

/-!
# Stele locals and expression evaluation

Reading locals through a chain of inserts (`get_ins_ne` and the `store_get` tactic), and the
evaluation of variables, integer literals, non-short-circuit binary operators, integer casts and
local assignments (`…F` for any frame, the plain forms for a frame built from its locals), `≥`, `-` and `+` on
words, and the range check `inRange (uint n) e` (for `uint256`, of word sums and differences).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs

theorem get_ins_ne {L : Store} {k a : Ident} {v : Value} (h : k ≠ a) :
    (L.insert k v).get? a = L.get? a :=
  store_get_ne L v (by simpa using h)

/-- Reads a local through the inserts above it: rewrites `(L.insert k v).get? a` to `L.get? a`
    for distinct literal names, to `some v` when `k = a`, and `(∅ : Store).get? a` to `none`. -/
macro "store_get" : tactic =>
  `(tactic| (simp +zetaDelta only [get_ins_ne, store_get_self, store_get_empty, ne_eq,
    String.reduceEq, not_false_eq_true]; try rfl))

theorem evalVarF {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident} {v : Value}
    (h : stele.locals.get? name = some v) : evalExpr? cfg stele evm (.var name) = .ok v := by
  rw [evalExpr?, h]; rfl

theorem evalLit {cfg : Config} {stele : Frame} {evm : EVM.State} (n : Int) :
    evalExpr? cfg stele evm (.intLit n) = .ok (.int n) := by
  rw [evalExpr?]; rfl

theorem evalBin {cfg : Config} {stele : Frame} {evm : EVM.State} {op : BinaryOp} {l r : Expr}
    {lv rv res : Value} (hand : op ≠ .and) (hor : op ≠ .or)
    (hl : evalExpr? cfg stele evm l = .ok lv) (hr : evalExpr? cfg stele evm r = .ok rv)
    (hop : evalBinaryOp? op lv rv = .ok res) :
    evalExpr? cfg stele evm (.binary op l r) = .ok res := by
  rw [evalExpr_binary_nonshort hand hor]
  simp only [hl, hr, EvalResult.bind, bind]
  exact hop

/-- `≥` on two words. -/
theorem evalBinaryOp_ge_word (a b : UInt256) :
    evalBinaryOp? .ge (.int (Int.ofNat a.toNat)) (.int (Int.ofNat b.toNat)) =
      .ok (.bool (decide (b.toNat ≤ a.toNat))) := by
  simp [evalBinaryOp?]

/-- `-` on two words, without underflow. -/
theorem evalBinaryOp_sub_word {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    evalBinaryOp? .sub (.int (Int.ofNat a.toNat)) (.int (Int.ofNat b.toNat)) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  simp [evalBinaryOp?, usub_toNat h]; omega

/-- `+` on two words. -/
theorem evalBinaryOp_add_word (a b : UInt256) :
    evalBinaryOp? .add (.int (Int.ofNat a.toNat)) (.int (Int.ofNat b.toNat)) =
      .ok (.int (Int.ofNat (a.toNat + b.toNat))) := by
  simp [evalBinaryOp?]

theorem evalCastInt {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {i : Int}
    (t : IntType) (he : evalExpr? cfg stele evm e = .ok (.int i)) :
    evalExpr? cfg stele evm (.cast e (.elem (.int t))) = .ok (.int (normalizeInt t i)) := by
  rw [evalExpr?]
  simp only [he, EvalResult.bind, bind, castValue_int, EvalResult.ofOption]

theorem assignLocalF {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident}
    {old value : Value} (hget : stele.locals.get? name = some old) :
    assignStorageRef? cfg stele evm .localVar { base := name } value =
      .ok ({ stele with locals := stele.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match stele.locals.get? name with
    | some _ => EvalResult.ok (({ stele with locals := stele.locals.insert name value } : Frame), evm)
    | none => EvalResult.error EvalError.unboundVariable) = _
  rw [hget]

theorem evalInRangeUint {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {w : BitWidth}
    {i : Int} (he : evalExpr? cfg stele evm e = .ok (.int i)) (h0 : 0 ≤ i) (hlt : i < 2 ^ w.val) :
    evalExpr? cfg stele evm (.inRange (.uint w) e) = .ok (.int i) := by
  rw [evalExpr?]
  simp [he, EvalResult.bind, bind, pure, not_lt.mpr h0, hlt]

theorem evalInRangeUint_revert {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr}
    {w : BitWidth} {i : Int} (he : evalExpr? cfg stele evm e = .ok (.int i))
    (h : i < 0 ∨ 2 ^ w.val ≤ i) :
    evalExpr? cfg stele evm (.inRange (.uint w) e) = .revert := by
  rw [evalExpr?]
  rcases h with h | h <;> simp [he, EvalResult.bind, bind, pure, h]

/-- `inRange (uint 256)` of a word difference without underflow. -/
theorem evalInRange256_sub {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr}
    {a b : UInt256} (he : evalExpr? cfg stele evm e = .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat)))
    (h : b.toNat ≤ a.toNat) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) e) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  have ha : a.toNat < UInt256.size := a.val.isLt
  rw [evalInRangeUint he (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [Int.ofNat_eq_natCast]; simp [UInt256.size] at ha ⊢; omega), usub_toNat h]
  simp only [Int.ofNat_eq_natCast]; congr 2; omega

/-- `inRange (uint 256)` of a word difference that underflows. -/
theorem evalInRange256_sub_revert {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr}
    {a b : UInt256} (he : evalExpr? cfg stele evm e = .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat)))
    (h : a.toNat < b.toNat) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) e) = .revert :=
  evalInRangeUint_revert he (Or.inl (by simp only [Int.ofNat_eq_natCast]; omega))

/-- `inRange (uint 256)` of a word sum below `2^256`. -/
theorem evalInRange256_add {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr}
    {a b : UInt256} (he : evalExpr? cfg stele evm e = .ok (.int (Int.ofNat (a.toNat + b.toNat))))
    (h : a.toNat + b.toNat < UInt256.size) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) e) = .ok (.int (Int.ofNat (a + b).toNat)) := by
  rw [evalInRangeUint he (Int.natCast_nonneg _)
    (by simp only [Int.ofNat_eq_natCast]; simp [UInt256.size] at h ⊢; omega), uadd_toNat,
    Nat.mod_eq_of_lt h]

/-- `inRange (uint 256)` of a word sum of at least `2^256`. -/
theorem evalInRange256_add_revert {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr}
    {a b : UInt256} (he : evalExpr? cfg stele evm e = .ok (.int (Int.ofNat (a.toNat + b.toNat))))
    (h : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) e) = .revert :=
  evalInRangeUint_revert he (Or.inr (by simp only [Int.ofNat_eq_natCast]; simp [UInt256.size] at h ⊢; omega))

/-- `assignLocalF` for a frame built from its locals, keeping that shape. -/
theorem assignLocal {cfg : Config} {c : ContractDecl} {L : Store} {evm : EVM.State} {x : Ident}
    {old v : Value} (hx : L.get? x = some old) :
    assignStorageRef? cfg { contract := c, locals := L } evm .localVar { base := x } v =
      .ok ({ contract := c, locals := L.insert x v }, evm) := by
  have hx' : L[x]? = some old := by simpa using hx
  simp [assignStorageRef?, hx', updateLocalPath?, bind, EvalResult.bind, pure]

/-- The non-payable `return e;` body reverts when `e` does.

LIBRARY CANDIDATE: `Reasoning/SteleBody.lean`, beside `nonpayableReturnExprBodyReturns`. -/
theorem nonpayableReturnExprBodyReverts {cfg : Config} {imms : Store} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {expr : Expr} (h : evm.executionEnv.weiValue = ⟨0⟩)
    (heval : evalExpr? cfg { contract := contract, locals := locals, immutables := imms } evm expr =
      .revert) :
    ExecTransitionBody cfg contract evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [expr]] .reverted imms :=
  ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
      ExecBlock.consRevert
        (ExecStmt.returnRevert (by simp only [evalExprs?, heval, bind, EvalResult.bind]))

end FeProofs
