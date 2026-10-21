import Reasoning.SteleBody
import Reasoning.SteleArithmetic
import Reasoning.VyperDispatch -- `evalExpr_caller`

/-!
# Stele locals and expression evaluation

Reading locals through a chain of inserts (`get_ins_ne` and the `store_get` tactic), and the
evaluation of variables, integer literals, non-short-circuit binary operators, integer casts and
local assignments (`…F` for any frame, the plain forms for a frame built from its locals), and the range check
`inRange (uint n) e`.
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
    {w : BitWidth} {i : Int} (he : evalExpr? cfg stele evm e = .ok (.int i)) (hge : 2 ^ w.val ≤ i) :
    evalExpr? cfg stele evm (.inRange (.uint w) e) = .revert := by
  rw [evalExpr?]
  simp [he, EvalResult.bind, bind, pure, hge]

/-- `assignLocalF` for a frame built from its locals, keeping that shape. -/
theorem assignLocal {cfg : Config} {c : ContractDecl} {L : Store} {evm : EVM.State} {x : Ident}
    {old v : Value} (hx : L.get? x = some old) :
    assignStorageRef? cfg { contract := c, locals := L } evm .localVar { base := x } v =
      .ok ({ contract := c, locals := L.insert x v }, evm) := by
  have hx' : L[x]? = some old := by simpa using hx
  simp [assignStorageRef?, hx', updateLocalPath?, bind, EvalResult.bind, pure]

end FeProofs
