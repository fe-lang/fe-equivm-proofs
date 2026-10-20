import Reasoning.Reach
import Stele.Semantics

/-!
# Small proof glue shared by the Fe examples

-- LIBRARY CANDIDATES: `not_selIs_of_selIs` (`Reasoning/Dispatch.lean`), `RDret.of_output_eq`
-- (`Reasoning/Reach.lean`), `evalExpr_var` (`Reasoning/SteleArithmetic.lean`; GENERALIZES
-- `evalExpr_varInt` to any value).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Common

/-- Distinct selector-table entries cannot both match the calldata selector. -/
theorem not_selIs_of_selIs {I : ExecutionEnv} {a b : ByteArray}
    (ha : (a == I.calldata.extract 0 4) = true) (hab : a ≠ b) :
    ¬ (b == I.calldata.extract 0 4) = true := fun hb =>
  hab ((byteArray_eq_of_beq ha).trans (byteArray_eq_of_beq hb).symm)

/-- Rewrite the bytes a terminal segment returns. -/
theorem RDret.of_output_eq {code : ByteArray} {g : Sat256} {s0 : State} {acc : AccountMap}
    {o o' : ByteArray} (h : RDret code g s0 acc o) (e : o = o') : RDret code g s0 acc o' :=
  e ▸ h

theorem evalExpr_var {cfg : Config} {contract : ContractDecl} {evm : EVM.State} {locals : Store}
    {name : Ident} {v : Value} (h : locals.get? name = some v) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok v
  rw [h]
  rfl

end FeProofs.Common
