import Reasoning.Reach
import Reasoning.Dispatch
import Stele.Semantics

/-!
# Small proof glue shared by the Fe examples

-- LIBRARY CANDIDATES: `not_selIs_of_selIs` (`Reasoning/Dispatch.lean`), `RDret.of_output_eq`
-- (`Reasoning/Reach.lean`), `evalLocalVar` (`Reasoning/SteleArithmetic.lean`; GENERALIZES
-- `evalExpr_varInt` to any value).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs

/-- Distinct selector-table entries cannot both match the calldata selector. -/
theorem not_selIs_of_selIs {I : ExecutionEnv} {a b : ByteArray}
    (ha : (a == I.calldata.extract 0 4) = true) (hab : a ≠ b) :
    ¬ (b == I.calldata.extract 0 4) = true := fun hb =>
  hab ((byteArray_eq_of_beq ha).trans (byteArray_eq_of_beq hb).symm)

/-- Rewrite the bytes a terminal segment returns. -/
theorem RDret.of_output_eq {code : ByteArray} {g : Sat256} {s0 : State} {acc : AccountMap}
    {o o' : ByteArray} (h : RDret code g s0 acc o) (e : o = o') : RDret code g s0 acc o' :=
  e ▸ h

/-- `dispatchMsg_eq_some_of_split` for a contract that may have a fallback or receive: a selector
    match dispatches before either is consulted. -/
theorem dispatchMsg_eq_some_of_selector_split {contract : ContractDecl}
    {pre post : List TransitionDecl} {ti : TransitionDecl} {cd : ByteArray}
    (htr : contract.transitions = pre ++ ti :: post)
    (hpre : ∀ t ∈ pre, (selectorOf t == cd.extract 0 4) = false)
    (hhit : (selectorOf ti == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some ti := by
  rw [dispatchMsg, selectorDispatchMsg_eq_dispatchList contract cd, htr,
    dispatchList_eq_some_of_split hpre hhit]

/-- Calldata that matches no selector dispatches to the fallback, when there is no receive. -/
theorem dispatchMsg_eq_fallback {contract : ContractDecl} {cd : ByteArray}
    (hnone : dispatchList contract.transitions cd = none)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = contract.fallback := by
  rw [dispatchMsg, selectorDispatchMsg_eq_dispatchList contract cd, hnone]
  simp [receiveDispatchMsg, hreceive]

end FeProofs
