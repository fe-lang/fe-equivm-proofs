import Reasoning.Reach
import Reasoning.Dispatch

/-!
# Fe runtime glue

Fe checks call value inside each selector arm, before decoding the arguments.  A matched
selector with non-zero call value therefore reverts whether or not its calldata decodes, while
Stele either reports a decoding failure or runs the body into its non-payable guard.

Fe's checked `u256` addition `a + b` panics when the wrapped sum is below `a`
(`addCarry_eq_zero`, `addCarry_ne_zero`).

-- LIBRARY CANDIDATE: `Reasoning/Dispatch.lean`, beside `RDrev.reEquivExecutionRevert`
-- (the decode-agnostic form of a dispatched revert).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Reach

/-- A revert after dispatching to `t` refines Stele when every decoded argument store makes the
    body revert: a decoding failure and a reverting body are both matched by the EVM revert. -/
theorem RDrev.reEquivDispatchedRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hbody : ∀ callargs, ExecTransitionBody cfg contract (initState σ σ₀ g A I) callargs t.body
      .reverted immutables)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables := by
  cases hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata with
  | none => exact RDrev.reEquivDecodingFailed hcode h hd hdec hfallback hreceive
  | some callargs =>
      exact RDrev.reEquivExecutionRevert hcode h hd hdec (hbody callargs) hfallback hreceive

end Reasoning.Reach

namespace FeProofs

/-- No carry: the wrapped sum is not below `a`. -/
theorem addCarry_eq_zero {a b : UInt256} (h : a.toNat + b.toNat < UInt256.size) :
    UInt256.lt (a + b) a = ⟨0⟩ :=
  ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt h]; omega)

/-- Carry: the wrapped sum is below `a`. -/
theorem addCarry_ne_zero {a b : UInt256} (h : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.lt (a + b) a ≠ ⟨0⟩ := by
  have ha : a.toNat < UInt256.size := a.val.isLt
  have hb : b.toNat < UInt256.size := b.val.isLt
  have hsum : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  rw [ult_one (by omega)]
  decide

end FeProofs
