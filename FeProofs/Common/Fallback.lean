import Reasoning.Dispatch
import Reasoning.Reach

/-!
# Refinement glue for contracts with a fallback

EquiVM's `RD*.reEquiv*` lemmas take `dispatchMsg contract I.calldata = some t` and assume that the
contract has no fallback or receive, only to recover `selectorDispatchMsg … = some t`, which is what
Stele's runtime semantics dispatches on.  The `…Sel` versions here take that fact directly, so they
also apply to a contract with a fallback.  `RDret.reEquivFallback` and
`RDstatic.reEquivFallbackStaticHalt` cover calldata that matches no selector.

LIBRARY CANDIDATE: EquiVM's lemmas could take `selectorDispatchMsg` (`Reasoning/Dispatch.lean`,
`Reasoning/Reach.lean`); the fallback ones generalize `Benchmarks/WETH9/Deposit.lean`'s.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Reasoning.Reach

/-- The selector of `ti` matches and none before it does. -/
theorem selectorDispatchMsg_eq_some_of_split {contract : ContractDecl}
    {pre post : List TransitionDecl} {ti : TransitionDecl} {cd : ByteArray}
    (htr : contract.transitions = pre ++ ti :: post)
    (hpre : ∀ t ∈ pre, (selectorOf t == cd.extract 0 4) = false)
    (hhit : (selectorOf ti == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some ti := by
  rw [selectorDispatchMsg_eq_dispatchList contract cd, htr, dispatchList_eq_some_of_split hpre hhit]

section
variable {immutables : Store} {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
  {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256} {code : ByteArray}

theorem RDrev.reEquivDecodingFailedSel (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables :=
  h.reEquivElim hcode fun _ _ hrev =>
    .execution hrev (.decodingFailed hsd hdec) (.decodingFailed rfl rfl)

theorem RDrev.reEquivExecutionRevertSel {callargs : Store} (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body .reverted immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables :=
  h.reEquivElim hcode fun _ _ hrev =>
    .execution rfl (.intro hsd rfl hdec rfl hbody) (by rw [hrev]; exact .revert rfl rfl)

/-- A revert after dispatching to `t`, when every decoded argument store makes the body revert. -/
theorem RDrev.reEquivDispatchedRevertSel (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hbody : ∀ callargs, ExecTransitionBody cfg contract (initState σ σ₀ g A I) callargs t.body
      .reverted immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables := by
  cases hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata with
  | none => exact h.reEquivDecodingFailedSel hcode hsd hdec
  | some callargs => exact h.reEquivExecutionRevertSel hcode hsd hdec (hbody callargs)

/-- Successful execution with a possibly changed account map. -/
theorem RDret.reEquivExecutionGenSel {o : ByteArray} {callargs : Store} {cs : Frame}
    {retVal : Option (List Value)} {acc : AccountMap} {evm'' : EVM.State}
    (hcode : I.code = code) (h : RDret code g (initState σ σ₀ g A I) acc o)
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body (.returned cs evm'' retVal) immutables)
    (hAccounts : acc = evm''.accountMap)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' : ExecTransitionBody cfg contract
        (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
        callargs t.body (.returned cs evm'' retVal) immutables := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine .execution rfl (.intro hsd rfl hdec rfl hbody') ?_
    rw [hxi]
    exact execResultsEquiv.success rfl rfl (hsacc.trans hAccounts) (.abi henc)

/-- Successful execution that leaves the accounts as they were. -/
theorem RDret.reEquivExecutionSel {o : ByteArray} {callargs : Store} {cs : Frame}
    {retVal : Option (List Value)}
    (hcode : I.code = code) (h : RDret code g (initState σ σ₀ g A I) σ o)
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body
              (.returned cs (initState σ σ₀ g A I) retVal) immutables)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables :=
  h.reEquivExecutionGenSel hcode hsd hdec hbody (by simp [initState]) henc

/-- A static-mode halt after dispatching to `t`, matched by the body's static violation. -/
theorem RDstatic.reEquivStaticHaltSel {callargs : Store} (hcode : I.code = code)
    (h : RDstatic code g (initState σ σ₀ g A I))
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body .staticViolation immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables :=
  h.reEquivElim hcode fun hst =>
    .execution rfl (.intro hsd rfl hdec rfl hbody) (by rw [hst]; exact .staticHalt rfl rfl)

/-- Calldata that matches no selector runs the fallback `t`, which returns. -/
theorem RDret.reEquivFallback {o : ByteArray} {callargs : Store} {cs : Frame}
    {retVal : Option (List Value)} {returnConv : ReturnConvention}
    {acc : AccountMap} {evm'' : EVM.State}
    (hcode : I.code = code) (h : RDret code g (initState σ σ₀ g A I) acc o)
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hnorecv : receiveDispatchMsg contract I.calldata = none)
    (hfb : contract.fallback = some t)
    (hargs : fallbackCallargs I.calldata t.params = some callargs)
    (hret : fallbackReturnConvention t = some returnConv)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body (.returned cs evm'' retVal) immutables)
    (hAccounts : acc = evm''.accountMap)
    (hRetData : returnDataEquiv o retVal returnConv) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' : ExecTransitionBody cfg contract
        (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
        callargs t.body (.returned cs evm'' retVal) immutables := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine .execution rfl (.fallback hnosel hnorecv hfb hargs hret rfl hbody') ?_
    rw [hxi]
    exact execResultsEquiv.success rfl rfl (hsacc.trans hAccounts) hRetData

/-- Calldata that matches no selector runs the fallback `t`, which halts in static mode. -/
theorem RDstatic.reEquivFallbackStaticHalt {callargs : Store} {returnConv : ReturnConvention}
    (hcode : I.code = code) (h : RDstatic code g (initState σ σ₀ g A I))
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hnorecv : receiveDispatchMsg contract I.calldata = none)
    (hfb : contract.fallback = some t)
    (hargs : fallbackCallargs I.calldata t.params = some callargs)
    (hret : fallbackReturnConvention t = some returnConv)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body .staticViolation immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables :=
  h.reEquivElim hcode fun hst => by
    have hbody' : ExecTransitionBody cfg contract
        (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
        callargs t.body .staticViolation immutables := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    exact .execution rfl (.fallback hnosel hnorecv hfb hargs hret rfl hbody')
      (by rw [hst]; exact .staticHalt rfl rfl)

end

end Reasoning.Reach
