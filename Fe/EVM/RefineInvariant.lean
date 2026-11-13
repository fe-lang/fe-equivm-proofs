import Fe.EVM.Invariant
import Fe.EVM.Refine

/-!
# A contract invariant from a certificate

`Fe.EVM.Invariant` proves, over EVMLean alone, that every admitted message call and creation keeps
an invariant `Holds a P` of the contract at `a`, given the per-frame hypothesis `FrameHyp`: an
admitted frame at `a` running the contract's code keeps it whenever the admitted calls and
creations below the frame do.  This file derives that hypothesis from a certificate
`RefinesOn p bytecode m admits'` and a statement about the model alone.

## The model-level statement

`ModelKeeps a P Trusted admits m`: on an admitted message call at `a` that starts where `Holds a P`
holds, every run of `m.runtime` that succeeds (`Succeeds`) ends with `a`'s account satisfying
`P`, if its code is still what it was, under any feed, given `Deeper` at the call's depth.
`Deeper` is a fact about EVMLean's `Θ` and `Lambda`: every admitted message call and creation
below the frame keeps `Holds` when it starts where `Holds` holds before and after its value
moves.  The model's `call`, `staticcall`, `delegatecall` and `create` run exactly those `Θ` and
`Lambda`, on the model's account map, one level deeper.  Before a call that moves value out of
`a`, the model must show `Holds` of the account map with the value already taken.  A
`delegatecall` runs code at `a`, and `Deeper` covers it only when `Trusted` admits that code.

## Why the certificate suffices, and where admission meets the feed

- A frame that halts exceptionally (the `Exhausted` escape included) ends in `.error`, and `Θ`
  then keeps the account map it started from, so only successful runs need an argument, and
  `RefinesFor.accounts` covers those.
- On a successful run, `Agrees` at profile `P0` equates the bytecode's account map with the
  model's.  The invariant is a property of the account map.
- The certificate must cover every admitted frame: `frameHyp_of_refinesOn` asks that `admits`
  imply the certificate's own condition, so a `RefinesOn … CalldataFits` certificate is used with
  an `admits` that includes `CalldataFits`.

The feed is existential and not tied to the calls the bytecode made.  `ModelKeeps` is shown for
every feed, and `Deeper` holds for every gas, substate and original account map, but only of
admitted calls.  With `admits := fun _ _ => True` every call is admitted (`admitted_of_all`) and
the model may use `Deeper` of any call it makes.  With a real admission condition, a model that
makes calls cannot show that its own calls are admitted: whether every frame at `a` in a callee's
execution is admitted depends on the callee's gas, which the model takes from its feed, not from
the bytecode.  The frame's own calls are admitted (`FrameHyp` gives `XiOk` of the bytecode's run),
but the model's calls are the bytecode's only if the feed is the gas and substate the bytecode
passed.  A model that makes no call, like ERC20's, never needs `Deeper`.  For one that does,
under a real admission condition, the relation would have to tie the feed to the bytecode's calls.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant

/-- The model keeps `P` on every admitted message call at `a` running code `Trusted` admits,
    under any feed, when the admitted message calls and creations below its frame do: every run
    that returns or stops ends with `a`'s account satisfying `P`, if its code is still what it
    was. -/
def ModelKeeps (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)
    (admits : AccountMap → ExecutionEnv → Prop) (m : ContractModel) : Prop :=
  ∀ (I : Env) σ A feed out (w : World), I.codeOwner = a → Trusted I.code →
    I.calldata.size < UInt256.size → admits σ I → Deeper a P Trusted admits I.depth →
    Holds a P σ → Succeeds (m.runtime.exec I (World.init σ A feed)) out w →
    ∀ acc acc', σ[a]? = some acc → w.accounts[a]? = some acc' → acc'.code = acc.code →
      P acc'

/-- The per-frame hypothesis from a certificate on the calls `admits'` holds of, when every
    admitted frame is one. -/
theorem frameHyp_of_refinesOn {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {admits' : ExecutionEnv → Prop} {a : AccountAddress} {P : Account → Prop}
    {Trusted : ByteArray → Prop} {admits : AccountMap → ExecutionEnv → Prop}
    (hcert : RefinesOn p bytecode m admits')
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted admits m) : FrameHyp a P Trusted admits := by
  intro σ σ₀ g A I σ' g' A' o howner htr hcd hadm hdeep _ hH hXi acc acc' hacc hacc' hcode
  obtain ⟨tail, hc, htail⟩ := htrusted I.code htr
  exact (hcert σ σ₀ g A I tail hc htail (hadmits σ I hcd hadm)).accounts
    (P := fun τ => ∀ acc', τ[a]? = some acc' → acc'.code = acc.code → P acc')
    (fun feed out w hrun acc' => hmodel I σ A feed out w howner htr hcd hadm hdeep hH hrun acc
      acc' hacc)
    hXi acc' hacc' hcode

/-- The per-frame hypothesis from a certificate. -/
theorem frameHyp_of_refines {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
    {admits : AccountMap → ExecutionEnv → Prop} (hcert : Refines p bytecode m)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted admits m) : FrameHyp a P Trusted admits :=
  frameHyp_of_refinesOn hcert htrusted (fun _ _ h _ => h) hmodel

/-- **A certified contract keeps its invariant.**  If the bytecode refines the model on the
    admitted calls, the model keeps `P` whenever the admitted calls below it do, and `P` is
    admissible, then every message call and every creation, at every depth, that starts where
    `Holds a P` holds and in whose execution every successful frame at `a` is admitted, ends where
    it holds, as `ThetaGood` and `LambdaGood` state. -/
theorem refinesOn_keeps {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {admits' : ExecutionEnv → Prop} {a : AccountAddress} {P : Account → Prop}
    {Trusted : ByteArray → Prop} {admits : AccountMap → ExecutionEnv → Prop}
    (hcert : RefinesOn p bytecode m admits') (hadm : Admissible P Trusted)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted admits m) (e : Fin 1025) :
    ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e :=
  good hadm (frameHyp_of_refinesOn hcert htrusted hadmits hmodel) e

/-- `refinesOn_keeps` for a certificate on every call. -/
theorem refines_keeps {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
    {admits : AccountMap → ExecutionEnv → Prop}
    (hcert : Refines p bytecode m) (hadm : Admissible P Trusted)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted admits m) (e : Fin 1025) :
    ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e :=
  refinesOn_keeps hcert hadm htrusted (fun _ _ h _ => h) hmodel e

end Fe.EVM
