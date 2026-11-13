import Fe.EVM.Invariant
import Fe.EVM.Refine

/-!
# A contract invariant from a certificate

`Fe.EVM.Invariant` proves, over EVMLean alone, that every message call and creation keeps an
invariant `Holds a P` of the contract at `a`, given the per-frame hypothesis `FrameHyp`: a frame at
`a` running the contract's code keeps it whenever the calls and creations below the frame do.
This file derives that hypothesis from a certificate `Refines p bytecode m` and a statement about
the model alone.

## The model-level statement

`ModelKeeps a P Trusted m`: on a message call at `a` that starts where `Holds a P` holds, every
run of `m.runtime` that returns or stops ends in an account map where it holds again, under any
feed, given `Deeper a P Trusted` at the call's depth.  `Deeper` is a fact about EVMLean's `Θ` and
`Lambda`: every message call and creation below the frame keeps `Holds` when it starts where
`Holds` holds before and after its value moves.  The model's `call`, `staticcall`,
`delegatecall` and `create` run exactly those `Θ` and `Lambda`, on the model's account map, one
level deeper, so a proof of `ModelKeeps` applies `Deeper` to each call the model makes.  Before
a call that moves value out of `a`, the model must show `Holds` of the account map with the value
already taken: the invariant holds before every external call.  A `delegatecall` runs code at
`a`, and `Deeper` covers it only when `Trusted` admits that code.

## Why the certificate suffices

`frameHyp_of_refines` is short because the relation carries what the argument needs:

- A frame that halts exceptionally (the `Exhausted` escape included) ends in `.error`, and `Θ`
  then keeps the account map it started from, so the frame hypothesis is about successful runs
  only, and `RefinesFor.accounts` covers those.
- On a run that returns or stops, `Agrees` at profile `P0` already equates the bytecode's
  account map with the model's.  The invariant is a property of the account map.
- The feed is existential and not tied to the calls the bytecode made.  That does no harm:
  `ModelKeeps` is shown for every feed, and `Deeper` holds for every gas, substate and original
  account map a call can be given, so it holds of the feed that witnesses the certificate.

What it needs from the certificate is coverage of every frame that can run the contract's code:
`Refines` admits every call whose calldata size fits a word, as every EVM call's does.  A
certificate `RefinesOn p bytecode m CalldataFits`, as the exported models have, covers only
calldata shorter than `2 ^ 64` bytes, and `frameHyp_of_refinesOn` then needs that bound for every
frame at `a`.  It holds on the real chain, where a block's gas limit makes such calldata
unaffordable, but EVMLean bounds a call's gas only by `2 ^ 256`, and memory expansion to `2 ^ 64`
bytes costs less than that, so the bound would have to come from a gas limit on the
transaction.  That argument is not made here.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant

/-- The model keeps `Holds a P` on every message call at `a` running code `Trusted` admits,
    under any feed, when the message calls and creations below its frame do. -/
def ModelKeeps (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)
    (m : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ (I : Env) σ A feed out (w : World), I.codeOwner = a → Trusted I.code → admits I →
    Deeper a P Trusted I.depth → Holds a P σ →
    (m.runtime.exec I (World.init σ A feed) = some (.ok (out, w))
      ∨ m.runtime.exec I (World.init σ A feed) = some (.error (.stop out w))) →
    Holds a P w.accounts

/-- The per-frame hypothesis from a certificate on the calls `admits` holds of, when every frame
    at `a` is one. -/
theorem frameHyp_of_refinesOn {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {admits : ExecutionEnv → Prop} {a : AccountAddress} {P : Account → Prop}
    {Trusted : ByteArray → Prop} (hcert : RefinesOn p bytecode m admits)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ I : ExecutionEnv, I.codeOwner = a → Trusted I.code →
      I.calldata.size < UInt256.size → admits I)
    (hmodel : ModelKeeps a P Trusted m admits) : FrameHyp a P Trusted := by
  intro σ σ₀ g A I σ' g' A' o howner htr hcd hdeep hH hXi
  obtain ⟨tail, hcode, htail⟩ := htrusted I.code htr
  have hadm := hadmits I howner htr hcd
  exact (hcert σ σ₀ g A I tail hcode htail hadm).accounts
    (fun feed out w hrun => hmodel I σ A feed out w howner htr hadm hdeep hH hrun) hXi

/-- The per-frame hypothesis from a certificate. -/
theorem frameHyp_of_refines {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
    (hcert : Refines p bytecode m)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted m fun I => I.calldata.size < UInt256.size) :
    FrameHyp a P Trusted :=
  frameHyp_of_refinesOn hcert htrusted (fun _ _ _ h => h) hmodel

/-- **A certified contract keeps its invariant.**  If the bytecode refines the model, the model
    keeps `Holds a P` whenever the calls below it do, and `P` is admissible, then every message
    call and every creation, at every depth, that starts where `Holds a P` holds ends where it
    holds, as `ThetaGood` and `LambdaGood` state. -/
theorem refines_keeps {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
    (hcert : Refines p bytecode m) (hadm : Admissible P Trusted)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted m fun I => I.calldata.size < UInt256.size)
    (e : Fin 1025) : ThetaGood a P Trusted e ∧ LambdaGood a P e :=
  good hadm (frameHyp_of_refines hcert htrusted hmodel) e

end Fe.EVM
