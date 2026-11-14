import Fe.EVM.Invariant
import Fe.EVM.Refine
import Fe.EVM.Calls

/-!
# A contract invariant from a certificate

`Fe.EVM.Invariant` proves, over EVMLean alone, that every admitted message call and creation keeps
an invariant `Holds a P` of the contract at `a`, given the per-frame hypothesis `FrameHyp`: an
admitted frame at `a` running the contract's code keeps it whenever the admitted calls and
creations below the frame do.  This file derives that hypothesis from a certificate
`RefinesOn p bytecode m admits'` and a statement about the model alone, and the base case
(`refinesDeploy_holds`) from a deployment certificate `RefinesDeploy` and a statement about the
model's constructor: run at the new address, from an account map where that address has empty
storage, it leaves there an account that satisfies `P` with the code it returns.  The certificate
equates the creation's return data with the model's, `runtime` followed by the immutables, and
`Lambda` installs that code (`Agrees.accounts_out`, `lambda_success`).

## The model-level statement

`ModelKeeps a P Trusted Enters admits callsAt m`: on an admitted message call at `a`, every run of
`m.runtime` that succeeds (`Succeeds`) ends with `a`'s account satisfying `P`, if its code is
still what it was, under any feed, given `Deeper` at the call's depth and that the calls
`callsAt` describes are admitted.  The run knows how the call was entered, as `FrameHyp` states
it: from `σpre`, where `Holds a P` holds and the balances add up to less than `2 ^ 256`, by
moving `v` from `I.source` to `a`, with `Enters σpre I v`; `Holds a P` holds after the move too.
`Deeper` is a fact about EVMLean's `Θ` and `Lambda`: every admitted message call and creation
below the frame keeps `Holds` when it starts where `Holds` holds before and after its value
moves.  The model's `call`, `staticcall`, `delegatecall` and `create` run exactly those `Θ` and
`Lambda`, on the model's account map, one level deeper.  Before a call that moves value out of
`a`, the model must show `Holds` of the account map with the value already taken, and, for a call
to `a`, `Enters` of that call.  A `delegatecall` runs code at `a`, and `Deeper` covers it only
when `Trusted` admits that code.

## The model's recorded calls

`m.callsAt` (`ContractModel.callsAt`) describes a frame's calls by the model: under every feed, on
a run of `m.runtime` from the frame's account map and substate that returns or stops, every call
and creation recorded in `World.calls` satisfies `Q`.  With it, `refinesOn_keeps_calls` asks only
for `ModelKeeps … m.callsAt m`.  At a call the model records, `made_theta_good` (and
`made_messageCall_good`, for the inputs `message` passes to `Θ`, one level deeper when the frame
is below depth 1024) gives `GoodTheta` of it from the premises `ModelKeeps` hands the run:
`Deeper`, `m.callsAt` of the frame, and the run.  `made_lambda_good` is the same for a creation.

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
admitted calls.  With `admits := fun _ _ => True` and `callsAt := XiOk` every call is admitted
(`admitted_of_all`) and the model may use `Deeper` of any call it makes.  With a real admission
condition, whether every frame at `a` in a callee's execution is admitted depends on the callee's
gas, which the model takes from its feed, not from the bytecode, so `XiOk` of the bytecode's run
does not reach the model's calls.  `callsAt := m.callsAt` closes that gap: admission describes the
calls of a frame at `a` by the calls the model records, and `ModelKeeps` receives that of the
frame's start state, substate and environment, the same `σ`, `A` and `I` its run starts from.  A
model that makes no call, like ERC20's, never needs `Deeper` and takes
`callsAt := fun _ _ _ _ _ _ => True`, which asks nothing of the calls below the frame.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant

/-- The model keeps `P` on every admitted message call at `a` running code `Trusted` admits,
    under any feed, when the admitted message calls and creations below its frame do and the
    calls the frame makes are as `callsAt` describes: every run that returns or stops ends with
    `a`'s account satisfying `P`, if its code is still what it was.  The call was entered from
    `σpre`, where `Holds` holds and the balances add up to less than `2 ^ 256`, by moving `v`
    from `I.source` to `a`, as `Enters` allows. -/
def ModelKeeps (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)
    (Enters : AccountMap → ExecutionEnv → UInt256 → Prop)
    (admits : AccountMap → ExecutionEnv → Prop) (callsAt : CallsAt) (m : ContractModel) : Prop :=
  ∀ (I : Env) σpre v σ σ₀ g A feed out (w : World), I.codeOwner = a → Trusted I.code →
    I.calldata.size < UInt256.size → admits σ I →
    Deeper a P Trusted Enters admits callsAt I.depth →
    callsAt (admBelow a admits callsAt (1024 - I.depth.val)) σ σ₀ g A I →
    σ = sendEth a I.source v true σpre → Enters σpre I v → v ≤ balOf σpre I.source →
    total σpre < UInt256.size → Holds a P σpre → Holds a P σ →
    Succeeds (m.runtime.exec I (World.init σ A feed)) out w →
    ∀ acc acc', σ[a]? = some acc → w.accounts[a]? = some acc' → acc'.code = acc.code → P acc'

/-- The calls and creations the model makes, as a description of a frame's calls: under every
    feed, on a run of `m.runtime` from the frame's account map and substate that returns or
    stops, every call and creation it records satisfies `Q`. -/
def ContractModel.callsAt (m : ContractModel) : CallsAt := fun Q σ _ _ A I =>
  ∀ feed out w, Succeeds (m.runtime.exec I (World.init σ A feed)) out w → ∀ c ∈ w.calls, c.Ok Q

section Keeps

variable {p : Profile} {bytecode : ByteArray} {m : ContractModel} {admits' : ExecutionEnv → Prop}
  {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
  {Enters : AccountMap → ExecutionEnv → UInt256 → Prop} {admits : AccountMap → ExecutionEnv → Prop}
  {callsAt : CallsAt}

/-- The per-frame hypothesis from a certificate on the calls `admits'` holds of, when every
    admitted frame is one. -/
theorem frameHyp_of_refinesOn (hcert : RefinesOn p bytecode m admits')
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted Enters admits callsAt m) :
    FrameHyp a P Trusted Enters admits callsAt := by
  intro σpre v σ σ₀ g A I σ' g' A' o howner htr hcd hadm hdeep hcalls hσ hen hv hTpre hHpre hH hXi
    acc acc' hacc hacc' hcode
  obtain ⟨tail, hc, htail⟩ := htrusted I.code htr
  exact (hcert σ σ₀ g A I tail hc htail (hadmits σ I hcd hadm)).accounts
    (P := fun τ => ∀ acc', τ[a]? = some acc' → acc'.code = acc.code → P acc')
    (fun feed out w hrun acc' => hmodel I σpre v σ σ₀ g A feed out w howner htr hcd hadm hdeep
      hcalls hσ hen hv hTpre hHpre hH hrun acc acc' hacc)
    hXi acc' hacc' hcode

/-- The per-frame hypothesis from a certificate. -/
theorem frameHyp_of_refines (hcert : Refines p bytecode m)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted Enters admits callsAt m) :
    FrameHyp a P Trusted Enters admits callsAt :=
  frameHyp_of_refinesOn hcert htrusted (fun _ _ h _ => h) hmodel

/-- **A certified contract keeps its invariant.**  If the bytecode refines the model on the
    admitted calls, the model keeps `P` whenever the admitted calls below it do, `P` is
    admissible, and every entry from another account that moves the value it reports satisfies
    `Enters`, then every message call and every creation, at every depth, that starts where
    `Holds a P` holds and in whose execution every successful frame at `a` is admitted, ends where
    it holds, as `ThetaGood` and `LambdaGood` state. -/
theorem refinesOn_keeps (hcert : RefinesOn p bytecode m admits') (hadm : Admissible P Trusted)
    (hent : FromOthers a Enters)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted Enters admits callsAt m) (e : Fin 1025) :
    ThetaGood a P Trusted Enters admits callsAt e ∧ LambdaGood a P admits callsAt e :=
  good hadm hent (frameHyp_of_refinesOn hcert htrusted hadmits hmodel) e

/-- `refinesOn_keeps` for a certificate on every call. -/
theorem refines_keeps (hcert : Refines p bytecode m) (hadm : Admissible P Trusted)
    (hent : FromOthers a Enters)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hmodel : ModelKeeps a P Trusted Enters admits callsAt m) (e : Fin 1025) :
    ThetaGood a P Trusted Enters admits callsAt e ∧ LambdaGood a P admits callsAt e :=
  refinesOn_keeps hcert hadm hent htrusted (fun _ _ h _ => h) hmodel e

/-! ## The model's recorded calls -/

/-- `frameHyp_of_refinesOn` with admission reaching the calls the model records. -/
theorem frameHyp_of_refinesOn_calls (hcert : RefinesOn p bytecode m admits')
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted Enters admits m.callsAt m) :
    FrameHyp a P Trusted Enters admits m.callsAt :=
  frameHyp_of_refinesOn hcert htrusted hadmits hmodel

/-- `refinesOn_keeps` with admission reaching the calls the model records. -/
theorem refinesOn_keeps_calls (hcert : RefinesOn p bytecode m admits')
    (hadm : Admissible P Trusted) (hent : FromOthers a Enters)
    (htrusted : ∀ code, Trusted code →
      ∃ tail, code = bytecode ++ tail ∧ tail.size = m.immutables)
    (hadmits : ∀ σ (I : ExecutionEnv), I.calldata.size < UInt256.size → admits σ I →
      admits' I)
    (hmodel : ModelKeeps a P Trusted Enters admits m.callsAt m) (e : Fin 1025) :
    ThetaGood a P Trusted Enters admits m.callsAt e ∧ LambdaGood a P admits m.callsAt e :=
  refinesOn_keeps hcert hadm hent htrusted hadmits hmodel e

/-- **A recorded message call is good.**  On a run that returns or stops, from the inputs of a
    frame at depth `I.depth`, a message call the model recorded one level deeper keeps `Holds`
    and `SubOk` and adds no ether (`GoodTheta`), given `Deeper` and that the recorded calls are
    admitted, as `ModelKeeps` supplies them. -/
theorem made_theta_good {I : Env} {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w : World}
    (hdeep : Deeper a P Trusted Enters admits m.callsAt I.depth)
    (hcalls : m.callsAt (admBelow a admits m.callsAt (1024 - I.depth.val)) σ σ₀ g A I)
    (hrun : Succeeds (m.runtime.exec I (World.init σ A feed)) out w) {T : ThetaCall}
    (hT : Made.theta T ∈ w.calls) (he : T.e.val = I.depth.val + 1) :
    GoodTheta a P Trusted Enters T :=
  hdeep.theta T he (hcalls feed out w hrun _ hT)

/-- `made_theta_good` for the call `message` makes, which is one level deeper whenever it is
    made (below depth 1024). -/
theorem made_messageCall_good {I : Env} {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w w₀ : World} {s : Supply}
    {gasArg value value' argsPtr argsLen : UInt256} {source recipient t : AccountAddress}
    {perm : Bool} (hdeep : Deeper a P Trusted Enters admits m.callsAt I.depth)
    (hcalls : m.callsAt (admBelow a admits m.callsAt (1024 - I.depth.val)) σ σ₀ g A I)
    (hrun : Succeeds (m.runtime.exec I (World.init σ A feed)) out w)
    (hT : Made.theta (messageCall I w₀ s gasArg source recipient t value value' argsPtr argsLen
      perm) ∈ w.calls) (hd : I.depth < 1024) :
    GoodTheta a P Trusted Enters
      (messageCall I w₀ s gasArg source recipient t value value' argsPtr argsLen perm) :=
  made_theta_good hdeep hcalls hrun hT (succ_depth_val hd)

/-- **A recorded creation is good**, as `made_theta_good`.  `createWith` records creations one
    level deeper. -/
theorem made_lambda_good {I : Env} {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w : World}
    (hdeep : Deeper a P Trusted Enters admits m.callsAt I.depth)
    (hcalls : m.callsAt (admBelow a admits m.callsAt (1024 - I.depth.val)) σ σ₀ g A I)
    (hrun : Succeeds (m.runtime.exec I (World.init σ A feed)) out w) {L : LambdaCall}
    (hL : Made.lambda L ∈ w.calls) (he : L.e.val = I.depth.val + 1) : GoodLambda a P L :=
  hdeep.lambda L he (hcalls feed out w hrun _ hL)

end Keeps

/-- `Agrees.accounts` with the return data: a property of the accounts and output every
    successful model run ends with holds of those a successful EVM run ends with. -/
theorem Agrees.accounts_out {p : Profile} {evm : EvmResult}
    {run : List Supply → Option (Except (Exit World) (ByteArray × World))} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {o : ByteArray} {Q : AccountMap → ByteArray → Prop}
    (h : Exhausted evm ∨ ∃ feed, Agrees p evm (run feed))
    (hQ : ∀ feed out w, Succeeds (run feed) out w → Q w.accounts out)
    (hrun : evm = .ok (.success (σ', g', A') o)) : Q σ' o := by
  subst hrun
  rcases h with (hoog | hoog) | ⟨feed, hag⟩
  · cases hoog
  · cases hoog
  cases hm : run feed with
  | none => rw [hm] at hag; exact hag.elim
  | some res =>
    rw [hm] at hag
    cases res with
    | error f =>
      cases f with
      | revert data => obtain ⟨_, _, h, _⟩ := hag; cases h
      | panic code => obtain ⟨_, _, h, _⟩ := hag; cases h
      | static => cases hag
      | trap => cases hag
      | oob => cases hag
      | stop out w =>
        obtain ⟨_, _, h, _⟩ := hag
        cases h
        exact hQ feed _ _ (Or.inr hm)
    | ok pr =>
      obtain ⟨out, w⟩ := pr
      obtain ⟨_, _, h, _⟩ := hag
      cases h
      exact hQ feed _ _ (Or.inl hm)

/-- **Deployment from a certificate.**  A creation of `creation ++ args` that succeeds ends where
    `Holds L.addr P` holds, if every successful run of the model's constructor, at the new
    address, with write permission, from an account map where that address has empty storage,
    leaves there an account that satisfies `P` with the code it returns. -/
theorem refinesDeploy_holds {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop} (hcert : RefinesDeploy p creation runtime m validArgs)
    {L : LambdaCall} {args : ByteArray} (hargs : validArgs args) (hi : L.i = creation ++ args)
    (hw : L.w = true) {P : Account → Prop}
    (hmodel : ∀ (I : Env) σ A feed out (w : World), I.codeOwner = L.addr → I.source = L.s →
      I.perm = true → (σ.getD L.addr default).storage = default →
      Succeeds ((m.init args >>= fun tail => pure (runtime ++ tail)).exec I
        (World.init σ A feed)) out w →
      P {w.accounts.getD L.addr default with code := out})
    (hz : L.run.2.2.2.2.1 = true) : L.run.1 = L.addr ∧ Holds L.addr P L.run.2.1 := by
  obtain ⟨hcode, hstor, -⟩ := lambda_success hz
  refine deploy_holds (fun σSS gSS ASS o hXi => ?_) hz
  exact Agrees.accounts_out
    (hcert L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2 args hargs (hcode.trans hi) hw)
    (Q := fun τ out => P {τ.getD L.addr default with code := out})
    (fun feed out w hrun => hmodel _ _ _ feed out w rfl rfl hw hstor hrun) hXi

end Fe.EVM
