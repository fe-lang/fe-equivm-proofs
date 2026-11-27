import Fe.Sonatina.CheckEvent
import Fe.Sonatina.Refine
import Reasoning.Stepping

/-!
# The real feed of a call, and refinement under it

`RefinesFor` (`Fe/EVM/Refine.lean`) lets the model's run take any feed: the bytes run out of gas
or of stack, or *some* feed makes the model end as the bytes do.  That is enough while the
model's run has no excuse, since `Agrees` forces it to reproduce the bytes' result whatever the
feed.  A source semantics with excuses (undefined behaviour, heap exhaustion) needs more: the
excuse must be available under the feed of the call the bytes actually ran, or a made-up feed
excuses any bytes.

`RealFeed σ σ₀ g A I feed`: `feed` is the feed the bytes' run of the call supplies, step by
step (`Check.Fut`: the word each `GAS` pushes, the gas, substate and original account map each
message call or creation hands its callee).  Every call has one (`realFeed_exists`) and only
one (`RealFeed.unique`, from `Fut.functional`: `Xstep` is a function).

`RefinesForFut`, `RefinesOnFut` and `RefinesDeployFut` are `RefinesFor`, `RefinesOn` and
`RefinesDeploy` with `RealFeed … feed` beside the agreement: the model agrees with the bytes
under the call's real feed.  Each implies the existing statement (`toRefinesFor`, …).

`ImplementsPSame` and `ImplementsDeployPSame` are `ImplementsP` and `ImplementsDeployP` with the
model's run under the same feed as the implementation's, what the step validator's
`Approx Eq` gives; they compose with the `Fut` statements as `ImplementsP` does with
`RefinesOn`.

The definitions live here, after `CheckEvent.lean` (which defines `Fut`) and before
`CheckCert.lean` (which proves the byte checker exports the real feed): `Fe/EVM/Refine.lean`
cannot import `Fut`, which depends on the checker's modules, and those import `Refine.lean`.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The bytes' run from a state supplies one feed and makes one list of calls: `Xstep` is a
    function. -/
theorem Fut.functional {s : State} {f₁ f₂ : List Supply} {m₁ m₂ : List Made}
    (h₁ : Fut s f₁ m₁) (h₂ : Fut s f₂ m₂) : f₁ = f₂ ∧ m₁ = m₂ := by
  induction h₁ generalizing f₂ m₂ with
  | stop h =>
    cases h₂ with
    | stop _ => exact ⟨rfl, rfl⟩
    | step hx _ => exact absurd hx (h _)
  | step hx _ ih =>
    cases h₂ with
    | stop h => exact absurd hx (h _)
    | step hx' rest' =>
      rw [hx] at hx'
      cases hx'
      obtain ⟨rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl⟩

end Fe.Sonatina.Check

namespace Fe.EVM

open Ethereum Ethereum.EVM Fe Fe.Sonatina

/-- `feed` is the feed the bytes' run of this call supplies, step by step (`Check.Fut`): the
    word each `GAS` pushes and the inputs each message call or creation hands its callee (gas,
    substate, original account map).  The bytes are deterministic, so a call has exactly one
    (`realFeed_exists`, `RealFeed.unique`).  Its gas entries are the gas the bytecode itself has
    left at those steps. -/
def RealFeed (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (feed : List Supply) : Prop :=
  ∃ M, Check.Fut (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I) feed M

/-- Every call has a real feed: each step of the bytes that goes on spends gas. -/
theorem realFeed_exists (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    ∃ feed, RealFeed σ σ₀ g A I feed := by
  obtain ⟨feed, M, h⟩ := Check.fut_exists (g.toNat + 1)
    (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I)
    (by simp [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toNat]; exact le_refl _)
  exact ⟨feed, M, h⟩

/-- A call has one real feed. -/
theorem RealFeed.unique {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {f₁ f₂ : List Supply} (h₁ : RealFeed σ σ₀ g A I f₁) (h₂ : RealFeed σ σ₀ g A I f₂) :
    f₁ = f₂ := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  exact (h₁.functional h₂).1

/-- A property of the real feed, stated for every feed that is real, is a property of the one
    real feed: the hypothesis "`P` at the call's real feed" is never vacuous. -/
theorem realFeed_forall_iff {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {P : List Supply → Prop} :
    (∀ feed, RealFeed σ σ₀ g A I feed → P feed) ↔ ∃ feed, RealFeed σ σ₀ g A I feed ∧ P feed := by
  constructor
  · intro h
    obtain ⟨feed, hr⟩ := realFeed_exists σ σ₀ g A I
    exact ⟨feed, hr, h feed hr⟩
  · rintro ⟨feed, hr, hp⟩ feed' hr'
    exact RealFeed.unique hr hr' ▸ hp

/-- `RefinesFor` under the call's real feed: the bytes run out of gas or of stack, or the model
    ends as the bytes do under the feed the bytes' run supplies. -/
def RefinesForFut (p : Profile) (m : ContractModel) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) : Prop :=
  Exhausted (Ξ σ σ₀ g A I) ∨
    ∃ feed, RealFeed σ σ₀ g A I feed ∧
      Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A feed))

/-- `RefinesOn` under each call's real feed. -/
def RefinesOnFut (p : Profile) (code : ByteArray) (m : ContractModel)
    (admits : ExecutionEnv → Prop) : Prop :=
  ∀ σ σ₀ g A I tail, I.code = code ++ tail → tail.size = m.immutables → OwnerExists σ I →
    admits I → RefinesForFut p m σ σ₀ g A I

/-- One deployment of `RefinesDeployFut`: the creation bytes run out of gas or of stack, or the
    model's constructor on `args`, its result after `runtime`, ends as the bytes do under the
    feed the bytes' run supplies. -/
def RefinesDeployForFut (p : Profile) (runtime : ByteArray) (m : ContractModel)
    (args : ByteArray) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Prop :=
  Exhausted (Ξ σ σ₀ g A I) ∨
    ∃ feed, RealFeed σ σ₀ g A I feed ∧ Agrees p (Ξ σ σ₀ g A I)
      ((m.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed))

/-- `RefinesDeploy` under each deployment's real feed. -/
def RefinesDeployFut (p : Profile) (creation runtime : ByteArray) (m : ContractModel)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true → RefinesDeployForFut p runtime m args σ σ₀ g A I

theorem RefinesForFut.toRefinesFor {p : Profile} {m : ContractModel} {σ σ₀ : AccountMap}
    {g : UInt256} {A : Substate} {I : ExecutionEnv} (h : RefinesForFut p m σ σ₀ g A I) :
    RefinesFor p m σ σ₀ g A I :=
  h.imp id fun ⟨feed, _, hag⟩ => ⟨feed, hag⟩

theorem RefinesOnFut.toRefinesOn {p : Profile} {code : ByteArray} {m : ContractModel}
    {admits : ExecutionEnv → Prop} (h : RefinesOnFut p code m admits) :
    RefinesOn p code m admits :=
  fun σ σ₀ g A I tail hc ht ho ha => (h σ σ₀ g A I tail hc ht ho ha).toRefinesFor

theorem RefinesDeployFut.toRefinesDeploy {p : Profile} {creation runtime : ByteArray}
    {m : ContractModel} {validArgs : ByteArray → Prop}
    (h : RefinesDeployFut p creation runtime m validArgs) :
    RefinesDeploy p creation runtime m validArgs :=
  fun σ σ₀ g A I args hv hc ho hp =>
    (h σ σ₀ g A I args hv hc ho hp).imp id fun ⟨feed, _, hag⟩ => ⟨feed, hag⟩

/-- A per-call refinement under the real feed carries over to a model each run of which, at
    that feed, the implementation's run ends as, in the sense of partial correctness. -/
theorem RefinesForFut.of_endsAsP {p : Profile} {model ir : ContractModel} {σ σ₀ : AccountMap}
    {g : UInt256} {A : Substate} {I : ExecutionEnv} (h : RefinesForFut p ir σ σ₀ g A I)
    (hm : ∀ feed, RealFeed σ σ₀ g A I feed →
      EndsAsP (model.runtime.exec I (World.init σ A feed)) (ir.runtime.exec I (World.init σ A feed))) :
    RefinesForFut p model σ σ₀ g A I :=
  h.imp id fun ⟨feed, hr, hag⟩ => ⟨feed, hr, Agrees.of_endsAsP (hm feed hr) hag⟩

/-- `RefinesForFut.of_endsAsP` for one deployment. -/
theorem RefinesDeployForFut.of_endsAsP {p : Profile} {runtime irRuntime : ByteArray}
    {model ir : ContractModel} {args : ByteArray} {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv} (h : RefinesDeployForFut p irRuntime ir args σ σ₀ g A I)
    (hm : ∀ feed, RealFeed σ σ₀ g A I feed →
      EndsAsP ((model.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed))
        ((ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed))) :
    RefinesDeployForFut p runtime model args σ σ₀ g A I :=
  h.imp id fun ⟨feed, hr, hag⟩ => ⟨feed, hr, Agrees.of_endsAsP (hm feed hr) hag⟩

end Fe.EVM

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-- `ImplementsP` with both runs under the same feed: each run of the IR, under any feed,
    diverges or ends as the model's run on the same call under that feed. -/
def ImplementsPSame (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, OwnerExists σ I → admits I →
    EndsAsP (model.runtime.exec I (World.init σ A feed)) (ir.runtime.exec I (World.init σ A feed))

/-- `ImplementsDeployP` with both runs under the same feed. -/
def ImplementsDeployPSame (model ir : ContractModel) (creation runtime irRuntime : ByteArray)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ I σ A feed args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true →
    EndsAsP ((model.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed))
      ((ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed))

theorem ImplementsPSame.toP {model ir : ContractModel} {admits : ExecutionEnv → Prop}
    (h : ImplementsPSame model ir admits) : ImplementsP model ir admits :=
  fun I σ A feed ho ha => ⟨feed, h I σ A feed ho ha⟩

theorem ImplementsDeployPSame.toP {model ir : ContractModel}
    {creation runtime irRuntime : ByteArray} {validArgs : ByteArray → Prop}
    (h : ImplementsDeployPSame model ir creation runtime irRuntime validArgs) :
    ImplementsDeployP model ir creation runtime irRuntime validArgs :=
  fun I σ A feed args hv hc ho hp => ⟨feed, h I σ A feed args hv hc ho hp⟩

/-- `RefinesOn.of_implementsP` under the real feed: as the IR's run and the model's take the
    same feed, the agreeing feed stays the real one. -/
theorem RefinesOnFut.of_implementsPSame {p : Profile} {code : ByteArray}
    {model ir : ContractModel} {admits : ExecutionEnv → Prop} (h : RefinesOnFut p code ir admits)
    (hm : ImplementsPSame model ir admits) (himm : model.immutables = ir.immutables) :
    RefinesOnFut p code model admits := by
  intro σ σ₀ g A I tail hcode htail hown hadmits
  exact (h σ σ₀ g A I tail hcode (himm ▸ htail) hown hadmits).of_endsAsP
    fun feed _ => hm I σ A feed hown hadmits

/-- `RefinesDeploy.of_implementsP` under the real feed. -/
theorem RefinesDeployFut.of_implementsPSame {p : Profile} {creation runtime irRuntime : ByteArray}
    {model ir : ContractModel} {validArgs : ByteArray → Prop}
    (h : RefinesDeployFut p creation irRuntime ir validArgs)
    (hm : ImplementsDeployPSame model ir creation runtime irRuntime validArgs) :
    RefinesDeployFut p creation runtime model validArgs := by
  intro σ σ₀ g A I args hargs hcode hown hperm
  exact (h σ σ₀ g A I args hargs hcode hown hperm).of_endsAsP
    fun feed _ => hm I σ A feed args hargs hcode hown hperm

end Fe.Sonatina
