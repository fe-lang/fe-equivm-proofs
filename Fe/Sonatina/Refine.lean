import Fe.EVM.Refine

/-!
# Splitting a certificate at Sonatina IR

A certificate `Refines p bytecode model` splits into two halves that meet at the contract model
of the IR (`Sidecar.model`, `Fe/Sonatina/Interp.lean`):

- the bytecode refines the IR, `RefinesOn p bytecode ir admits`, which a checker of the
  bytecode against the IR and its hints is to decide once proved sound;
- the IR implements the model, `Implements model ir admits`: each run of the IR ends as a run
  of the model on the same call does.  It speaks of SSA values, storage and explicit memory, not
  of the stack, jumps or the memory plan.

`RefinesOn.of_implements` and `RefinesDeploy.of_implements` compose them.

`ImplementsP` is `Implements` in the sense of partial correctness (`EndsAsP`: the IR's run
diverges or ends as the model's does), what a validator of compiler steps proves;
`RefinesOn.of_implementsP` and `RefinesDeploy.of_implementsP` compose it the same way.
-/

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-- The IR's runtime implements the model's on the calls `admits` holds of, at an account that
    exists (`OwnerExists`): each run of the IR, under any feed, ends as a run of the model on the
    same call under some feed.  The memory of the two may differ. -/
def Implements (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, OwnerExists σ I → admits I → ∃ feed', EndsAs (model.runtime.exec I (World.init σ A feed'))
    (ir.runtime.exec I (World.init σ A feed))

theorem RefinesOn.of_implements {p : Profile} {code : ByteArray} {model ir : ContractModel}
    {admits : ExecutionEnv → Prop} (h : RefinesOn p code ir admits)
    (hm : Implements model ir admits) (himm : model.immutables = ir.immutables) :
    RefinesOn p code model admits := by
  intro σ σ₀ g A I tail hcode htail hown hadmits
  rcases h σ σ₀ g A I tail hcode (himm ▸ htail) hown hadmits with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed hown hadmits
    exact Or.inr ⟨feed', Agrees.of_endsAs hend hag⟩

/-- The IR's constructor implements the model's on the argument bytes `validArgs` holds of: each
    deployment by the IR, which returns the deployed code after the code `irRuntime`, ends as a
    deployment by the model, which returns it after `runtime`.  The IR of a Sonatina object
    returns the whole deployed code, so its `irRuntime` is empty.  The deployment runs the
    creation code with the arguments after it, which the IR reads from its own code, at an
    account that exists (`OwnerExists`). -/
def ImplementsDeploy (model ir : ContractModel) (creation runtime irRuntime : ByteArray)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ I σ A feed args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true → ∃ feed',
    EndsAs ((model.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed'))
      ((ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed))

theorem RefinesDeploy.of_implements {p : Profile} {creation runtime irRuntime : ByteArray}
    {model ir : ContractModel} {validArgs : ByteArray → Prop}
    (h : RefinesDeploy p creation irRuntime ir validArgs)
    (hm : ImplementsDeploy model ir creation runtime irRuntime validArgs) :
    RefinesDeploy p creation runtime model validArgs := by
  intro σ σ₀ g A I args hargs hcode hown hperm
  rcases h σ σ₀ g A I args hargs hcode hown hperm with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed args hargs hcode hown hperm
    exact Or.inr ⟨feed', Agrees.of_endsAs hend hag⟩

/-- Ending as is transitive: a run that ends as one that ends as a third ends as the third. -/
theorem _root_.Fe.EVM.EndsAs.trans {a b c : Option (Except (Exit World) (ByteArray × World))}
    (h₁ : EndsAs a b) (h₂ : EndsAs b c) : EndsAs a c := by
  cases h₁ <;> cases h₂ <;> first
    | exact .diverge | exact .exit _
    | (constructor <;> simp_all)

/-- Two reverts with equal payloads end alike. -/
theorem endsAs_revert {a b : ByteArray} (h : a = b) :
    EndsAs (some (.error (.revert a))) (some (.error (.revert b))) := h ▸ .exit _

/-! ## Partial correctness

`Implements` is total correctness: `EndsAs a none` holds only of `a = none`
(`endsAs_none_iff`), so an IR that implements a model diverges exactly where the model does.  A
translation validator proves less: each run of the output that ends, ends as the input's run
does.  `ImplementsP` is that relation; it composes with `RefinesOn` as `Implements` does, since
a bytecode result agrees with no diverging run. -/

/-- Only a diverging run ends as a diverging run does. -/
theorem endsAs_none_iff {a : Option (Except (Exit World) (ByteArray × World))} :
    EndsAs a none ↔ a = none := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .diverge

/-- A run ends as a diverging run does only if it diverges. -/
theorem none_endsAs_iff {b : Option (Except (Exit World) (ByteArray × World))} :
    EndsAs none b ↔ b = none := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .diverge

/-- Partial correctness: the implementation's run `b` diverges, or ends as the model's `a`
    does. -/
def EndsAsP (a b : Option (Except (Exit World) (ByteArray × World))) : Prop :=
  b = none ∨ EndsAs a b

theorem EndsAs.toP {a b : Option (Except (Exit World) (ByteArray × World))} (h : EndsAs a b) :
    EndsAsP a b := Or.inr h

theorem EndsAsP.trans {a b c : Option (Except (Exit World) (ByteArray × World))}
    (h₁ : EndsAsP a b) (h₂ : EndsAsP b c) : EndsAsP a c := by
  rcases h₂ with h₂ | h₂
  · exact Or.inl h₂
  rcases h₁ with h₁ | h₁
  · subst h₁; exact Or.inl (none_endsAs_iff.mp h₂)
  · exact Or.inr (h₁.trans h₂)

/-- The IR's runtime implements the model's in the sense of partial correctness, on the calls
    `admits` holds of, at an account that exists: each run of the IR, under any feed, diverges or
    ends as a run of the model on the same call under some feed. -/
def ImplementsP (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, OwnerExists σ I → admits I → ∃ feed',
    EndsAsP (model.runtime.exec I (World.init σ A feed')) (ir.runtime.exec I (World.init σ A feed))

theorem Implements.toP {model ir : ContractModel} {admits : ExecutionEnv → Prop}
    (h : Implements model ir admits) : ImplementsP model ir admits := fun I σ A feed ho ha =>
  (h I σ A feed ho ha).imp fun _ => EndsAs.toP

theorem ImplementsP.trans {model mid ir : ContractModel} {admits : ExecutionEnv → Prop}
    (h₁ : ImplementsP model mid admits) (h₂ : ImplementsP mid ir admits) :
    ImplementsP model ir admits := by
  intro I σ A feed ho ha
  obtain ⟨feed', h⟩ := h₂ I σ A feed ho ha
  obtain ⟨feed'', h'⟩ := h₁ I σ A feed' ho ha
  exact ⟨feed'', h'.trans h⟩

/-- A result that agrees with a run agrees with any run that it ends as in the sense of partial
    correctness: agreement excludes divergence. -/
theorem Agrees.of_endsAsP {p : Profile} {evm : EvmResult}
    {a b : Option (Except (Exit World) (ByteArray × World))} (h : EndsAsP a b)
    (hb : Agrees p evm b) : Agrees p evm a := by
  rcases h with h | h
  · subst h; exact hb.elim
  · exact Agrees.of_endsAs h hb

/-- `RefinesOn.of_implements` for partial correctness: the same proof, since when `Agrees evm b`
    holds, `b ≠ none`. -/
theorem RefinesOn.of_implementsP {p : Profile} {code : ByteArray} {model ir : ContractModel}
    {admits : ExecutionEnv → Prop} (h : RefinesOn p code ir admits)
    (hm : ImplementsP model ir admits) (himm : model.immutables = ir.immutables) :
    RefinesOn p code model admits := by
  intro σ σ₀ g A I tail hcode htail hown hadmits
  rcases h σ σ₀ g A I tail hcode (himm ▸ htail) hown hadmits with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed hown hadmits
    exact Or.inr ⟨feed', Agrees.of_endsAsP hend hag⟩

/-- `ImplementsDeploy` in the sense of partial correctness. -/
def ImplementsDeployP (model ir : ContractModel) (creation runtime irRuntime : ByteArray)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ I σ A feed args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true → ∃ feed',
    EndsAsP ((model.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed'))
      ((ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed))

theorem ImplementsDeployP.trans {model mid ir : ContractModel}
    {creation runtime midRuntime irRuntime : ByteArray} {validArgs : ByteArray → Prop}
    (h₁ : ImplementsDeployP model mid creation runtime midRuntime validArgs)
    (h₂ : ImplementsDeployP mid ir creation midRuntime irRuntime validArgs) :
    ImplementsDeployP model ir creation runtime irRuntime validArgs := by
  intro I σ A feed args hv hc ho hp
  obtain ⟨feed', h⟩ := h₂ I σ A feed args hv hc ho hp
  obtain ⟨feed'', h'⟩ := h₁ I σ A feed' args hv hc ho hp
  exact ⟨feed'', h'.trans h⟩

theorem RefinesDeploy.of_implementsP {p : Profile} {creation runtime irRuntime : ByteArray}
    {model ir : ContractModel} {validArgs : ByteArray → Prop}
    (h : RefinesDeploy p creation irRuntime ir validArgs)
    (hm : ImplementsDeployP model ir creation runtime irRuntime validArgs) :
    RefinesDeploy p creation runtime model validArgs := by
  intro σ σ₀ g A I args hargs hcode hown hperm
  rcases h σ σ₀ g A I args hargs hcode hown hperm with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed args hargs hcode hown hperm
    exact Or.inr ⟨feed', Agrees.of_endsAsP hend hag⟩

end Fe.Sonatina
