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
-/

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-- The IR's runtime implements the model's on the calls `admits` holds of: each run of the IR,
    under any feed, ends as a run of the model on the same call under some feed.  The memory of
    the two may differ. -/
def Implements (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, admits I → ∃ feed', EndsAs (model.runtime.exec I (World.init σ A feed'))
    (ir.runtime.exec I (World.init σ A feed))

theorem RefinesOn.of_implements {p : Profile} {code : ByteArray} {model ir : ContractModel}
    {admits : ExecutionEnv → Prop} (h : RefinesOn p code ir admits)
    (hm : Implements model ir admits) (himm : model.immutables = ir.immutables) :
    RefinesOn p code model admits := by
  intro σ σ₀ g A I tail hcode htail hadmits
  rcases h σ σ₀ g A I tail hcode (himm ▸ htail) hadmits with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed hadmits
    exact Or.inr ⟨feed', Agrees.of_endsAs hend hag⟩

/-- The IR's constructor implements the model's on the argument bytes `validArgs` holds of: each
    deployment by the IR, which returns the deployed code after the code `irRuntime`, ends as a
    deployment by the model, which returns it after `runtime`.  The IR of a Sonatina object
    returns the whole deployed code, so its `irRuntime` is empty.  The deployment runs the
    creation code with the arguments after it, which the IR reads from its own code. -/
def ImplementsDeploy (model ir : ContractModel) (creation runtime irRuntime : ByteArray)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ I σ A feed args, validArgs args → I.code = creation ++ args → I.perm = true → ∃ feed',
    EndsAs ((model.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed'))
      ((ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed))

theorem RefinesDeploy.of_implements {p : Profile} {creation runtime irRuntime : ByteArray}
    {model ir : ContractModel} {validArgs : ByteArray → Prop}
    (h : RefinesDeploy p creation irRuntime ir validArgs)
    (hm : ImplementsDeploy model ir creation runtime irRuntime validArgs) :
    RefinesDeploy p creation runtime model validArgs := by
  intro σ σ₀ g A I args hargs hcode hperm
  rcases h σ σ₀ g A I args hargs hcode hperm with hex | ⟨feed, hag⟩
  · exact Or.inl hex
  · obtain ⟨feed', hend⟩ := hm I σ A feed args hargs hcode hperm
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

end Fe.Sonatina
