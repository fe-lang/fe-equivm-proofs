import Reasoning.Reach
import Fe.EVM.Refine

/-!
# From a finished EVM trace to model refinement

EquiVM's terminals `RDret` and `RDrev` say how a run of the bytecode ends, or that it runs out of
gas.  Paired with the model's run on the same inputs, each gives `RefinesFor`.

`RDret` does not expose the final substate and `RDrev` hides the revert payload, so these lemmas
conclude at profile `P0` only.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-- The bytecode returns `o` with account map `σ'`, and so does the model. -/
theorem refinesFor_of_ret {m : ContractModel} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {code o : ByteArray} {σ' : AccountMap} {w' : World}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : m.runtime.exec I (World.init σ A) = some (.ok (o, w')))
    (hw : w'.accounts = σ') :
    RefinesFor .P0 m σ σ₀ g.toUInt256 A I := by
  subst hcode
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    refine Or.inr ?_
    rw [hm]
    exact ⟨_, _, by rw [hxi, hw, hacc], fun h => by cases h⟩

/-- The bytecode reverts, and the model fails with a revert or a panic. -/
theorem refinesFor_of_rev {m : ContractModel} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {code : ByteArray} {f : Fail}
    (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hm : m.runtime.exec I (World.init σ A) = some (.error f))
    (hf : f ≠ .static) :
    RefinesFor .P0 m σ σ₀ g.toUInt256 A I := by
  subst hcode
  rcases h with hoog | ⟨g', o, hX⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    refine Or.inr ?_
    rw [hm]
    cases f with
    | revert data => exact ⟨g', o, hxi, fun h => by cases h⟩
    | panic code => exact ⟨g', o, hxi, fun h => by cases h⟩
    | static => exact absurd rfl hf

end Fe.EVM
