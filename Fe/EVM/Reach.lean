import Reasoning.Reach
import Fe.EVM.Refine

/-!
# From a finished EVM trace to model refinement

EquiVM's terminals `RDret`, `RDrev` and `RDstatic` say how a run of the bytecode ends, or that it
runs out of gas.  Paired with the model's run on the same inputs, each gives agreement.

`RDret` does not expose the final substate and `RDrev` hides the revert payload, so these lemmas
conclude at profile `P0` only.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256} {code : ByteArray}
  {r : Option (Except (Exit World) (ByteArray × World))}

/-- The bytecode returns `o` with account map `σ'`, and so does the model. -/
theorem agrees_of_ret {o : ByteArray} {σ' : AccountMap} {w' : World}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : r = some (.ok (o, w'))) (hw : w'.accounts = σ') :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    exact Or.inr ⟨_, _, by rw [hxi, hw, hacc], fun h => by cases h⟩

/-- The bytecode returns `o` with account map `σ'`, and the model stops with the same. -/
theorem agrees_of_stop {o : ByteArray} {σ' : AccountMap} {w' : World}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : r = some (.error (.stop o w'))) (hw : w'.accounts = σ') :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    exact Or.inr ⟨_, _, by rw [hxi, hw, hacc], fun h => by cases h⟩

/-- The bytecode reverts, and the model fails with a revert or a panic. -/
theorem agrees_of_rev {f : Exit World}
    (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hm : r = some (.error f)) (hf : f.reverts = true) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨g', o, hX⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    refine Or.inr ?_
    cases f with
    | revert data => exact ⟨g', o, hxi, fun h => by cases h⟩
    | panic code => exact ⟨g', o, hxi, fun h => by cases h⟩
    | static => cases hf
    | trap => cases hf
    | stop o w => cases hf

/-- The bytecode halts on a static-mode violation, and the model fails the same way. -/
theorem agrees_of_static
    (hcode : I.code = code)
    (h : RDstatic code g (initState σ σ₀ g A I))
    (hm : r = some (.error .static)) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | hst
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · exact Or.inr (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hst))

/-- The model's storage write is the account-map update the trace lemmas use. -/
theorem storeWord_eq_sstoreAccountMap (owner : AccountAddress) (σ : AccountMap)
    (slot val : UInt256) : storeWord owner σ slot val = sstoreAccountMap owner σ slot val := rfl

end Fe.EVM
