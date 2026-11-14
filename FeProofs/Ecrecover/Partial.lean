import FeProofs.Ecrecover.Exported

/-!
# Ecrecover: partial correctness of exported loops

A `partial_fixpoint` loop of the exported model comes with `fixpoint_induct` for admissible
predicates.  "Every run that returns satisfies `Q`" is admissible (`admissible_exec`): a run
that diverges is `none`, the bottom of the flat order, and satisfies it.  This is what the
partial correctness of `invert`'s outer loop goes through.  The lemma is general in the
monad's environment and world.
-/

open Lean.Order

namespace Fe.M

theorem admissible_exec {ρ σ α : Type} (Q : α → σ → Prop) :
    admissible (fun (m : Fe.M ρ σ α) =>
      ∀ env w r w', m.exec env w = some (.ok (r, w')) → Q r w') := by
  apply admissible_pi_apply (β := fun _ : ρ => StateT σ (ExceptT (Exit σ) Option) α)
    (P := fun _ g => ∀ w r w', ((g.run w).run) = some (.ok (r, w')) → Q r w')
  intro env
  apply admissible_pi_apply (β := fun _ : σ => ExceptT (Exit σ) Option (α × σ))
    (P := fun _ g => ∀ r w', g.run = some (.ok (r, w')) → Q r w')
  intro w
  apply admissible_flatOrder
  intro r w' h
  cases h

end Fe.M
