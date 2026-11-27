import Fe.Sonatina.Steps.SchemasStepSound
import Fe.Sonatina.Steps.GvnInsert

/-!
# `gvn_rewrite` is sound

The checker (`GvnRewrite.lean`) adds the inserted phis to the input (`insPhis`), which approximates
the input (`insPhis_sound`), and checks the rewrite from there in the schema checkers' `gvn` mode,
whose simulation carries GVN's classes and the inserted phis' terms as invariants of the input's
run (`GvnInv.lean`, `SF.sim`).  The two approximations compose.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-- A `gvn_rewrite` step the checker accepts is sound. -/
theorem gvnRewrite_sound {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : checkGvnRewrite f ids s F = true)
    {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  unfold checkGvnRewrite gvnRewriteReject at h
  rcases ids with _ | is
  · simp at h
  rcases hG : F.gvn with _ | G
  · simp [hG] at h
  simp only [hG] at h
  split at h
  · simp at h
  split at h
  · simp at h
  generalize hp : gvnPrep f is s F G = P at h
  obtain ⟨ps, f₁, is₁, m⟩ := P
  simp only at h
  split at h
  · simp at h
  next hins =>
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hins
  have hal : aliasReject m f₁ (some is₁) s F = none := by
    cases hr : aliasReject m f₁ (some is₁) s F with
    | none => rfl
    | some r => rw [hr] at h; simp at h
  simp only [gvnPrep, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl, _, rfl⟩ := hp
  have hwf₁ := insPhis_wf hwf hins
  exact (aliasReject_sound (Or.inr (Or.inr ⟨_, _, rfl⟩)) hwf₁ hal (fun h' => by cases h') ho hoi c).trans
    (insPhis_sound hwf hins ho hoi c)

theorem gvnRewrite_stepSound : StepSound .gvnRewrite :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    gvnRewrite_sound hw (by simpa only [checkFunc] using h) ho hoi c

end Fe.Sonatina.Steps.Schemas
