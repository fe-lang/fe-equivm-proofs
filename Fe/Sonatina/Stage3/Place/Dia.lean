import Fe.Sonatina.Stage3.Place.Fns

/-!
# Templates that branch

The dynamic `evm_mload_bytes` and the heap base clamp end the block their template starts in
with a branch whose arms meet in a join; the template ends with the join's phis and the
statements the join's body starts with.  `DiaOk` is what such a pattern lemma gives, for a frame
and the live sets before and after the statement: the shape of the diamond, and that every run
of it (`diaRun`) from related states ends as H's step does.  It is `DiaK` of the function
(`DiaOk.diaK`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- A statement whose template is a diamond from block `mb` to the join `mb'`, with the
    statements `ms'` of the join left after it, and whose every run ends as H's step does. -/
def DiaOk (P : HSection) (I : Fe.EVM.Env) (cM : Ctx) (S : SecFacts) (F : Frame) (c : FCtx)
    (s : HStmt) (mb : Nat) (ms : List Stmt) (mb' : Nat) (ms' : List Stmt) (L L' : List Nat) :
    Prop :=
  ∃ mblk cv t₁ t₂ jb pre₂, c.mf.block? mb = some mblk ∧ mblk.term = .br cv t₁ t₂ ∧
    c.mf.block? mb' = some jb ∧ jb.body = pre₂ ++ ms' ∧
    (∀ a, (a = t₁ ∨ a = t₂) → a ≠ mb' →
      ∃ ab, c.mf.block? a = some ab ∧ ab.phis = [] ∧ ab.term = .jump mb') ∧
    ∀ O g hst w envH envM, Inv S hst w g → EnvRel S.z F g hst envH envM L →
      ∀ r, (diaRun cM O c.mf mb ms cv t₁ t₂ mb' jb pre₂ envM).exec I w = some r →
        StepOk P I S F g hst envH s L' r

theorem DiaOk.diaK {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts}
    {CP : Oracle → Prop} {fn : Fn} {b : HBlock} {i : Nat} {s : HStmt} {mb : Nat}
    {ms : List Stmt} {mb' : Nat} {ms' : List Stmt}
    (h : DiaOk P I cM S fn.F fn.c s mb ms mb' ms' (fn.live b i) (fn.live b (i + 1))) :
    DiaK P I cM S CP fn b i s mb ms mb' ms' := by
  obtain ⟨mblk, cv, t₁, t₂, jb, pre₂, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨mblk, cv, t₁, t₂, jb, pre₂, h1, h2, h3, h4, h5,
    fun O _ g hst w envH envM hI hE r hr => h6 O g hst w envH envM hI hE r hr⟩

end Fe.Sonatina.Stage3.Place
