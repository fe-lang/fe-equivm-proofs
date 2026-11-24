import Fe.Sonatina.Steps.EdgeSplit
import Fe.Sonatina.Steps.Record

/-!
# Validating a record of machine steps

`validate syms r final` replays the record: from the lowered module, each pass's steps in
order, each step checked (`checkStep`) and its functions substituted (`Module.update`), and the
composed module compared with `final`, the sidecar's machine IR.  The lowered module is checked
well formed (`Module.wf`) against the section's symbol names `syms`, and so is every step's
output function, which keeps its input's signature: so every module of the replay is well
formed (`stepOut_wf`).  `validateWith allowed` also rejects records with a step kind outside
`allowed`.

`StepSound k`: a step of kind `k` that the check accepts on a well-formed module gives, for
every function, an output that approximates the input on integers under any oracle that
approximates itself and returns integers, in any context with the symbols.  `edgeSplit_stepSound`
proves it for `edge_split`; the other kinds enter `validate_sound` as hypotheses.  Within a pass
every step runs calls by the pass input's semantics; C1 (`modRefines_of_funcs`) closes each
pass, and passes compose by `ModRefines.trans`.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-- The module with the functions `fs` in place of those of the same name. -/
def _root_.Fe.Sonatina.Module.update (M : Module) (fs : List Func) : Module :=
  { M with funcs := M.funcs.map fun g => (fs.find? (·.name == g.name)).getD g }

theorem Module.update_func? (M : Module) (fs : List Func) (name : String) :
    (M.update fs).func? name = (M.func? name).map fun g => (fs.find? (·.name == g.name)).getD g := by
  unfold Module.update Module.func?
  rw [List.find?_map]
  congr 2
  funext g
  simp only [Function.comp]
  cases h : fs.find? (·.name == g.name) with
  | none => rfl
  | some r =>
    have := List.find?_some h
    simp only [beq_iff_eq] at this
    simp [this]

/-- The check of one function by a step kind.  Kinds without a checker reject. -/
def checkFunc : StepKind → Func → Func → Bool
  | .edgeSplit, f, f' => checkEdgeSplit f f'
  | _, _, _ => false

/-- `g` has the parameters and results of `f`. -/
def sameSig (f g : Func) : Bool := decide (g.params = f.params) && decide (g.rets = f.rets)

/-- A step: every function it lists exists in the input, is renamed to nothing, keeps its
    signature, has no facts (no kind of this phase reads any), is well formed in the input
    module (whose signatures it keeps) with its instruction ids, and passes its kind's check. -/
def checkStep (k : StepKind) (syms : List String) (_O : Option (List Summary)) (M : Module)
    (fs : List FuncStep) : Bool :=
  fs.all fun s => s.facts.isEmpty && s.out.func.name == s.func && s.out.wf M.sig syms &&
    (M.func? s.func).any fun f => sameSig f s.out.func && checkFunc k f s.out.func

/-- A step's output module. -/
def stepOut (M : Module) (fs : List FuncStep) : Module := M.update (fs.map (·.out.func))

/-- `k`'s check is sound: each function of an accepted step's output, its calls run by an
    oracle that approximates itself and returns integers on integers, approximates the same
    function of the input on integers, in any context with the symbols. -/
def StepSound (k : StepKind) : Prop :=
  ∀ (syms : List String) (O : Option (List Summary)) (M : Module) (fs : List FuncStep),
    M.wf syms = true → checkStep k syms O M fs = true →
    ∀ (o : Oracle) (c : Ctx), c.Has syms → Oracle.Mono o → o.IntRet →
      ∀ name, FuncRef o c ((stepOut M fs).func? name) (M.func? name)

/-- A function approximates itself under an oracle that does and returns integers. -/
theorem FuncRef.refl {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {f : Func}
    (hf : f.machine = true) : FuncRef o c (some f) (some f) := by
  have sim : Sim o c f f (fun s' s => s' = s ∧ EnvInt s.1) := Sim.of_steps fun s' s hR => by
    obtain ⟨hR, he⟩ := hR
    subst hR
    left
    exact Approx.mono (Approx.strengthen (Approx.stepBlock ho hoi rfl hf _ he _ _)
      (returns_stepBlock hoi c hf he _ _)) fun n' n ⟨e, hn⟩ => by
        cases e
        cases n' with
        | goto env' d => exact ⟨rfl, hn⟩
        | done v => rfl
  intro args hargs
  unfold runFuncO
  dsimp only
  cases f.blocks.head? with
  | none => exact Approx.stuck _
  | some e =>
    exact Approx.bind (Approx.strengthen (Approx.bindVals _ _ _)
      (returns_bind_int EnvInt.empty hargs)) fun env env₀ ⟨e₁, he⟩ => by
        cases e₁; exact Sim.approx sim (env, none, e.id) _ ⟨rfl, he⟩

theorem FuncRef.none (o : Oracle) (c : Ctx) : FuncRef o c none none := fun _ _ => Approx.stuck _

theorem checkStep_spec {k : StepKind} {syms : List String} {O : Option (List Summary)}
    {M : Module} {fs : List FuncStep} (h : checkStep k syms O M fs = true) :
    ∀ s ∈ fs, s.facts.isEmpty = true ∧ s.out.func.name = s.func ∧
      s.out.func.wf M.sig syms = true ∧
      ∃ f, M.func? s.func = some f ∧ sameSig f s.out.func = true ∧ checkFunc k f s.out.func = true := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, FuncSnap.wf] at this
  obtain ⟨⟨⟨hf, hn⟩, hw, _⟩, f, hMf, hsig, hck⟩ := this
  exact ⟨hf, hn, hw, f, hMf, hsig, hck⟩

/-- A step's output function, if any, of the name of a function `g` of the input: one with the
    signature of `g`, well formed in the input. -/
theorem stepOut_func {k : StepKind} {syms : List String} {O : Option (List Summary)} {M : Module}
    {fs : List FuncStep} (h : checkStep k syms O M fs = true) {name : String} {g : Func}
    (hg : M.func? name = some g) :
    (fs.map (·.out.func)).find? (·.name == g.name) = none ∨
      ∃ s ∈ fs, (fs.map (·.out.func)).find? (·.name == g.name) = some s.out.func ∧
        s.out.func.name = g.name ∧ sameSig g s.out.func = true ∧ s.out.func.wf M.sig syms = true ∧
        checkFunc k g s.out.func = true := by
  cases hr : (fs.map (·.out.func)).find? (·.name == g.name) with
  | none => exact Or.inl rfl
  | some r =>
    right
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hr)
    have hsn : s.out.func.name = g.name := by simpa using List.find?_some hr
    have hgname : g.name = name := by simpa using List.find?_some hg
    obtain ⟨_, hname, hw, f, hf, hsig, hck⟩ := checkStep_spec h s hs
    rw [← hname, hsn, hgname, hg] at hf
    cases hf
    exact ⟨s, hs, rfl, hsn, hsig, hw, hck⟩

/-- A step's output module has the signatures of its input. -/
theorem stepOut_sig {k : StepKind} {syms : List String} {O : Option (List Summary)} {M : Module}
    {fs : List FuncStep} (h : checkStep k syms O M fs = true) : (stepOut M fs).sig = M.sig := by
  funext name
  unfold Module.sig
  rw [stepOut, Module.update_func?]
  cases hg : M.func? name with
  | none => rfl
  | some g =>
    simp only [Option.map_some]
    rcases stepOut_func h hg with hr | ⟨s, _, hr, _, hsig, _⟩
    · rw [hr]; rfl
    · rw [hr]
      simp only [sameSig, Bool.and_eq_true, decide_eq_true_eq] at hsig
      simp only [Option.getD_some, hsig.1, hsig.2]

/-- A step's output module is well formed when its input is. -/
theorem stepOut_wf {k : StepKind} {syms : List String} {O : Option (List Summary)} {M : Module}
    {fs : List FuncStep} (hM : M.wf syms = true) (h : checkStep k syms O M fs = true) :
    (stepOut M fs).wf syms = true := by
  unfold Module.wf
  rw [stepOut_sig h]
  refine List.all_eq_true.mpr fun g' hg' => ?_
  simp only [stepOut, Module.update, List.mem_map] at hg'
  obtain ⟨g, hg, rfl⟩ := hg'
  cases hr : (fs.map (·.out.func)).find? (·.name == g.name) with
  | none => exact List.all_eq_true.mp hM g hg
  | some r =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hr)
    exact (checkStep_spec h s hs).2.2.1

/-- A step kind whose check of each function gives `FuncRef` is sound. -/
theorem StepSound.of_func {k : StepKind}
    (h : ∀ (sig : Sigs) (syms : List String) (o : Oracle) (c : Ctx), Oracle.Mono o → o.IntRet →
      ∀ f f', f.wf sig syms = true → checkFunc k f f' = true → FuncRef o c (some f') (some f)) :
    StepSound k := by
  intro syms O M fs hM hc o c _ ho hoi name
  rw [stepOut, Module.update_func?]
  cases hg : M.func? name with
  | none => exact FuncRef.none o c
  | some g =>
    have hgw := Module.wf_func hM hg
    dsimp only [Option.map]
    rcases stepOut_func hc hg with hr | ⟨s, _, hr, _, _, _, hck⟩
    · rw [hr]; exact FuncRef.refl ho hoi c (Func.wf_machine hgw)
    · rw [hr]; exact h _ _ o c ho hoi _ s.out.func hgw hck

theorem edgeSplit_stepSound : StepSound .edgeSplit :=
  StepSound.of_func fun _ _ o c ho hoi _ _ hw h => edgeSplit_sound ho hoi c hw h

/-! ## Replaying a record -/

/-- One pass from module `M`: each step checked, its output substituted. -/
def validatePass (p : Pass) (syms : List String) (M : Module) : Option Module :=
  p.steps.foldlM (fun M st =>
    if checkStep st.kind syms p.funcBehavior M st.funcs then some (stepOut M st.funcs) else none) M

/-- The lowered module of a record, with the struct types `structs`, which no machine
    instruction reads. -/
def MachineSteps.module (r : MachineSteps) (structs : List (String × List Ty)) : Module :=
  ⟨structs, r.lowered.map (·.func)⟩

/-- `F` has the functions of `M`, by name (the machine IR prints them in another order than
    the record lists them). -/
def sameFuncs (M F : Module) : Bool :=
  F.funcs.all (fun f => decide (M.func? f.name = some f)) &&
    M.funcs.all (fun g => decide (F.func? g.name = some g))

theorem sameFuncs_func? {M F : Module} (h : sameFuncs M F = true) (n : String) :
    F.func? n = M.func? n := by
  simp only [sameFuncs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  cases hF : F.func? n with
  | some f =>
    have hn : f.name = n := by simpa using List.find?_some hF
    rw [← hn, h.1 f (List.mem_of_find?_eq_some hF)]
  | none =>
    cases hM : M.func? n with
    | none => rfl
    | some g =>
      have hn : g.name = n := by simpa using List.find?_some hM
      have := h.2 g (List.mem_of_find?_eq_some hM)
      rw [hn, hF] at this; cases this

theorem sameFuncs_wf {syms : List String} {M F : Module} (h : sameFuncs M F = true)
    (hM : M.wf syms = true) : F.wf syms = true := by
  have hsig : F.sig = M.sig := funext fun n => by simp only [Module.sig, sameFuncs_func? h n]
  simp only [sameFuncs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  unfold Module.wf
  rw [hsig]
  exact List.all_eq_true.mpr fun f hf =>
    List.all_eq_true.mp hM f (List.mem_of_find?_eq_some (h.1 f hf))

/-- Validate a record against the final machine IR, with only the step kinds `allowed`, for a
    section with the symbol names `syms`. -/
def validateWith (allowed : List StepKind) (syms : List String) (r : MachineSteps)
    (final : Module) : Bool :=
  r.kinds.all allowed.contains && (r.module final.structs).wf syms && r.lowered.all FuncSnap.idsOk &&
    match r.passes.foldlM (fun M p => validatePass p syms M) (r.module final.structs) with
    | some M => sameFuncs M final
    | none => false

def validate (syms : List String) (r : MachineSteps) (final : Module) : Bool :=
  validateWith StepKind.all syms r final

theorem validatePass_sound {syms : List String} {p : Pass}
    (hk : ∀ st ∈ p.steps, StepSound st.kind) :
    ∀ {M M' : Module}, M.wf syms = true → validatePass p syms M = some M' →
      M'.wf syms = true ∧ ModRefines syms M' M := by
  intro M M' hM h
  have hMm := Module.wf_machine hM
  -- Within the pass, every step runs calls by `M`'s semantics.
  suffices H : ∀ (steps : List Step), (∀ st ∈ steps, StepSound st.kind) → ∀ N N',
      N.wf syms = true →
      (∀ c : Ctx, c.Has syms → ∀ name, FuncRef (runFunc M c) c (N.func? name) (M.func? name)) →
      steps.foldlM (fun M st => if checkStep st.kind syms p.funcBehavior M st.funcs then
        some (stepOut M st.funcs) else none) N = some N' →
      N'.wf syms = true ∧
        ∀ c : Ctx, c.Has syms → ∀ name, FuncRef (runFunc M c) c (N'.func? name) (M.func? name) by
    obtain ⟨hm', href⟩ := H p.steps hk M M' hM (fun c _ name => by
      cases h : M.func? name with
      | none => exact FuncRef.none _ c
      | some g =>
        exact FuncRef.refl (runFunc_mono hMm c) (runFunc_intRet hMm c) c
          (Module.machine_func hMm h)) h
    exact ⟨hm', modRefines_of_funcs hMm (Module.wf_machine hm') href⟩
  intro steps
  induction steps with
  | nil =>
    intro _ N N' hN href h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨hN, href⟩
  | cons st rest ih =>
    intro hks N N' hN href h
    simp only [List.foldlM_cons] at h
    split at h
    · next hc =>
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      refine ih (fun s hs => hks s (List.mem_cons_of_mem _ hs)) _ N' (stepOut_wf hN hc)
        (fun c hcs name => ?_) h
      exact (hks st (List.mem_cons_self ..) syms p.funcBehavior N st.funcs hN hc (runFunc M c) c
        hcs (runFunc_mono hMm c) (runFunc_intRet hMm c) name).trans (href c hcs name)
    · simp at h

/-- A record that validates: the final machine IR refines the lowered module on the section's
    symbols, function by function, given the soundness of each step kind it uses; both are
    well formed. -/
theorem validate_sound {allowed : List StepKind} {syms : List String} {r : MachineSteps}
    {final : Module} (hk : ∀ k ∈ allowed, StepSound k) (h : validateWith allowed syms r final = true) :
    (r.module final.structs).wf syms = true ∧ final.wf syms = true ∧
      ModRefines syms final (r.module final.structs) := by
  simp only [validateWith, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hkinds, hlm⟩, _⟩, hfold⟩ := h
  have hks : ∀ p ∈ r.passes, ∀ st ∈ p.steps, StepSound st.kind := fun p hp st hst =>
    hk _ (hkinds _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨st, hst, rfl⟩⟩))
  suffices H : ∀ (ps : List Pass), (∀ p ∈ ps, ∀ st ∈ p.steps, StepSound st.kind) → ∀ N N',
      N.wf syms = true → ps.foldlM (fun M p => validatePass p syms M) N = some N' →
      N'.wf syms = true ∧ ModRefines syms N' N by
    split at hfold
    · next M hM =>
      obtain ⟨hm, href⟩ := H r.passes hks _ M hlm hM
      have hfm := sameFuncs_wf hfold hm
      have hmm := Module.wf_machine hm
      refine ⟨hlm, hfm, (modRefines_of_funcs hmm (Module.wf_machine hfm) fun c _ name => ?_).trans
        href⟩
      rw [sameFuncs_func? hfold]
      cases hg : M.func? name with
      | none => exact FuncRef.none _ c
      | some g =>
        exact FuncRef.refl (runFunc_mono hmm c) (runFunc_intRet hmm c) c
          (Module.machine_func hmm hg)
    · cases hfold
  intro ps
  induction ps with
  | nil =>
    intro _ N N' hN h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨hN, ModRefines.refl (Module.wf_machine hN)⟩
  | cons p rest ih =>
    intro hks N N' hN h
    simp only [List.foldlM_cons] at h
    rcases hp : validatePass p syms N with _ | N₁
    · rw [hp] at h; cases h
    rw [hp] at h
    obtain ⟨hm₁, hr₁⟩ := validatePass_sound (hks p (List.mem_cons_self ..)) hN hp
    obtain ⟨hm', hr'⟩ := ih (fun q hq => hks q (List.mem_cons_of_mem _ hq)) N₁ N' hm₁ h
    exact ⟨hm', hr'.trans hr₁⟩

end Fe.Sonatina.Steps
