import Fe.Sonatina.Steps.EdgeSplit
import Fe.Sonatina.Steps.Record

/-!
# Validating a record of machine steps

`validate r final` replays the record: from the lowered module, each pass's steps in order,
each step checked (`checkStep`) and its functions substituted (`Module.update`), and the
composed module compared with `final`, the sidecar's machine IR.  `validateWith allowed` also
rejects records with a step kind outside `allowed`.

`StepSound k`: a step of kind `k` that the check accepts gives, for every function, an output
that approximates the input under any oracle that approximates itself.  `edgeSplit_stepSound`
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

/-- A step: every function it lists exists in the input, is renamed to nothing, has no facts
    (no kind of this phase reads any), is machine IR, and passes its kind's check. -/
def checkStep (k : StepKind) (_O : Option (List Summary)) (M : Module) (fs : List FuncStep) :
    Bool :=
  fs.all fun s => s.facts.isEmpty && s.out.func.name == s.func && s.out.func.machine &&
    (M.func? s.func).any fun f => checkFunc k f s.out.func

/-- A step's output module. -/
def stepOut (M : Module) (fs : List FuncStep) : Module := M.update (fs.map (·.out.func))

/-- `k`'s check is sound: each function of an accepted step's output, its calls run by an
    oracle that approximates itself, approximates the same function of the input. -/
def StepSound (k : StepKind) : Prop :=
  ∀ (O : Option (List Summary)) (M : Module) (fs : List FuncStep), M.machine = true →
    checkStep k O M fs = true → ∀ (o : Oracle) (c : Ctx), Oracle.Mono o →
      ∀ name, FuncRef o c ((stepOut M fs).func? name) (M.func? name)

/-- A function approximates itself under an oracle that does. -/
theorem FuncRef.refl {o : Oracle} (ho : Oracle.Mono o) (c : Ctx) {f : Func}
    (hf : f.machine = true) : FuncRef o c (some f) (some f) := by
  have sim : Sim o c f f Eq := Sim.of_steps fun s' s hR => by
    subst hR
    left
    exact Approx.mono (Approx.stepBlock ho rfl hf _ _ _) fun n' n e => by
      subst e; cases n' <;> simp [NextRel]
  intro args
  unfold runFuncO
  dsimp only
  cases f.blocks.head? with
  | none => exact Approx.stuck _
  | some e =>
    exact Approx.bind_eq (Approx.bindVals _ _ _) fun env => Sim.approx sim (env, none, e.id) _ rfl

theorem FuncRef.none (o : Oracle) (c : Ctx) : FuncRef o c none none := fun _ => Approx.stuck _

theorem stepOut_machine {M : Module} {fs : List FuncStep} (hM : M.machine = true)
    (hfs : ∀ s ∈ fs, s.out.func.machine = true) : (stepOut M fs).machine = true := by
  unfold stepOut Module.update Module.machine
  simp only [List.all_map, List.all_eq_true, Function.comp]
  intro g hg
  cases h : (fs.map (·.out.func)).find? (·.name == g.name) with
  | none => exact List.all_eq_true.mp hM g hg
  | some r =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h)
    exact hfs s hs

theorem checkStep_machine {k : StepKind} {O : Option (List Summary)} {M : Module}
    {fs : List FuncStep} (h : checkStep k O M fs = true) : ∀ s ∈ fs, s.out.func.machine = true := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  simp only [Bool.and_eq_true] at this
  exact this.1.2

/-- A step kind whose check of each function gives `FuncRef` is sound. -/
theorem StepSound.of_func {k : StepKind}
    (h : ∀ (o : Oracle) (c : Ctx), Oracle.Mono o → ∀ f f', f.machine = true →
      checkFunc k f f' = true → FuncRef o c (some f') (some f)) : StepSound k := by
  intro O M fs hM hc o c ho name
  rw [stepOut, Module.update_func?]
  cases hg : M.func? name with
  | none => exact FuncRef.none o c
  | some g =>
    have hgm := Module.machine_func hM hg
    have hgname : g.name = name := by simpa using List.find?_some hg
    dsimp only [Option.map]
    cases hr : (fs.map (·.out.func)).find? (·.name == g.name) with
    | none => exact FuncRef.refl ho c hgm
    | some r =>
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hr)
      have hsn : s.out.func.name = g.name := by simpa using List.find?_some hr
      have := List.all_eq_true.mp hc s hs
      simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at this
      obtain ⟨⟨⟨_, hname⟩, _⟩, f, hf, hck⟩ := this
      rw [← hname, hsn, hgname, hg] at hf
      cases hf
      exact h o c ho _ s.out.func hgm hck

theorem edgeSplit_stepSound : StepSound .edgeSplit :=
  StepSound.of_func fun o c ho f f' hm h => edgeSplit_sound ho c hm h

/-! ## Replaying a record -/

/-- One pass from module `M`: each step checked, its output substituted. -/
def validatePass (p : Pass) (M : Module) : Option Module :=
  p.steps.foldlM (fun M st =>
    if checkStep st.kind p.funcBehavior M st.funcs then some (stepOut M st.funcs) else none) M

/-- The lowered module of a record, with the struct types `structs`, which no machine
    instruction reads. -/
def MachineSteps.module (r : MachineSteps) (structs : List (String × List Ty)) : Module :=
  ⟨structs, r.lowered.map (·.func)⟩

/-- Validate a record against the final machine IR, with only the step kinds `allowed`. -/
def validateWith (allowed : List StepKind) (r : MachineSteps) (final : Module) : Bool :=
  r.kinds.all allowed.contains && (r.module final.structs).machine &&
    match r.passes.foldlM (fun M p => validatePass p M) (r.module final.structs) with
    | some M => decide (M = final)
    | none => false

def validate (r : MachineSteps) (final : Module) : Bool := validateWith StepKind.all r final

theorem validatePass_sound {p : Pass} (hk : ∀ st ∈ p.steps, StepSound st.kind) :
    ∀ {M M' : Module}, M.machine = true → validatePass p M = some M' →
      M'.machine = true ∧ ModRefines M' M := by
  intro M M' hM h
  -- Within the pass, every step runs calls by `M`'s semantics.
  suffices H : ∀ (steps : List Step), (∀ st ∈ steps, StepSound st.kind) → ∀ N N',
      N.machine = true → (∀ c name, FuncRef (runFunc M c) c (N.func? name) (M.func? name)) →
      steps.foldlM (fun M st => if checkStep st.kind p.funcBehavior M st.funcs then
        some (stepOut M st.funcs) else none) N = some N' →
      N'.machine = true ∧ ∀ c name, FuncRef (runFunc M c) c (N'.func? name) (M.func? name) by
    obtain ⟨hm', href⟩ := H p.steps hk M M' hM (fun c name => by
      cases h : M.func? name with
      | none => exact FuncRef.none _ c
      | some g => exact FuncRef.refl (runFunc_mono hM c) c (Module.machine_func hM h)) h
    exact ⟨hm', modRefines_of_funcs hM hm' href⟩
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
      refine ih (fun s hs => hks s (List.mem_cons_of_mem _ hs)) _ N'
        (stepOut_machine hN (checkStep_machine hc)) (fun c name => ?_) h
      exact (hks st (List.mem_cons_self ..) p.funcBehavior N st.funcs hN hc (runFunc M c) c
        (runFunc_mono hM c) name).trans (href c name)
    · simp at h

/-- A record that validates: the final machine IR refines the lowered module, function by
    function, given the soundness of each step kind it uses. -/
theorem validate_sound {allowed : List StepKind} {r : MachineSteps} {final : Module}
    (hk : ∀ k ∈ allowed, StepSound k) (h : validateWith allowed r final = true) :
    (r.module final.structs).machine = true ∧ final.machine = true ∧
      ModRefines final (r.module final.structs) := by
  simp only [validateWith, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨hkinds, hlm⟩, hfold⟩ := h
  have hks : ∀ p ∈ r.passes, ∀ st ∈ p.steps, StepSound st.kind := fun p hp st hst =>
    hk _ (hkinds _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨st, hst, rfl⟩⟩))
  suffices H : ∀ (ps : List Pass), (∀ p ∈ ps, ∀ st ∈ p.steps, StepSound st.kind) → ∀ N N',
      N.machine = true → ps.foldlM (fun M p => validatePass p M) N = some N' →
      N'.machine = true ∧ ModRefines N' N by
    split at hfold
    · next M hM =>
      simp only [decide_eq_true_eq] at hfold
      obtain ⟨hm, href⟩ := H r.passes hks _ M hlm hM
      subst hfold
      exact ⟨hlm, hm, href⟩
    · cases hfold
  intro ps
  induction ps with
  | nil =>
    intro _ N N' hN h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨hN, ModRefines.refl hN⟩
  | cons p rest ih =>
    intro hks N N' hN h
    simp only [List.foldlM_cons] at h
    rcases hp : validatePass p N with _ | N₁
    · rw [hp] at h; cases h
    rw [hp] at h
    obtain ⟨hm₁, hr₁⟩ := validatePass_sound (hks p (List.mem_cons_self ..)) hN hp
    obtain ⟨hm', hr'⟩ := ih (fun q hq => hks q (List.mem_cons_of_mem _ hq)) N₁ N' hm₁ h
    exact ⟨hm', hr'.trans hr₁⟩

end Fe.Sonatina.Steps
