import Fe.Sonatina.Steps.Validate
import Fe.Sonatina.CheckCert

/-!
# The machine stage end to end

`Sidecar.lowered s rr ri` is the sidecar with each section's machine IR replaced by the module
right after lowering that its record `rr` (runtime) or `ri` (init) starts from.  When both
records validate against the sidecar's machine IR, the machine IR implements the lowered
module in the sense of partial correctness (`machine_implementsP`), and with `check_sound` the
bytes refine the lowered module (`machine_sound`).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Fe.Sonatina.Check

/-- The sidecar with section `name`'s machine IR replaced by `m`. -/
def _root_.Fe.Sonatina.Sidecar.withMachine (s : Sidecar) (name : String) (m : Module) : Sidecar :=
  { s with sections := s.sections.map fun c =>
      if c.name == name then { c with lowering := c.lowering.map fun l => { l with machine := m } }
      else c }

/-- The machine IR of section `name`, empty if it has none. -/
def _root_.Fe.Sonatina.Sidecar.machineOf (s : Sidecar) (name : String) : Module :=
  (((s.section? name).bind (·.lowering)).map (·.machine)).getD default

/-- The sidecar whose machine IR is, per section, the module right after lowering. -/
def _root_.Fe.Sonatina.Sidecar.lowered (s : Sidecar) (rr ri : MachineSteps) : Sidecar :=
  (s.withMachine "runtime" (rr.module (s.machineOf "runtime").structs)).withMachine "init"
    (ri.module (s.machineOf "init").structs)

theorem withMachine_section? (s : Sidecar) (name : String) (m : Module) (n : String) :
    (s.withMachine name m).section? n = (s.section? n).map fun c =>
      if c.name == name then { c with lowering := c.lowering.map fun l => { l with machine := m } }
      else c := by
  unfold Sidecar.withMachine Sidecar.section?
  rw [List.find?_map]
  congr 2
  funext c
  simp only [Function.comp]
  split <;> rfl

/-- A diverging run, or one related to another, ends as it in the sense of partial
    correctness. -/
theorem endsAsP_of_resRel {r' r : Option (Except (Exit World) (ByteArray × World))}
    (h : ResRel Eq r' r) : EndsAsP r r' := by
  rcases r' with _ | (e' | ⟨v', w'⟩)
  · exact Or.inl rfl
  · rcases r with _ | (e | ⟨v, w⟩) <;> simp only [ResRel] at h
    right
    cases e' <;> cases e <;> simp only [ExitRel, reduceCtorEq] at h
    case stop.stop d' w₁' d w₁ =>
      obtain ⟨rfl, hw⟩ := h
      exact .stop_stop hw.1.symm hw.2.symm hw.6.symm
    all_goals first | (subst h; exact .exit _) | (cases h; exact .exit _)
  · rcases r with _ | (e | ⟨v, w⟩) <;> simp only [ResRel] at h
    obtain ⟨rfl, hw⟩ := h
    exact Or.inr (.ok_ok hw.1.symm hw.2.symm hw.6.symm)

/-- The run of a section approximates the run of the same section with its machine IR
    replaced by a module it refines. -/
theorem runSection_approx {s : Sidecar} {name : String} {m' : Module}
    (h : ∀ low, (s.section? name).bind (·.lowering) = some low →
      low.machine.machine = true ∧ ModRefines low.machine m') :
    Approx Eq (s.runSection name .machine) ((s.withMachine name m').runSection name .machine) := by
  unfold Sidecar.runSection Sidecar.runSectionWith
  rw [withMachine_section?]
  simp only [Sidecar.withMachine]
  cases s.objects.find? (·.name == s.object) with
  | none => exact Approx.stuck _
  | some obj =>
  dsimp only
  cases obj.sections.find? (·.name == name) with
  | none => exact Approx.stuck _
  | some sec =>
  dsimp only
  cases hc : s.section? name with
  | none => exact Approx.stuck _
  | some code =>
  have hname : code.name = name := by simpa [Sidecar.section?] using List.find?_some hc
  simp only [Option.map_some, hname, beq_self_eq_true, ite_true, Sidecar.moduleAt]
  cases hl : code.lowering with
  | none => exact Approx.stuck _
  | some low =>
  obtain ⟨hm, href⟩ := h low (by simp [hc, hl])
  simp only [Option.map_some, Option.bind_some, show (Level.machine == Level.machine) = true from rfl,
    ite_true, runFuncG_none]
  have key : ∀ e, Approx Eq
      (runFunc low.machine ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩ e [])
      (runFunc m' ⟨(code.symbols.lookup ·), m'.fixedEnd, m'.structs⟩ e []) := fun e =>
    (runFunc_ctx (c' := ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩)
      (c := ⟨(code.symbols.lookup ·), m'.fixedEnd, m'.structs⟩) hm rfl e []).trans_eq
      (href _ e [])
  repeat' first
    | exact Approx.bind (R := Eq) (key _) fun _ _ _ => Approx.stuck _
    | refine Approx.bind (R := Eq) (approx_mstore _ _) fun _ _ _ => ?_
    | split

theorem withMachine_section?_ne (s : Sidecar) {name n : String} (m : Module) (hn : n ≠ name) :
    (s.withMachine name m).section? n = s.section? n := by
  rw [withMachine_section?]
  cases hc : s.section? n with
  | none => rfl
  | some code =>
    have : code.name = n := by simpa [Sidecar.section?] using List.find?_some hc
    simp [this, hn]

theorem runSection_withMachine_ne {s : Sidecar} {name n : String} (m : Module) (hn : n ≠ name)
    (level : Level) : (s.withMachine name m).runSection n level = s.runSection n level := by
  unfold Sidecar.runSection Sidecar.runSectionWith
  rw [withMachine_section?_ne s m hn]
  rfl

theorem withMachine_lowering (s : Sidecar) (name : String) (m : Module) :
    ((s.withMachine name m).section? name).bind (·.lowering) =
      ((s.section? name).bind (·.lowering)).map fun l => { l with machine := m } := by
  rw [withMachine_section?]
  cases hc : s.section? name with
  | none => rfl
  | some code =>
    have : code.name = name := by simpa [Sidecar.section?] using List.find?_some hc
    simp [this]

/-- The hypothesis of `runSection_approx` from a validated record. -/
theorem section_refines {allowed : List StepKind} {s : Sidecar} {name : String} {r : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k) (h : validateWith allowed r (s.machineOf name) = true) :
    ∀ low, (s.section? name).bind (·.lowering) = some low →
      low.machine.machine = true ∧ ModRefines low.machine (r.module (s.machineOf name).structs) := by
  intro low hlow
  have hm : s.machineOf name = low.machine := by simp [Sidecar.machineOf, hlow]
  obtain ⟨_, hfm, href⟩ := validate_sound hk h
  rw [hm] at hfm href ⊢
  exact ⟨hfm, href⟩

/-- When both sections' records validate, the machine IR implements the lowered modules in the
    sense of partial correctness, on every call and every deployment. -/
theorem machine_implementsP {allowed : List StepKind} {s : Sidecar} {rr ri : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k)
    (hr : validateWith allowed rr (s.machineOf "runtime") = true)
    (hi : validateWith allowed ri (s.machineOf "init") = true) :
    ImplementsP ((s.lowered rr ri).model .machine) (s.model .machine) CalldataFits ∧
      ImplementsDeployP ((s.lowered rr ri).model .machine) (s.model .machine) (s.code "init")
        .empty .empty (fun _ => True) := by
  have hrt : Approx Eq (s.runSection "runtime" .machine)
      ((s.lowered rr ri).runSection "runtime" .machine) := by
    unfold Sidecar.lowered
    rw [runSection_withMachine_ne _ (by decide)]
    exact runSection_approx (section_refines hk hr)
  have hin : Approx Eq (s.runSection "init" .machine)
      ((s.lowered rr ri).runSection "init" .machine) := by
    unfold Sidecar.lowered
    have e := runSection_withMachine_ne (s := s) (name := "runtime") (n := "init")
      (rr.module (s.machineOf "runtime").structs) (by decide) .machine
    rw [← e]
    refine runSection_approx fun low hlow => ?_
    rw [withMachine_section?_ne s _ (by decide)] at hlow
    have := section_refines hk hi low hlow
    simpa [Sidecar.machineOf, withMachine_section?_ne s _ (show "init" ≠ "runtime" by decide)]
      using this
  constructor
  · intro I σ A feed _ _
    exact ⟨feed, endsAsP_of_resRel (hrt I _ _ (WRel.refl _))⟩
  · intro I σ A feed args _ _ _ _
    refine ⟨feed, endsAsP_of_resRel ?_⟩
    exact Approx.bind (R := Eq) hin (fun _ _ e => e ▸ Approx.pure_eq _) I _ _ (WRel.refl _)

/-- The bytes of both sections refine the modules right after lowering: `check_sound` for the
    bytes against the machine IR, and the validated records for the machine IR against the
    lowered modules, composed by `RefinesOn.of_implementsP`. -/
theorem machine_sound {allowed : List StepKind} {s : Sidecar} {rr ri : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k)
    (hr : validateWith allowed rr (s.machineOf "runtime") = true)
    (hi : validateWith allowed ri (s.machineOf "init") = true) (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) := by
  obtain ⟨hrun, hdep⟩ := check_sound hc
  obtain ⟨himp, hdimp⟩ := machine_implementsP hk hr hi
  exact ⟨RefinesOn.of_implementsP hrun himp rfl, RefinesDeploy.of_implementsP hdep hdimp⟩

/-- `machine_sound` for records that use only `edge_split`: no hypothesis. -/
theorem machine_sound_edgeSplit {s : Sidecar} {rr ri : MachineSteps}
    (hr : validateWith [.edgeSplit] rr (s.machineOf "runtime") = true)
    (hi : validateWith [.edgeSplit] ri (s.machineOf "init") = true) (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound (fun k hk => by simp at hk; subst hk; exact edgeSplit_stepSound) hr hi hc

end Fe.Sonatina.Steps
