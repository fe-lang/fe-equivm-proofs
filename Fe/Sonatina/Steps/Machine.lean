import Fe.Sonatina.Steps.CfgCleanupSound
import Fe.Sonatina.Steps.BranchCanonSound
import Fe.Sonatina.Steps.CoalesceSound
import Fe.Sonatina.Steps.LowerSwitchesSound
import Fe.Sonatina.Steps.AdceSound
import Fe.Sonatina.Steps.SchemasStepSound
import Fe.Sonatina.CheckCert

/-!
# The machine stage end to end

`Sidecar.lowered s rr ri` is the sidecar with each section's machine IR replaced by the module
right after lowering that its record `rr` (runtime) or `ri` (init) starts from.  When both
records validate against the sidecar's machine IR, with the names of each section's symbols
(`Sidecar.symbolsOf`), the machine IR implements the lowered module in the sense of partial
correctness (`machine_implementsP`), and wherever the bytes refine the machine IR (`Sound s`) they
refine the lowered module (`machine_sound_of_sound`).  `Sound s` comes from `check_sound` for a
sidecar without memory spills (`machine_sound`, `machine_sound_proved`), or from
`checkSpills_sound` and `FrameSafe s` for one with spills (`machine_sound_spills_proved`).

The records `rr` and `ri` are arguments: the statements tie them to `s` only through `validate`,
whose composed module must be `s`'s machine IR, under `s`'s symbols (see `machine_sound_proved`).
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

/-- The names of section `name`'s symbols, none if it has no section of the name. -/
def _root_.Fe.Sonatina.Sidecar.symbolsOf (s : Sidecar) (name : String) : List String :=
  (((s.section? name).map (·.symbols)).getD []).map (·.1)

/-- A context that looks symbols up in a list has each of its names. -/
theorem lookup_has (heap : Nat) (structs : List (String × List Ty)) :
    ∀ l : List (String × Nat × Nat), Ctx.Has ⟨(l.lookup ·), heap, structs⟩ (l.map (·.1))
  | [] => fun _ h => nomatch h
  | (k, v) :: l => by
    intro s hs
    simp only [List.map_cons, List.mem_cons] at hs
    show (List.lookup s ((k, v) :: l)).isSome = true
    simp only [List.lookup]
    split
    · rfl
    · next he =>
      rcases hs with rfl | hs
      · simp at he
      · exact lookup_has heap structs l s hs

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
    (h : ∀ code low, s.section? name = some code → code.lowering = some low →
      low.machine.machine = true ∧ ModRefines (code.symbols.map (·.1)) low.machine m') :
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
  obtain ⟨hm, href⟩ := h code low hc hl
  simp only [Option.map_some, Option.bind_some, show (Level.machine == Level.machine) = true from rfl,
    ite_true, runFuncG_none]
  have key : ∀ e, Approx Eq
      (runFunc low.machine ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩ e [])
      (runFunc m' ⟨(code.symbols.lookup ·), m'.fixedEnd, m'.structs⟩ e []) := fun e =>
    (runFunc_ctx (c' := ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩)
      (c := ⟨(code.symbols.lookup ·), m'.fixedEnd, m'.structs⟩) hm rfl e [] rfl).trans_eq
      (href _ (lookup_has _ _ code.symbols) e [] rfl)
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
    (hk : ∀ k ∈ allowed, StepSound k)
    (h : validateWith allowed (s.symbolsOf name) r (s.machineOf name) = true) :
    ∀ code low, s.section? name = some code → code.lowering = some low →
      low.machine.machine = true ∧
        ModRefines (code.symbols.map (·.1)) low.machine (r.module (s.machineOf name).structs) := by
  intro code low hc hl
  have hm : s.machineOf name = low.machine := by simp [Sidecar.machineOf, hc, hl]
  have hsy : s.symbolsOf name = code.symbols.map (·.1) := by simp [Sidecar.symbolsOf, hc]
  obtain ⟨_, hfm, href⟩ := validate_sound hk h
  rw [hsy] at href
  rw [hm] at hfm href ⊢
  exact ⟨Module.wf_machine hfm, href⟩

/-- When both sections' records validate, the machine IR implements the lowered modules in the
    sense of partial correctness, on every call and every deployment. -/
theorem machine_implementsP {allowed : List StepKind} {s : Sidecar} {rr ri : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k)
    (hr : validateWith allowed (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validateWith allowed (s.symbolsOf "init") ri (s.machineOf "init") = true) :
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
    refine runSection_approx fun code low hc hl => ?_
    rw [withMachine_section?_ne s _ (by decide)] at hc
    have := section_refines hk hi code low hc hl
    simpa [Sidecar.machineOf, withMachine_section?_ne s _ (show "init" ≠ "runtime" by decide)]
      using this
  constructor
  · intro I σ A feed _ _
    exact ⟨feed, endsAsP_of_resRel (hrt I _ _ (WRel.refl _))⟩
  · intro I σ A feed args _ _ _ _
    refine ⟨feed, endsAsP_of_resRel ?_⟩
    exact Approx.bind (R := Eq) hin (fun _ _ e => e ▸ Approx.pure_eq _) I _ _ (WRel.refl _)

/-- Wherever the bytes refine the machine IR (`Sound s`), they refine the modules right after
    lowering: the validated records for the machine IR against the lowered modules, composed by
    `RefinesOn.of_implementsP`.  This is all `machine_sound` reads of `check s = true`. -/
theorem machine_sound_of_sound {allowed : List StepKind} {s : Sidecar} {rr ri : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k)
    (hr : validateWith allowed (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validateWith allowed (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hs : Sound s) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) := by
  obtain ⟨hrun, hdep⟩ := hs
  obtain ⟨himp, hdimp⟩ := machine_implementsP hk hr hi
  exact ⟨RefinesOn.of_implementsP hrun himp rfl, RefinesDeploy.of_implementsP hdep hdimp⟩

/-- The bytes of both sections refine the modules right after lowering: `check_sound` for the
    bytes against the machine IR, and `machine_sound_of_sound`. -/
theorem machine_sound {allowed : List StepKind} {s : Sidecar} {rr ri : MachineSteps}
    (hk : ∀ k ∈ allowed, StepSound k)
    (hr : validateWith allowed (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validateWith allowed (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound_of_sound hk hr hi (check_sound hc)

/-- `machine_sound` for records that use only `edge_split`: no hypothesis. -/
theorem machine_sound_edgeSplit {s : Sidecar} {rr ri : MachineSteps}
    (hr : validateWith [.edgeSplit] (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validateWith [.edgeSplit] (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound (fun k hk => by simp at hk; subst hk; exact edgeSplit_stepSound) hr hi hc

/-- Every kind `validate` accepts is sound. -/
theorem StepKind.proved_sound : ∀ k ∈ StepKind.proved, StepSound k := by
  intro k hk
  simp only [StepKind.proved, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact edgeSplit_stepSound
  · exact cfgCleanup_stepSound
  · exact branchCanon_stepSound
  · exact branchConditions_stepSound
  · exact coalesceCopies_stepSound
  · exact Schemas.sccpFold_stepSound
  · exact Schemas.knownBitsSimplify_stepSound
  · exact lowerSwitches_stepSound
  · exact adce_stepSound

/-- `machine_sound_of_sound` for records that `validate` accepts, which use only the proved
    kinds: wherever the bytes refine the machine IR, they refine the modules right after
    lowering. -/
theorem machine_sound_proved_of_sound {s : Sidecar} {rr ri : MachineSteps}
    (hr : validate (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validate (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hs : Sound s) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound_of_sound StepKind.proved_sound hr hi hs

/-- `machine_sound` for records that `validate` accepts, which use only the proved kinds
    (`StepKind.proved`: `edge_split`, `cfg_cleanup`, `branch_canonicalize`, `branch_conditions`,
    `coalesce_copies`, `sccp_fold`, `known_bits_simplify`, `lower_switches` and `adce`): no
    hypothesis.

    It applies to sidecars without memory spills only (`check s = true` holds `s.noSpills`); a
    sidecar with spills has `machine_sound_spills_proved`.

    What ties the records `rr` (runtime) and `ri` (init) to `s`: `validate` composes each record
    from its lowered functions through its steps and requires the result to be the section's
    machine IR (`s.machineOf`), under the section's symbols (`s.symbolsOf`); the conclusion is
    about `s.lowered rr ri`, `s` with each section's machine IR replaced by the module its record
    starts from.  Nothing else: the statement holds for every pair of records `validate`
    accepts, not only for the sidecar's own `machine_steps`.  `Sidecar` keeps no record (a
    section's `Lowering` has no field for one), so the statement cannot name them; that a use of
    the theorem passes the records of the same file is the elaborator's part: `machine_steps`
    (`Read.lean`) reads them from the JSON file `sonatina_sidecar` reads `s` from.  Nor does
    anything tie a record's lowered functions to the lowering of `s`'s source IR: they are what
    the record says lowering produced.  For a record with no passes, its lowered functions are
    the machine IR, `s.lowered rr ri` has `s`'s machine IR, and the theorem restates
    `check_sound`. -/
theorem machine_sound_proved {s : Sidecar} {rr ri : MachineSteps}
    (hr : validate (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validate (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound_proved_of_sound hr hi (check_sound hc)

/-- `machine_sound_proved` for a sidecar with memory spills: the spill-aware checker
    (`checkSpills`) in place of `check`, under `FrameSafe s` (the machine IR with its spills, under
    the sidecar's spill plan, ends as the machine IR does on every call and deployment), which
    `checkSpills_sound` needs and nothing here proves for a sidecar with spills.  The records are
    tied to `s` as in `machine_sound_proved`. -/
theorem machine_sound_spills_proved {s : Sidecar} {rr ri : MachineSteps}
    (hr : validate (s.symbolsOf "runtime") rr (s.machineOf "runtime") = true)
    (hi : validate (s.symbolsOf "init") ri (s.machineOf "init") = true)
    (hc : checkSpills s = true) (hf : FrameSafe s) :
    RefinesOn .P1 (s.code "runtime") ((s.lowered rr ri).model .machine) CalldataFits ∧
      RefinesDeploy .P1 (s.code "init") .empty ((s.lowered rr ri).model .machine)
        (fun _ => True) :=
  machine_sound_proved_of_sound hr hi (checkSpills_sound hc hf)

end Fe.Sonatina.Steps
