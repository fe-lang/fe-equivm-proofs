import Fe.Sonatina.CheckCalls
import Fe.Sonatina.Spill
import Reasoning.Stepping
import Fe.EVM.RefineInvariant

/-!
# The checker is sound

`check_sound : check s = true → Sound s`: a sidecar the checker accepts has a runtime whose
bytes refine the machine IR's runtime on every call whose calldata fits, and a constructor whose
bytes refine the machine IR's constructor on every deployment, at profile `P1`.  `check_xiOk`:
neither makes a message call nor a creation, so `XiOk` holds of their frames for every condition
on calls.  `check_xiOk_callsAt`: a frame that succeeds makes only the calls the machine IR's
successful runs record, so a condition `ContractModel.callsAt` states of the model holds of them.

`section_sound` gives it of each section: `runSection_eq` rewrites the machine IR's run of the
section to the prologue and its entry function's blocks from the entry block, `section_run`
gives their agreement with the bytes' iterator from the state `Ξ` starts in (at the entry block,
offset 0, an empty stack), and `Xi_agrees` takes it to `Ξ`.  A constructor runs its code with its
arguments after it, which `section_run` allows of any section.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The IR's run, ended where the machine IR's entry returns (the section never does). -/
def endRun (r : Option (Except (Fe.Exit World) (List Val × World))) :
    Option (Except (Fe.Exit World) (ByteArray × World)) :=
  match r with
  | some (.error e) => some (.error e)
  | _ => none

/-- A frame whose iterator agrees with the IR's run refines it, as `Ξ` runs it. -/
theorem Xi_agrees {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {r : Option (Except (Fe.Exit World) (List Val × World))}
    (h : XAgrees (X (g.toNat + 1) (D_J I.code 0)
      (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I)) r) :
    Exhausted (Ξ σ σ₀ g A I) ∨ Agrees .P1 (Ξ σ σ₀ g A I) (endRun r) := by
  rcases h with h | h | h
  · exact .inl (.inl (Reasoning.Theory.Xi_error_of_X h))
  · exact .inl (.inr (Reasoning.Theory.Xi_error_of_X h))
  · right
    match r, h with
    | some (.error (.stop out w)), ⟨s', hx, ha, hl⟩ =>
      exact ⟨_, _, by rw [Reasoning.Theory.Xi_success_of_X hx, ha], fun _ => hl⟩
    | some (.error (.revert data)), ⟨g', hx⟩ =>
      exact ⟨_, _, Reasoning.Theory.Xi_revert_of_X hx, fun _ => rfl⟩
    | some (.error .static), hx => exact Reasoning.Theory.Xi_error_of_X hx
    | some (.error .trap), hx => exact Reasoning.Theory.Xi_error_of_X hx
    | some (.error .oob), hx => exact Reasoning.Theory.Xi_error_of_X hx

/-- A frame that succeeds has an iterator that succeeds. -/
theorem X_of_Xi_success {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {r : AccountMap × UInt256 × Substate} {o : ByteArray}
    (h : Ξ σ σ₀ g A I = .ok (.success r o)) :
    ∃ s' o', X (g.toNat + 1) (D_J I.code 0)
      (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I) = .ok (.success s' o') := by
  cases hX : X (g.toNat + 1) (D_J I.code 0) (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I)
    with
  | error e =>
    simp only [Reasoning.Theory.initState] at hX
    simp only [Ξ, hX] at h
    cases h
  | ok res =>
    cases res with
    | success s' o' => exact ⟨s', o', rfl⟩
    | revert g' o' =>
      simp only [Reasoning.Theory.initState] at hX
      simp only [Ξ, hX] at h
      cases h

/-- A statement of an instrumented block is one of the block's, or a spill store. -/
theorem mem_instrument_body {words : List (Nat × Nat)} {f : Func} {b' : Block}
    (hb' : b' ∈ (f.instrument words).blocks) :
    ∃ b ∈ f.blocks, ∀ s ∈ b'.body, s ∈ b.body ∨ ∃ w o, s = spillStore w o := by
  unfold Func.instrument at hb'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
  refine ⟨b, hb, fun s hs => ?_⟩
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons] at hs
  rcases hs with (hp | ⟨t, ht, rfl | hs⟩) | he
  · split at hp
    · obtain ⟨x, _, hx⟩ := List.mem_filterMap.mp hp
      obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact .inr ⟨w, _, rfl⟩
    · cases hp
  · exact .inl ht
  · obtain ⟨x, _, hx⟩ := List.mem_filterMap.mp hs
    obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact .inr ⟨w, _, rfl⟩
  · split at he
    · split at he
      · obtain ⟨phi, _, hphi⟩ := List.mem_filterMap.mp he
        split at hphi
        · split_ifs at hphi; cases hphi; exact .inr ⟨_, _, rfl⟩
        · cases hphi; exact .inr ⟨_, _, rfl⟩
        · cases hphi
      · cases he
    · cases he

/-- Spill stores make no message call. -/
theorem Module.hasCalls_of_instrument {plan : SpillPlan} {m : Module}
    (h : (m.instrument plan).hasCalls = true) : m.hasCalls = true := by
  unfold Module.instrument at h
  split at h
  · exact h
  simp only [Module.hasCalls, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
  obtain ⟨f, hf, b', hb', s, hs, hm⟩ := h
  refine ⟨f, hf, ?_⟩
  split at hb'
  · obtain ⟨b, hb, hsub⟩ := mem_instrument_body hb'
    rcases hsub s hs with hs' | ⟨w, o, rfl⟩
    · exact ⟨b, hb, s, hs', hm⟩
    · simp [spillStore, Inst.messages] at hm
  · exact ⟨b', hb', s, hs, hm⟩

/-- The instrumented machine IR's run of a section is the prologue and its entry function's
    blocks from the entry block, under the plan's guard, ended where it would return. -/
theorem runSectionWith_eq {s : Sidecar} {name : String} {obj : Object} {sec : Section}
    {code : CodeSection} {low : Lowering} {p : SpillPlan} {f : Func} {eb : Block}
    {I : ExecutionEnv} {w : World} (hobj : s.objects.find? (·.name == s.object) = some obj)
    (hsec : obj.sections.find? (·.name == name) = some sec)
    (hcode : s.section? name = some code) (hlow : code.lowering = some low)
    (hf : (low.machine.instrument p).func? sec.entry = some f) (he : f.blocks.head? = some eb)
    (hp : f.params = []) :
    (s.runSectionWith name .machine p.prepare).exec I w = endRun ((pre low eb eb >>= fun _ =>
      runBlocksG (p.guard (low.machine.instrument p)) (low.machine.instrument p)
        ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩ [] f {} none
        eb.id).exec I w) := by
  unfold Sidecar.runSectionWith
  simp only [hobj, hsec, hcode, Sidecar.moduleAt, hlow, Option.map_some, Option.bind_some,
    SpillPlan.prepare]
  have hrun : ∀ ic, runFuncG (p.guard (low.machine.instrument p)) (low.machine.instrument p) ic []
      sec.entry [] = runBlocksG (p.guard (low.machine.instrument p)) (low.machine.instrument p)
        ic [] f {} none eb.id :=
    fun ic => by
      rw [runFuncG.eq_1]
      simp [guarded, hf, he, hp, Fe.Sonatina.bind]
  simp only [show (Level.machine == Level.machine) = true from rfl, if_true, hrun, pre]
  cases low.entryFreePtr <;> simp only [Fe.M.exec_bind, pure_bind, endRun, Fe.EVM.mstore,
    Fe.M.exec_modify]
  all_goals
    generalize M.exec (runBlocksG _ _ _ _ _ _ _ _) I _ = y
    rcases y with _ | _ | _ <;> rfl

/-- The machine IR's run of a section is the prologue and its entry function's blocks from the
    entry block, ended where it would return. -/
theorem runSection_eq {s : Sidecar} {name : String} {obj : Object} {sec : Section}
    {code : CodeSection} {low : Lowering} {f : Func} {eb : Block} {I : ExecutionEnv}
    {w : World} (hobj : s.objects.find? (·.name == s.object) = some obj)
    (hsec : obj.sections.find? (·.name == name) = some sec)
    (hcode : s.section? name = some code) (hlow : code.lowering = some low)
    (hf : low.machine.func? sec.entry = some f) (he : f.blocks.head? = some eb)
    (hp : f.params = []) :
    (s.runSection name .machine).exec I w = endRun ((pre low eb eb >>= fun _ =>
      runBlocks low.machine ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩
        f {} none eb.id).exec I w) := by
  unfold Sidecar.runSection Sidecar.runSectionWith
  simp only [hobj, hsec, hcode, Sidecar.moduleAt, hlow, Option.map_some, Option.bind_some,
    runFuncG_none]
  have hrun : ∀ ic,
      runFunc low.machine ic sec.entry [] = runBlocks low.machine ic f {} none eb.id :=
    fun ic => by
      rw [runFunc_eq]
      simp [hf, he, hp, Fe.Sonatina.bind]
  simp only [show (Level.machine == Level.machine) = true from rfl, if_true, hrun, pre]
  cases low.entryFreePtr <;> simp only [Fe.M.exec_bind, pure_bind, endRun, Fe.EVM.mstore,
    Fe.M.exec_modify]
  all_goals
    generalize M.exec (runBlocks _ _ _ _ _ _) I _ = y
    rcases y with _ | _ | _ <;> rfl

/-- A run that ends where the section's entry returns does not panic where the run does not. -/
theorem NoPanicAt.of_endRun {r : Option (Except (Fe.Exit World) (List Val × World))}
    (h : NoPanicAt (endRun r)) : NoPanicAt r := fun c hc => h c (by rw [hc]; rfl)

/-- What a sidecar the checker accepts is: each section of its object checked, `init` and
    `runtime` among them. -/
theorem checkWith_ok {s : Sidecar} {plan : String → SpillPlan} (h : checkWith plan s = true) :
    (∀ ne ∈ entries s, checkEntry s plan ne.1 ne.2 = .ok ()) ∧
      ((entries s).lookup "init").isSome ∧ ((entries s).lookup "runtime").isSome := by
  unfold checkWith at h
  cases hc : checkAll plan s with
  | error e => rw [hc] at h; cases h
  | ok u =>
  unfold checkAll at hc
  cases hf : (entries s).forM (fun ne => checkEntry s plan ne.1 ne.2) with
  | error e => simp [hf] at hc; cases hc
  | ok u' =>
  simp only [hf] at hc
  refine ⟨fun ne hne => forM_ok hf ne hne, ?_⟩
  split_ifs at hc with h1
  · simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1.2, h1.2⟩
  · cases hc

theorem lookup_entries {secs : List Section} {name entry : String}
    (h : (secs.map fun sec => (sec.name, sec.entry)).lookup name = some entry) :
    ∃ sec, secs.find? (·.name == name) = some sec ∧ sec.entry = entry ∧
      (name, entry) ∈ secs.map fun sec => (sec.name, sec.entry) := by
  induction secs with
  | nil => cases h
  | cons sec secs ih =>
    by_cases hn : name = sec.name
    · subst hn
      simp only [List.map_cons, List.lookup, BEq.rfl, Option.some.injEq] at h
      subst h
      exact ⟨sec, by simp, rfl, by simp⟩
    · have hb : (name == sec.name) = false := by simpa using hn
      simp only [List.map_cons, List.lookup, hb] at h
      obtain ⟨sec', h1, h2, h3⟩ := ih h
      have hb' : (sec.name == name) = false := by simpa using Ne.symm hn
      exact ⟨sec', by simp [hb', h1], h2, List.mem_cons_of_mem _ h3⟩

/-- A section of a checked sidecar, run as `Ξ` runs a frame on its code followed by any bytes,
    refines the machine IR's run of it at profile `P1`; if its machine IR makes no message call,
    the frame makes no message call nor creation: `XiOk` holds of it for every condition on
    them; and a frame that succeeds makes only the calls the machine IR's run records. -/
theorem section_sound {s : Sidecar} {plan : String → SpillPlan} (h : checkWith plan s = true)
    {name : String} (hn : ((entries s).lookup name).isSome) {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv} {tail : ByteArray} (hI : I.code = s.code name ++ tail)
    (hnp : ∀ feed, NoPanicAt
      ((s.runSectionWith name .machine (plan name).prepare).exec I (World.init σ A feed))) :
    (Exhausted (Ξ σ σ₀ g A I) ∨ ∃ feed, Agrees .P1 (Ξ σ σ₀ g A I)
      ((s.runSectionWith name .machine (plan name).prepare).exec I (World.init σ A feed))) ∧
      (s.hasCalls name = false → ∀ Q, Invariant.XiOk Q σ σ₀ g A I) ∧
      ∀ Q, (∀ feed out w, Succeeds ((s.runSectionWith name .machine (plan name).prepare).exec I
        (World.init σ A feed)) out w → ∀ c ∈ w.calls, c.Ok Q) →
        (∃ r o, Ξ σ σ₀ g A I = .ok (.success r o)) → Invariant.XiOk Q σ σ₀ g A I := by
  obtain ⟨hall, -, -⟩ := checkWith_ok h
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hn
  unfold entries at hentry hall
  cases hobj : s.objects.find? (·.name == s.object) with
  | none => simp [hobj] at hentry
  | some obj =>
  simp only [hobj, Option.map_some, Option.getD_some] at hentry hall
  obtain ⟨sec, hsec, hse, hmem⟩ := lookup_entries hentry
  have hce := hall _ hmem
  simp only at hce
  unfold checkEntry at hce
  cases hcode : s.section? name with
  | none => simp [hcode] at hce
  | some code =>
  simp only [hcode] at hce
  split at hce
  · next hcs =>
    obtain ⟨low, hlow, hsize, hany, hfuncs⟩ := checkSection_ok hcs
    set low' : Lowering := { low with machine := low.machine.instrument (plan name) }
    obtain ⟨hint, hmemh, hname⟩ := List.any_eq_true.mp hany
    simp only [beq_iff_eq] at hname
    obtain ⟨f, eb, hf, he, -, -, -, -, -, -, -, -, -, -, -, hroot, hent, hephi⟩ :=
      func_facts (hfuncs hint hmemh)
    obtain ⟨hpar, hret, hplace⟩ := hroot hname
    rw [hname] at hf
    have hcode' : s.code name = code.bytecode := by simp [Sidecar.code, hcode]
    rw [hcode'] at hI
    -- The feed is what the bytes' run supplies.
    obtain ⟨feed, M, hfeed⟩ := fut_exists (g.toNat + 1)
      (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I)
      (by simp [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toNat]; exact le_refl _)
    obtain ⟨hebm, hblk⟩ := head_block he
    obtain ⟨hb, hhb, hentry⟩ : ∃ hb, hint.blocks.find? (·.block == eb.id) = some hb ∧
        hb.entryStack = [] := by
      cases hfe : hint.blocks.find? (·.block == eb.id) with
      | none => rw [hfe] at hent; cases hent
      | some hb =>
        rw [hfe] at hent
        refine ⟨hb, rfl, ?_⟩
        have := Option.some.inj hent
        simpa [hpar, hret] using this
    have hslots : (frameOf low' entry f).slots hb = [] := by
      unfold Frame.slots; split <;> simp [hentry]
    have hfe : (low.machine.instrument (plan name)).func? sec.entry = some f := by
      rw [hse]; exact hf
    have hnpf : NoPanicAt ((preIf (hint.name == entry) low' eb eb >>= fun _ =>
        runBlocksG ((plan name).guard low'.machine) low'.machine
          ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩ [] f {} none
          eb.id).exec I (World.init σ A feed)) := by
      simp only [show (hint.name == entry) = true by simp [hname], preIf, if_true]
      have h2 := hnp feed
      rw [runSectionWith_eq hobj hsec hcode hlow hfe he hpar] at h2
      exact NoPanicAt.of_endRun h2
    have hfin := func_run (low := low') (K := low.machine.hasCalls) (M := M) (tail := tail)
      (ic := ⟨(code.symbols.lookup ·), low.machine.fixedEnd, low.machine.structs⟩) hI hsize rfl
      hfuncs Module.hasCalls_of_instrument (g.toNat + 1) hint f eb eb none {}
      (World.init σ A feed) (Reasoning.Theory.initState σ σ₀ (.ofUInt256 g) A I) none [] []
      hmemh (by rw [hname]; exact hf) he
      (by simp [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toNat]; exact le_refl _)
      ⟨hebm, hblk, rfl, ⟨rfl, rfl, rfl, rfl, ⟨M, hfeed, rfl⟩⟩, hb, 0, {}, [], hhb, hplace,
        rfl, by simp [enter, hephi, Fe.Sonatina.bind], rfl, by rw [hslots]; exact .nil,
        by simp [hephi]⟩
      (fun h => by rw [hret] at h; cases h) hnpf
    simp only [show (hint.name == entry) = true by simp [hname], preIf, if_true, ite_self] at hfin
    have hF := hfin.final
    refine ⟨(Xi_agrees (hF.agrees (by
      simp [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toNat]; exact le_refl _))).imp
      id fun h => ⟨feed, ?_⟩, fun hnc Q => ?_, fun Q hQ ⟨_, _, hΞ⟩ => ?_⟩
    · rw [runSectionWith_eq hobj hsec hcode hlow hfe he hpar]
      exact h
    -- Without message calls every step is calm.
    · have hnc' : low.machine.hasCalls = false := by
        simpa [Sidecar.hasCalls, hcode, hlow] using hnc
      rw [hnc'] at hF
      exact hF.xOk (g.toNat + 1)
    -- A frame that succeeds is the IR's run that stops, so its calls are the run's.
    obtain ⟨s', o', hX⟩ := X_of_Xi_success hΞ
    obtain ⟨out, w', hr, hc⟩ := hF.success (by
      simp [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toNat]; exact le_refl _) hX
    have hrun : (s.runSectionWith name .machine (plan name).prepare).exec I
        (World.init σ A feed) = some (.error (.stop out w')) := by
      rw [runSectionWith_eq hobj hsec hcode hlow hfe he hpar]
      exact (congrArg endRun hr).trans rfl
    exact hfeed.xOk (fun c hc' => hQ feed out w' (.inr hrun) c (hc ▸ hc')) (g.toNat + 1)
  · simp at hce

/-- A section's run never returns: it ends stuck where its entry would. -/
theorem runSection_not_ok (s : Sidecar) (name : String) (level : Level) (I : ExecutionEnv)
    (w : World) (v : ByteArray) (w' : World) :
    (s.runSection name level).exec I w ≠ some (.ok (v, w')) := by
  unfold Sidecar.runSection Sidecar.runSectionWith
  intro hx
  repeat' (split at hx)
  all_goals simp only [stuck, Fe.M.exec_bind, Fe.M.exec_diverge, reduceCtorEq] at hx
  all_goals repeat' (split at hx)
  all_goals simp_all

/-- `section_sound` for the machine IR itself, the empty plan's, which never panics. -/
theorem section_sound_machine {s : Sidecar} (h : check s = true) {name : String}
    (hn : ((entries s).lookup name).isSome) {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} {tail : ByteArray} (hI : I.code = s.code name ++ tail) :
    (Exhausted (Ξ σ σ₀ g A I) ∨ ∃ feed,
      Agrees .P1 (Ξ σ σ₀ g A I) ((s.runSection name .machine).exec I (World.init σ A feed))) ∧
      (s.hasCalls name = false → ∀ Q, Invariant.XiOk Q σ σ₀ g A I) ∧
      ∀ Q, (∀ feed out w, Succeeds ((s.runSection name .machine).exec I (World.init σ A feed)) out w →
        ∀ c ∈ w.calls, c.Ok Q) → (∃ r o, Ξ σ σ₀ g A I = .ok (.success r o)) →
        Invariant.XiOk Q σ σ₀ g A I :=
  section_sound (plan := fun _ => []) h hn hI fun feed c =>
    runSection_noPanic s name .machine I (World.init σ A feed) c

/-- The checker's soundness: a sidecar it accepts has bytes that refine its machine IR, the
    runtime on every call whose calldata fits and the constructor on every deployment, at
    profile `P1`. -/
theorem check_sound {s : Sidecar} (h : check s = true) : Sound s := by
  obtain ⟨-, hinit, hrt⟩ := checkWith_ok h
  refine ⟨fun σ σ₀ g A I tail hI _ _ _ => ?_, fun σ σ₀ g A I args _ hI _ _ => ?_⟩
  · exact (section_sound_machine h hrt hI).1
  · rcases (section_sound_machine h hinit hI).1 with hx | ⟨feed, hx⟩
    · exact .inl hx
    · refine .inr ⟨feed, ?_⟩
      show Agrees .P1 _ ((s.runSection "init" .machine >>= fun tail => pure (.empty ++ tail)).exec
        I (World.init σ A feed))
      rw [Fe.M.exec_bind]
      cases hr : (s.runSection "init" .machine).exec I (World.init σ A feed) with
      | none => rw [hr] at hx; exact hx
      | some x =>
        cases x with
        | error e => rw [hr] at hx; exact hx
        | ok p => exact absurd hr (runSection_not_ok s "init" .machine I _ p.1 p.2)

/-- The frames of a checked sidecar whose machine IR makes no message call make no message call
    nor creation: `XiOk` holds, for every condition on calls, of a frame that runs the runtime
    bytes followed by any bytes, and of one that runs the init bytes followed by any
    arguments. -/
theorem check_xiOk {s : Sidecar} (h : check s = true) (hrc : s.hasCalls "runtime" = false)
    (hic : s.hasCalls "init" = false) :
    (∀ Q σ σ₀ g A (I : ExecutionEnv) tail, I.code = s.code "runtime" ++ tail →
      Invariant.XiOk Q σ σ₀ g A I) ∧
    ∀ Q σ σ₀ g A (I : ExecutionEnv) args, I.code = s.code "init" ++ args →
      Invariant.XiOk Q σ σ₀ g A I := by
  obtain ⟨-, hinit, hrt⟩ := checkWith_ok h
  exact ⟨fun Q _ _ _ _ _ _ hI => (section_sound_machine h hrt hI).2.1 hrc Q,
    fun Q _ _ _ _ _ _ hI => (section_sound_machine h hinit hI).2.1 hic Q⟩

/-- The calls of a checked sidecar's frames are the model's: a frame that succeeds, of the
    runtime bytes followed by any bytes or of the init bytes followed by any arguments, makes only
    calls and creations satisfying `Q`, given that every successful run of the machine IR's
    runtime (or constructor) from the frame's account map and substate records only such calls,
    under any feed.  For the runtime that hypothesis is `ContractModel.callsAt`. -/
theorem check_xiOk_callsAt {s : Sidecar} (h : check s = true) :
    (∀ Q σ σ₀ g A (I : ExecutionEnv) tail, I.code = s.code "runtime" ++ tail → CalldataFits I →
      (s.model .machine).callsAt Q σ σ₀ g A I → (∃ r o, Ξ σ σ₀ g A I = .ok (.success r o)) →
      Invariant.XiOk Q σ σ₀ g A I) ∧
    ∀ Q σ σ₀ g A (I : ExecutionEnv) args, I.code = s.code "init" ++ args →
      (∀ feed out w, Succeeds (((s.model .machine).init args).exec I (World.init σ A feed)) out w →
        ∀ c ∈ w.calls, c.Ok Q) → (∃ r o, Ξ σ σ₀ g A I = .ok (.success r o)) →
      Invariant.XiOk Q σ σ₀ g A I := by
  obtain ⟨-, hinit, hrt⟩ := checkWith_ok h
  exact ⟨fun Q _ _ _ _ _ _ hI _ hc hx => (section_sound_machine h hrt hI).2.2 Q hc hx,
    fun Q _ _ _ _ _ _ hI hc hx => (section_sound_machine h hinit hI).2.2 Q hc hx⟩

end Fe.Sonatina.Check
