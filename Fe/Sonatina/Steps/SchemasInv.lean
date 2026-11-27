import Fe.Sonatina.Steps.SchemasEval

/-!
# SCCP's facts along a run of the input

What `sccpFactsOk` gives (`SccpSpec`), and the invariants a run of the input keeps under it:

- the run stays in the executable set, each edge it takes not claimed dead (`runTerm_slot`,
  `exec_next`): a terminator goes by a slot `slotTaken` allows under the constants, which hold;
- the constants hold of every value bound to a word (`CHolds`): entering a block over an
  executable edge binds each claimed phi to its claimed constant (`cholds_enter`), and a claimed
  statement of an executable block computes its constant, by evaluation or by a schema at the
  point (`cholds_stmt`);
- a folded phi holds its operand's value wherever its block is a tree ancestor-or-self
  (`TPI`, `tpi_enter`, `tpi_stmt`), as for `cfg_cleanup`'s trivial phis.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-! ## What the facts give -/

/-- What `sccpFactsOk` checks, on the check's context. -/
structure SccpSpec (f : Func) (X : StepCtx) : Prop where
  lt : ∀ v c, X.cs.find? v = some c → c < W
  closed : execClosed f X.E X.dead = true
  dead : ∀ pk ∈ X.dead, (X.E.find? pk.1).isNone = true ∨
    (X.inB.find? pk.1).any (fun blk => !slotTaken X.cs blk.term pk.2) = true
  claims : ∀ v c, X.cs.find? v = some c → (match X.inD.find? v with
    | some (.phi b) => (X.E.find? b).isNone || (phiOf X.inB b v).any fun p =>
        p.incoming.all fun ob => !edgeExec X.inB X.E X.dead ob.2 b || constOf X.cs ob.1 == some c
    | some (.stmt b _) => (X.E.find? b).isNone ||
        ((defStmt X.inB X.inD v).bind fun s => pureInst? s.inst).any fun p =>
          stmtConstOk X.inB X.inD X.K X.cs p c
    | _ => false) = true

theorem sccpSpec_of {f : Func} {s : FuncSnap} {F : StepFacts}
    (h : sccpFactsOk f (.ofListBy (·.id) f.blocks) (defsOf f) (kbMap F) F = true) :
    SccpSpec f (ctxOf .sccp f s F) := by
  unfold sccpFactsOk at h
  split at h
  · cases h
  next consts hc =>
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨_, hlt⟩, hcl⟩, hdead⟩, hcl'⟩ := h
  have hcs : (ctxOf .sccp f s F).cs = .ofList consts := by
    simp [ctxOf, StepCtx.of, Mode.sccp?, hc]
  refine ⟨fun v c hv => ?_, hcl, fun pk hpk => by have := hdead pk hpk; rw [hcs]; exact this,
    fun v c hv => ?_⟩
  · rw [hcs, NatMap.find?_ofList] at hv
    exact hlt _ (lookup_mem hv)
  · rw [hcs, NatMap.find?_ofList] at hv
    have := hcl' _ (lookup_mem hv)
    simp only at this
    rw [hcs]
    exact this

/-! ## The edge a terminator takes -/

theorem constOf_val {cs : NatMap Nat} {env : Env} (hC : CHolds cs env) {o : Operand}
    (ho : o.wf = true) {n : Nat} (hn : intVal env o = some (256, n)) {x : Nat}
    (hx : constOf cs o = some x) : x = n := by
  cases o with
  | imm bits w =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
    simp only [intVal, opVal, Option.some.injEq, Prod.mk.injEq] at hn
    simp only [constOf, Option.some.injEq] at hx
    rw [← hx, ← hn.2, Nat.mod_eq_of_lt ho.2]
  | var u =>
    exact (hC u x n hx (opVal_of_intVal hn)).symm

theorem Total.returns {α : Type} {P : α → Prop} {x : FeM α} (h : Total P x) : Returns P x := by
  intro I w a w' hx
  obtain ⟨a', ha', hP⟩ := h I w
  rw [hx] at ha'
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at ha'
  exact ha'.1 ▸ hP

theorem find_zipIdx {cs : NatMap Nat} {env : Env} (hC : CHolds cs env) (v : Nat) :
    ∀ {cases : List (Operand × Nat)} {vals : List (Nat × Nat)},
    List.Forall₂ (fun (ci : Operand × Nat) (a : Nat × Nat) =>
      intVal env ci.1 = some (256, a.1) ∧ a.2 = ci.2) cases vals →
    (∀ ci ∈ cases, ci.1.wf = true ∧ (constOf cs ci.1).isSome = true) → ∀ n,
    (∀ a, vals.find? (·.1 == v) = some a → ∃ ci, (cases.zipIdx n).find?
        (fun ci => constOf cs ci.1.1 == some v) = some ci ∧ n ≤ ci.2 ∧
        (cases.map (·.2))[ci.2 - n]? = some a.2) ∧
    (vals.find? (·.1 == v) = none →
      (cases.zipIdx n).find? (fun ci => constOf cs ci.1.1 == some v) = none)
  | [], [], .nil, _, n => ⟨fun a h => by simp at h, fun _ => rfl⟩
  | ci :: cases, a :: vals, .cons ⟨hi, ha⟩ hrest, hw, n => by
    have hw0 := hw ci (List.mem_cons_self ..)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hw0.2
    have hxa := constOf_val hC hw0.1 hi hx
    obtain ⟨ih1, ih2⟩ := find_zipIdx hC v hrest (fun c hc => hw c (List.mem_cons_of_mem _ hc)) (n + 1)
    simp only [List.zipIdx_cons, List.find?_cons, hx]
    by_cases hv : a.1 = v
    · have h1 : (a.1 == v) = true := by simp [hv]
      have h2 : (some x == some v) = true := by simp [hxa, hv]
      simp only [h1, h2]
      refine ⟨fun a' ha' => ⟨(ci, n), rfl, le_rfl, ?_⟩, fun h => by simp at h⟩
      simp only [Option.some.injEq] at ha'
      subst ha'
      simp [ha]
    · have h1 : (a.1 == v) = false := by simp [hv]
      have h2 : (some x == some v) = false := by simp [hxa, hv]
      simp only [h1, h2]
      refine ⟨fun a' ha' => ?_, ih2⟩
      obtain ⟨cj, hcj, hle, hget⟩ := ih1 a' ha'
      refine ⟨cj, hcj, by omega, ?_⟩
      have : cj.2 - n = (cj.2 - (n + 1)) + 1 := by omega
      rw [this, List.map_cons, List.getElem?_cons_succ]
      exact hget

theorem orElse_none' (d : Option Nat) : (none <|> d) = d := rfl
theorem orElse_some' (a : Nat) (d : Option Nat) : (some a <|> d) = some a := rfl

/-- A terminator of a function goes by a slot `slotTaken` allows, when the constants hold. -/
theorem runTerm_slot {cs : NatMap Nat} {env : Env} (hC : CHolds cs env) {t : Fe.Sonatina.Term}
    {nr : Nat} (hwf : t.wf nr = true) (hdef : ∀ o ∈ t.args, ∃ v, intVal env o = some (256, v)) :
    Returns (fun nx => match nx with
      | .goto _ d => ∃ k, t.succs[k]? = some d ∧ slotTaken cs t k = true
      | .done _ => True) (runTerm env t) := by
  have hargs : ∀ o ∈ t.args, o.wf = true := by
    unfold Fe.Sonatina.Term.wf at hwf
    simp only [Bool.and_eq_true, List.all_eq_true] at hwf
    exact hwf.1
  cases t with
  | jump d => exact Returns.pure ⟨0, rfl, rfl⟩
  | br c nz z =>
    obtain ⟨v, hv⟩ := hdef c (List.mem_singleton_self _)
    simp only [runTerm]
    rw [evalInt_eq, hv]
    simp only [Steps.lift, pure_bind]
    refine Returns.pure ⟨if v != 0 then 0 else 1, ?_, ?_⟩
    · by_cases h : v != 0 <;> simp [h, Term.succs]
    · simp only [slotTaken]
      cases hx : constOf cs c with
      | none => rfl
      | some x =>
        have := constOf_val hC (hargs c (List.mem_singleton_self _)) hv hx
        subst this
        simp
  | brTable sc d cases =>
    have hwfT := hwf
    unfold Fe.Sonatina.Term.wf at hwfT
    simp only [Bool.and_eq_true, List.all_eq_true] at hwfT
    have hkeys : ∀ ci ∈ cases, ci.1.wf = true ∧ (constOf cs ci.1).isSome = true := by
      intro ci hci
      have hw := hargs ci.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hci))
      refine ⟨hw, ?_⟩
      have := hwfT.2.1.2 ci hci
      cases ho : ci.1 with
      | var => rw [ho] at this; simp [Operand.immVal?] at this
      | imm => simp [constOf]
    obtain ⟨v, hv⟩ := hdef sc (List.mem_cons_self ..)
    simp only [runTerm]
    rw [evalInt_eq, hv]
    simp only [Steps.lift, pure_bind]
    have hmap : Returns (fun vals => List.Forall₂ (fun (ci : Operand × Nat) (a : Nat × Nat) =>
        intVal env ci.1 = some (256, a.1) ∧ a.2 = ci.2) cases vals)
        (cases.mapM fun (o, dest) => (do return ((← evalInt env o).2, dest) : FeM (Nat × Nat))) := by
      refine Total.returns (Total.mapM fun ci hci => ?_)
      obtain ⟨n, hn⟩ := hdef ci.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hci))
      rcases ci with ⟨o, dest⟩
      simp only at hn ⊢
      rw [evalInt_eq, hn]
      simp only [Steps.lift, pure_bind]
      exact Total.pure ⟨rfl, rfl⟩
    refine Returns.bind hmap fun vals hvals => ?_
    -- where the table goes is a slot of it
    have hmem : ∀ dest, ((vals.find? (·.1 == v)).map (·.2) <|> d) = some dest →
        dest ∈ (Fe.Sonatina.Term.brTable sc d cases).succs := by
      intro dest hd
      simp only [Term.succs, List.mem_append, Option.mem_toList, List.mem_map]
      rcases hf : vals.find? (·.1 == v) with _ | a
      · rw [hf] at hd; simp only [Option.map_none, orElse_none'] at hd
        exact Or.inl hd
      · rw [hf] at hd; simp only [Option.map_some, orElse_some', Option.some.injEq] at hd
        subst hd
        have ha := List.mem_of_find?_eq_some hf
        obtain ⟨ci, hci, hr⟩ := forall₂_mem_right hvals ha
        exact Or.inr ⟨ci, hci, hr.2.symm⟩
    split
    · next dest hd =>
      refine Returns.pure ?_
      simp only
      cases hx : constOf cs sc with
      | none =>
        obtain ⟨k, hk⟩ := List.getElem?_of_mem (hmem dest hd)
        exact ⟨k, hk, by simp [slotTaken, hx]⟩
      | some x =>
        have hxv := constOf_val hC (hargs sc (List.mem_cons_self ..)) hv hx
        subst hxv
        cases d with
        | none =>
          obtain ⟨k, hk⟩ := List.getElem?_of_mem (hmem dest hd)
          exact ⟨k, hk, by simp [slotTaken, hx]⟩
        | some dd =>
          have hall : (cases.all fun ci => (constOf cs ci.1).isSome) = true :=
            List.all_eq_true.mpr fun ci hci => (hkeys ci hci).2
          obtain ⟨h1, h2⟩ := find_zipIdx hC x hvals hkeys 0
          rcases hf : vals.find? (·.1 == x) with _ | a
          · rw [hf] at hd
            simp only [Option.map_none, orElse_none', Option.some.injEq] at hd
            subst hd
            refine ⟨0, rfl, ?_⟩
            simp [slotTaken, hx, hall, h2 hf]
          · rw [hf] at hd
            simp only [Option.map_some, orElse_some', Option.some.injEq] at hd
            subst hd
            obtain ⟨ci, hci, _, hget⟩ := h1 a hf
            refine ⟨ci.2 + 1, ?_, ?_⟩
            · simp only [Term.succs, Option.toList_some, List.singleton_append,
                List.getElem?_cons_succ]
              simpa using hget
            · simp [slotTaken, hx, hall, hci]
    · exact Returns.stuck _
  | ret vs =>
    unfold runTerm
    exact Returns.bind_any fun _ => Returns.pure trivial
  | evmReturn a l =>
    unfold runTerm
    exact Returns.bind_any fun _ => Returns.bind_any fun _ => Returns.bind_any fun e => nomatch e
  | evmRevert a l =>
    unfold runTerm
    exact Returns.bind_any fun _ => Returns.bind_any fun _ => Returns.bind_any fun e => nomatch e
  | evmStop => unfold runTerm; exact Returns.bind_any fun e => nomatch e
  | evmInvalid => unfold runTerm; exact Returns.bind_any fun e => nomatch e
  | evmSelfDestruct a =>
    unfold runTerm
    exact Returns.bind_any fun _ => Returns.bind_any fun e => nomatch e
  | unreachable => unfold runTerm; exact Returns.bind_any fun e => nomatch e

/-- An edge the run takes from an executable block is executable and leads into the set. -/
theorem exec_next {f : Func} {X : StepCtx} (Sp : SccpSpec f X)
    (hB : X.inB = .ofListBy (·.id) f.blocks) {b : Nat} {ib : Block} (hb : f.block? b = some ib)
    (hex : (X.E.find? b).isSome = true) {d k : Nat} (hk : ib.term.succs[k]? = some d)
    (hs : slotTaken X.cs ib.term k = true) :
    (X.E.find? d).isSome = true ∧ edgeExec X.inB X.E X.dead b d = true := by
  have hid : ib.id = b := by simpa using List.find?_some hb
  have hib : X.inB.find? b = some ib := by rw [hB, NatMap.find?_ofListBy]; exact hb
  have hnd : X.dead.contains (b, k) = false := by
    cases hc : X.dead.contains (b, k)
    · rfl
    · rcases Sp.dead (b, k) (List.contains_iff_mem.mp hc) with h | h
      · simp only [Option.isNone_iff_eq_none] at h; rw [h] at hex; cases hex
      · simp only [hib, Option.any_some, Bool.not_eq_true'] at h
        rw [hs] at h; cases h
  have hz : (d, k) ∈ ib.term.succs.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hk
  refine ⟨?_, ?_⟩
  · have := Sp.closed
    unfold execClosed at this
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at this
    rcases this.2 ib (List.mem_of_find?_eq_some hb) with h | h
    · rw [hid] at h; simp only [Option.isNone_iff_eq_none] at h
      rw [h] at hex; cases hex
    · rcases h (d, k) hz with h | h
      · rw [hid, hnd] at h; cases h
      · exact h
  · unfold edgeExec
    simp only [hex, hib, Bool.true_and, Option.any_some, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true']
    exact ⟨(d, k), hz, rfl, hnd⟩

/-! ## The constants hold -/

theorem cholds_empty (env : Env) : CHolds .empty env := fun _ _ _ h => by simp at h

theorem intVal_of_evalOperand {env : Env} {o : Operand} {x : Nat}
    (h : evalOperand env o = pure (.int 256 x)) : intVal env o = some (256, x) := by
  rw [evalOperand_eq] at h
  cases hv : opVal env o with
  | none =>
    rw [hv] at h
    have := congrArg (fun y => y.exec default someWorld) h
    simp [Steps.lift, stuck, Fe.M.exec_pure, Fe.M.exec_diverge] at this
  | some v =>
    rw [hv] at h
    have := pure_inj h
    subst this
    simp [intVal, hv]

theorem argsAre_unique {env : Env} : ∀ {os : List Operand} {xs ys : List Nat},
    ArgsAre env os xs → ArgsAre env os ys → xs = ys
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons ⟨h1, _⟩ hx, .cons ⟨h2, _⟩ hy => by
    rw [h1] at h2
    have := pure_inj h2
    simp only [Val.int.injEq, true_and] at this
    rw [this, argsAre_unique hx hy]

theorem constOf_args {cs : NatMap Nat} {env : Env} (hC : CHolds cs env) :
    ∀ {os : List Operand} {xs ys : List Nat}, (∀ a ∈ os, a.wf = true) → ArgsAre env os xs →
      List.Forall₂ (fun a y => constOf cs a = some y) os ys → ys = xs
  | [], _, _, _, .nil, .nil => rfl
  | a :: _, _ :: _, _ :: _, hw, .cons ⟨h1, _⟩ hA, .cons hy hF => by
    rw [constOf_val hC (hw a (List.mem_cons_self ..)) (intVal_of_evalOperand h1) hy,
      constOf_args hC (fun b hb => hw b (List.mem_cons_of_mem _ hb)) hA hF]

/-- A claimed constant of a pure statement's result holds where the statement runs. -/
theorem stmtConst_sound {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) {e : Env} {b k : Nat} (S : SidePt sig syms f e b k) (c : Ctx)
    (hK : KBHolds X.K e) (hC : CHolds X.cs e) {ib : Block} (hb : f.block? b = some ib)
    {st : Stmt} (hst : ib.body[k]? = some st) {p : PureInst} (hp : pureInst? st.inst = some p)
    {c0 : Nat} (hc0 : c0 < W) (h : stmtConstOk X.inB X.inD X.K X.cs p c0 = true) :
    noClz p = true ∧ ∃ xs, ArgsAre e p.args xs ∧ p.evalOn xs = c0 := by
  unfold stmtConstOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨hc, h⟩ := h
  have hmem := List.mem_of_find?_eq_some hb
  have hsm : st ∈ ib.body := List.mem_of_getElem? hst
  have hops : ∀ d, ∀ a ∈ p.args, ∃ n, intVal e a = some (256, n) ∧ n < W ∧
      TermOk e (unfold (.ofListBy (·.id) f.blocks) (defsOf f) X.cs d a) n := fun d a ha => by
    have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
    exact S.unfold_sound (EnvSub.refl e) c hC d a ((Func.wf_operands S.wf hmem).2.1 st hsm a ha')
      fun w hw => by subst hw; exact stmt_operand S.wf S.ssa hb S.reach hst ha'
  obtain ⟨xs, hargs, _⟩ := termOf_ok (hops 0)
  refine ⟨hc, xs, hargs, ?_⟩
  rcases h with h | ⟨d, _, h⟩
  · split at h
    · next ys hys =>
      simp only [beq_iff_eq] at h
      have hwa : ∀ a ∈ p.args, a.wf = true := fun a ha =>
        (Func.wf_operands S.wf hmem).2.1 st hsm a (by rw [pureInst?_args hp]; exact ha)
      have hyx : ys = xs := constOf_args hC hwa hargs (mapM_option_forall₂ hys)
      subst hyx
      have h1 := evalConst_sound (c := c) hp (noClz_ne hc) hargs h
      have h2 := Schemas.runInst_pure (c := c) (env := e) (noClz_ne hc) hargs
      rw [pureInst?_toInst hp, h1] at h2
      have := pure_inj h2
      simp only [List.cons.injEq, Val.int.injEq, true_and, and_true] at this
      exact this.symm
    · cases h
  · obtain ⟨xs', hargs', hok⟩ := termOf_ok (hops d)
    rw [argsAre_unique hargs' hargs] at hok
    rw [hB, hD] at h
    have hf : FactsOn (kbOf X.K) (envWord e) [termOf (unfold (.ofListBy (·.id) f.blocks) (defsOf f) X.cs d) p,
        .lit c0] := factsOn_env hK fun a ha => by
      simp only [List.any_cons, List.any_nil, Bool.or_false, Term.hasAtom] at ha
      exact hok.2 a ha
    have := checkExact_sound h hf
    rw [hok.1] at this
    simp only [Term.eval, Nat.mod_eq_of_lt hc0] at this
    exact this

/-- A statement of an executable block keeps the constants. -/
theorem cholds_stmt {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (Sp : SccpSpec f X) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (c : Ctx) (hK : KBHolds X.K e) (hC : CHolds X.cs e)
    (hex : (X.E.find? b).isSome = true) {ib : Block} (hb : f.block? b = some ib) {st : Stmt}
    (hst : ib.body[k]? = some st) {vals : List Val}
    (hpv : st.inst.pure = true → pureVals e st.inst = some vals) (hl : st.dsts.length = vals.length) :
    CHolds X.cs ((st.dsts.zip vals).foldl bindStep e) := by
  intro v c0 n hcv hvn
  rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, hxv, hval⟩ | ⟨he, _⟩
  swap
  · exact hC v c0 n hcv he
  have hmem := List.mem_of_find?_eq_some hb
  have hid : ib.id = b := by simpa using List.find?_some hb
  have hxd := (List.of_mem_zip hx).1
  have hdef : (v, Def.stmt b k) ∈ defList f := hxv ▸ hid ▸ stmt_def hmem hst hxd
  have hfind : X.inD.find? v = some (.stmt b k) := hD ▸ defsOf_find S.uniq hdef
  have hcl := Sp.claims v c0 hcv
  rw [hfind] at hcl
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hcl
  rcases hcl with hcl | hcl
  · rw [hcl] at hex; cases hex
  have hds : defStmt X.inB X.inD v = some st := by
    simp only [defStmt, hfind, hB, NatMap.find?_ofListBy]
    exact Option.bind_eq_some_iff.mpr ⟨ib, hb, hst⟩
  rw [hds, Option.bind_some] at hcl
  rcases hp : pureInst? st.inst with _ | p
  · rw [hp] at hcl; cases hcl
  rw [hp, Option.any_some] at hcl
  obtain ⟨hc, xs, hargs, hval'⟩ := stmtConst_sound hB hD S c hK hC hb hst hp (Sp.lt v c0 hcv) hcl
  have hpv' := hpv (pureInst?_pure hp hc)
  rw [pureVals_of (c := c) hp hc hargs] at hpv'
  cases hpv'
  have hx2 : x.2 = .int p.bits (p.evalOn xs) := by
    have := (List.of_mem_zip hx).2
    simpa using this
  have hty := ((Func.wf_words S.wf).2 ib hmem).2 st (List.mem_of_getElem? hst) x.1 hxd
  rw [hx2, hty, Val.as_word (evalOn_lt' hargs)] at hval
  cases hval
  exact hval'

/-- Entering an executable block over an executable edge keeps the constants. -/
theorem cholds_enter {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (Sp : SccpSpec f X) (hwf : f.wf sig syms = true)
    (hs : ssa f (domTree f) = true) {env : Env} {q b : Nat} (hw : EnvW env)
    (hC : CHolds X.cs env) (hex : (X.E.find? b).isSome = true)
    (hedge : edgeExec X.inB X.E X.dead q b = true) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) : CHolds X.cs e₁ := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨vals, hF2, _, rfl⟩ := enterOpt_spec he
  intro v c0 n hcv hvn
  rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, hxv, hval⟩ | ⟨he', _⟩
  swap
  · exact hC v c0 n hcv he'
  obtain ⟨φ, hφ, hx1, hgv⟩ := zip_map_forall₂ hF2 hx
  simp only [Option.bind_eq_bind, Option.bind_some] at hgv
  obtain ⟨o, hinc, hov⟩ := Option.bind_eq_some_iff.mp hgv
  have hin := inc_mem hinc
  rw [hx1] at hxv
  simp only at hxv
  subst hxv
  have hdef := hid ▸ phi_def hmem hφ
  have hfind : X.inD.find? φ.dst = some (.phi b) := hD ▸ defsOf_find hU hdef
  have hcl := Sp.claims _ c0 hcv
  rw [hfind] at hcl
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hcl
  rcases hcl with hcl | hcl
  · rw [hcl] at hex; cases hex
  have hphi : phiOf X.inB b φ.dst = some φ := by
    simp only [phiOf, hB, NatMap.find?_ofListBy]
    exact Option.bind_eq_some_iff.mpr ⟨blk, hb, find?_dst (hU.phis hmem) hφ⟩
  rw [hphi, Option.any_some, List.all_eq_true] at hcl
  have := hcl _ hin
  simp only [hedge, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  have hword := phi_val_word hwf hmem hφ hin hw hov
  rw [hx1] at hval
  simp only [((Func.wf_words hwf).2 blk hmem).1 φ hφ] at hval
  rw [hword] at hval
  rw [← hval] at hov
  exact (constOf_val hC ((Func.wf_operands hwf hmem).1 φ hφ _ hin) (by simp [intVal, hov]) this).symm

/-! ## Folded phis -/

theorem phiFold_spec {X : StepCtx} {v : Nat} {x : Operand} (h : X.phiFold v x = true) :
    ∃ B φ, X.inD.find? v = some (.phi B) ∧ X.above B x = true ∧ phiOf X.inB B v = some φ ∧
      (∃ ob ∈ φ.incoming, edgeExec X.inB X.E X.dead ob.2 B = true ∧ ob.1 = x) ∧
      ∀ ob ∈ φ.incoming, edgeExec X.inB X.E X.dead ob.2 B = true → ob.1 = x ∨ ob.1 = .var v := by
  unfold StepCtx.phiFold at h
  split at h
  · next B hB =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hφ⟩ := h
    rcases hp : phiOf X.inB B v with _ | φ
    · rw [hp] at hφ; cases hφ
    rw [hp, Option.any_some] at hφ
    simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_filter,
      beq_iff_eq, Bool.or_eq_true] at hφ
    obtain ⟨⟨ob, ⟨hob, he⟩, hx⟩, hall⟩ := hφ
    exact ⟨B, φ, hB, ha, hp, ⟨ob, hob, he, hx⟩, fun ob hob he => hall ob ⟨hob, he⟩⟩
  · cases h

theorem above_spec {X : StepCtx} {B : Nat} {x : Operand} (h : X.above B x = true) :
    ∀ w, x = .var w → X.inD.find? w = some .param ∨ ∃ d, d ≠ B ∧ X.T.Anc d B ∧
      (X.inD.find? w = some (.phi d) ∨ ∃ j, X.inD.find? w = some (.stmt d j)) := by
  intro w hw
  subst hw
  simp only [StepCtx.above] at h
  split at h
  · next he => exact Or.inl he
  · next d he =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact Or.inr ⟨d, h.1, DomTree.anc_sound h.2, Or.inl he⟩
  · next d j he =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact Or.inr ⟨d, h.1, DomTree.anc_sound h.2, Or.inr ⟨j, he⟩⟩
  · cases h

/-- Entering a block over an executable edge keeps the trivial-phi invariant. -/
theorem tpi_enter {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) (hwf : f.wf sig syms = true)
    (hv : (domTree f).valid f = true) (hs : ssa f (domTree f) = true) {env : Env} {q b : Nat}
    (hi : BlockInv f (domTree f) (env, some q, b)) (ht : TPI X f env q)
    (hedge : edgeExec X.inB X.E X.dead q b = true) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) : TPI X f e₁ b := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨hw, _, hr, hqr, hed, _⟩ := hi
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  obtain ⟨e, he0⟩ : ∃ e, f.blocks.head? = some e := by
    cases h : f.blocks.head? with
    | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
    | some e => exact ⟨e, rfl⟩
  have hroot := (DomTree.valid_entry hv he0).2
  have hbroot : (domTree f).Anc e.id b := hid ▸ DomTree.valid_root hv he0 hmem (hid ▸ hr)
  intro v x hpf B hB' hanc
  obtain ⟨B0, φ, hB0, hab, hphi, ⟨ob0, hob0, _, hx0⟩, hlive⟩ := phiFold_spec hpf
  rw [hD] at hB0
  have hBB : B0 = B := Def.phi.inj (hU.fn (defsOf_mem hB0) hB')
  subst hBB
  -- `φ` is the phi of `v` in block `B0`
  simp only [phiOf, hB, NatMap.find?_ofListBy] at hphi
  obtain ⟨bB, hbB, hφf⟩ := Option.bind_eq_some_iff.mp hphi
  have hbB' : f.block? B0 = some bB := hbB
  have hφ : φ ∈ bB.phis := List.mem_of_find?_eq_some hφf
  have hφv : φ.dst = v := by simpa using List.find?_some hφf
  have hbBm := List.mem_of_find?_eq_some hbB'
  have hxw : x.wf = true := hx0 ▸ (Func.wf_operands hwf hbBm).1 φ hφ _ hob0
  -- entering `b` does not rebind `x`
  have hxkeep : opVal (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env) x =
      opVal env x := by
    cases x with
    | var u =>
      show (List.foldl bindStep env _)[u]? = env[u]?
      refine fold_get_not _ _ _ ?_
      rw [hkeys]
      intro hu
      obtain ⟨φu, hφu, rfl⟩ := List.mem_map.mp hu
      have hdu := hid ▸ phi_def hmem hφu
      rcases above_spec hab _ rfl with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
      · rw [hD] at hp; cases hU.fn (defsOf_mem hp) hdu
      · rw [hD] at hd
        rw [hT] at ha
        have hdb : d = b := Def.phi.inj (hU.fn (defsOf_mem hd) hdu)
        subst hdb
        exact hne (DomTree.anc_antisymm hroot hbroot hanc ha).symm
      · rw [hD] at hd; cases hU.fn (defsOf_mem hd) hdu
    | imm => rfl
  by_cases hBb : B0 = b
  · subst hBb
    rw [hb] at hbB'
    cases hbB'
    obtain ⟨o, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hφ
    have hom : (o, B0) ∈ φ.incoming ∨ True := Or.inr trivial
    clear hom
    have hom : (o, q) ∈ φ.incoming := inc_mem hinc
    have hword := phi_val_word hwf hmem hφ hom hw hov
    have hox : opVal env o = opVal env x := by
      rcases hlive (o, q) hom hedge with h | h
      · simp only at h; rw [h]
      · simp only at h
        subst h
        exact ht v x hpf _ hB' (phiUse_anc hwf hs hb hr hqr hφ hom hB')
    rw [hxkeep, ← hox, hov]
    show (List.foldl bindStep env _)[v]? = some val
    rw [← hφv, hget, ((Func.wf_words hwf).2 blk hmem).1 φ hφ, hword]
  · have hBq := (DomTree.anc_of_edge hv hqr hed hanc).resolve_left hBb
    rw [hxkeep, ← ht v x hpf _ hB' hBq]
    show (List.foldl bindStep env _)[v]? = env[v]?
    refine fold_get_not _ _ _ ?_
    rw [hkeys]
    intro hvm
    obtain ⟨φv, hφv', e'⟩ := List.mem_map.mp hvm
    have := Def.phi.inj (hU.fn (e' ▸ hid ▸ phi_def hmem hφv') hB')
    exact hBb this.symm

/-- A statement of block `b` keeps the trivial-phi invariant at `b`. -/
theorem tpi_stmt {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hv : (domTree f).valid f = true) (hs : ssa f (domTree f) = true) {env : Env} {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true)
    {k : Nat} {st : Stmt} (hst : blk.body[k]? = some st) (ht : TPI X f env b)
    (l : List ((Nat × Ty) × Val)) (hl : ∀ y ∈ l, y.1 ∈ st.dsts) :
    TPI X f (l.foldl bindStep env) b := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e, he0⟩ : ∃ e, f.blocks.head? = some e := by
    cases h : f.blocks.head? with
    | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
    | some e => exact ⟨e, rfl⟩
  have hroot := (DomTree.valid_entry hv he0).2
  have hbroot : (domTree f).Anc e.id b := hid ▸ DomTree.valid_root hv he0 hmem (hid ▸ hr)
  have hnot : ∀ u d, (u, d) ∈ defList f → (∀ j, d ≠ Def.stmt b j) → u ∉ l.map (·.1.1) := by
    intro u d hd hne hu
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
    have := hU.fn hd (hid ▸ stmt_def hmem hst (hl y hy))
    exact hne k this
  intro v x hpf B hB' hanc
  obtain ⟨B0, φ, hB0, hab, _, _, _⟩ := phiFold_spec hpf
  rw [hD] at hB0
  have hBB : B0 = B := Def.phi.inj (hU.fn (defsOf_mem hB0) hB')
  subst hBB
  have hx : opVal (l.foldl bindStep env) x = opVal env x := by
    cases x with
    | var u =>
      show (l.foldl bindStep env)[u]? = env[u]?
      refine fold_get_not _ _ _ ?_
      rcases above_spec hab _ rfl with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
      · rw [hD] at hp; exact hnot u _ (defsOf_mem hp) fun _ h => by cases h
      · rw [hD] at hd; exact hnot u _ (defsOf_mem hd) fun _ h => by cases h
      · rw [hD] at hd
        refine hnot u _ (defsOf_mem hd) fun j' h => ?_
        cases h
        rw [hT] at ha
        exact hne (DomTree.anc_antisymm hroot hbroot hanc ha).symm
    | imm => rfl
  rw [hx, ← ht v x hpf _ hB' hanc]
  show (l.foldl bindStep env)[v]? = env[v]?
  exact fold_get_not _ _ _ (hnot v _ hB' fun _ h => by cases h)

end Fe.Sonatina.Steps.Schemas
