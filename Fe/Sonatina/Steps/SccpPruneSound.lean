import Fe.Sonatina.Steps.GvnPruneInv
import Fe.Sonatina.Steps.PruneSound
import Fe.Sonatina.Steps.CfgCleanupSound

/-!
# `sccp_prune` is sound

`sccpPrune_sound` composes two approximations at the pruned input `pruneFunc f dead`:

- the pruned input approximates the input (`prune_sound_of`), on the invariant `QS` of the
  input's block states: definedness, L2 at the predecessor's end, the known bits and SCCP's
  constants (`CHolds`, `cholds_enter`, `cholds_stmt`), the block executable and entered over a
  slot not claimed dead.  At a block's end the slot the terminator takes is one `slotTaken`
  allows under the constants (`slotTaken_of`), so it is not claimed dead (`qs_live`, from
  `sccpFactsOk`);
- `cfgCleanup_sound` with no summary table: the output approximates the pruned input, which is
  well formed (`pruneFunc_wf`, with the control flow the check checks).
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-! ## The slot taken under the constants -/

theorem constOf_key (cs : NatMap Nat) {o : Operand} (h : o.wf = true) {w : Nat}
    (hw : o.immVal? = some w) : constOf cs o = some w := by
  cases o with
  | var => cases hw
  | imm bits w' =>
    simp only [Operand.immVal?, Option.some.injEq] at hw
    subst hw
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [constOf, Option.some.injEq]
    exact Nat.mod_eq_of_lt h.2

/-- On keys that are immediates, `slotTaken`'s search for the scrutinee's constant finds the
    first case of that key. -/
theorem find_constOf (cs : NatMap Nat) (v : Nat) : ∀ (cases : List (Operand × Nat)) (n : Nat),
    (∀ c ∈ cases, c.1.wf = true ∧ c.1.immVal?.isSome = true) →
    ((cases.zipIdx n).find? fun ci => constOf cs ci.1.1 == some v).map (·.2) =
      (caseIdx v cases).map (· + n)
  | [], _, _ => rfl
  | c :: cases, n, h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (h c (List.mem_cons_self ..)).2
    have hk := constOf_key cs (h c (List.mem_cons_self ..)).1 hw
    have ih := find_constOf cs v cases (n + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.zipIdx_cons, List.find?_cons, hk]
    simp only [caseIdx, hw]
    by_cases hwv : w = v
    · subst hwv
      simp
    · have h1 : (some w == some v) = false := by simpa using hwv
      simp only [h1]
      rw [ih]
      cases caseIdx v cases with
      | none => rfl
      | some i => simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]; omega

/-- Under the constants, a terminator takes only a slot `slotTaken` allows. -/
theorem slotTaken_of {cs : NatMap Nat} {env : Env} (hC : CHolds cs env) {t : Fe.Sonatina.Term}
    {n : Nat} (hwf : t.wf n = true) {k : Nat} (h : Takes env t k) : slotTaken cs t k = true := by
  have hargs : ∀ o ∈ t.args, o.wf = true := by
    unfold Fe.Sonatina.Term.wf at hwf
    simp only [Bool.and_eq_true, List.all_eq_true] at hwf
    exact hwf.1
  cases t with
  | jump => rfl
  | br c nz z =>
    obtain ⟨v, hv, rfl⟩ := h
    simp only [slotTaken]
    cases hx : constOf cs c with
    | none => rfl
    | some x =>
      have := constOf_val hC (hargs c (List.mem_singleton_self _)) hv hx
      subst this
      simp
  | brTable s dd cases =>
    rcases dd with _ | D
    · cases h
    obtain ⟨v, hv, rfl⟩ := h
    have hkeys : ∀ c ∈ cases, c.1.wf = true ∧ c.1.immVal?.isSome = true := by
      intro c hc
      refine ⟨hargs c.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)), ?_⟩
      unfold Fe.Sonatina.Term.wf at hwf
      simp only [Bool.and_eq_true, List.all_eq_true] at hwf
      exact hwf.2.1.2 c hc
    simp only [slotTaken]
    cases hx : constOf cs s with
    | none => rfl
    | some x =>
      have := constOf_val hC (hargs s (List.mem_cons_self ..)) hv hx
      subst this
      have hall : (cases.all fun ci => (constOf cs ci.1).isSome) = true := by
        refine List.all_eq_true.mpr fun ci hci => ?_
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hkeys ci hci).2
        rw [constOf_key cs (hkeys ci hci).1 hw]
        rfl
      have hf := find_constOf cs x cases 0 hkeys
      simp only [Option.isNone_some, hall, Bool.not_true, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte]
      unfold tableSlot
      cases hci : caseIdx x cases with
      | none =>
        rw [hci, Option.map_none] at hf
        rw [Option.map_eq_none_iff.mp hf]
        rfl
      | some i =>
        rw [hci] at hf
        obtain ⟨ci, hfi, hci2⟩ := Option.map_eq_some_iff.mp hf
        rw [hfi]
        simp [hci2]
  | _ => cases h

/-! ## The invariant -/

/-- What the `sccp_prune` check gives about the unpruned input. -/
structure QSpec (sig : Sigs) (syms : List String) (f : Func) (X : StepCtx) (F : StepFacts) :
    Prop where
  wf : f.wf sig syms = true
  hB : X.inB = .ofListBy (·.id) f.blocks
  hD : X.inD = defsOf f
  hK : X.K = kbMap F
  hv : (domTree f).valid f = true
  hs : ssa f (domTree f) = true
  kb : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true
  sp : SccpSpec f X

/-- The facts at a point `(b, k)` of the input's run. -/
structure QPt (sig : Sigs) (syms : List String) (f : Func) (X : StepCtx) (F : StepFacts)
    (e : Env) (b k : Nat) : Prop where
  side : SidePt sig syms f e b k
  kb : KBHolds (kbMap F) e
  cs : CHolds X.cs e
  ex : (X.E.find? b).isSome = true

/-- The facts at a block state of the input's run: definedness, L2 at the predecessor's end, the
    known bits, the constants, the block executable, and the predecessor executable with a slot
    not claimed dead into the block. -/
def QS (f : Func) (X : StepCtx) (F : StepFacts) (s : BState) :
    Prop :=
  BlockInv f (domTree f) s ∧ BlockPure f (domTree f) s ∧ KBHolds (kbMap F) s.1 ∧
    CHolds X.cs s.1 ∧ AncReach (domTree f) s.2.2 ∧ (X.E.find? s.2.2).isSome = true ∧
    ∀ p, s.2.1 = some p → (X.E.find? p).isSome = true ∧ ∃ pblk k, f.block? p = some pblk ∧
      pblk.term.succs[k]? = some s.2.2 ∧ X.dead.contains (p, k) = false

section spec

variable {f : Func} {X : StepCtx} {F : StepFacts} (P : QSpec sig syms f X F)

include P

/-- A statement keeps the facts. -/
theorem qs_stmt {o : Oracle} (hoi : o.IntRet) (c : Ctx) {e : Env} {b k : Nat}
    (H : QPt sig syms f X F e b k) {blk : Block} (hb : f.block? b = some blk) {st : Stmt}
    (hst : blk.body[k]? = some st) :
    Returns (fun vals => st.dsts.length = vals.length →
      QPt sig syms f X F ((st.dsts.zip vals).foldl bindStep e) b (k + 1)) (runStmtO o c e st) := by
  have hm := Func.machine_block (Func.wf_machine P.wf) hb _ (List.mem_of_getElem? hst)
  refine Returns.mono (Returns.and (returns_runStmtO_pure hoi c H.side.pi.1.int hm)
    (kb_stmt_step P.wf P.hs P.kb hb H.side.reach hst H.side.pi H.kb))
    fun vals ⟨⟨hiv, hpv⟩, hkv⟩ hl => ?_
  exact ⟨SidePt.step H.side hb hst hiv hpv hl, hkv hl,
    cholds_stmt P.hB P.hD P.sp H.side c (by rw [P.hK]; exact H.kb) H.cs H.ex hb hst hpv hl, H.ex⟩

/-- A block's first `k` statements keep the facts. -/
theorem qs_take {o : Oracle} (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) {e₁ : Env} (h₀ : QPt sig syms f X F e₁ b 0) :
    ∀ k, k ≤ blk.body.length → Returns (fun e => QPt sig syms f X F e b k)
      (runBodyO o c e₁ (blk.body.take k))
  | 0, _ => by simp only [List.take_zero, runBodyO]; exact Returns.pure h₀
  | k + 1, hkl => by
    have hlt : k < blk.body.length := by omega
    have hsk : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hsk, Option.toList_some, runBodyO_append]
    refine Returns.bind (qs_take hoi c hb h₀ k (by omega)) fun env H => ?_
    simp only [runBodyO]
    refine Returns.bind (qs_stmt P hoi c H hb hsk) fun vals hv =>
      Returns.bind (returns_bind env _ vals) fun env₂ ⟨hl, he⟩ => Returns.pure ?_
    subst he
    exact hv hl

/-- Entering the block of a block state establishes the facts at its start. -/
theorem qs_enter {env : Env} {prev : Option Nat} {b : Nat}
    (hS : QS f X F (env, prev, b)) {blk : Block} (hb : f.block? b = some blk) :
    Returns (fun e₁ => QPt sig syms f X F e₁ b 0) (enter env prev blk) := by
  obtain ⟨hbi, hbp, hkb, hcs, hanc, hex, hprev⟩ := hS
  have hc : Returns (CHolds X.cs) (enter env prev blk) := by
    rw [enter_eq]
    refine Returns.lift fun e₁ he₁ => ?_
    cases prev with
    | none =>
      have hph := phis_nil_of_root P.wf P.hv hb hbi.2.2.1 hbi.2.2.2
      rw [enterOpt_nil hph] at he₁
      cases he₁
      exact hcs
    | some q =>
      obtain ⟨hEq, qblk, kq, hqb, hkq, hnd⟩ := hprev q rfl
      exact cholds_enter P.hB P.hD P.sp P.wf P.hs hbi.1 hcs hex
        (edgeExec_of P.hB hEq hqb hkq hnd) hb he₁
  refine Returns.mono (Returns.and (Returns.and (Returns.and (point_zero P.wf P.hv hbi hb)
    (pureInv_enter P.wf P.hv P.hs hbi hbp hb)) (kb_enter P.wf P.hs P.kb hbi.1 hkb hb)) hc)
    fun e₁ ⟨⟨⟨hpi, hpu⟩, hk⟩, hc⟩ => ⟨⟨P.wf, P.hv, P.hs, ⟨blk, hb⟩, hpi, hpu, hanc⟩, hk, hc, hex⟩

/-- A slot `slotTaken` allows of an executable block is not claimed dead. -/
theorem qs_live {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (hex : (X.E.find? b).isSome = true) {k : Nat} (hs : slotTaken X.cs blk.term k = true) :
    X.dead.contains (b, k) = false := by
  have hib : X.inB.find? b = some blk := by rw [P.hB, NatMap.find?_ofListBy]; exact hb
  cases hc : X.dead.contains (b, k)
  · rfl
  · rcases P.sp.dead (b, k) (List.contains_iff_mem.mp hc) with h | h
    · simp only [Option.isNone_iff_eq_none] at h
      rw [h] at hex; cases hex
    · simp only [hib, Option.any_some, Bool.not_eq_true'] at h
      rw [hs] at h; cases h

theorem term_wf' {b : Nat} {blk : Block} (hb : f.block? b = some blk) :
    blk.term.wf f.rets.length = true := by
  have hw := P.wf
  unfold Func.wf at hw
  simp only [Bool.and_eq_true, List.all_eq_true] at hw
  exact (hw.2 blk (List.mem_of_find?_eq_some hb)).2

/-- At a block's end, the terminator's operands are defined and the slot it takes is not claimed
    dead. -/
theorem qs_termLive {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : QPt sig syms f X F e b blk.body.length) : TermLive X.dead b e blk.term :=
  ⟨term_defined P.wf P.hs hb H.side.reach H.side.pi, fun _ hk =>
    qs_live P hb H.ex (slotTaken_of H.cs (term_wf' P hb) hk)⟩

/-- At a block's end, the terminator goes by a slot not claimed dead to an executable block, and
    the facts hold at the next block state. -/
theorem qs_term {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : QPt sig syms f X F e b blk.body.length) :
    Returns (fun n => match n with
      | .goto e' d => QS f X F (e', some b, d)
      | .done _ => True) (runTerm e blk.term) := by
  have hdef := term_defined P.wf P.hs hb H.side.reach H.side.pi
  refine Returns.mono (Returns.and (runTerm_sem hdef) (runTerm_slot H.cs (term_wf' P hb) hdef))
    fun nx hnx => ?_
  cases nx with
  | done _ => trivial
  | goto e' d =>
    obtain ⟨⟨rfl, -⟩, k, hk, hsl⟩ := hnx
    have hd : d ∈ blk.term.succs := List.mem_of_getElem? hk
    have hnd := qs_live P hb H.ex hsl
    have hEd := (exec_next P.sp P.hB hb H.ex hk hsl).1
    refine ⟨blockInv_of_point P.hv hb H.side.reach H.side.pi hd, fun pblk hp => ?_, H.kb, H.cs,
      ancReach_edge P.hv H.side.anc ⟨blk, hb, hd⟩, hEd, fun p hp => ?_⟩
    · rw [hb] at hp; cases hp; exact H.side.pu
    · simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨H.ex, blk, k, hb, hk, hnd⟩

/-- A block of a block state goes to a block state where the facts hold. -/
theorem qs_step {o : Oracle} (hoi : o.IntRet) (c : Ctx) {s : BState}
    (hS : QS f X F s) :
    Returns (fun n => match n with
      | .goto e d => QS f X F (e, some s.2.2, d)
      | .done _ => True) (stepBlock o c f s.1 s.2.1 s.2.2) := by
  obtain ⟨env, prev, b⟩ := s
  unfold stepBlock
  cases hb : f.block? b with
  | none => exact Returns.stuck _
  | some blk =>
    dsimp only
    refine Returns.bind (qs_enter P hS hb) fun e₁ h₀ => ?_
    have hbody := qs_take P hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    exact Returns.bind hbody fun e₂ H => qs_term P hb H

/-- The block state at the entry: the parameters have no claims. -/
theorem qs_entry {e : Block} (he : f.blocks.head? = some e) {args : List Val}
    (hargs : IntVals args) :
    Returns (fun env => QS f X F (env, none, e.id)) (bind {} f.params args) := by
  have hU := UniqueDefs.of_ssa P.hs
  refine Returns.mono (Returns.and (entry_inv P.wf P.hv he hargs) (returns_bind {} f.params args))
    fun env ⟨hbi, _, hfold⟩ =>
      ⟨hbi, trivial, ?_, ?_, ancReach_entry P.hv he, ?_, fun p hp => by cases hp⟩
  · intro v n hvn
    rw [hfold] at hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he', _⟩
    · rw [kb_param P.kb (defsOf_find hU (param_def (List.of_mem_zip hx).1))]
      exact sat_unknown n
    · simp at he'
  · intro v c0 n hcv hvn
    rw [hfold] at hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he', _⟩
    · have hcl := P.sp.claims _ c0 hcv
      have hp : X.inD.find? x.1.1 = some .param := by
        rw [P.hD]; exact defsOf_find hU (param_def (List.of_mem_zip hx).1)
      rw [hp] at hcl
      cases hcl
    · simp at he'
  · have := P.sp.closed
    unfold execClosed at this
    simp only [Bool.and_eq_true, Option.any_eq_true] at this
    rw [he] at this
    simpa using this.1

/-- `sccp_prune`'s invariant is one the prune's simulation runs on. -/
theorem qs_run {o : Oracle} (hoi : o.IntRet) (c : Ctx) :
    PruneRun o c f X.dead (QS f X F) where
  int _ hS := hS.1.1.int
  root _ _ _ hS hb := phis_nil_of_root P.wf P.hv hb hS.1.2.2.1 hS.1.2.2.2
  edge _ q _ hS := (hS.2.2.2.2.2.2 q rfl).2
  body _ _ _ blk hS hb := Returns.mono (qs_enter P hS hb) fun _ h₀ => by
    have hbody := qs_take P hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    exact Returns.mono hbody fun _ H => qs_termLive P hb H
  step _ hS := qs_step P hoi c hS
  entry _ he _ hargs := qs_entry P he hargs

end spec

/-! ## The step -/

/-- What `sccpPruneReject = none` gives. -/
theorem sccpPruneReject_spec {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : sccpPruneReject f ids s F = none) :
    ∃ is, ids = some is ∧ QSpec sig syms f (ctxOf .sccp f s F) F ∧
      (pruneFunc f F.deadEdges).cfgOk = true ∧
      checkCfgCleanup none (pruneFunc f F.deadEdges) (some is) s = true := by
  rcases ids with _ | is
  · simp [sccpPruneReject] at h
  unfold sccpPruneReject at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  next hssa =>
  split at h
  · cases h
  next hkb =>
  split at h
  · cases h
  next hsc =>
  split at h
  · cases h
  next hcfg =>
  split at h
  · cases h
  next hcc =>
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hssa hkb hsc hcfg hcc
  refine ⟨is, rfl, ⟨hwf, rfl, rfl, rfl, ?_, ?_, ?_, sccpSpec_of hsc⟩, hcfg, hcc⟩
  · simp only [ssaOk, Bool.and_eq_true] at hssa; exact hssa.1
  · simp only [ssaOk, Bool.and_eq_true] at hssa; exact hssa.2
  · rcases Bool.or_eq_true_iff.mp hkb with h | h
    · simp only [List.isEmpty_iff] at h
      simp [kbFactsOk, h, distinct, distinctAux]
    · exact h

/-- An `sccp_prune` step the checker accepts is sound: the output approximates the well-formed
    input on integers. -/
theorem sccpPrune_sound {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : checkSccpPrune f ids s F = true)
    {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  unfold checkSccpPrune at h
  obtain ⟨is, _, P, hcfg, hcc⟩ := sccpPruneReject_spec hwf (Option.isNone_iff_eq_none.mp h)
  have hnr : NoRetHolds none o := fun g _ hg => by simp [noRet] at hg
  exact (cfgCleanup_sound (sig := sig) (syms := syms) ho hoi hnr c (pruneFunc_wf hwf hcfg) hcc).trans
    (prune_sound_of (qs_run P hoi c) hwf ho hoi)

theorem sccpPrune_stepSound : StepSound .sccpPrune :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    sccpPrune_sound hw (by simpa only [checkFunc] using h) ho hoi c

end Fe.Sonatina.Steps.Schemas
