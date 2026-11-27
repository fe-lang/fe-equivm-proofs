import Fe.Sonatina.Steps.GvnPruneInv
import Fe.Sonatina.Steps.PruneSound
import Fe.Sonatina.Steps.CfgCleanupSound

/-!
# `gvn_prune` is sound

`gvnPrune_sound` composes two approximations at the pruned input `pruneFunc f dead`:

- `prune_sound`: the pruned input approximates the input.  The two run alike, block for block
  from the same state: the run of the input never takes a dead slot (`ps_live`, on the facts of
  `prune_reaches`'s invariant `PS`), so a `br` the prune turned into a `jump` goes where the input's
  goes, and entering a block over a live edge reads the phi operand the prune kept.  Each step of
  the pruned input equals the input's, run on the same world (`prune_exec`).
- `cfgCleanup_sound` with no summary table: the output approximates the pruned input, which is
  well formed (`pruneFunc_wf`, with the control flow the check checks).
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-! ## The simulation (`PruneSound.lean`), from `gvn_prune`'s invariant -/

section sim

variable {f : Func} {X : StepCtx} {F : StepFacts} {E : NatMap Unit} {dead : List (Nat × Nat)}
  {PU : List UPred} {cls : List (Nat × Operand)} (P : PSpec sig syms f X F E dead PU cls)

include P

/-- At a block's end, the terminator's operands are defined and the slot it takes is not claimed
    dead: a `br`'s by `ps_live`, and no other terminator of an executable block has a dead slot
    (`deadOk`). -/
theorem ps_termLive {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : PPt sig syms f F E PU cls e b blk.body.length) : TermLive dead b e blk.term := by
  refine ⟨term_defined P.wf P.hs hb H.side.reach H.side.pi, fun k hk => ?_⟩
  have hib : X.inB.find? b = some blk := by rw [P.hB, NatMap.find?_ofListBy]; exact hb
  cases ht : blk.term with
  | br c nz z => rw [ht] at hk; exact ps_live P hb H (by rw [ht]; exact hk)
  | _ =>
    cases hc : dead.contains (b, k)
    · rfl
    · exfalso
      have hok := P.dok (b, k) (List.contains_iff_mem.mp hc)
      simp only [deadOk, Bool.or_eq_true] at hok
      rcases hok with hno | hok
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp H.ex
        rw [hx] at hno; cases hno
      · simp [hib, ht] at hok

/-- The terminator the prune left, at a block's end, goes where the input's goes. -/
theorem prune_term {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : PPt sig syms f F E PU cls e b blk.body.length) :
    ∀ I w, (runTerm e (pruneTerm dead b blk.term)).exec I w = (runTerm e blk.term).exec I w := by
  have htw : blk.term.wf f.rets.length = true := by
    have hw := P.wf
    unfold Func.wf at hw
    simp only [Bool.and_eq_true, List.all_eq_true] at hw
    exact (hw.2 blk (List.mem_of_find?_eq_some hb)).2
  intro I w
  rw [prune_term_of htw (ps_termLive P hb H)]

/-- The block state at the entry. -/
theorem ps_entry {e : Block} (he : f.blocks.head? = some e) {args : List Val}
    (hargs : IntVals args) :
    Returns (fun env => PS sig syms f F E dead PU cls (env, none, e.id)) (bind {} f.params args) := by
  have hU := UniqueDefs.of_ssa P.hs
  refine Returns.mono (Returns.and (entry_inv P.wf P.hv he hargs) (returns_bind {} f.params args))
    fun env ⟨hbi, _, hfold⟩ => ⟨hbi, trivial, ?_, ancReach_entry P.hv he, ?_, fun p hp => by cases hp⟩
  · intro v n hvn
    rw [hfold] at hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he', _⟩
    · rw [kb_param P.kb (defsOf_find hU (param_def (List.of_mem_zip hx).1))]
      exact sat_unknown n
    · simp at he'
  · have := P.closed
    unfold execClosed at this
    simp only [Bool.and_eq_true, Option.any_eq_true] at this
    rw [he] at this
    simpa using this.1

/-- `gvn_prune`'s invariant is one the prune's simulation runs on. -/
theorem ps_run {o : Oracle} (hoi : o.IntRet) (c : Ctx) :
    PruneRun o c f dead (PS sig syms f F E dead PU cls) where
  int _ hS := hS.1.1.int
  root _ _ _ hS hb := phis_nil_of_root P.wf P.hv hb hS.1.2.2.1 hS.1.2.2.2
  edge _ q _ hS := by
    obtain ⟨qblk, hqb, _, qblk', kq, hqb', hkq, hnd, _⟩ := hS.2.2.2.2.2 q rfl
    rw [hqb] at hqb'
    cases hqb'
    exact ⟨qblk, kq, hqb, hkq, hnd⟩
  body _ _ _ blk hS hb := Returns.mono (ps_enter P hS hb) fun _ h₀ => by
    have hbody := ps_take P hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    exact Returns.mono hbody fun _ H => ps_termLive P hb H
  step _ hS := ps_step P hoi c hS
  entry _ he _ hargs := ps_entry P he hargs

/-- From a block state of the input's run, the pruned input's block runs as the input's. -/
theorem prune_exec {o : Oracle} (hoi : o.IntRet) (c : Ctx) {env : Env} {prev : Option Nat}
    {b : Nat} (hS : PS sig syms f F E dead PU cls (env, prev, b)) :
    ∀ I w, (stepBlock o c (pruneFunc f dead) env prev b).exec I w =
      (stepBlock o c f env prev b).exec I w :=
  prune_exec_of (ps_run P hoi c) P.wf hS

/-- **The prune**: the pruned input approximates the input on integers. -/
theorem prune_sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some (pruneFunc f dead)) (some f) :=
  prune_sound_of (ps_run P hoi c) P.wf ho hoi

end sim

/-! ## The step -/

/-- What `gvnPruneReject = none` gives. -/
theorem gvnPruneReject_spec {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : gvnPruneReject f ids s F = none) :
    ∃ is G, ids = some is ∧ F.gvn = some G ∧
      PSpec sig syms f (prunePrep f s F G).1 F (prunePrep f s F G).2.1 G.deadEdges
        (prunePrep f s F G).2.2.1 (prunePrep f s F G).2.2.2 ∧
      (pruneFunc f G.deadEdges).cfgOk = true ∧
      checkCfgCleanup none (pruneFunc f G.deadEdges) (some is) s = true := by
  rcases ids with _ | is
  · simp [gvnPruneReject] at h
  rcases hG : F.gvn with _ | G
  · simp [gvnPruneReject, hG] at h
  unfold gvnPruneReject at h
  simp only [hG] at h
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
  next hcl =>
  split at h
  · cases h
  next hsh =>
  split at h
  · cases h
  next hcert =>
  split at h
  · cases h
  next hfind =>
  split at h
  · cases h
  next hcfg =>
  split at h
  · cases h
  next hcc =>
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hssa hkb hcl hsh hcert hcfg hcc
  refine ⟨is, G, rfl, rfl, ⟨hwf, rfl, rfl, rfl, rfl, ?_, ?_, ?_, hcl, hcert, ?_, ?_⟩, hcfg, hcc⟩
  · simp only [ssaOk, Bool.and_eq_true] at hssa; exact hssa.1
  · simp only [ssaOk, Bool.and_eq_true] at hssa; exact hssa.2
  · rcases Bool.or_eq_true_iff.mp hkb with h | h
    · simp only [List.isEmpty_iff] at h
      simp [kbFactsOk, h, distinct, distinctAux]
    · exact h
  · intro bk hbk
    have := List.find?_eq_none.mp hfind bk hbk
    simpa using this
  · intro u hu
    obtain ⟨e, _, he⟩ := List.mem_filterMap.mp hu
    exact ⟨e, he⟩

/-- A `gvn_prune` step the checker accepts is sound: the output approximates the well-formed
    input on integers. -/
theorem gvnPrune_sound {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap} {F : StepFacts}
    (hwf : f.wf sig syms = true) (h : checkGvnPrune f ids s F = true) {o : Oracle}
    (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) : FuncRef o c (some s.func) (some f) := by
  unfold checkGvnPrune at h
  obtain ⟨is, G, _, _, P, hcfg, hcc⟩ := gvnPruneReject_spec hwf (Option.isNone_iff_eq_none.mp h)
  have hnr : NoRetHolds none o := fun g _ hg => by simp [noRet] at hg
  exact (cfgCleanup_sound (sig := sig) (syms := syms) ho hoi hnr c (pruneFunc_wf hwf hcfg) hcc).trans
    (prune_sound P ho hoi c)

theorem gvnPrune_stepSound : StepSound .gvnPrune :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    gvnPrune_sound hw (by simpa only [checkFunc] using h) ho hoi c

end Fe.Sonatina.Steps.Schemas
