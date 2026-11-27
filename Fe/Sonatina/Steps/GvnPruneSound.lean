import Fe.Sonatina.Steps.GvnPruneInv
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

/-! ## The pruned function -/

theorem pruneFunc_block? (f : Func) (dead : List (Nat × Nat)) (b : Nat) :
    (pruneFunc f dead).block? b =
      (f.block? b).map (pruneBlock (.ofListBy (·.id) f.blocks) dead) := by
  unfold pruneFunc Func.block?
  rw [List.find?_map]
  rfl

theorem pruneFunc_head (f : Func) (dead : List (Nat × Nat)) :
    (pruneFunc f dead).blocks.head? = f.blocks.head?.map (pruneBlock (.ofListBy (·.id) f.blocks) dead) := by
  unfold pruneFunc
  rw [List.head?_map]

/-- A slot the prune keeps still goes to its target. -/
theorem pruneTerm_succ {dead : List (Nat × Nat)} {q k d : Nat} {t : Fe.Sonatina.Term}
    (hk : t.succs[k]? = some d) (hnd : dead.contains (q, k) = false) :
    d ∈ (pruneTerm dead q t).succs := by
  cases t with
  | br c nz z =>
    have hnd' : (q, k) ∉ dead := fun h => by rw [List.contains_iff_mem.mpr h] at hnd; cases hnd
    rcases k with _ | _ | k
    · simp only [Fe.Sonatina.Term.succs, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      unfold pruneTerm
      by_cases h1 : (q, 1) ∈ dead <;> simp [h1, hnd', Fe.Sonatina.Term.succs]
    · simp only [Fe.Sonatina.Term.succs, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hk
      subst hk
      unfold pruneTerm
      by_cases h0 : (q, 0) ∈ dead <;> simp [h0, hnd', Fe.Sonatina.Term.succs]
    · simp [Fe.Sonatina.Term.succs] at hk
  | _ => exact List.mem_of_getElem? hk

/-- The phis of a block entered over a kept slot: each its operand from that predecessor. -/
theorem inc_prune {B : NatMap Block} {dead : List (Nat × Nat)} {T q : Nat} (φ : Phi)
    (hq : ∀ o, keepIn B dead T (o, q) = true) :
    inc { φ with incoming := φ.incoming.filter (keepIn B dead T) } q = inc φ q := by
  unfold inc
  congr 1
  simp only
  induction φ.incoming with
  | nil => rfl
  | cons ob rest ih =>
    rw [List.filter_cons]
    by_cases hq' : ob.2 = q
    · have := hq ob.1
      rw [show ob = (ob.1, q) from Prod.ext rfl hq'] at this ⊢
      simp [this]
    · split
      · simp [hq', ih]
      · simp [hq', ih]

theorem enterOpt_prune {B : NatMap Block} {dead : List (Nat × Nat)} {env : Env} {q : Nat}
    {blk : Block} (hq : ∀ o, keepIn B dead blk.id (o, q) = true) :
    enterOpt env (some q) (pruneBlock B dead blk) = enterOpt env (some q) blk := by
  unfold enterOpt pruneBlock
  simp only [List.map_map]
  rw [List.mapM_map]
  have h1 : (fun phi : Phi => (phi.dst, phi.ty)) ∘
      (fun φ : Phi => { φ with incoming := φ.incoming.filter (keepIn B dead blk.id) }) =
      fun phi => (phi.dst, phi.ty) := rfl
  have h2 : ((fun phi : Phi => some q >>= inc phi >>= opVal env) ∘
      fun φ : Phi => { φ with incoming := φ.incoming.filter (keepIn B dead blk.id) }) =
      fun phi => some q >>= inc phi >>= opVal env := by
    funext φ
    simp only [Function.comp, Option.bind_eq_bind, Option.bind_some, inc_prune φ hq]
  rw [h1, h2]

/-- The pruned function is well formed, given its control flow. -/
theorem pruneFunc_wf {f : Func} {dead : List (Nat × Nat)} (hwf : f.wf sig syms = true)
    (hcfg : (pruneFunc f dead).cfgOk = true) : (pruneFunc f dead).wf sig syms = true := by
  unfold Func.wf at hwf ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at hwf ⊢
  obtain ⟨⟨⟨hm, hw⟩, _⟩, hb⟩ := hwf
  refine ⟨⟨⟨?_, ?_⟩, hcfg⟩, ?_⟩
  · unfold Func.machine at hm ⊢
    simp only [List.all_eq_true] at hm ⊢
    intro b hbm
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hbm
    exact hm b0 hb0
  · unfold Func.wordTyped at hw ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at hw ⊢
    refine ⟨hw.1, fun b hbm => ?_⟩
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hbm
    obtain ⟨h1, h2⟩ := hw.2 b0 hb0
    refine ⟨fun φ hφ => ?_, h2⟩
    obtain ⟨φ0, hφ0, rfl⟩ := List.mem_map.mp hφ
    exact h1 φ0 hφ0
  · intro b hbm
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hbm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb b0 hb0
    refine ⟨⟨fun φ hφ => ?_, h2⟩, ?_⟩
    · obtain ⟨φ0, hφ0, rfl⟩ := List.mem_map.mp hφ
      intro ob hob
      exact h1 φ0 hφ0 ob (List.mem_filter.mp hob).1
    · show (pruneTerm dead b0.id b0.term).wf f.rets.length = true
      cases ht : b0.term with
      | br c nz z =>
        rw [ht] at h3
        simp only [pruneTerm]
        split
        · rfl
        · split
          · rfl
          · exact h3
      | _ => rw [ht] at h3; exact h3

/-! ## The simulation -/

theorem exec_bind_congr {α β : Type} {x : FeM α} {k k' : α → FeM β} {P : α → Prop}
    (hx : Returns P x) (h : ∀ a, P a → ∀ I w, (k' a).exec I w = (k a).exec I w) :
    ∀ I w, (x >>= k').exec I w = (x >>= k).exec I w := by
  intro I w
  rw [Fe.M.exec_bind, Fe.M.exec_bind]
  rcases hxe : x.exec I w with _ | (e | ⟨a, w'⟩)
  · rfl
  · rfl
  · exact h a (hx I w a w' hxe) I w'

section sim

variable {f : Func} {X : StepCtx} {F : StepFacts} {E : NatMap Unit} {dead : List (Nat × Nat)}
  {PU : List UPred} {cls : List (Nat × Operand)} (P : PSpec sig syms f X F E dead PU cls)

include P

/-- The terminator the prune left, at a block's end, goes where the input's goes. -/
theorem prune_term {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : PPt sig syms f F E PU cls e b blk.body.length) :
    ∀ I w, (runTerm e (pruneTerm dead b blk.term)).exec I w = (runTerm e blk.term).exec I w := by
  have hdef := term_defined P.wf P.hs hb H.side.reach H.side.pi
  revert hdef
  have hlive := fun k => ps_live P hb H (k := k)
  revert hlive
  cases blk.term with
  | br c nz z =>
    intro hlive hdef
    obtain ⟨v, hv⟩ := hdef c (List.mem_singleton_self _)
    have hrun : runTerm e (.br c nz z) = pure (.goto e (if v != 0 then nz else z)) := by
      simp only [runTerm]
      rw [evalInt_eq, hv]
      simp only [Steps.lift, pure_bind]
    have hs0 : SlotSem e (.br c nz z) (if v != 0 then 0 else 1) := ⟨v, hv, rfl⟩
    have hl := hlive _ hs0
    intro I w
    simp only [pruneTerm]
    split
    · next h =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      have hv0 : v ≠ 0 := by
        intro h0
        subst h0
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hl
        rw [h.1] at hl; cases hl
      have : (v != 0) = true := by simp [hv0]
      rw [hrun, this]
      rfl
    · split
      · next _ h =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        have hv0 : v = 0 := by
          by_contra h0
          have : (v != 0) = true := by simp [h0]
          rw [this] at hl
          simp only [↓reduceIte] at hl
          rw [h.1] at hl; cases hl
        subst hv0
        rw [hrun]
        rfl
      · rfl
  | _ => intro _ _ I w; rfl

/-- From a block state of the input's run, the pruned input's block runs as the input's. -/
theorem prune_exec {o : Oracle} (hoi : o.IntRet) (c : Ctx) {env : Env} {prev : Option Nat}
    {b : Nat} (hS : PS sig syms f F E dead PU cls (env, prev, b)) :
    ∀ I w, (stepBlock o c (pruneFunc f dead) env prev b).exec I w =
      (stepBlock o c f env prev b).exec I w := by
  unfold stepBlock
  rw [pruneFunc_block?]
  cases hb : f.block? b with
  | none => intro I w; rfl
  | some blk =>
    have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    -- entering reads the same operands
    have henter : enter env prev (pruneBlock (.ofListBy (·.id) f.blocks) dead blk) =
        enter env prev blk := by
      rw [enter_eq, enter_eq]
      congr 1
      cases prev with
      | none =>
        have hph := phis_nil_of_root P.wf P.hv hb hS.1.2.2.1 hS.1.2.2.2
        simp [enterOpt, pruneBlock, hph]
      | some q =>
        obtain ⟨qblk, hqb, _, qblk', kq, hqb', hkq, hnd, _⟩ := hS.2.2.2.2.2 q rfl
        rw [hqb] at hqb'
        cases hqb'
        refine enterOpt_prune fun o => ?_
        have hm : (pruneTerm dead q qblk.term).succs.contains b = true :=
          List.contains_iff_mem.mpr (pruneTerm_succ hkq hnd)
        have hq : (f.blocks.find? fun x => x.id == q) = some qblk := hqb
        rw [hid]
        simp only [keepIn, NatMap.find?_ofListBy, hq, hm, Bool.or_true]
    simp only [Option.map_some]
    rw [henter]
    refine exec_bind_congr (ps_enter P hS hb) fun e₁ h₀ => ?_
    have hbody := ps_take P hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    refine exec_bind_congr hbody fun e₂ H => ?_
    show ∀ I w, (runTerm e₂ (pruneTerm dead blk.id blk.term)).exec I w = _
    rw [hid]
    exact prune_term P hb H

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

/-- **The prune**: the pruned input approximates the input on integers. -/
theorem prune_sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some (pruneFunc f dead)) (some f) := by
  have hm := Func.wf_machine P.wf
  have sim : Sim o c (pruneFunc f dead) f
      (fun s' s => s' = s ∧ PS sig syms f F E dead PU cls s) := Sim.of_steps fun s' s hR => by
    obtain ⟨rfl, hS⟩ := hR
    left
    have happ := Approx.strengthen (Approx.stepBlock ho hoi rfl hm s'.1 hS.1.1.int s'.2.1 s'.2.2)
      (ps_step P hoi c hS)
    intro I w' w hw
    rw [prune_exec P hoi c hS I w']
    have := happ I w' w hw
    revert this
    rcases (stepBlock o c f s'.1 s'.2.1 s'.2.2).exec I w' with _ | (_ | ⟨n', _⟩) <;>
      rcases (stepBlock o c f s'.1 s'.2.1 s'.2.2).exec I w with _ | (_ | ⟨n, _⟩) <;>
      simp only [ResRel] <;> try exact id
    rintro ⟨⟨rfl, hn⟩, hw'⟩
    refine ⟨?_, hw'⟩
    cases n' with
    | goto env d => exact ⟨rfl, hn⟩
    | done v => rfl
  intro args hargs
  unfold runFuncO
  dsimp only
  rw [pruneFunc_head]
  cases he : f.blocks.head? with
  | none => exact Approx.stuck _
  | some e =>
    simp only [Option.map_some]
    show Approx Eq (do let env ← bind {} f.params args; runBlocksO o c (pruneFunc f dead) env none e.id)
      (do let env ← bind {} f.params args; runBlocksO o c f env none e.id)
    exact Approx.bind (Approx.strengthen (Approx.bindVals _ _ _) (ps_entry P he hargs))
      fun env env₀ ⟨e₁, hS⟩ => by
        cases e₁
        exact Sim.approx sim (env, none, e.id) _ ⟨rfl, hS⟩

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
