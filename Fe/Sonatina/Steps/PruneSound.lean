import Fe.Sonatina.Steps.Prune
import Fe.Sonatina.Steps.LowerSwitchesSound

/-!
# Removing dead slots is sound where the run takes none

`prune_sound_of`: the pruned input `pruneFunc f dead` approximates the input on integers, given
an invariant of the input's block states (`PruneRun`) under which a block is entered over a slot
not claimed dead, and at each block's end the slot the terminator takes (`Takes`) is not claimed
dead.  The two run alike, block for block from the same state: a terminator the prune changed goes
where the input's goes (`prune_term_of`), and entering a block over a live edge reads the phi
operand the prune kept (`enterOpt_prune`).  `gvn_prune` (`GvnPruneSound.lean`) and `sccp_prune`
(`SccpPruneSound.lean`) each give the invariant from their facts.
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

/-! ## The live cases of a `br_table` -/

/-- The live cases, the slots numbered from `n`. -/
theorem liveCases_eq (dead : List (Nat × Nat)) (b : Nat) (cases : List (Operand × Nat)) :
    liveCases dead b cases = ((cases.zipIdx 1).filter fun ci => !dead.contains (b, ci.2)).map (·.1) :=
  rfl

theorem liveFrom_sublist (dead : List (Nat × Nat)) (b : Nat) :
    ∀ (cases : List (Operand × Nat)) (n : Nat),
      (((cases.zipIdx n).filter fun ci => !dead.contains (b, ci.2)).map (·.1)).Sublist cases
  | [], _ => by simp
  | c :: cases, n => by
    rw [List.zipIdx_cons, List.filter_cons]
    split
    · simp only [List.map_cons]
      exact (liveFrom_sublist dead b cases (n + 1)).cons_cons c
    · exact (liveFrom_sublist dead b cases (n + 1)).cons c

theorem liveCases_sublist (dead : List (Nat × Nat)) (b : Nat) (cases : List (Operand × Nat)) :
    (liveCases dead b cases).Sublist cases := liveFrom_sublist dead b cases 1

/-- A case of a live slot is a live case. -/
theorem mem_liveFrom {dead : List (Nat × Nat)} {b : Nat} :
    ∀ {cases : List (Operand × Nat)} {n i : Nat} {c : Operand × Nat}, cases[i]? = some c →
      dead.contains (b, i + n) = false →
      c ∈ ((cases.zipIdx n).filter fun ci => !dead.contains (b, ci.2)).map (·.1)
  | [], _, _, _, h, _ => by simp at h
  | c0 :: cases, n, 0, c, h, hd => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.zipIdx_cons, List.filter_cons]
    have hd' : (b, n) ∉ dead := by simpa using hd
    simp [hd']
  | c0 :: cases, n, i + 1, c, h, hd => by
    simp only [List.getElem?_cons_succ] at h
    have := mem_liveFrom (n := n + 1) h (by rw [← hd]; congr 2; omega)
    rw [List.zipIdx_cons, List.filter_cons]
    split
    · exact List.mem_cons_of_mem _ this
    · exact this

/-- The index of the first case whose key is `v`. -/
def caseIdx (v : Nat) : List (Operand × Nat) → Option Nat
  | [] => none
  | c :: cs => if c.1.immVal? == some v then some 0 else (caseIdx v cs).map (· + 1)

theorem look_none_of {v : Nat} : ∀ {cases : List (Operand × Nat)}, caseIdx v cases = none →
    look cases v = none
  | [], _ => rfl
  | c :: cs, h => by
    unfold caseIdx at h
    unfold look
    split at h
    · cases h
    · next hc =>
      simp only [Option.map_eq_none_iff] at h
      have := look_none_of h
      unfold look at this
      simp [hc, this]

theorem look_some_of {v : Nat} : ∀ {cases : List (Operand × Nat)} {i : Nat}, caseIdx v cases = some i →
    ∃ c, cases[i]? = some c ∧ c.1.immVal? = some v ∧ look cases v = some c.2
  | [], _, h => by cases h
  | c :: cs, i, h => by
    unfold caseIdx at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at hc
      exact ⟨c, rfl, hc, by simp [look, hc]⟩
    · next hc =>
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨c', h1, h2, h3⟩ := look_some_of hj
      refine ⟨c', by simpa using h1, h2, ?_⟩
      unfold look at h3 ⊢
      simpa [List.find?_cons, hc] using h3

/-- The live cases look a key up as the cases do, if the first case of the key is live. -/
theorem look_liveFrom (dead : List (Nat × Nat)) (b v : Nat) :
    ∀ (cases : List (Operand × Nat)) (n : Nat),
      (∀ i, caseIdx v cases = some i → dead.contains (b, i + n) = false) →
      look (((cases.zipIdx n).filter fun ci => !dead.contains (b, ci.2)).map (·.1)) v = look cases v
  | [], _, _ => by simp [look]
  | c :: cases, n, h => by
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hc : (c.1.immVal? == some v) = true
    · have hd := h 0 (by simp [caseIdx, hc])
      have hd' : (b, n) ∉ dead := by simpa using hd
      simp [hd', look, hc]
    · have ih := look_liveFrom dead b v cases (n + 1) fun i hi => by
        rw [← h (i + 1) (by simp [caseIdx, hc, hi])]
        congr 2
        omega
      have hl : look (c :: cases) v = look cases v := by
        simp only [Bool.not_eq_true] at hc
        simp [look, hc]
      rw [hl, ← ih]
      split
      · simp only [Bool.not_eq_true] at hc
        simp [look, hc]
      · rfl

/-! ## The slot a terminator takes -/

/-- The slot of a `br_table` with a default taken on scrutinee `v`. -/
def tableSlot (v : Nat) (cases : List (Operand × Nat)) : Nat := ((caseIdx v cases).map (· + 1)).getD 0

/-- Slot `k` is the one terminator `t` takes on `env`. -/
def Takes (env : Env) : Fe.Sonatina.Term → Nat → Prop
  | .jump _, k => k = 0
  | .br c _ _, k => ∃ v, intVal env c = some (256, v) ∧ k = if v != 0 then 0 else 1
  | .brTable s (some _) cases, k => ∃ v, intVal env s = some (256, v) ∧ k = tableSlot v cases
  | _, _ => False

/-- At a block's end: the terminator's operands are defined, and the slot it takes is not
    claimed dead. -/
def TermLive (dead : List (Nat × Nat)) (b : Nat) (env : Env) (t : Fe.Sonatina.Term) : Prop :=
  (∀ x ∈ t.args, ∃ v, intVal env x = some (256, v)) ∧ ∀ k, Takes env t k → dead.contains (b, k) = false

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
  | brTable s dd cases =>
    rcases dd with _ | D
    · exact List.mem_of_getElem? hk
    simp only [Fe.Sonatina.Term.succs, Option.toList_some, List.singleton_append] at hk
    simp only [pruneTerm]
    rcases k with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      rw [hnd]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · simp [Fe.Sonatina.Term.succs]
      · split <;> simp [Fe.Sonatina.Term.succs]
    · simp only [List.getElem?_cons_succ, List.getElem?_map] at hk
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hk
      have hm : c ∈ liveCases dead q cases := mem_liveFrom hc hnd
      split
      · split
        · next h => rw [h] at hm; cases hm
        · next c' h => rw [h, List.mem_singleton] at hm; subst hm; simp [Fe.Sonatina.Term.succs]
        · simp only [Fe.Sonatina.Term.succs, Option.toList_some, List.singleton_append,
            List.mem_cons, List.mem_map]
          exact Or.inr ⟨c, hm, rfl⟩
      · split
        · simp only [Fe.Sonatina.Term.succs, Option.toList_some, List.singleton_append,
            List.mem_cons, List.mem_map]
          exact Or.inr ⟨c, List.mem_of_getElem? hc, rfl⟩
        · split
          · next h =>
            rw [List.isEmpty_iff] at h
            rw [h] at hm; cases hm
          · simp only [Fe.Sonatina.Term.succs, Option.toList_some, List.singleton_append,
              List.mem_cons, List.mem_map]
            exact Or.inr ⟨c, hm, rfl⟩
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

/-! ## Well-formedness -/

theorem distinctAux_of : ∀ (seen : NatMap Unit) (l : List Nat), l.Nodup →
    (∀ x ∈ l, seen.find? x = none) → distinctAux seen l = true
  | _, [], _, _ => rfl
  | seen, x :: xs, hn, hs => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hn
    simp only [distinctAux, Bool.and_eq_true, Option.isNone_iff_eq_none]
    refine ⟨hs x (List.mem_cons_self ..), distinctAux_of _ xs hxs fun y hy => ?_⟩
    rw [NatMap.find?_insert]
    split
    · next h => subst h; exact absurd hy hx
    · exact hs y (List.mem_cons_of_mem _ hy)

theorem distinct_sublist {l l' : List Nat} (hs : l'.Sublist l) (h : distinct l = true) :
    distinct l' = true :=
  distinctAux_of _ _ (hs.nodup (distinct_nodup h)) fun _ _ => by simp

/-- The prune keeps a terminator well formed. -/
theorem pruneTerm_wf {dead : List (Nat × Nat)} {b n : Nat} {t : Fe.Sonatina.Term}
    (h : t.wf n = true) : (pruneTerm dead b t).wf n = true := by
  cases t with
  | br c nz z =>
    simp only [pruneTerm]
    split
    · rfl
    · split
      · rfl
      · exact h
  | brTable s dd cases =>
    rcases dd with _ | D
    · exact h
    have hsub := liveCases_sublist dead b cases
    have htab : (Fe.Sonatina.Term.brTable s (some D) (liveCases dead b cases)).wf n = true := by
      unfold Fe.Sonatina.Term.wf at h ⊢
      simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
      obtain ⟨hargs, ⟨_, hkeys⟩, hd⟩ := h
      refine ⟨fun x hx => ?_, ⟨rfl, fun c hc => hkeys c (hsub.subset hc)⟩,
        distinct_sublist (hsub.filterMap _) hd⟩
      simp only [Fe.Sonatina.Term.args, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨c, hc, rfl⟩
      · exact hargs _ (List.mem_cons_self ..)
      · exact hargs _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (hsub.subset hc)))
    simp only [pruneTerm]
    split
    · split
      · rfl
      · rfl
      · exact htab
    · split
      · exact h
      · split
        · rfl
        · exact htab
  | _ => exact h

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
    refine ⟨⟨fun φ hφ => ?_, h2⟩, pruneTerm_wf h3⟩
    obtain ⟨φ0, hφ0, rfl⟩ := List.mem_map.mp hφ
    intro ob hob
    exact h1 φ0 hφ0 ob (List.mem_filter.mp hob).1

/-! ## The terminator -/

/-- The terminator the prune left goes where the input's goes, when the slot it takes is not
    claimed dead. -/
theorem prune_term_of {e : Env} {dead : List (Nat × Nat)} {b n : Nat} {t : Fe.Sonatina.Term}
    (hwf : t.wf n = true) (H : TermLive dead b e t) :
    runTerm e (pruneTerm dead b t) = runTerm e t := by
  obtain ⟨hdef, hlive⟩ := H
  cases t with
  | br c nz z =>
    obtain ⟨v, hv⟩ := hdef c (List.mem_singleton_self _)
    have hrun : runTerm e (.br c nz z) = pure (.goto e (if v != 0 then nz else z)) := by
      simp only [runTerm]
      rw [evalInt_eq, hv]
      simp only [Steps.lift, pure_bind]
    have hl := hlive _ ⟨v, hv, rfl⟩
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
  | brTable s dd cases =>
    rcases dd with _ | D
    · rfl
    obtain ⟨v, hv⟩ := hdef s (List.mem_cons_self ..)
    have hkeys : ∀ c ∈ cases, c.1.immVal?.isSome = true := by
      unfold Fe.Sonatina.Term.wf at hwf
      simp only [Bool.and_eq_true, List.all_eq_true] at hwf
      exact hwf.2.1.2
    have hl := hlive _ ⟨v, hv, rfl⟩
    -- the live cases look the scrutinee up as the cases do
    have hlook : look (liveCases dead b cases) v = look cases v :=
      look_liveFrom dead b v cases 1 fun i hi => by
        rw [← hl]; simp [tableSlot, hi]
    have hrun := runTerm_table (d := some D) hv hkeys (t := (look cases v).getD D) (by
      cases look cases v <;> rfl)
    -- a dead default: the first case of the scrutinee is live
    have hcase : dead.contains (b, 0) = true → ∃ x, look cases v = some x := by
      intro h0
      cases hc : caseIdx v cases with
      | none =>
        have h0' : tableSlot v cases = 0 := by simp [tableSlot, hc]
        rw [h0', h0] at hl; cases hl
      | some i => obtain ⟨c, _, _, h⟩ := look_some_of hc; exact ⟨_, h⟩
    have hsub : ∀ c ∈ liveCases dead b cases, c.1.immVal?.isSome = true :=
      fun c hc => hkeys c ((liveCases_sublist dead b cases).subset hc)
    simp only [pruneTerm]
    split
    · next h0 =>
      obtain ⟨x, hx⟩ := hcase h0
      split
      · next h => rw [h, hx] at hlook; simp [look] at hlook
      · next c h =>
        rw [h, hx] at hlook
        have hcx : c.2 = x := by
          unfold look at hlook
          simp only [List.find?_cons, List.find?_nil] at hlook
          split at hlook
          · simpa using hlook
          · cases hlook
        rw [hrun, hx, ← hcx]
        rfl
      · rw [runTerm_table (d := some D) hv hsub (t := (look cases v).getD D) (by
          rw [hlook]; cases look cases v <;> rfl), hrun]
    · split
      · rfl
      · split
        · next h =>
          rw [List.isEmpty_iff] at h
          rw [h] at hlook
          have : look cases v = none := by rw [← hlook]; rfl
          rw [hrun, this]
          rfl
        · rw [runTerm_table (d := some D) hv hsub (t := (look cases v).getD D) (by
            rw [hlook]; cases look cases v <;> rfl), hrun]
  | _ => rfl

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

/-- What the prune's simulation needs of an invariant of the input's block states: integers bound;
    the entry has no phis; a block entered over a slot not claimed dead; at a block's end, the
    slot taken not claimed dead; the invariant kept by a step and established at the entry. -/
structure PruneRun (o : Oracle) (c : Ctx) (f : Func) (dead : List (Nat × Nat))
    (Inv : BState → Prop) : Prop where
  int : ∀ s, Inv s → EnvInt s.1
  root : ∀ env b blk, Inv (env, none, b) → f.block? b = some blk → blk.phis = []
  edge : ∀ env q b, Inv (env, some q, b) → ∃ qblk k, f.block? q = some qblk ∧
    qblk.term.succs[k]? = some b ∧ dead.contains (q, k) = false
  body : ∀ env prev b blk, Inv (env, prev, b) → f.block? b = some blk →
    Returns (fun e₁ => Returns (fun e₂ => TermLive dead b e₂ blk.term) (runBodyO o c e₁ blk.body))
      (enter env prev blk)
  step : ∀ s, Inv s → Returns (fun n => match n with
      | .goto e d => Inv (e, some s.2.2, d)
      | .done _ => True) (stepBlock o c f s.1 s.2.1 s.2.2)
  entry : ∀ e, f.blocks.head? = some e → ∀ args, IntVals args →
    Returns (fun env => Inv (env, none, e.id)) (bind {} f.params args)

section sim

variable {o : Oracle} {c : Ctx} {f : Func} {dead : List (Nat × Nat)} {Inv : BState → Prop}
  (P : PruneRun o c f dead Inv)

include P

/-- From a block state of the input's run, the pruned input's block runs as the input's. -/
theorem prune_exec_of (hwf : f.wf sig syms = true) {env : Env} {prev : Option Nat} {b : Nat}
    (hS : Inv (env, prev, b)) :
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
        have hph := P.root env b blk hS hb
        simp [enterOpt, pruneBlock, hph]
      | some q =>
        obtain ⟨qblk, kq, hqb, hkq, hnd⟩ := P.edge env q b hS
        refine enterOpt_prune fun o => ?_
        have hm : (pruneTerm dead q qblk.term).succs.contains b = true :=
          List.contains_iff_mem.mpr (pruneTerm_succ hkq hnd)
        have hq : (f.blocks.find? fun x => x.id == q) = some qblk := hqb
        rw [hid]
        simp only [keepIn, NatMap.find?_ofListBy, hq, hm, Bool.or_true]
    have htw : blk.term.wf f.rets.length = true := by
      have hw := hwf
      unfold Func.wf at hw
      simp only [Bool.and_eq_true, List.all_eq_true] at hw
      exact (hw.2 blk hmem).2
    simp only [Option.map_some]
    rw [henter]
    refine exec_bind_congr (P.body env prev b blk hS hb) fun e₁ h₁ => ?_
    refine exec_bind_congr h₁ fun e₂ H => ?_
    show ∀ I w, (runTerm e₂ (pruneTerm dead blk.id blk.term)).exec I w = _
    rw [hid, prune_term_of htw H]
    exact fun _ _ => rfl

/-- **The prune**: the pruned input approximates the input on integers. -/
theorem prune_sound_of (hwf : f.wf sig syms = true) (ho : Oracle.Mono o) (hoi : o.IntRet) :
    FuncRef o c (some (pruneFunc f dead)) (some f) := by
  have hm := Func.wf_machine hwf
  have sim : Sim o c (pruneFunc f dead) f (fun s' s => s' = s ∧ Inv s) := Sim.of_steps fun s' s hR => by
    obtain ⟨rfl, hS⟩ := hR
    left
    have happ := Approx.strengthen (Approx.stepBlock ho hoi rfl hm s'.1 (P.int _ hS) s'.2.1 s'.2.2)
      (P.step _ hS)
    intro I w' w hw
    rw [prune_exec_of P hwf hS I w']
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
    exact Approx.bind (Approx.strengthen (Approx.bindVals _ _ _) (P.entry e he args hargs))
      fun env env₀ ⟨e₁, hS⟩ => by
        cases e₁
        exact Sim.approx sim (env, none, e.id) _ ⟨rfl, hS⟩

end sim

end Fe.Sonatina.Steps.Schemas
