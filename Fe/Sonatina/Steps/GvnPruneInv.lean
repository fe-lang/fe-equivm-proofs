import Fe.Sonatina.Steps.GvnInv
import Fe.Sonatina.Steps.SchemasStepSound
import Fe.Sonatina.Steps.GvnPrune

/-!
# `gvn_prune`'s facts along the input's run

Along a run of the unpruned input from its entry, at every block state (`PS`, `prune_reaches`):

- the block is executable, entered over a slot not claimed dead (`EdgeOk`): a terminator goes by a
  slot it takes (`runTerm_sem`, `SlotSem`), and a dead slot of an executable block is one its `br`
  does not take (`deadOk`), so the run never takes a dead slot and stays in the executable set;
- each usable predicate holds wherever its target dominates (`PredInv`): entering the target over
  its one live slot, by the terminator's semantics (`predOk_sound`); then it stays, as its sides are
  defined strictly above the target and so are not rebound while the target dominates the point,
  and every other entry into a block the target dominates comes from a block the target dominates;
- the classes hold (`GInv`): a statement's pair as in `gvn_rewrite` (`ginv_stmt`), a phi's from the
  predecessor's end, its operands' terms there through the predicates (`gTermAt_ok`,
  `ginv_enterP`);
- definedness, L2 and the known bits, as for the schema checkers.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-- The usable predicates hold at block `b`: each whose target is a tree ancestor-or-self of `b`. -/
def PredInv (f : Func) (PU : List UPred) (e : Env) (b : Nat) : Prop :=
  ∀ u ∈ PU, (domTree f).Anc u.1 b → opVal e u.2.2.2.1 = opVal e u.2.2.2.2

/-- What `usePred` checks of a usable predicate. -/
theorem usePred_spec {X : StepCtx} {f : Func} {E : NatMap Unit} {dead : List (Nat × Nat)}
    {e : Nat × Nat × GOp × GOp} {u : UPred} (h : usePred X f E dead e = some u) :
    ∃ pb, X.inB.find? u.2.1 = some pb ∧ pb.term.succs[u.2.2.1]? = some u.1 ∧
      u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧
      predOk X.K pb.term u.2.2.1 u.2.2.2.1 u.2.2.2.2 = true ∧
      X.above u.1 u.2.2.2.1 = true ∧ X.above u.1 u.2.2.2.2 = true ∧
      inSlots f E dead u.1 = [(u.2.1, u.2.2.1)] := by
  unfold usePred at h
  dsimp only at h
  split at h
  · next pb hpb =>
    split at h
    · next T hT =>
      split at h
      · next hc =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
        exact ⟨pb, hpb, hT, h1, h2, h3, h4, h5, h6⟩
      · cases h
    · cases h
  · cases h

/-- A slot into `T` of an executable block not claimed dead is one of `inSlots`. -/
theorem mem_inSlots {f : Func} {E : NatMap Unit} {dead : List (Nat × Nat)} {T b k : Nat}
    {blk : Block} (hb : f.block? b = some blk) (hE : (E.find? b).isSome = true)
    (hk : blk.term.succs[k]? = some T) (hd : dead.contains (b, k) = false) :
    (b, k) ∈ inSlots f E dead T := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  unfold inSlots
  refine List.mem_flatMap.mpr ⟨blk, hmem, ?_⟩
  rw [hid, if_pos hE]
  refine List.mem_map.mpr ⟨(T, k), List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr hk, ?_⟩, rfl⟩
  simp only [beq_self_eq_true, hd, Bool.not_false, Bool.and_self]

/-! ## The slot a terminator takes -/

/-- Slot `k` of terminator `t` is the one it takes on `env`: a `br`'s by its condition; a
    `br_table`'s case slot only where the scrutinee equals the case's key. -/
def SlotSem (env : Env) : Fe.Sonatina.Term → Nat → Prop
  | .br c _ _, k => ∃ v, intVal env c = some (256, v) ∧ k = if v != 0 then 0 else 1
  | .brTable s d cases, k => ∃ v, intVal env s = some (256, v) ∧
      ∀ i, k = i + (if d.isSome then 1 else 0) → ∀ ci, cases[i]? = some ci →
        intVal env ci.1 = some (256, v)
  | _, _ => True

theorem find_case {env : Env} {v : Nat} : ∀ {cases : List (Operand × Nat)} {vals : List (Nat × Nat)},
    List.Forall₂ (fun (ci : Operand × Nat) (a : Nat × Nat) =>
      intVal env ci.1 = some (256, a.1) ∧ a.2 = ci.2) cases vals →
    ∀ {a : Nat × Nat}, vals.find? (·.1 == v) = some a →
      ∃ (i : Nat) (ci : Operand × Nat), cases[i]? = some ci ∧ ci.2 = a.2 ∧
        intVal env ci.1 = some (256, v)
  | [], [], .nil, _, h => by simp at h
  | ci :: cases, b :: vals, .cons ⟨hi, hb⟩ hrest, a, h => by
    rw [List.find?_cons] at h
    by_cases hv : b.1 = v
    · have hbv : (b.1 == v) = true := by simp [hv]
      rw [hbv] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨0, ci, rfl, hb.symm, hv ▸ hi⟩
    · have hbv : (b.1 == v) = false := by simp [hv]
      rw [hbv] at h
      obtain ⟨i, cj, h1, h2, h3⟩ := find_case hrest h
      exact ⟨i + 1, cj, by simpa using h1, h2, h3⟩

/-- A terminator goes by a slot it takes, on the environment it leaves. -/
theorem runTerm_sem {env : Env} {t : Fe.Sonatina.Term}
    (hdef : ∀ o ∈ t.args, ∃ v, intVal env o = some (256, v)) :
    Returns (fun nx => match nx with
      | .goto e d => e = env ∧ ∃ k, t.succs[k]? = some d ∧ SlotSem env t k
      | .done _ => True) (runTerm env t) := by
  cases t with
  | jump d => exact Returns.pure ⟨rfl, 0, rfl, trivial⟩
  | br c nz z =>
    obtain ⟨v, hv⟩ := hdef c (List.mem_singleton_self _)
    simp only [runTerm]
    rw [evalInt_eq, hv]
    simp only [Steps.lift, pure_bind]
    refine Returns.pure ⟨rfl, if v != 0 then 0 else 1, ?_, v, hv, rfl⟩
    by_cases h : v != 0 <;> simp [h, Fe.Sonatina.Term.succs]
  | brTable sc d cases =>
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
    split
    · next dest hd =>
      refine Returns.pure ⟨rfl, ?_⟩
      rcases hf : vals.find? (·.1 == v) with _ | a
      · rw [hf] at hd
        simp only [Option.map_none, orElse_none'] at hd
        subst hd
        refine ⟨0, rfl, v, hv, fun i hi => ?_⟩
        simp at hi
      · rw [hf] at hd
        simp only [Option.map_some, orElse_some', Option.some.injEq] at hd
        subst hd
        obtain ⟨i, ci, hci, h2, h3⟩ := find_case hvals hf
        refine ⟨i + (if d.isSome then 1 else 0), ?_, v, hv, fun i' hi' cj hcj => ?_⟩
        · cases d <;> simp [Fe.Sonatina.Term.succs, hci, h2]
        · have : i' = i := by omega
          subst this
          rw [hci] at hcj
          cases hcj
          exact h3
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

/-- A word whose bits above bit 0 are known zero is `0` or `1`. -/
theorem le_one_of_bool {f : KB} {x : Nat} (hx : x < W) (hs : f.Sat x) (h : f.allZero (M ^^^ 1) = true) :
    x ≤ 1 := by
  simp only [KB.allZero, beq_iff_eq] at h
  have hb : ∀ i, 1 ≤ i → x.testBit i = false := by
    intro i hi
    by_cases h256 : i < 256
    · have h1 : (M ^^^ 1).testBit i = true := by
        have h1' : Nat.testBit 1 i = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        simp [Nat.testBit_xor, testBit_M, h256, h1']
      have h2 : f.kz.testBit i = true := by
        have := congrArg (·.testBit i) h
        simp only [Nat.testBit_and, h1, Bool.and_true] at this
        exact this
      have h3 := congrArg (·.testBit i) hs.1
      simp only [Nat.testBit_and, h2, Bool.and_true, Nat.zero_testBit] at h3
      exact h3
    · exact testBit_hi hx (by omega)
  have : x < 2 ^ 1 := Nat.lt_pow_two_of_testBit x hb
  omega

/-- What a usable predicate says holds once its slot is taken. -/
theorem predOk_sound {K : NatMap KB} {env : Env} (hw : EnvW env) (hkb : KBHolds K env)
    {t : Fe.Sonatina.Term} {n k : Nat} {l r : Operand} (htw : t.wf n = true)
    (hp : predOk K t k l r = true) (hs : SlotSem env t k) : opVal env l = opVal env r := by
  have hargs : ∀ o ∈ t.args, o.wf = true := by
    unfold Fe.Sonatina.Term.wf at htw
    simp only [Bool.and_eq_true, List.all_eq_true] at htw
    exact htw.1
  cases t with
  | br c nz z =>
    obtain ⟨v, hv, hk⟩ := hs
    simp only [predOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, ⟨⟨rfl, rfl⟩, hb⟩ | ⟨rfl, rfl⟩⟩ := hp
    · have hv0 : v ≠ 0 := by
        intro h0; subst h0; simp at hk
      obtain ⟨hlt, hsat⟩ := opFact_sat hw hkb (hargs l (List.mem_singleton_self _)) hv
      have h1 := le_one_of_bool hlt hsat hb
      have : v = 1 := by omega
      subst this
      rw [opVal_of_intVal hv]; rfl
    · have hv0 : v = 0 := by
        by_contra h0
        have : (v != 0) = true := by simp [h0]
        rw [this] at hk; simp at hk
      subst hv0
      rw [opVal_of_intVal hv]; rfl
  | brTable sc d cases =>
    obtain ⟨v, hv, hcase⟩ := hs
    simp only [predOk, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    cases d with
    | none =>
      rcases hci : cases[k]? with _ | ci <;> rw [hci] at hp
      · cases hp
      simp only [Option.any_some, beq_iff_eq] at hp
      subst hp
      rw [opVal_of_intVal hv, opVal_of_intVal (hcase k (by simp) ci hci)]
    | some dd =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
      obtain ⟨hk0, hp⟩ := hp
      rcases hci : cases[k - 1]? with _ | ci <;> rw [hci] at hp
      · cases hp
      simp only [Option.any_some, beq_iff_eq] at hp
      subst hp
      rw [opVal_of_intVal hv, opVal_of_intVal (hcase (k - 1) (by simp; omega) ci hci)]
  | _ => simp [predOk] at hp

section ctx

variable {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
  (hn : (f.blocks.map (·.id)).Nodup) {e0 : Nat} (hroot : (domTree f).idom.find? e0 = none)

include hD hT hn hroot in
/-- A value defined strictly above `T` dominates every point of a block that `T` dominates. -/
theorem above_opAt {T b k : Nat} (hbroot : (domTree f).Anc e0 b) {x : Operand}
    (h : X.above T x = true) (hTb : (domTree f).Anc T b) : OpAt f b k x := by
  intro w hw
  rcases above_spec h w hw with hp | ⟨d, hne, ha, hd⟩
  · rw [hD] at hp
    rcases mem_defList (defsOf_mem hp) with ⟨_, hpm⟩ | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, _, h1, _⟩
    · exact Or.inl hpm
    · cases h1
    · cases h1
  · rw [hT] at ha
    have hdb : d ≠ b := fun hdb => by
      subst hdb
      exact hne (DomTree.anc_antisymm hroot hbroot hTb ha).symm
    refine Or.inr (Or.inr ⟨d, hdb, ha.trans hTb, ?_⟩)
    rcases hd with hd | ⟨j, hd⟩
    · rw [hD] at hd
      rcases mem_defList (defsOf_mem hd) with ⟨h1, _⟩ | ⟨bb, hbb, φ, hφ, h1, rfl⟩ |
          ⟨_, _, _, _, _, h1, _⟩
      · cases h1
      · cases h1
        exact ⟨bb, block?_of_mem hn hbb, Or.inl (List.mem_map_of_mem hφ)⟩
      · cases h1
    · rw [hD] at hd
      rcases mem_defList (defsOf_mem hd) with ⟨h1, _⟩ | ⟨_, _, _, _, h1, _⟩ |
          ⟨bb, hbb, k', s, hs, h1, hw'⟩
      · cases h1
      · cases h1
      · simp only [Def.stmt.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨bb, block?_of_mem hn hbb, Or.inr ⟨s, List.mem_of_getElem? hs, hw'⟩⟩

include hD hT hn hroot in
/-- A value defined strictly above `T` is no phi of a block that `T` dominates. -/
theorem above_not_phi {T b : Nat} (hbroot : (domTree f).Anc e0 b) {x : Operand}
    (h : X.above T x = true) (hTb : (domTree f).Anc T b) {blk : Block} (hb : f.block? b = some blk)
    (hU : UniqueDefs f) : ∀ w, x = .var w → w ∉ blk.phis.map (·.dst) := by
  intro w hw hm
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hm
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hdφ := hid ▸ phi_def hmem hφ
  rcases above_spec h _ hw with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
  · rw [hD] at hp; cases hU.fn (defsOf_mem hp) hdφ
  · rw [hD] at hd
    have hdb := Def.phi.inj (hU.fn (defsOf_mem hd) hdφ)
    subst hdb
    rw [hT] at ha
    exact hne (DomTree.anc_antisymm hroot hbroot hTb ha).symm
  · rw [hD] at hd; cases hU.fn (defsOf_mem hd) hdφ

variable {cls : List (Nat × Operand)} (hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true)
  {PU : List UPred}
  (hPU : ∀ u ∈ PU, u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧ X.above u.1 u.2.2.2.1 = true ∧
    X.above u.1 u.2.2.2.2 = true)

include hD hT hn hroot hcl hPU in
/-- An operand's term at a point of block `b`, through its representative and the predicates that
    hold there, evaluates to its word. -/
theorem gTermAt_ok (hU : UniqueDefs f) {b k : Nat} (hbroot : (domTree f).Anc e0 b) {e : Env}
    (hG : GInv f cls e b k) (hP : PredInv f PU e b) (hW : Words f e b k) {o : Operand}
    (hw : o.wf = true) (ho : OpAt f b k o) :
    ∃ n, opVal e o = some (.int 256 n) ∧ n < W ∧ TermOk e (gTermAt X (.ofList cls) PU b o) n := by
  have G : ∀ {o : Operand}, o.wf = true → OpAt f b k o →
      ∃ n, opVal e o = some (.int 256 n) ∧ n < W ∧ TermOk e (gTerm (.ofList cls) o) n :=
    fun hw ho => gTerm_ok hD hT hU hn hroot hcl hbroot hG hW hw ho
  obtain ⟨n, h1, h2, h3⟩ := G hw ho
  refine ⟨n, h1, h2, ?_⟩
  -- a predicate `l = r` that holds at `b`, `l` with the representative `a` of `o`: `r`'s term
  have side : ∀ {a : Nat} {l r : Operand}, gTerm (.ofList cls) o = .atom a →
      gTerm (.ofList cls) l = .atom a → l.wf = true → r.wf = true → OpAt f b k l → OpAt f b k r →
      opVal e l = opVal e r → TermOk e (gTerm (.ofList cls) r) n := by
    intro a l r ha hl hlw hrw hlo hro hlr
    obtain ⟨nl, hl1, _, hl3⟩ := G hlw hlo
    obtain ⟨nr, hr1, _, hr3⟩ := G hrw hro
    rw [ha] at h3
    rw [hl] at hl3
    have hnl : nl = n := by rw [← hl3.1, ← h3.1]
    subst hnl
    rw [hlr, hr1] at hl1
    cases hl1
    exact hr3
  unfold gTermAt
  split
  · next a ha =>
    rcases hf1 : PU.find? (fun u => X.T.anc u.1 b && gTerm (.ofList cls) u.2.2.2.1 == .atom a) with
      _ | u <;> rw [hf1]
    · rcases hf2 : PU.find? (fun u => X.T.anc u.1 b && gTerm (.ofList cls) u.2.2.2.2 == .atom a) with
        _ | u <;> simp only [hf2]
      · rw [← ha]; exact h3
      · have hm := List.mem_of_find?_eq_some hf2
        have hc := List.find?_some hf2
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hTb, hr⟩ := hc
        rw [hT] at hTb
        have hTb' := DomTree.anc_sound hTb
        obtain ⟨hlw, hrw, hla, hra⟩ := hPU u hm
        exact side ha hr hrw hlw (above_opAt hD hT hn hroot hbroot hra hTb')
          (above_opAt hD hT hn hroot hbroot hla hTb') (hP u hm hTb').symm
    · have hm := List.mem_of_find?_eq_some hf1
      have hc := List.find?_some hf1
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hTb, hl⟩ := hc
      rw [hT] at hTb
      have hTb' := DomTree.anc_sound hTb
      obtain ⟨hlw, hrw, hla, hra⟩ := hPU u hm
      exact side ha hl hlw hrw (above_opAt hD hT hn hroot hbroot hla hTb')
        (above_opAt hD hT hn hroot hbroot hra hTb') (hP u hm hTb')
  · exact h3

end ctx

/-! ## The classes' checks -/

theorem pairOkP_stmt {X : StepCtx} {E : NatMap Unit} {dead : List (Nat × Nat)} {C : NatMap Operand}
    {PU : List UPred} {v : Nat} {r : Operand} {B j : Nat} (hv : X.inD.find? v = some (.stmt B j)) :
    X.pairOkP E dead C PU v r = X.pairOk C v r := by
  simp only [StepCtx.pairOkP, hv]

theorem pairOkP_param {X : StepCtx} {E : NatMap Unit} {dead : List (Nat × Nat)} {C : NatMap Operand}
    {PU : List UPred} {v : Nat} {r : Operand} (h : X.pairOkP E dead C PU v r = true)
    (hv : X.inD.find? v = some .param) : False := by
  simp [StepCtx.pairOkP, hv] at h

/-- A pair of a phi's result: from each executable edge, the operands' terms at the
    predecessor's end. -/
theorem pairOkP_phi {X : StepCtx} {E : NatMap Unit} {dead : List (Nat × Nat)} {C : NatMap Operand}
    {PU : List UPred} {v : Nat} {r : Operand} {B : Nat} (h : X.pairOkP E dead C PU v r = true)
    (hv : X.inD.find? v = some (.phi B)) :
    ∃ φ, phiOf X.inB B v = some φ ∧
      ((∃ w ψ, r = .var w ∧ X.inD.find? w = some (.phi B) ∧ phiOf X.inB B w = some ψ ∧
        ∀ ob ∈ φ.incoming, edgeExec X.inB E dead ob.2 B = true →
          ∃ o, inc ψ ob.2 = some o ∧ gTermAt X C PU ob.2 ob.1 = gTermAt X C PU ob.2 o) ∨
      (X.above B r = true ∧ ∀ ob ∈ φ.incoming, edgeExec X.inB E dead ob.2 B = true →
        gTermAt X C PU ob.2 ob.1 = gTermAt X C PU ob.2 r)) := by
  simp only [StepCtx.pairOkP, hv] at h
  rcases hφ : phiOf X.inB B v with _ | φ
  · rw [hφ] at h; cases h
  rw [hφ, Option.any_some, Bool.or_eq_true] at h
  refine ⟨φ, rfl, ?_⟩
  rcases h with h | h
  · left
    cases r with
    | imm => cases h
    | var w =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hw, h⟩ := h
      rcases hψ : phiOf X.inB B w with _ | ψ
      · rw [hψ] at h; cases h
      rw [hψ, Option.any_some, List.all_eq_true] at h
      refine ⟨w, ψ, rfl, hw, hψ, fun ob hob hex => ?_⟩
      have := h ob (List.mem_filter.mpr ⟨hob, hex⟩)
      rcases hi : inc ψ ob.2 with _ | o
      · rw [hi] at this; cases this
      rw [hi, Option.any_some, beq_iff_eq] at this
      exact ⟨o, rfl, this⟩
  · right
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    exact ⟨h.1, fun ob hob hex => h.2 ob (List.mem_filter.mpr ⟨hob, hex⟩)⟩

theorem clsOkP_spec {X : StepCtx} {E : NatMap Unit} {dead : List (Nat × Nat)} {PU : List UPred}
    {cls : List (Nat × Operand)} (h : X.clsOkP E dead PU cls = true) :
    ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true ∧
      X.pairOkP E dead (.ofList cls) PU v r = true := by
  intro v r hm
  have := List.all_eq_true.mp h (v, r) hm
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem ginv_rootP {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hs : ssa f (domTree f) = true)
    {E : NatMap Unit} {dead : List (Nat × Nat)} {PU : List UPred} {cls : List (Nat × Operand)}
    (hok : X.clsOkP E dead PU cls = true) (e : Env) {b : Nat}
    (hroot : (domTree f).idom.find? b = none) {blk : Block} (hb : f.block? b = some blk)
    (hph : blk.phis = []) : GInv f cls e b 0 := by
  intro v r hvr hdom
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (domAt_root hroot hb hph hdom)
  exact (pairOkP_param (clsOkP_spec hok _ r hvr).2.2
    (hD ▸ defsOf_find (UniqueDefs.of_ssa hs) (param_def hp))).elim

/-- Entering a block over an executable edge keeps the classes, and establishes those of its
    phis, from the terms at the predecessor's end through the predicates that hold there. -/
theorem ginv_enterP {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) (hwf : f.wf sig syms = true)
    (hs : ssa f (domTree f) = true) {E : NatMap Unit} {dead : List (Nat × Nat)} {PU : List UPred}
    {cls : List (Nat × Operand)} (hok : X.clsOkP E dead PU cls = true)
    (hPU : ∀ u ∈ PU, u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧ X.above u.1 u.2.2.2.1 = true ∧
      X.above u.1 u.2.2.2.2 = true)
    {env : Env} {q b : Nat} (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block}
    (hqb : f.block? q = some qblk) (SP : SidePt sig syms f env q qblk.body.length)
    (hGq : GInv f cls env q qblk.body.length) (hPq : PredInv f PU env q)
    (hex : edgeExec X.inB E dead q b = true) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) : GInv f cls e₁ b 0 := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have hv := SP.valid
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e1, _, hroot, hbrootq⟩ := SP.root
  have hbroot : (domTree f).Anc e1.id b := hid ▸ DomTree.valid_root hv (by assumption) hmem
    (hid ▸ hi.2.2.1)
  have hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true := fun v r h =>
    ⟨(clsOkP_spec hok v r h).1, (clsOkP_spec hok v r h).2.1⟩
  have G : ∀ {o : Operand}, o.wf = true → OpAt f q qblk.body.length o →
      ∃ n, opVal env o = some (.int 256 n) ∧ n < W ∧ TermOk env (gTerm (.ofList cls) o) n :=
    fun hw ho => gTerm_ok hD hT hU hn hroot hcl hbrootq hGq SP.words hw ho
  have GA : ∀ {o : Operand}, o.wf = true → OpAt f q qblk.body.length o →
      ∃ n, opVal env o = some (.int 256 n) ∧ n < W ∧
        TermOk env (gTermAt X (.ofList cls) PU q o) n :=
    fun hw ho => gTermAt_ok hD hT hn hroot hcl hPU hU hbrootq hGq hPq SP.words hw ho
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  have hkeep : ∀ u, u ∉ blk.phis.map (·.dst) →
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[u]? = env[u]? :=
    fun u hu => fold_get_not _ _ _ (by rw [hkeys]; exact hu)
  have hqr := hi.2.2.2.1
  have hssa := (ssa_block hs hmem (hid ▸ hi.2.2.1)).1
  have phival : ∀ φ ∈ blk.phis, ∃ o n, (o, q) ∈ φ.incoming ∧ inc φ q = some o ∧ o.wf = true ∧
      OpAt f q qblk.body.length o ∧ opVal env o = some (.int 256 n) ∧
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[φ.dst]? =
        some (.int 256 n) := by
    intro φ hφ
    obtain ⟨o, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hφ
    have hin := inc_mem hinc
    have how := (Func.wf_operands hwf hmem).1 φ hφ _ hin
    have hoat : OpAt f q qblk.body.length o := fun w hw =>
      domAt_phiUse hwf hqb (hw ▸ hssa φ hφ _ hin hqr)
    obtain ⟨n, hn1, _, _⟩ := G how hoat
    refine ⟨o, n, hin, hinc, how, hoat, hn1, ?_⟩
    rw [hget, ((Func.wf_words hwf).2 blk hmem).1 φ hφ, phi_val_word hwf hmem hφ hin hi.1 hov]
    rw [hov] at hn1
    exact congrArg some (Option.some.inj hn1)
  intro v r hvr hdom
  obtain ⟨hrw, hbef, hpair⟩ := clsOkP_spec hok v r hvr
  by_cases hph : v ∈ blk.phis.map (·.dst)
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
    have hdefv := hid ▸ phi_def hmem hφ
    have hfind : X.inD.find? φ.dst = some (.phi b) := hD ▸ defsOf_find hU hdefv
    obtain ⟨φ', hφ', hcase⟩ := pairOkP_phi hpair hfind
    obtain ⟨blk', hb', hφm', hφd'⟩ := phiOf_spec hB hφ'
    rw [hb] at hb'
    cases hb'
    have hφφ : φ' = φ := List.inj_on_of_nodup_map (hU.phis hmem) hφm' hφ hφd'
    subst hφφ
    obtain ⟨o, n, hin, _, how, hoat, hov, hget⟩ := phival φ' hφ
    obtain ⟨n', ho1, _, hot⟩ := GA how hoat
    rw [hov] at ho1
    cases ho1
    rcases hcase with ⟨w, ψ, rfl, _, hψ, hall⟩ | ⟨hab, hall⟩
    · obtain ⟨blk'', hb'', hψm, hψd⟩ := phiOf_spec hB hψ
      rw [hb] at hb''
      cases hb''
      obtain ⟨o', hinc', hgt⟩ := hall (o, q) hin hex
      obtain ⟨o'', m, _, hinc'', how', hoat', hov', hget'⟩ := phival ψ hψm
      rw [hinc'] at hinc''
      cases hinc''
      obtain ⟨m', hm1, _, hmt⟩ := GA how' hoat'
      rw [hov'] at hm1
      cases hm1
      have hnm : n = m := by rw [← hot.1, ← hmt.1, hgt]
      subst hnm
      show (List.foldl bindStep env _)[φ'.dst]? = (List.foldl bindStep env _)[w]?
      rw [hget, ← hψd, hget']
    · obtain ⟨hrat, hrnot⟩ := above_enter hD hT hwf hU hv hi hqb hb hab
      obtain ⟨m, hm1, _, hmt⟩ := GA hrw hrat
      have hnm : n = m := by rw [← hot.1, ← hmt.1, hall (o, q) hin hex]
      subst hnm
      show (List.foldl bindStep env _)[φ'.dst]? = _
      rw [hget]
      cases r with
      | imm => exact hm1.symm
      | var u =>
        show _ = (List.foldl bindStep env _)[u]?
        rw [hkeep u (hrnot u rfl)]
        exact hm1.symm
  · have hvq := domAt_enter hv hi hqb hb hdom hph
    have hrq := before_domAt hD hT hU hn hroot hbrootq hbef hvq
    have hrnot : ∀ u, r = .var u → u ∉ blk.phis.map (·.dst) := by
      intro u hu hum
      subst hu
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hum
      have hfu : X.inD.find? φ.dst = some (.phi b) := hD ▸ defsOf_find hU (hid ▸ phi_def hmem hφ)
      rcases hdom with hp | ⟨blk', hb', hph' | ⟨j, hj, _⟩⟩ | ⟨d, hne, ha, hdef⟩
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
        exact pairOkP_param hpair (hD ▸ defsOf_find hU (param_def hp'))
      · rw [hb] at hb'; cases hb'; exact hph hph'
      · exact absurd hj (Nat.not_lt_zero _)
      · exact before_not_phi hD hT hU hroot hbroot hbef hfu hdef hne ha
    have h1 := hGq v r hvr hvq
    show (List.foldl bindStep env _)[v]? = opVal (List.foldl bindStep env _) r
    rw [hkeep v hph]
    cases r with
    | imm => exact h1
    | var u =>
      show _ = (List.foldl bindStep env _)[u]?
      rw [hkeep u (hrnot u rfl)]
      exact h1

/-! ## The predicates along the run -/

/-- A statement keeps the predicates: their sides are defined strictly above their targets. -/
theorem predInv_stmt {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true) {PU : List UPred}
    (hPU : ∀ u ∈ PU, u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧ X.above u.1 u.2.2.2.1 = true ∧
      X.above u.1 u.2.2.2.2 = true)
    {e : Env} {b k : Nat} (S : SidePt sig syms f e b k) (hP : PredInv f PU e b) {blk : Block}
    (hb : f.block? b = some blk) {st : Stmt} (hst : blk.body[k]? = some st) (vals : List Val) :
    PredInv f PU ((st.dsts.zip vals).foldl bindStep e) b := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  obtain ⟨e1, _, hroot, hbroot⟩ := S.root
  intro u hu hTb
  obtain ⟨_, _, hla, hra⟩ := hPU u hu
  rw [opVal_stmt hU hb hst vals (above_opAt hD hT hn hroot hbroot hla hTb),
    opVal_stmt hU hb hst vals (above_opAt hD hT hn hroot hbroot hra hTb)]
  exact hP u hu hTb

/-- No slot goes to the entry. -/
theorem not_mem_inSlots_entry {f : Func} (hwf : f.wf sig syms = true) {e : Block}
    (he : f.blocks.head? = some e) {E : NatMap Unit} {dead : List (Nat × Nat)} (x : Nat × Nat) :
    x ∉ inSlots f E dead e.id := by
  intro hx
  unfold inSlots at hx
  obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hx
  split at hx
  · obtain ⟨tk, htk, rfl⟩ := List.mem_map.mp hx
    obtain ⟨htk, hc⟩ := List.mem_filter.mp htk
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hsucc : e.id ∈ b.term.succs := by
      rw [← hc.1]; exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp htk)
    unfold Func.wf at hwf
    simp only [Bool.and_eq_true] at hwf
    have hcfg := hwf.1.2
    unfold Func.cfgOk at hcfg
    rw [he] at hcfg
    simp only [Bool.and_eq_true, List.all_eq_true] at hcfg
    have := (hcfg.2 b hb).1 e.id hsucc
    simp at this
  · cases hx

/-- At the entry, no predicate is usable: none has the entry as its target. -/
theorem predInv_root {f : Func} {X : StepCtx} (hwf : f.wf sig syms = true)
    (hv : (domTree f).valid f = true) {E : NatMap Unit} {dead : List (Nat × Nat)} {PU : List UPred}
    (hpu : ∀ u ∈ PU, ∃ e, usePred X f E dead e = some u) {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true)
    (hroot : (domTree f).idom.find? b = none) (e : Env) : PredInv f PU e b := by
  intro u hu hTb
  have hTe : u.1 = b := by
    rcases hTb.inv with h | ⟨i, hi, _⟩
    · exact h
    · rw [hroot] at hi; cases hi
  obtain ⟨e', he'⟩ := hpu u hu
  obtain ⟨_, _, _, _, _, _, _, _, hslots⟩ := usePred_spec he'
  obtain ⟨e0, he0, hbe⟩ := root_is_entry hv hb hr hroot
  have := not_mem_inSlots_entry hwf he0 (E := E) (dead := dead) (u.2.1, u.2.2.1)
  rw [← hbe, ← hTe, hslots] at this
  exact absurd (List.mem_singleton_self _) this

/-- The edge a block state was entered by: a slot of the predecessor not claimed dead, and the
    predicates of that slot hold at the predecessor's end. -/
def EdgeOk (f : Func) (dead : List (Nat × Nat)) (PU : List UPred) (env : Env) (p b : Nat) : Prop :=
  ∃ pblk k, f.block? p = some pblk ∧ pblk.term.succs[k]? = some b ∧ dead.contains (p, k) = false ∧
    ∀ u ∈ PU, u.2.1 = p → u.2.2.1 = k → opVal env u.2.2.2.1 = opVal env u.2.2.2.2

theorem edgeExec_of {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    {E : NatMap Unit} {dead : List (Nat × Nat)} {q b k : Nat} {qblk : Block}
    (hE : (E.find? q).isSome = true) (hqb : f.block? q = some qblk)
    (hk : qblk.term.succs[k]? = some b) (hnd : dead.contains (q, k) = false) :
    edgeExec X.inB E dead q b = true := by
  have hib : X.inB.find? q = some qblk := by rw [hB, NatMap.find?_ofListBy]; exact hqb
  have hz : (b, k) ∈ qblk.term.succs.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hk
  unfold edgeExec
  simp only [hE, hib, Bool.true_and, Option.any_some, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true']
  exact ⟨(b, k), hz, rfl, hnd⟩

/-- Entering a block over an executable edge keeps the predicates, and establishes those whose
    target it is. -/
theorem predInv_enter {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true) {E : NatMap Unit}
    {dead : List (Nat × Nat)} {PU : List UPred}
    (hPU : ∀ u ∈ PU, u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧ X.above u.1 u.2.2.2.1 = true ∧
      X.above u.1 u.2.2.2.2 = true)
    (hpu : ∀ u ∈ PU, ∃ e, usePred X f E dead e = some u)
    {env : Env} {q b : Nat} (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block}
    (SP : SidePt sig syms f env q qblk.body.length) (hPq : PredInv f PU env q)
    (hE : (E.find? q).isSome = true) (hedge : EdgeOk f dead PU env q b) {blk : Block}
    (hb : f.block? b = some blk) {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) :
    PredInv f PU e₁ b := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have hv := SP.valid
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e1, _, hroot, _⟩ := SP.root
  have hbroot : (domTree f).Anc e1.id b := hid ▸ DomTree.valid_root hv (by assumption) hmem
    (hid ▸ hi.2.2.1)
  obtain ⟨vals, _, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  have hkeep : ∀ o : Operand, (∀ w, o = .var w → w ∉ blk.phis.map (·.dst)) →
      opVal (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env) o =
        opVal env o := by
    intro o ho
    cases o with
    | imm => rfl
    | var w => exact fold_get_not _ _ _ (by rw [hkeys]; exact ho w rfl)
  intro u hu hTb
  obtain ⟨_, _, hla, hra⟩ := hPU u hu
  rw [hkeep _ (above_not_phi hD hT hn hroot hbroot hla hTb hb hU),
    hkeep _ (above_not_phi hD hT hn hroot hbroot hra hTb hb hU)]
  obtain ⟨qblk', kq, hqb', hkq, hnd, hfacts⟩ := hedge
  by_cases hTeq : u.1 = b
  · obtain ⟨e', he'⟩ := hpu u hu
    obtain ⟨_, _, _, _, _, _, _, _, hslots⟩ := usePred_spec he'
    have hm := mem_inSlots hqb' hE hkq hnd
    rw [← hTeq, hslots, List.mem_singleton, Prod.mk.injEq] at hm
    exact hfacts u hu hm.1.symm hm.2.symm
  · rcases DomTree.anc_of_edge hv hi.2.2.2.1 ⟨qblk', hqb', List.mem_of_getElem? hkq⟩ hTb with h | h
    · exact absurd h hTeq
    · exact hPq u hu h

/-! ## The invariant -/

/-- What the prune check gives about the unpruned input. -/
structure PSpec (sig : Sigs) (syms : List String) (f : Func) (X : StepCtx) (F : StepFacts)
    (E : NatMap Unit) (dead : List (Nat × Nat)) (PU : List UPred) (cls : List (Nat × Operand)) :
    Prop where
  wf : f.wf sig syms = true
  hB : X.inB = .ofListBy (·.id) f.blocks
  hD : X.inD = defsOf f
  hT : X.T = domTree f
  hK : X.K = kbMap F
  hv : (domTree f).valid f = true
  hs : ssa f (domTree f) = true
  kb : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true
  closed : execClosed f E dead = true
  cert : X.clsOkP E dead PU cls = true
  dok : ∀ bk ∈ dead, deadOk X E (.ofList cls) PU bk = true
  pu : ∀ u ∈ PU, ∃ e, usePred X f E dead e = some u

/-- The facts at a point `(b, k)` of the input's run. -/
structure PPt (sig : Sigs) (syms : List String) (f : Func) (F : StepFacts) (E : NatMap Unit)
    (PU : List UPred) (cls : List (Nat × Operand)) (e : Env) (b k : Nat) : Prop where
  side : SidePt sig syms f e b k
  kb : KBHolds (kbMap F) e
  gi : GInv f cls e b k
  pr : PredInv f PU e b
  ex : (E.find? b).isSome = true

/-- The facts at a block state of the input's run: definedness, L2 at the predecessor's end, the
    known bits, the block executable, and the predecessor's end with the edge taken. -/
def PS (sig : Sigs) (syms : List String) (f : Func) (F : StepFacts) (E : NatMap Unit)
    (dead : List (Nat × Nat)) (PU : List UPred) (cls : List (Nat × Operand)) (s : BState) : Prop :=
  BlockInv f (domTree f) s ∧ BlockPure f (domTree f) s ∧ KBHolds (kbMap F) s.1 ∧
    AncReach (domTree f) s.2.2 ∧ (E.find? s.2.2).isSome = true ∧
    ∀ p, s.2.1 = some p → ∃ pblk, f.block? p = some pblk ∧
      PPt sig syms f F E PU cls s.1 p pblk.body.length ∧ EdgeOk f dead PU s.1 p s.2.2

section spec

variable {f : Func} {X : StepCtx} {F : StepFacts} {E : NatMap Unit} {dead : List (Nat × Nat)}
  {PU : List UPred} {cls : List (Nat × Operand)} (P : PSpec sig syms f X F E dead PU cls)

include P

theorem PSpec.hPU : ∀ u ∈ PU, u.2.2.2.1.wf = true ∧ u.2.2.2.2.wf = true ∧
    X.above u.1 u.2.2.2.1 = true ∧ X.above u.1 u.2.2.2.2 = true := by
  intro u hu
  obtain ⟨e, he⟩ := P.pu u hu
  obtain ⟨_, _, _, h1, h2, _, h3, h4, _⟩ := usePred_spec he
  exact ⟨h1, h2, h3, h4⟩

theorem PSpec.hok : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true ∧
    ∀ B j, X.inD.find? v = some (.stmt B j) → X.pairOk (.ofList cls) v r = true := by
  intro v r h
  obtain ⟨h1, h2, h3⟩ := clsOkP_spec P.cert v r h
  exact ⟨h1, h2, fun B j hv => by rw [← pairOkP_stmt hv]; exact h3⟩

/-- A statement keeps the facts. -/
theorem ps_stmt {o : Oracle} (hoi : o.IntRet) (c : Ctx) {e : Env} {b k : Nat}
    (H : PPt sig syms f F E PU cls e b k) {blk : Block} (hb : f.block? b = some blk) {st : Stmt}
    (hst : blk.body[k]? = some st) :
    Returns (fun vals => st.dsts.length = vals.length →
      PPt sig syms f F E PU cls ((st.dsts.zip vals).foldl bindStep e) b (k + 1))
      (runStmtO o c e st) := by
  have hm := Func.machine_block (Func.wf_machine P.wf) hb _ (List.mem_of_getElem? hst)
  refine Returns.mono (Returns.and (returns_runStmtO_pure hoi c H.side.pi.1.int hm)
    (kb_stmt_step P.wf P.hs P.kb hb H.side.reach hst H.side.pi H.kb))
    fun vals ⟨⟨hiv, hpv⟩, hkv⟩ hl => ?_
  have S' := SidePt.step H.side hb hst hiv hpv hl
  exact ⟨S', hkv hl, ginv_stmt_of P.hB P.hD P.hT P.wf P.hs P.hK c (fun v r h =>
    ⟨(P.hok v r h).1, (P.hok v r h).2.1, fun B j hv => Or.inl ((P.hok v r h).2.2 B j hv)⟩) H.side H.gi
    hb hst S' (hkv hl), predInv_stmt P.hD P.hT P.wf P.hs P.hPU H.side H.pr hb hst vals, H.ex⟩

/-- A block's first `k` statements keep the facts. -/
theorem ps_take {o : Oracle} (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) {e₁ : Env} (h₀ : PPt sig syms f F E PU cls e₁ b 0) :
    ∀ k, k ≤ blk.body.length → Returns (fun e => PPt sig syms f F E PU cls e b k)
      (runBodyO o c e₁ (blk.body.take k))
  | 0, _ => by simp only [List.take_zero, runBodyO]; exact Returns.pure h₀
  | k + 1, hkl => by
    have hlt : k < blk.body.length := by omega
    have hsk : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hsk, Option.toList_some, runBodyO_append]
    refine Returns.bind (ps_take hoi c hb h₀ k (by omega)) fun env H => ?_
    simp only [runBodyO]
    refine Returns.bind (ps_stmt P hoi c H hb hsk) fun vals hv =>
      Returns.bind (returns_bind env _ vals) fun env₂ ⟨hl, he⟩ => Returns.pure ?_
    subst he
    exact hv hl

/-- Entering the block of a block state establishes the facts at its start. -/
theorem ps_enter {env : Env} {prev : Option Nat} {b : Nat}
    (hS : PS sig syms f F E dead PU cls (env, prev, b)) {blk : Block} (hb : f.block? b = some blk) :
    Returns (fun e₁ => PPt sig syms f F E PU cls e₁ b 0) (enter env prev blk) := by
  obtain ⟨hbi, hbp, hkb, hanc, hex, hprev⟩ := hS
  have hgp : Returns (fun e₁ => GInv f cls e₁ b 0 ∧ PredInv f PU e₁ b) (enter env prev blk) := by
    rw [enter_eq]
    refine Returns.lift fun e₁ he₁ => ?_
    cases prev with
    | none =>
      have hph := phis_nil_of_root P.wf P.hv hb hbi.2.2.1 hbi.2.2.2
      rw [enterOpt_nil hph] at he₁
      cases he₁
      exact ⟨ginv_rootP P.hD P.hs P.cert env hbi.2.2.2 hb hph,
        predInv_root P.wf P.hv P.pu hb hbi.2.2.1 hbi.2.2.2 env⟩
    | some q =>
      obtain ⟨qblk, hqb, Hq, hedge⟩ := hprev q rfl
      obtain ⟨qblk', kq, hqb', hkq, hnd, hfacts⟩ := hedge
      rw [hqb] at hqb'
      cases hqb'
      exact ⟨ginv_enterP P.hB P.hD P.hT P.wf P.hs P.cert P.hPU hbi hqb Hq.side Hq.gi Hq.pr
          (edgeExec_of P.hB Hq.ex hqb hkq hnd) hb he₁,
        predInv_enter P.hD P.hT P.wf P.hs P.hPU P.pu hbi Hq.side Hq.pr Hq.ex
          ⟨qblk, kq, hqb, hkq, hnd, hfacts⟩ hb he₁⟩
  refine Returns.mono (Returns.and (Returns.and (Returns.and (point_zero P.wf P.hv hbi hb)
    (pureInv_enter P.wf P.hv P.hs hbi hbp hb)) (kb_enter P.wf P.hs P.kb hbi.1 hkb hb)) hgp)
    fun e₁ ⟨⟨⟨hpi, hpu⟩, hk⟩, hg, hp⟩ => ⟨⟨P.wf, P.hv, P.hs, ⟨blk, hb⟩, hpi, hpu, hanc⟩, hk, hg, hp, hex⟩

/-- At a block's end, the slot the terminator takes is not claimed dead: a dead slot of an
    executable block is one its `br` does not take. -/
theorem ps_live {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : PPt sig syms f F E PU cls e b blk.body.length) {k : Nat} (hsem : SlotSem e blk.term k) :
    dead.contains (b, k) = false := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hU := UniqueDefs.of_ssa P.hs
  have hn := Func.wf_ids P.wf
  have hib : X.inB.find? b = some blk := by rw [P.hB, NatMap.find?_ofListBy]; exact hb
  obtain ⟨e1, _, hroot, hbroot⟩ := H.side.root
  have hargs : ∀ o ∈ blk.term.args, o.wf = true := (Func.wf_operands P.wf hmem).2.2
  have hssa := (ssa_block P.hs hmem (hid ▸ H.side.reach)).2.2
  cases hc : dead.contains (b, k)
  · rfl
  · exfalso
    have hok := P.dok (b, k) (List.contains_iff_mem.mp hc)
    simp only [deadOk, Bool.or_eq_true] at hok
    rcases hok with hno | hok
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp H.ex
      rw [hx] at hno; cases hno
    · rw [hib, Option.any_some] at hok
      revert hok hsem
      cases hterm : blk.term with
      | br c nz z =>
        intro hsem hok
        have hcm : c ∈ blk.term.args := by rw [hterm]; exact List.mem_singleton_self _
        have hcat : OpAt f b blk.body.length c := fun w hw => by
          subst hw
          have := hssa _ hcm
          rw [hid] at this
          exact useOk_sound hn this
        obtain ⟨n, hn1, _, hnt⟩ := gTermAt_ok P.hD P.hT hn hroot
          (fun v r h => ⟨(P.hok v r h).1, (P.hok v r h).2.1⟩) P.hPU hU hbroot H.gi H.pr
          H.side.words (hargs c hcm) hcat
        dsimp only at hok
        rcases hg : gTermAt X (.ofList cls) PU b c with a | w | _ | _ | _ <;> rw [hg] at hok
        all_goals try cases hok
        rw [hg] at hnt
        have hnw : n = w % W := hnt.1.symm
        obtain ⟨v, hv, hkv⟩ := hsem
        have hvn : v = n := by
          rw [opVal_of_intVal hv] at hn1
          cases hn1
          rfl
        rw [hvn, hnw] at hkv
        simp only [beq_iff_eq] at hok
        rw [← hok] at hkv
        by_cases h0 : w % W = 0 <;> simp [h0] at hkv
      | _ => intro _ hok; cases hok

/-- At a block's end, the terminator goes by a slot not claimed dead to an executable block, and
    the facts hold at the next block state. -/
theorem ps_term {e : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (H : PPt sig syms f F E PU cls e b blk.body.length) :
    Returns (fun n => match n with
      | .goto e' d => PS sig syms f F E dead PU cls (e', some b, d)
      | .done _ => True) (runTerm e blk.term) := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hU := UniqueDefs.of_ssa P.hs
  have hn := Func.wf_ids P.wf
  have hib : X.inB.find? b = some blk := by rw [P.hB, NatMap.find?_ofListBy]; exact hb
  obtain ⟨e1, _, hroot, hbroot⟩ := H.side.root
  have hwfT : blk.term.wf f.rets.length = true := by
    have hw := P.wf
    unfold Func.wf at hw
    simp only [Bool.and_eq_true, List.all_eq_true] at hw
    exact (hw.2 blk hmem).2
  have hargs : ∀ o ∈ blk.term.args, o.wf = true := by
    have := hwfT
    unfold Fe.Sonatina.Term.wf at this
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this.1
  have hssa := (ssa_block P.hs hmem (hid ▸ H.side.reach)).2.2
  have hdef := term_defined P.wf P.hs hb H.side.reach H.side.pi
  refine Returns.mono (runTerm_sem hdef) fun nx hnx => ?_
  cases nx with
  | done _ => trivial
  | goto e' d =>
    obtain ⟨rfl, k, hk, hsem⟩ := hnx
    have hd : d ∈ blk.term.succs := List.mem_of_getElem? hk
    have hnd : dead.contains (b, k) = false := ps_live P hb H hsem
    -- the next block is executable
    have hEd : (E.find? d).isSome = true := by
      have := P.closed
      unfold execClosed at this
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at this
      rcases this.2 blk hmem with h | h
      · rw [hid] at h
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp H.ex
        simp [hx] at h
      · rcases h (d, k) (List.mem_zipIdx_iff_getElem?.mpr hk) with h | h
        · rw [hid, hnd] at h; cases h
        · exact h
    -- the slot's predicates hold
    have hfacts : ∀ u ∈ PU, u.2.1 = b → u.2.2.1 = k →
        opVal e' u.2.2.2.1 = opVal e' u.2.2.2.2 := by
      intro u hu h1 h2
      obtain ⟨e'', he''⟩ := P.pu u hu
      obtain ⟨pb, hpb, _, _, _, hpred, _⟩ := usePred_spec he''
      rw [h1, hib] at hpb
      cases hpb
      rw [h2] at hpred
      exact predOk_sound H.side.pi.1 (by rw [P.hK]; exact H.kb) hwfT hpred hsem
    refine ⟨blockInv_of_point P.hv hb H.side.reach H.side.pi hd, fun pblk hp => ?_, H.kb,
      ancReach_edge P.hv H.side.anc ⟨blk, hb, hd⟩, hEd, fun p hp => ?_⟩
    · rw [hb] at hp; cases hp; exact H.side.pu
    · simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨blk, hb, H, blk, k, hb, hk, hnd, hfacts⟩

/-- A block of a block state goes to a block state where the facts hold. -/
theorem ps_step {o : Oracle} (hoi : o.IntRet) (c : Ctx) {s : BState}
    (hS : PS sig syms f F E dead PU cls s) :
    Returns (fun n => match n with
      | .goto e d => PS sig syms f F E dead PU cls (e, some s.2.2, d)
      | .done _ => True) (stepBlock o c f s.1 s.2.1 s.2.2) := by
  obtain ⟨env, prev, b⟩ := s
  unfold stepBlock
  cases hb : f.block? b with
  | none => exact Returns.stuck _
  | some blk =>
    dsimp only
    refine Returns.bind (ps_enter P hS hb) fun e₁ h₀ => ?_
    have hbody := ps_take P hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    exact Returns.bind hbody fun e₂ H => ps_term P hb H

/-- **The run's facts**: at every block state a run of the input from its entry reaches, with
    integer arguments and an oracle that returns integers. -/
theorem ps_reaches {o : Oracle} (hoi : o.IntRet) (c : Ctx) {e : Block}
    (he : f.blocks.head? = some e) {args : List Val} (hargs : IntVals args) {I : ExecutionEnv}
    {w w₀ : World} {env₀ : Env} (h₀ : (bind {} f.params args).exec I w = some (.ok (env₀, w₀)))
    {s : BState} (hr : Reaches o c f (env₀, none, e.id) s) : PS sig syms f F E dead PU cls s := by
  have hU := UniqueDefs.of_ssa P.hs
  induction hr with
  | start =>
    refine ⟨entry_inv P.wf P.hv he hargs I w env₀ w₀ h₀, trivial, ?_, ancReach_entry P.hv he, ?_,
      fun p hp => by cases hp⟩
    · obtain ⟨_, rfl⟩ := returns_bind {} f.params args I w env₀ w₀ h₀
      intro v n hvn
      rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he', _⟩
      · rw [kb_param P.kb (defsOf_find hU (param_def (List.of_mem_zip hx).1))]
        exact sat_unknown n
      · simp at he'
    · have := P.closed
      unfold execClosed at this
      simp only [Bool.and_eq_true, Option.any_eq_true] at this
      rw [he] at this
      simpa using this.1
  | step _ hx ih => exact ps_step P hoi c ih _ _ _ _ hx

end spec

end Fe.Sonatina.Steps.Schemas
