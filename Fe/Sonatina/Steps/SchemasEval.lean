import Fe.Sonatina.Steps.SchemasPair

/-!
# Unfolded terms at a reached point, and the justification of `σ`'s entries

At a point `(b, k)` of a snapshot that the run has reached (`SidePt`: definedness and L2 at the
point, every tree ancestor of `b` reachable), an operand whose definition dominates the point,
unfolded through the snapshot's pure statements (`unfold`), evaluates in the words of the
input's environment `e` to the operand's word, and its atoms are bound to words (`TermOk`,
`unfold_sound`): the snapshot's environment `ε` binds less than `e` (`EnvSub`, the output's
against the input's, or the input's own), and SCCP's constants hold in `e` (`CHolds`).

So an entry `v ↦ x` that `entryOk` justifies holds at a point where the input reads `v` and the
output `x` (`entryOk_sound`): the schema's two terms evaluate to the words of `v` and `x`, and
the schema proves them equal under the known bits (`checkExact_sound`, `KBHolds`); an SCCP
constant holds by `CHolds`; a folded phi by the trivial-phi invariant (`TPI`); a chain link by
the same argument for the deleted operand, which the output does not define, so that its term on
the output side is its atom.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

/-! ## Invariants -/

/-- SCCP's constants hold of every value bound to a word. -/
def CHolds (cs : NatMap Nat) (env : Env) : Prop :=
  ∀ v c n, cs.find? v = some c → env[v]? = some (.int 256 n) → n = c

/-- Every tree ancestor-or-self of `b` is in the tree's reachable set. -/
def AncReach (T : DomTree) (b : Nat) : Prop := ∀ d, T.Anc d b → (T.reach.find? d).isSome = true

/-- A term evaluates, in the words of `e`, to `n`, and its atoms are bound to words. -/
def TermOk (e : Env) (t : Term) (n : Nat) : Prop :=
  t.eval (envWord e) = n ∧ ∀ a, t.hasAtom a = true → ∃ x, e[a]? = some (.int 256 x) ∧ x < W

/-- A point `(b, k)` of a snapshot `g` the run has reached, with environment `ε`. -/
structure SidePt (sig : Sigs) (syms : List String) (g : Func) (ε : Env) (b k : Nat) : Prop where
  wf : g.wf sig syms = true
  valid : (domTree g).valid g = true
  ssa : ssa g (domTree g) = true
  blk : ∃ blk, g.block? b = some blk
  pi : PointInv g (domTree g) b k ε
  pu : PureInv g (domTree g) b k ε
  anc : AncReach (domTree g) b

/-- The trivial-phi invariant at block `b`: each folded phi whose block is a tree ancestor-or-self
    of `b` holds its operand's value. -/
def TPI (X : StepCtx) (f : Func) (env : Env) (b : Nat) : Prop :=
  ∀ v x, X.phiFold v x = true → ∀ B, (v, Def.phi B) ∈ defList f → (domTree f).Anc B b →
    opVal env (.var v) = opVal env x

variable {sig : Sigs} {syms : List String}

theorem SidePt.reach {g : Func} {ε : Env} {b k : Nat} (S : SidePt sig syms g ε b k) :
    ((domTree g).reach.find? b).isSome = true := S.anc b .refl

theorem SidePt.root {g : Func} {ε : Env} {b k : Nat} (S : SidePt sig syms g ε b k) :
    ∃ e, g.blocks.head? = some e ∧ (domTree g).idom.find? e.id = none ∧ (domTree g).Anc e.id b := by
  obtain ⟨blk, hb⟩ := S.blk
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e, he⟩ : ∃ e, g.blocks.head? = some e := by
    cases h : g.blocks.head? with
    | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
    | some e => exact ⟨e, rfl⟩
  exact ⟨e, he, (DomTree.valid_entry S.valid he).2,
    hid ▸ DomTree.valid_root S.valid he hmem (hid ▸ S.reach)⟩

/-! ## Dominance -/

/-- A use dominated at a point before which statement `j` of block `d` comes is dominated at
    the point. -/
theorem domAt_trans {g : Func} {T : DomTree} {e b : Nat} (hroot : T.idom.find? e = none)
    (hbroot : T.Anc e b) {d j k w : Nat} (h : DomAt g T d j w) (hbef : Before T d j b k) :
    DomAt g T b k w := by
  rcases h with hp | ⟨blk, hb, hph | ⟨j', hj', s, hs, hv⟩⟩ | ⟨d', hne, ha, hdef⟩
  · exact Or.inl hp
  · rcases hbef with ⟨hne, ha⟩ | ⟨rfl, _⟩
    · exact Or.inr (Or.inr ⟨d, hne, ha, blk, hb, Or.inl hph⟩)
    · exact Or.inr (Or.inl ⟨blk, hb, Or.inl hph⟩)
  · rcases hbef with ⟨hne, ha⟩ | ⟨rfl, hjk⟩
    · exact Or.inr (Or.inr ⟨d, hne, ha, blk, hb, Or.inr ⟨s, List.mem_of_getElem? hs, hv⟩⟩)
    · exact Or.inr (Or.inl ⟨blk, hb, Or.inr ⟨j', by omega, s, hs, hv⟩⟩)
  · rcases hbef with ⟨hne', ha'⟩ | ⟨rfl, _⟩
    · refine Or.inr (Or.inr ⟨d', fun h => ?_, ha.trans ha', hdef⟩)
      exact hne' (DomTree.anc_antisymm hroot hbroot ha' (h ▸ ha))
    · exact Or.inr (Or.inr ⟨d', hne, ha, hdef⟩)

/-- A dominated use of a statement's result: the statement comes before the point. -/
theorem before_of_domAt {g : Func} (hU : UniqueDefs g) {T : DomTree} {b k w d0 j0 : Nat}
    (h : DomAt g T b k w) (hd : (w, Def.stmt d0 j0) ∈ defList g) : Before T d0 j0 b k := by
  rcases h with hp | ⟨blk, hb, hph | ⟨j', hj', s, hs, hv⟩⟩ | ⟨d', hne, ha, hdef⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; cases hU.fn (param_def hq) hd
  · have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph; cases hU.fn (hid ▸ phi_def hmem hφ) hd
  · have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv
    have := hU.fn (hid ▸ stmt_def hmem hs hdd) hd
    simp only [Def.stmt.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact Or.inr ⟨rfl, hj'⟩
  · rcases definedIn_def hdef with h' | ⟨j'', h'⟩
    · cases hU.fn h' hd
    · have := (Def.stmt.inj (hU.fn h' hd)).1
      subst this
      exact Or.inl ⟨hne, ha⟩

/-- A dominated use of a phi: its block is a tree ancestor-or-self of the point's. -/
theorem anc_of_domAt_phi {g : Func} (hU : UniqueDefs g) {T : DomTree} {b k w B : Nat}
    (h : DomAt g T b k w) (hd : (w, Def.phi B) ∈ defList g) : T.Anc B b := by
  rcases h with hp | ⟨blk, hb, hph | ⟨j', _, s, hs, hv⟩⟩ | ⟨d', _, ha, hdef⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; cases hU.fn (param_def hq) hd
  · have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
    have := Def.phi.inj (hU.fn (hid ▸ phi_def hmem hφ) hd)
    subst this; exact .refl
  · have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv
    cases hU.fn (hid ▸ stmt_def hmem hs hdd) hd
  · exact phi_of_definedIn hU hdef hd ▸ ha

/-- The statement `defStmt` finds: the value's definition, in the block of its id. -/
theorem defStmt_spec {g : Func} (hn : (g.blocks.map (·.id)).Nodup) {w : Nat} {st : Stmt}
    (h : defStmt (.ofListBy (·.id) g.blocks) (defsOf g) w = some st) :
    ∃ d0 j0 blk0, (w, Def.stmt d0 j0) ∈ defList g ∧ g.block? d0 = some blk0 ∧
      blk0.body[j0]? = some st ∧ w ∈ st.dsts.map (·.1) := by
  unfold defStmt at h
  split at h
  · next d0 j0 hD =>
    rw [NatMap.find?_ofListBy] at h
    obtain ⟨blk0, hb0, hj0⟩ := Option.bind_eq_some_iff.mp h
    have hb0' : g.block? d0 = some blk0 := hb0
    have hdef := defsOf_mem hD
    refine ⟨d0, j0, blk0, hdef, hb0', hj0, ?_⟩
    rcases mem_defList hdef with ⟨h1, _⟩ | ⟨_, _, _, _, h1, _⟩ | ⟨b', hb', k', s', hs', h1, hv⟩
    · cases h1
    · cases h1
    · simp only [Def.stmt.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [block?_of_mem hn hb'] at hb0'
      cases hb0'
      rw [hs'] at hj0; cases hj0
      exact hv
  · cases h

/-! ## Terms -/

theorem evalOperand_of_intVal {env : Env} {o : Operand} {n : Nat} (h : intVal env o = some (256, n)) :
    evalOperand env o = pure (.int 256 n) := by
  rw [evalOperand_eq, opVal_of_intVal h]; rfl

theorem termOk_atom {e : Env} {w n : Nat} (h : e[w]? = some (.int 256 n)) (hn : n < W) :
    TermOk e (.atom w) n := by
  refine ⟨eval_atom_env h hn, fun a ha => ?_⟩
  simp only [Term.hasAtom, beq_iff_eq] at ha
  subst ha
  exact ⟨n, h, hn⟩

theorem termOk_lit {e : Env} {n : Nat} (hn : n < W) : TermOk e (.lit n) n :=
  ⟨by simp [Term.eval, Nat.mod_eq_of_lt hn], fun a ha => by simp [Term.hasAtom] at ha⟩

/-- A pure instruction's term from its operands' terms. -/
theorem termOf_ok {e ε : Env} {G : Operand → Term} {p : PureInst}
    (h : ∀ a ∈ p.args, ∃ n, intVal ε a = some (256, n) ∧ n < W ∧ TermOk e (G a) n) :
    ∃ xs, ArgsAre ε p.args xs ∧ TermOk e (termOf G p) (p.evalOn xs) := by
  rcases p with ⟨o, a⟩ | ⟨o, a, b⟩ | ⟨o, a, b, m⟩ <;> simp only [PureInst.args] at h
  · obtain ⟨x, hx, hxl, hxt⟩ := h a (by simp)
    refine ⟨[x], .cons ⟨evalOperand_of_intVal hx, hxl⟩ .nil, ?_, fun v hv => ?_⟩
    · simp only [termOf, Term.eval, PureInst.evalOn, hxt.1]
    · exact hxt.2 v (by simpa [termOf, Term.hasAtom] using hv)
  · obtain ⟨x, hx, hxl, hxt⟩ := h a (by simp)
    obtain ⟨y, hy, hyl, hyt⟩ := h b (by simp)
    refine ⟨[x, y], .cons ⟨evalOperand_of_intVal hx, hxl⟩ (.cons ⟨evalOperand_of_intVal hy, hyl⟩ .nil),
      ?_, fun v hv => ?_⟩
    · simp only [termOf, Term.eval, PureInst.evalOn, hxt.1, hyt.1]
    · simp only [termOf, Term.hasAtom, Bool.or_eq_true] at hv
      rcases hv with hv | hv
      · exact hxt.2 v hv
      · exact hyt.2 v hv
  · obtain ⟨x, hx, hxl, hxt⟩ := h a (by simp)
    obtain ⟨y, hy, hyl, hyt⟩ := h b (by simp)
    obtain ⟨z, hz, hzl, hzt⟩ := h m (by simp)
    refine ⟨[x, y, z], .cons ⟨evalOperand_of_intVal hx, hxl⟩ (.cons ⟨evalOperand_of_intVal hy, hyl⟩
      (.cons ⟨evalOperand_of_intVal hz, hzl⟩ .nil)), ?_, fun v hv => ?_⟩
    · simp only [termOf, Term.eval, PureInst.evalOn, hxt.1, hyt.1, hzt.1]
    · simp only [termOf, Term.hasAtom, Bool.or_eq_true] at hv
      rcases hv with (hv | hv) | hv
      · exact hxt.2 v hv
      · exact hyt.2 v hv
      · exact hzt.2 v hv

theorem pure_inj {α : Type} {a b : α} (h : (pure a : FeM α) = pure b) : a = b := by
  have := congrArg (fun x => x.exec default someWorld) h
  simpa [Fe.M.exec_pure] using this

theorem noClz_ne {p : PureInst} (hc : noClz p = true) : ∀ a, p ≠ .op1 .clz a := by
  intro a h; subst h; cases hc

/-- The values a pure instruction other than `clz` gives on words. -/
theorem pureVals_of {c : Ctx} {env : Env} {i : Inst} {p : PureInst} (hp : pureInst? i = some p)
    (hc : noClz p = true) {xs : List Nat} (hargs : ArgsAre env p.args xs) :
    pureVals env i = some [.int p.bits (p.evalOn xs)] := by
  have h1 := Schemas.runInst_pure (c := c) (noClz_ne hc) hargs
  rw [pureInst?_toInst hp, Steps.runInst_pure c env i (pureInst?_pure hp hc)] at h1
  cases hv : pureVals env i with
  | none =>
    rw [hv] at h1
    have := congrArg (fun x => x.exec default someWorld) h1
    simp [Steps.lift, stuck, Fe.M.exec_pure, Fe.M.exec_diverge] at this
  | some vals =>
    rw [hv] at h1
    exact congrArg some (pure_inj h1)

theorem evalOn_lt' {p : PureInst} {env : Env} {xs : List Nat} (h : ArgsAre env p.args xs) :
    p.evalOn xs < W :=
  evalOn_lt (List.Forall₂.imp (fun _ _ h => h.2) h)

/-- The word a pure statement that holds binds to its result. -/
theorem pureHolds_val {c : Ctx} {env : Env} {st : Stmt} {p : PureInst} (hp : pureInst? st.inst = some p)
    (hc : noClz p = true) {xs : List Nat} (hargs : ArgsAre env p.args xs) (hh : PureHolds env st)
    (hty : ∀ d ∈ st.dsts, d.2 = .int 256) {w : Nat} (hw : w ∈ st.dsts.map (·.1)) :
    env[w]? = some (.int 256 (p.evalOn xs)) := by
  obtain ⟨vals, hv, hl, hb⟩ := hh
  rw [pureVals_of (c := c) hp hc hargs] at hv
  cases hv
  obtain ⟨dw, hdw, rfl⟩ := List.mem_map.mp hw
  match hds : st.dsts, hl with
  | [d1], _ =>
    rw [hds] at hdw
    rcases List.mem_singleton.mp hdw with rfl
    have := hb (dw, .int p.bits (p.evalOn xs)) (by rw [hds]; exact List.mem_singleton_self _)
    rw [this, hty dw (by rw [hds]; exact List.mem_singleton_self _)]
    simp only [Val.as_word (evalOn_lt' hargs)]

section unfold

variable {g : Func} {ε e : Env} {b k : Nat}

theorem SidePt.uniq (S : SidePt sig syms g ε b k) : UniqueDefs g := UniqueDefs.of_ssa S.ssa

/-- A dominated value is bound to a word, in `ε` and so in `e`. -/
theorem SidePt.bound (S : SidePt sig syms g ε b k) (hsub : EnvSub ε e) {w : Nat}
    (hw : DomAt g (domTree g) b k w) : ∃ n, ε[w]? = some (.int 256 n) ∧ e[w]? = some (.int 256 n) ∧ n < W := by
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (S.pi.2 w hw)
  obtain ⟨n, hn, rfl⟩ := S.pi.1 w val hval
  exact ⟨n, hval, hsub w _ hval, hn⟩

/-- The term of a pure statement's result that dominates the point, its operands unfolded `d`
    levels, given the lemma for those operands. -/
theorem SidePt.stmt_ok (S : SidePt sig syms g ε b k) (hsub : EnvSub ε e) (c : Ctx)
    {G : Operand → Term} (ih : ∀ o : Operand, o.wf = true → (∀ w, o = .var w → DomAt g (domTree g) b k w) →
      ∃ n, intVal ε o = some (256, n) ∧ n < W ∧ TermOk e (G o) n)
    {w : Nat} (hw : DomAt g (domTree g) b k w) {st : Stmt}
    (hst : defStmt (.ofListBy (·.id) g.blocks) (defsOf g) w = some st) {p : PureInst}
    (hp : pureInst? st.inst = some p) (hc : noClz p = true) :
    ∃ n, ε[w]? = some (.int 256 n) ∧ n < W ∧ TermOk e (termOf G p) n := by
  obtain ⟨e0, _, hroot, hbroot⟩ := S.root
  obtain ⟨d0, j0, blk0, hdef, hb0, hj0, hwd⟩ := defStmt_spec (Func.wf_ids S.wf) hst
  have hbef := before_of_domAt S.uniq hw hdef
  have hreach : ((domTree g).reach.find? d0).isSome = true := by
    rcases hbef with ⟨_, ha⟩ | ⟨rfl, _⟩
    · exact S.anc d0 ha
    · exact S.reach
  have hh := S.pu d0 j0 blk0 st hb0 hj0 (pureInst?_pure hp hc) hreach hbef
  have hmem0 := List.mem_of_find?_eq_some hb0
  have hsm : st ∈ blk0.body := List.mem_of_getElem? hj0
  obtain ⟨xs, hargs, hok⟩ := termOf_ok (ε := ε) (e := e) (G := G) (p := p) fun a ha => by
      have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
      refine ih a ((Func.wf_operands S.wf hmem0).2.1 st hsm a ha') fun w' hw' => ?_
      subst hw'
      exact domAt_trans hroot hbroot (stmt_operand S.wf S.ssa hb0 hreach hj0 ha') hbef
  have hty := ((Func.wf_words S.wf).2 blk0 hmem0).2 st hsm
  exact ⟨_, pureHolds_val (c := c) hp hc hargs hh hty hwd, evalOn_lt' hargs, hok⟩

theorem unfold_succ_var (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) (d v : Nat)
    (hcs : cs.find? v = none) :
    unfold B D cs (d + 1) (.var v) = .atom v ∨ ∃ st p, defStmt B D v = some st ∧
      pureInst? st.inst = some p ∧ noClz p = true ∧
      unfold B D cs (d + 1) (.var v) = termOf (unfold B D cs d) p := by
  rcases hds : defStmt B D v with _ | st
  · left; simp [unfold, hcs, hds]
  rcases hp : pureInst? st.inst with _ | p
  · left; simp [unfold, hcs, hds, hp]
  by_cases hc : noClz p = true
  · right
    refine ⟨st, p, rfl, hp, hc, ?_⟩
    simp only [unfold, hcs, hds, Option.bind_some, hp]
    split <;> simp_all [noClz]
  · left
    have : ∃ a, p = .op1 .clz a := by
      rcases p with ⟨o, a⟩ | _ | _ <;> simp [noClz] at hc
      · cases o <;> simp at hc ⊢
    obtain ⟨a, rfl⟩ := this
    simp [unfold, hcs, hds, hp]

/-- An operand dominating the point, unfolded `d` levels through the snapshot's pure statements
    with SCCP's constants as literals, evaluates to its word, its atoms bound to words. -/
theorem SidePt.unfold_sound (S : SidePt sig syms g ε b k) (hsub : EnvSub ε e) (c : Ctx)
    {cs : NatMap Nat} (hC : CHolds cs e) :
    ∀ d (o : Operand), o.wf = true → (∀ w, o = .var w → DomAt g (domTree g) b k w) →
      ∃ n, intVal ε o = some (256, n) ∧ n < W ∧
        TermOk e (unfold (.ofListBy (·.id) g.blocks) (defsOf g) cs d o) n := by
  intro d
  induction d with
  | zero =>
    intro o ho hd
    cases o with
    | imm bits v =>
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
      obtain ⟨rfl, hv⟩ := ho
      exact ⟨v, rfl, hv, termOk_lit hv⟩
    | var w =>
      obtain ⟨n, hε, he, hn⟩ := S.bound hsub (hd w rfl)
      refine ⟨n, by simp [intVal, opVal, hε], hn, ?_⟩
      cases hcs : cs.find? w with
      | some c0 =>
        have := hC w c0 n hcs he
        subst this
        simp only [unfold, hcs]
        exact termOk_lit hn
      | none =>
        simp only [unfold, hcs]
        exact termOk_atom he hn
  | succ d ih =>
    intro o ho hd
    cases o with
    | imm bits v =>
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
      obtain ⟨rfl, hv⟩ := ho
      exact ⟨v, rfl, hv, termOk_lit hv⟩
    | var w =>
      obtain ⟨n, hε, he, hn⟩ := S.bound hsub (hd w rfl)
      refine ⟨n, by simp [intVal, opVal, hε], hn, ?_⟩
      cases hcs : cs.find? w with
      | some c0 =>
        have := hC w c0 n hcs he
        subst this
        simp only [unfold, hcs]
        exact termOk_lit hn
      | none =>
        rcases unfold_succ_var _ _ cs d w hcs with h | ⟨st, p, hst, hp, hc, h⟩
        · rw [h]; exact termOk_atom he hn
        · rw [h]
          obtain ⟨n', hε', _, hok⟩ := S.stmt_ok hsub c ih (hd w rfl) hst hp hc
          rw [hε] at hε'
          cases hε'
          exact hok

theorem unfoldStop_succ_var (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) (stop : List Nat)
    (d v : Nat) (hcs : cs.find? v = none) (hs : stop.contains v = false) :
    unfoldStop B D cs stop (d + 1) (.var v) = .atom v ∨ ∃ st p, defStmt B D v = some st ∧
      pureInst? st.inst = some p ∧ noClz p = true ∧
      unfoldStop B D cs stop (d + 1) (.var v) = termOf (unfoldStop B D cs stop d) p := by
  rcases hds : defStmt B D v with _ | st
  · left; simp [unfoldStop, hcs, hs, hds]
  rcases hp : pureInst? st.inst with _ | p
  · left; simp [unfoldStop, hcs, hs, hds, hp]
  by_cases hc : noClz p = true
  · right
    refine ⟨st, p, rfl, hp, hc, ?_⟩
    simp only [unfoldStop, hcs, hs, hds, Option.bind_some, hp, Bool.false_eq_true, ↓reduceIte]
    split <;> simp_all [noClz]
  · left
    have : ∃ a, p = .op1 .clz a := by
      rcases p with ⟨o, a⟩ | _ | _ <;> simp [noClz] at hc
      · cases o <;> simp at hc ⊢
    obtain ⟨a, rfl⟩ := this
    simp [unfoldStop, hcs, hs, hds, hp]

/-- `unfold_sound` for `unfoldStop`: stopping early leaves an atom, bound to its word. -/
theorem SidePt.unfoldStop_sound (S : SidePt sig syms g ε b k) (hsub : EnvSub ε e) (c : Ctx)
    {cs : NatMap Nat} (hC : CHolds cs e) (stop : List Nat) :
    ∀ d (o : Operand), o.wf = true → (∀ w, o = .var w → DomAt g (domTree g) b k w) →
      ∃ n, intVal ε o = some (256, n) ∧ n < W ∧
        TermOk e (unfoldStop (.ofListBy (·.id) g.blocks) (defsOf g) cs stop d o) n := by
  intro d
  induction d with
  | zero =>
    intro o ho hd
    cases o with
    | imm bits v =>
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
      obtain ⟨rfl, hv⟩ := ho
      exact ⟨v, rfl, hv, termOk_lit hv⟩
    | var w =>
      obtain ⟨n, hε, he, hn⟩ := S.bound hsub (hd w rfl)
      refine ⟨n, by simp [intVal, opVal, hε], hn, ?_⟩
      cases hcs : cs.find? w with
      | some c0 =>
        have := hC w c0 n hcs he
        subst this
        simp only [unfoldStop, hcs]
        exact termOk_lit hn
      | none =>
        simp only [unfoldStop, hcs]
        split <;> exact termOk_atom he hn
  | succ d ih =>
    intro o ho hd
    cases o with
    | imm bits v =>
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
      obtain ⟨rfl, hv⟩ := ho
      exact ⟨v, rfl, hv, termOk_lit hv⟩
    | var w =>
      obtain ⟨n, hε, he, hn⟩ := S.bound hsub (hd w rfl)
      refine ⟨n, by simp [intVal, opVal, hε], hn, ?_⟩
      cases hcs : cs.find? w with
      | some c0 =>
        have := hC w c0 n hcs he
        subst this
        simp only [unfoldStop, hcs]
        exact termOk_lit hn
      | none =>
        cases hs : stop.contains w with
        | true => simp only [unfoldStop, hcs, hs, ↓reduceIte]; exact termOk_atom he hn
        | false =>
          rcases unfoldStop_succ_var _ _ cs stop d w hcs hs with h | ⟨st, p, hst, hp, hc, h⟩
          · rw [h]; exact termOk_atom he hn
          · rw [h]
            obtain ⟨n', hε', _, hok⟩ := S.stmt_ok hsub c ih (hd w rfl) hst hp hc
            rw [hε] at hε'
            cases hε'
            exact hok

end unfold

/-! ## The justification of an entry -/

section entry

variable {m : Mode} {f : Func} {s : FuncSnap} {F : StepFacts} {pairs : List (Line × Line)}
  {deleted : List Line} {σ : NatMap Operand}

theorem tout_del {X : StepCtx} {u : Nat} (hu : X.outD.find? u = none) (d : Nat) :
    X.tout d (.var u) = match X.cs.find? u with
      | some c => .lit c
      | none => .atom u := by
  cases d <;> cases hcs : X.cs.find? u <;> simp [StepCtx.tout, unfold, defStmt, hu, hcs]

/-- The input's term of a value dominating the point evaluates to its word. -/
theorem tin_ok {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks) (hD : X.inD = defsOf f)
    {e : Env} {b k : Nat} (S : SidePt sig syms f e b k) (c : Ctx) (hC : CHolds X.cs e) {v : Nat}
    (hv : DomAt f (domTree f) b k v) :
    ∃ n, e[v]? = some (.int 256 n) ∧ n < W ∧ ∀ d t, X.tin d v = some t → TermOk e t n := by
  obtain ⟨n, hn, _, hlt⟩ := S.bound (EnvSub.refl e) hv
  refine ⟨n, hn, hlt, fun d t ht => ?_⟩
  unfold StepCtx.tin at ht
  rw [hB, hD] at ht
  obtain ⟨st, hst, ht⟩ := Option.bind_eq_some_iff.mp ht
  unfold instTerm at ht
  split at ht
  · next p hp =>
    split at ht
    · next hc =>
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨n', hn', _, hok⟩ := S.stmt_ok (EnvSub.refl e) c
        (S.unfold_sound (EnvSub.refl e) c hC d) hv hst hp hc
      rw [hn] at hn'; cases hn'
      exact hok
    · cases ht
  · cases ht

/-- A deleted value dominating the point: its output term is its atom or its constant. -/
theorem tout_del_ok {X : StepCtx} {e : Env} (hC : CHolds X.cs e) {u n : Nat}
    (hu : X.outD.find? u = none) (hn : e[u]? = some (.int 256 n)) (hlt : n < W) :
    ∀ d, TermOk e (X.tout d (.var u)) n := by
  intro d
  rw [tout_del hu]
  cases hcs : X.cs.find? u with
  | some c0 =>
    have := hC u c0 n hcs hn
    subst this
    exact termOk_lit hlt
  | none => exact termOk_atom hn hlt

theorem kbOf_eq (K : NatMap KB) (v : Nat) : kbOf K v = kbOf K v := rfl

/-- One justification of `v ↦ x`, at a point where both terms evaluate. -/
theorem entryDirect_sound {X : StepCtx} {m : Mode} (hm : m = .exact ∨ m = .sccp ∨ m = .scalar) {e : Env}
    (hK : KBHolds X.K e) (hC : CHolds X.cs e) {v : Nat} {x : Operand} {nv : Nat}
    (hv : e[v]? = some (.int 256 nv)) (hvt : ∀ d t, X.tin d v = some t → TermOk e t nv)
    {nx : Nat} (hx : opVal e x = some (.int 256 nx)) (hxt : ∀ d, TermOk e (X.tout d x) nx)
    (hphi : m = .sccp → X.phiFold v x = true → opVal e (.var v) = opVal e x)
    (h : entryDirect X m v x = true) : opVal e x = opVal e (.var v) := by
  have exact_case : (depths.any fun dd => (X.tin dd.1 v).any fun t =>
      checkExact (kbOf X.K) t (X.tout dd.2 x)) = true → opVal e x = opVal e (.var v) := by
    intro h
    obtain ⟨dd, _, h⟩ := List.any_eq_true.mp h
    rcases ht : X.tin dd.1 v with _ | t
    · rw [ht] at h; cases h
    rw [ht] at h
    have hc : checkExact (kbOf X.K) t (X.tout dd.2 x) = true := h
    have h1 := hvt dd.1 t ht
    have h2 := hxt dd.2
    have hf : FactsOn (kbOf X.K) (envWord e) [t, X.tout dd.2 x] := factsOn_env hK fun a ha => by
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · exact h1.2 a ha
      · exact h2.2 a ha
    have := checkExact_sound hc hf
    rw [h1.1, h2.1] at this
    subst this
    rw [hx]; exact hv.symm
  rcases hm with rfl | rfl | rfl
  · exact exact_case h
  · simp only [entryDirect, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · cases x with
      | var => simp at h
      | imm bits c0 =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        simp only [opVal, Option.some.injEq, Val.int.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have := hC v _ nv h.1 hv
        rw [Nat.mod_eq_of_lt h.2] at this
        subst this
        simp [opVal, hv]
    · exact (hphi rfl h).symm
    · exact exact_case h
  · exact exact_case h

/-- A folded phi's value: the phi of its block. -/
theorem phiFold_def {X : StepCtx} {v : Nat} {x : Operand} (h : X.phiFold v x = true) :
    ∃ B, X.inD.find? v = some (.phi B) := by
  unfold StepCtx.phiFold at h
  split at h
  · next B hB => exact ⟨B, hB⟩
  · cases h

/-- The justification of `v ↦ x` holds at a point where the input reads `v` and the output's
    term of `x` evaluates. -/
theorem entryOk_sound {X : StepCtx} {m : Mode} (hm : m = .exact ∨ m = .sccp ∨ m = .scalar)
    (hB : X.inB = .ofListBy (·.id) f.blocks) (hD : X.inD = defsOf f) {dels : List Nat}
    (hfresh : ∀ u ∈ dels, X.outD.find? u = none) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (c : Ctx) (hK : KBHolds X.K e) (hC : CHolds X.cs e)
    (hT : m = .sccp → TPI X f e b) {x : Operand} {nx : Nat} (hx : opVal e x = some (.int 256 nx))
    (hxt : ∀ d, TermOk e (X.tout d x) nx) :
    ∀ n v, DomAt f (domTree f) b k v → entryOk X m dels n v x = true →
      opVal e x = opVal e (.var v) := by
  have hphi : ∀ v y, DomAt f (domTree f) b k v → m = .sccp → X.phiFold v y = true →
      opVal e (.var v) = opVal e y := fun v y hv hms hpf => by
    obtain ⟨B, hB'⟩ := phiFold_def hpf
    rw [hD] at hB'
    have hdef := defsOf_mem hB'
    exact hT hms v y hpf B hdef (anc_of_domAt_phi S.uniq hv hdef)
  intro n
  induction n with
  | zero =>
    intro v hv h
    obtain ⟨nv, hnv, _, hvt⟩ := tin_ok hB hD S c hC hv
    exact entryDirect_sound hm hK hC hnv hvt hx hxt (fun hms => hphi v x hv hms) h
  | succ n ih =>
    intro v hv h
    obtain ⟨nv, hnv, _, hvt⟩ := tin_ok hB hD S c hC hv
    simp only [entryOk, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨o, ho, h⟩
    · exact entryDirect_sound hm hK hC hnv hvt hx hxt (fun hms => hphi v x hv hms) h
    cases o with
    | imm => cases h
    | var u =>
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨⟨hu, hdir⟩, hrest⟩ := h
      -- `u` is an operand of `v`'s definition, which dominates the point
      unfold StepCtx.inOps at ho
      rcases hst : defStmt X.inB X.inD v with _ | st
      · rw [hst] at ho; cases ho
      rw [hst] at ho
      simp only [Option.map_some, Option.getD_some] at ho
      rw [hB, hD] at hst
      obtain ⟨e0, _, hroot, hbroot⟩ := S.root
      obtain ⟨d0, j0, blk0, hdef, hb0, hj0, _⟩ := defStmt_spec (Func.wf_ids S.wf) hst
      have hbef := before_of_domAt S.uniq hv hdef
      have hreach : ((domTree f).reach.find? d0).isSome = true := by
        rcases hbef with ⟨_, ha⟩ | ⟨rfl, _⟩
        · exact S.anc d0 ha
        · exact S.reach
      have hud : DomAt f (domTree f) b k u :=
        domAt_trans hroot hbroot (stmt_operand S.wf S.ssa hb0 hreach hj0 ho) hbef
      obtain ⟨nu, hnu, _, hlu⟩ := S.bound (EnvSub.refl e) hud
      have h1 : opVal e (.var u) = opVal e (.var v) :=
        entryDirect_sound hm hK hC hnv hvt (by simp [opVal, hnu]) (tout_del_ok hC (hfresh u hu) hnu hlu)
          (fun hms => hphi v _ hv hms) hdir
      rw [ih u hud hrest, h1]

/-- A paired line's operand: at a point where the input reads `o` and the output `subst σ o`,
    the input's environment gives both the same value. -/
theorem alias_use (A : AF m f s F pairs deleted σ) (hm : m = .exact ∨ m = .sccp ∨ m = .scalar) {e e' : Env}
    {b k k' : Nat} (S : SidePt sig syms f e b k) (S' : SidePt sig syms s.func e' b k')
    (hsub : EnvSub e' e) (c : Ctx) (hK : KBHolds (ctxOf m f s F).K e)
    (hC : CHolds (ctxOf m f s F).cs e) (hT : m = .sccp → TPI (ctxOf m f s F) f e b)
    {o : Operand} (ho : ∀ v, o = .var v → DomAt f (domTree f) b k v)
    (hw' : (subst σ o).wf = true) (hd' : ∀ w, subst σ o = .var w → DomAt s.func (domTree s.func) b k' w)
    (hkey : ∀ v x, o = .var v → σ.find? v = some x →
      entryOk (ctxOf m f s F) m (deleted.flatMap lineDefs) 3 v x = true) :
    opVal e (subst σ o) = opVal e o := by
  cases o with
  | imm => rfl
  | var v =>
    cases hx : σ.find? v with
    | none => simp [subst, hx]
    | some x =>
      have hsx : subst σ (.var v) = x := by simp [subst, hx]
      rw [hsx] at hw' hd' ⊢
      obtain ⟨nx, hnx, _, hxt⟩ := S'.unfold_sound hsub c hC 0 x hw' hd'
      have hxe : opVal e x = some (.int 256 nx) := hsub.opVal (opVal_of_intVal hnx)
      refine entryOk_sound hm rfl rfl (fun u hu => A.fresh u hu) S c hK hC hT hxe
        (fun d => ?_) 3 v (ho v rfl) (hkey v x rfl hx)
      obtain ⟨nx', hnx', _, hok⟩ := S'.unfold_sound hsub c hC d x hw' hd'
      rw [hnx] at hnx'; cases hnx'
      exact hok

end entry

end Fe.Sonatina.Steps.Schemas
