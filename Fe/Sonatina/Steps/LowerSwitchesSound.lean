import Fe.Sonatina.Steps.Validate

/-!
# `lower_switches` is sound

The simulation (`LSCtx.R`, with the input's `BlockInv`): the output at an input block `b`,
entered from `p'`, is the input at `b` entered from the block `p'` stands for (`lab`: itself,
or a leaf's switch); the output at a node `n` of the tree of the switch of block `r`, on the
interval `[a, b)`, is the input entering `t` from `r`, where the input's scrutinee `v` lies in
`[a, b)` and `t` is the input table's target for `v`.  The output's environment agrees with the
input's on every value the input mentions (`Agree`); it also binds the trees' fresh `lt`
results.

A lowered switch's block steps with the input's: the input's phis and statements on both
sides, then the output's `lt` and `br` to a node of an interval holding `v`, where the input's
table goes to `t`.  An internal node steps alone (`Sim.of_steps_env`), its `lt` bound and the
interval narrowed; a leaf steps alone to the table's target for `v`, which on its interval is
the input's (`leafOk_sel`), and arrives as from `r`.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## The values the input mentions -/

namespace LSCtx

/-- `o` is an immediate or a value the input mentions. -/
def inV (X : LSCtx) (o : Operand) : Prop := ∀ u, o = .var u → (X.V.find? u).isSome = true

/-- The environments agree on every value the input mentions. -/
def Agree (X : LSCtx) (env' env : Env) : Prop :=
  ∀ k, (X.V.find? k).isSome = true → env'[k]? = env[k]?

variable {X : LSCtx}

theorem Agree.opVal {env' env : Env} (h : X.Agree env' env) {o : Operand} (ho : X.inV o) :
    opVal env' o = opVal env o := by
  cases o with
  | var u => exact h u (ho u rfl)
  | imm => rfl

theorem Agree.fold {env' env : Env} (h : X.Agree env' env) :
    ∀ l : List ((Nat × Ty) × Val), X.Agree (l.foldl bindStep env') (l.foldl bindStep env)
  | [] => h
  | x :: l => by
    rw [List.foldl_cons, List.foldl_cons]
    refine Agree.fold (fun k hk => ?_) l
    unfold bindStep
    rw [env_insert_get, env_insert_get]
    split
    · rfl
    · exact h k hk

theorem Agree.insert_fresh {env' env : Env} (h : X.Agree env' env) {d : Nat}
    (hd : X.fresh d = true) (v : Val) : X.Agree (env'.insert d v) env := fun k hk => by
  rw [env_insert_get]
  split
  · next e =>
    subst e
    rw [LSCtx.fresh, Option.isNone_iff_eq_none] at hd
    rw [hd] at hk
    cases hk
  · exact h k hk

end LSCtx

theorem LSCtx.of_V {f f' : Func} {u : Nat} (h : u ∈ funcVars f) :
    ((LSCtx.of f f').V.find? u).isSome = true := by
  show ((NatMap.ofList ((funcVars f).map (·, ()))).find? u).isSome = true
  rw [NatMap.find?_ofList, List.lookup_isSome_iff]
  exact ⟨(u, ()), List.mem_map_of_mem h, by simp⟩

theorem LSCtx.of_B (f f' : Func) (id : Nat) : (LSCtx.of f f').B.find? id = f.block? id := by
  show (NatMap.ofListBy (·.id) f.blocks).find? id = _
  rw [NatMap.find?_ofListBy]; rfl

theorem LSCtx.of_B' (f f' : Func) (id : Nat) : (LSCtx.of f f').B'.find? id = f'.block? id := by
  show (NatMap.ofListBy (·.id) f'.blocks).find? id = _
  rw [NatMap.find?_ofListBy]; rfl

theorem opVar_mem {o : Operand} {u : Nat} {l : List Operand} (ho : o ∈ l) (hu : o = .var u) :
    u ∈ l.filterMap opVar :=
  List.mem_filterMap.mpr ⟨o, ho, by rw [hu]; rfl⟩

theorem vars_stmt {f : Func} {b : Block} (hb : b ∈ f.blocks) {s : Stmt} (hs : s ∈ b.body)
    {o : Operand} (ho : o ∈ s.inst.args) {u : Nat} (hu : o = .var u) : u ∈ funcVars f := by
  unfold funcVars
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, ?_⟩)
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, ?_⟩))
  exact List.mem_append_right _ (opVar_mem ho hu)

theorem vars_term {f : Func} {b : Block} (hb : b ∈ f.blocks) {o : Operand} (ho : o ∈ b.term.args)
    {u : Nat} (hu : o = .var u) : u ∈ funcVars f := by
  unfold funcVars
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, List.mem_append_right _
    (opVar_mem ho hu)⟩)

theorem vars_phi {f : Func} {b : Block} (hb : b ∈ f.blocks) {φ : Phi} (hφ : φ ∈ b.phis)
    {p : Operand × Nat} (hp : p ∈ φ.incoming) {u : Nat} (hu : p.1 = .var u) : u ∈ funcVars f := by
  unfold funcVars
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, ?_⟩)
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨φ, hφ, ?_⟩))
  exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨p, hp, by rw [hu]; rfl⟩)

/-! ## Runs in agreeing environments -/

theorem mapM_congr' {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {F G : α → m β} :
    ∀ {l : List α}, (∀ a ∈ l, F a = G a) → l.mapM F = l.mapM G
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

section congr

variable {env' env : Env}

theorem ev_congr_env {o : Operand} (h : opVal env' o = opVal env o) :
    evalOperand env' o = evalOperand env o ∧ evalInt env' o = evalInt env o ∧
      evalWord env' o = evalWord env o := by
  have hi : evalInt env' o = evalInt env o := by
    rw [evalInt_eq, evalInt_eq]; unfold intVal; rw [h]
  exact ⟨by rw [evalOperand_eq, evalOperand_eq, h], hi, by unfold evalWord; rw [hi]⟩

theorem runInst_congr (c : Ctx) (i : Inst) (h : ∀ o ∈ i.args, opVal env' o = opVal env o) :
    runInst c env' i = runInst c env i := by
  have E := fun o ho => ev_congr_env (env' := env') (env := env) (o := o) (h o ho)
  cases i
  case evm op args =>
    simp only [runInst]
    rw [mapM_congr' (l := args) fun o ho => (E o ho).2.2]
  case keccakWords ws =>
    simp only [runInst]
    rw [mapM_congr' (l := ws) fun o ho => (E o ho).2.2]
  case call => rfl
  case select c a b =>
    simp only [Inst.args, List.forall_mem_cons] at E
    simp only [runInst, E.1.2.1]
    congr 1; funext x; rcases x with ⟨_, n⟩
    cases hc : (n != 0) <;> simp only [Bool.false_eq_true, ↓reduceIte, E.2.1.1, E.2.2.1]
  all_goals simp only [Inst.args, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true] at E
  all_goals simp only [runInst, evalPair, E]

theorem runStmtO_congr (o : Oracle) (c : Ctx) (s : Stmt)
    (h : ∀ a ∈ s.inst.args, opVal env' a = opVal env a) :
    runStmtO o c env' s = runStmtO o c env s := by
  rcases s with ⟨dsts, inst⟩
  cases inst
  case call callee args =>
    simp only [runStmtO]
    rw [mapM_congr' (l := args) fun a ha => (ev_congr_env (h a ha)).1]
  all_goals exact runInst_congr c _ h

/-- A terminator's result with its environment replaced. -/
def Next.reenv (e : Env) : Next → Next
  | .goto _ d => .goto e d
  | .done v => .done v

theorem stuck_bind {α β : Type} (k : α → FeM β) : (stuck >>= k) = stuck := rfl

theorem runTerm_congr (t : Term) (h : ∀ o ∈ t.args, opVal env' o = opVal env o) :
    runTerm env' t = runTerm env t >>= fun n => pure (n.reenv env') := by
  have E := fun o ho => ev_congr_env (env' := env') (env := env) (o := o) (h o ho)
  cases t
  case jump d => simp only [runTerm, pure_bind, Next.reenv]
  case br cnd nz z =>
    have Ec := E cnd (by simp [Term.args])
    simp only [runTerm, Ec.2.1, bind_assoc, pure_bind, Next.reenv]
  case brTable sc d cs =>
    have Es := E sc (List.mem_cons_self ..)
    have Ec : ∀ c ∈ cs, evalInt env' c.1 = evalInt env c.1 := fun c hc =>
      (E c.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))).2.1
    simp only [runTerm, Es.2.1, bind_assoc]
    congr 1; funext x; rcases x with ⟨_, v⟩
    dsimp only
    congr 1
    · apply mapM_congr'
      rintro ⟨o, dest⟩ hc
      have := Ec _ hc
      dsimp only at this ⊢
      rw [this]
    · funext vals
      split
      · simp only [pure_bind, Next.reenv]
      · rfl
  case ret vs =>
    simp only [runTerm, bind_assoc, pure_bind, Next.reenv]
    rw [mapM_congr' (l := vs) fun o ho => (E o ho).1]
  case evmReturn a l =>
    have Ea := E a (by simp [Term.args])
    have El := E l (by simp [Term.args])
    simp only [runTerm, Ea.2.2, El.2.2, bind_assoc]
    congr 1
  case evmRevert a l =>
    have Ea := E a (by simp [Term.args])
    have El := E l (by simp [Term.args])
    simp only [runTerm, Ea.2.2, El.2.2, bind_assoc]
    congr 1
  case evmSelfDestruct a =>
    have Ea := E a (by simp [Term.args])
    simp only [runTerm, Ea.2.2, bind_assoc]
    congr 1; funext x; congr 1; funext e; exact e.elim
  case evmStop =>
    simp only [runTerm, bind_assoc]
    congr 1; funext e; exact e.elim
  case evmInvalid =>
    simp only [runTerm, bind_assoc]
    congr 1; funext e; exact e.elim
  case unreachable =>
    simp only [runTerm, bind_assoc]
    congr 1; funext e; exact e.elim

/-- A terminator run in an agreeing environment: its targets and values are the input's. -/
theorem approx_runTerm_agree {t : Term} (h : ∀ o ∈ t.args, opVal env' o = opVal env o)
    (he : EnvInt env) :
    Approx (fun n' n => match n', n with
      | .goto e' d', .goto e d => e' = env' ∧ e = env ∧ d' = d ∧ d ∈ t.succs
      | .done v', .done v => v' = v
      | _, _ => False) (runTerm env' t) (runTerm env t) := by
  rw [runTerm_congr t h]
  conv => rhs; rw [← bind_pure (runTerm env t)]
  refine Approx.bind (Approx.strengthen (Approx.runTerm env t) (returns_runTerm he t))
    fun n' n ⟨e, hn⟩ => ?_
  subst e
  refine Approx.pure ?_
  cases n' with
  | goto e d => obtain ⟨rfl, hd⟩ := hn; exact ⟨rfl, rfl, rfl, hd⟩
  | done v => rfl

end congr

theorem forall₂_with_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ (fun a b => R a b ∧ b ∈ l₂) l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons ⟨h, List.mem_cons_self ..⟩
      ((forall₂_with_mem t).imp fun _ _ ⟨h₁, h₂⟩ => ⟨h₁, List.mem_cons_of_mem _ h₂⟩)

namespace LSCtx

variable {X : LSCtx}

theorem approx_runBodyO {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    ∀ (stmts : List Stmt) (env' env : Env), X.Agree env' env → EnvInt env →
      (∀ s ∈ stmts, s.inst.machine = true ∧ ∀ a ∈ s.inst.args, X.inV a) →
      Approx X.Agree (runBodyO o c env' stmts) (runBodyO o c env stmts)
  | [], _, _, ha, _, _ => Approx.pure ha
  | s :: rest, env', env, ha, he, hs => by
    obtain ⟨hm, hargs⟩ := hs s (List.mem_cons_self ..)
    unfold runBodyO
    rw [runStmtO_congr o c s fun a h => ha.opVal (hargs a h)]
    refine Approx.bind (Approx.strengthen (Approx.runStmtO_sub ho (EnvSub.refl env) he s hm)
      (returns_runStmtO hoi c he hm)) fun vals vals₀ ⟨e, hv⟩ => ?_
    cases e
    refine Approx.bind (Approx.strengthen (bind_rel env' env s.dsts vals) (returns_bind_int he hv))
      fun e₁' e₁ ⟨⟨_, h₁, h₂⟩, he₁⟩ => ?_
    subst h₁ h₂
    exact approx_runBodyO ho hoi c rest _ _ (ha.fold _) he₁ fun s hs' =>
      hs s (List.mem_cons_of_mem _ hs')

theorem phisOk_forall₂ {b : Nat} :
    ∀ {ps' ps : List Phi}, X.phisOk b ps' ps = true →
      List.Forall₂ (fun p' p => X.phiOk b p' p = true) ps' ps
  | [], [], _ => .nil
  | p' :: ps', p :: ps, h => by
    simp only [LSCtx.phisOk, Bool.and_eq_true] at h
    exact .cons h.1 (phisOk_forall₂ h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [LSCtx.phisOk] at h

theorem phisOk_dsts {b : Nat} :
    ∀ {ps' ps : List Phi}, X.phisOk b ps' ps = true →
      ps'.map (fun phi => (phi.dst, phi.ty)) = ps.map (fun phi => (phi.dst, phi.ty))
  | [], [], _ => rfl
  | p' :: ps', p :: ps, h => by
    simp only [LSCtx.phisOk, LSCtx.phiOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [List.map_cons, h.1.1.1.1, h.1.1.1.2, phisOk_dsts h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [LSCtx.phisOk] at h

/-- Entering a block whose phis the check accepts, in an agreeing environment, approximates
    entering the input's from the block its predecessor stands for. -/
theorem approx_enter {b : Nat} {b' bb : Block} (h : X.phisOk b b'.phis bb.phis = true)
    (hin : ∀ φ ∈ bb.phis, ∀ p ∈ φ.incoming, X.inV p.1) {env' env : Env} (ha : X.Agree env' env)
    (prev' : Option Nat) :
    Approx X.Agree (enter env' prev' b') (enter env (prev'.bind X.lab) bb) := by
  unfold enter
  rw [phisOk_dsts h]
  refine Approx.bind (R := List.Forall₂ Eq) (Approx.mapM_rel (P := fun p' p =>
      X.phiOk b p' p = true ∧ p ∈ bb.phis) ?_ ?_) fun vals' vals hv => ?_
  · intro p' p ⟨hp, hpm⟩
    simp only [LSCtx.phiOk, Bool.and_eq_true, List.all_eq_true] at hp
    obtain ⟨⟨_, hinc⟩, _⟩ := hp
    cases prev' with
    | none => exact Approx.stuck _
    | some q' =>
      dsimp only [Option.bind]
      rcases hf : p'.incoming.find? (·.2 == q') with _ | ⟨o, q''⟩
      · rw [hf]; exact Approx.stuck _
      rw [hf]
      have hq : q'' = q' := by simpa using List.find?_some hf
      subst hq
      have hl := hinc _ (List.mem_of_find?_eq_some hf)
      simp only at hl
      rcases hlab : X.lab q'' with _ | q
      · rw [hlab] at hl; cases hl
      rw [hlab] at hl
      dsimp only
      simp only [decide_eq_true_eq] at hl
      unfold inc at hl
      rcases hg : p.incoming.find? (·.2 == q) with _ | ⟨o', q₂⟩
      · rw [hg] at hl; cases hl
      rw [hg] at hl
      rw [hg]
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      dsimp only
      rw [(ev_congr_env (ha.opVal (hin p hpm _ (List.mem_of_find?_eq_some hg)))).1]
      exact Approx.evalOperand (EnvSub.refl env) _
  · exact forall₂_with_mem (phisOk_forall₂ h)
  · rw [List.forall₂_eq_eq_eq] at hv
    subst hv
    refine Approx.mono (bind_rel env' env _ _) fun a' a ⟨_, h₁, h₂⟩ => ?_
    subst h₁ h₂
    exact ha.fold _

theorem pivot?_spec {s : Operand} {st : Stmt} {c : Operand} {k : Nat}
    (h : X.pivot? s st c = some k) :
    ∃ d, st = ⟨[(d, .int 256)], .cmp .lt s (.imm 256 k)⟩ ∧ c = .var d ∧ X.fresh d = true := by
  rcases st with ⟨dsts, inst⟩
  unfold LSCtx.pivot? at h
  split at h
  · next d ty s' bits k' hd hi =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, rfl, rfl, rfl, hf⟩ := hc
      simp only at hd hi
      subst hd hi
      exact ⟨d, rfl, rfl, hf⟩
    · cases h
  · cases h

end LSCtx

/-! ## Tables on intervals -/

theorem look_some {cs : List (Operand × Nat)} {k t : Nat} (h : look cs k = some t) :
    ∃ c ∈ cs, c.1.immVal? = some k ∧ c.2 = t := by
  unfold look at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c, List.mem_of_find?_eq_some hc, by simpa using List.find?_some hc, rfl⟩

/-- On its interval, a leaf's table goes where the input's does. -/
theorem leafOk_sel {a b v : Nat} {cs cs' : List (Operand × Nat)} (h : leafOk a b cs cs' = true)
    (hav : a ≤ v) (hvb : v < b) (D : Nat) :
    (look cs' v <|> some D) = some ((look cs v).getD D) := by
  simp only [leafOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases hl : look cs v with
  | some t =>
    obtain ⟨c, hc, hk, rfl⟩ := look_some hl
    have := h₂ c hc
    rw [hk] at this
    simp only [hav, hvb, and_self, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [this]; rfl
  | none =>
    cases hl' : look cs' v with
    | none => rfl
    | some t' =>
      obtain ⟨c, hc, hk, rfl⟩ := look_some hl'
      have := h₁ c hc
      rw [hk] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      rw [hl] at this
      cases this.2

theorem mapM_pure {α β : Type} {F : α → FeM β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, F a = pure (g a)) → l.mapM F = pure (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_pure fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp only [pure_bind, List.map_cons]

theorem find_keys (v : Nat) : ∀ {cs : List (Operand × Nat)}, (∀ c ∈ cs, c.1.immVal?.isSome = true) →
    ((cs.map fun c => ((c.1.immVal?).getD 0, c.2)).find? (·.1 == v)).map (·.2) = look cs v
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (h c (List.mem_cons_self ..))
    have ih := find_keys v (cs := cs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold look at ih ⊢
    simp only [List.map_cons, List.find?_cons, hk, Option.getD_some]
    by_cases hkv : k = v
    · subst hkv; simp
    · have : (k == v) = false := by simpa using hkv
      have h' : (some k == some v) = false := by simpa using hkv
      simp only [this, h']
      exact ih

/-- A table of immediate keys, its scrutinee an integer, goes to its target for the
    scrutinee's value. -/
theorem runTerm_table {env : Env} {sc : Operand} {d : Option Nat} {cs : List (Operand × Nat)}
    {bits v : Nat} (hs : intVal env sc = some (bits, v))
    (hk : ∀ c ∈ cs, c.1.immVal?.isSome = true) {t : Nat} (ht : (look cs v <|> d) = some t) :
    runTerm env (.brTable sc d cs) = pure (.goto env t) := by
  simp only [runTerm, evalInt_eq, hs, lift, pure_bind]
  rw [mapM_pure (g := fun c => ((c.1.immVal?).getD 0, c.2)) fun c hc => ?_]
  · simp only [pure_bind, find_keys v hk, ht]
  · rcases c with ⟨o, dest⟩
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp (hk _ hc)
    cases o with
    | var => cases hk'
    | imm b k₀ =>
      simp only [Operand.immVal?, Option.some.injEq] at hk'
      subst hk'
      simp only [intVal, opVal, pure_bind, Option.getD_some, Operand.immVal?]

theorem intVal_lt {env : Env} (hw : EnvW env) {o : Operand} (ho : o.wf = true) {bits n : Nat}
    (h : intVal env o = some (bits, n)) : n < 2 ^ 256 := by
  cases o with
  | var u =>
    simp only [intVal, opVal] at h
    rcases hu : env[u]? with _ | val
    · rw [hu] at h; cases h
    obtain ⟨m, hm, rfl⟩ := hw u val hu
    rw [hu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hm
  | imm b k =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
    simp only [intVal, opVal, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ ho.2

theorem enter_nil {env : Env} {prev : Option Nat} {b : Block} (h : b.phis = []) :
    enter env prev b = pure env := by
  simp [Fe.Sonatina.enter, h, Fe.Sonatina.bind]

/-- A leaf block steps to its table's target. -/
theorem stepBlock_leaf {o : Oracle} {c : Ctx} {f' : Func} {env : Env} {prev : Option Nat}
    {n : Nat} {nb : Block} (hnb : f'.block? n = some nb) (hph : nb.phis = []) (hbo : nb.body = [])
    {sc : Operand} {d : Option Nat} {cs : List (Operand × Nat)} (htm : nb.term = .brTable sc d cs)
    {bits v : Nat} (hs : intVal env sc = some (bits, v))
    (hk : ∀ c ∈ cs, c.1.immVal?.isSome = true) {t : Nat} (ht : (look cs v <|> d) = some t) :
    stepBlock o c f' env prev n = pure (.goto env t) := by
  simp only [stepBlock, hnb, enter_nil hph, pure_bind, hbo, runBodyO, htm,
    runTerm_table hs hk ht]

/-- An internal node's `lt` and `br`: to the side of the pivot that holds the scrutinee. -/
theorem lt_br_run (o : Oracle) (c : Ctx) (env : Env) (d : Nat) (sc : Operand) (k lo hi v : Nat)
    (hs : intVal env sc = some (256, v)) :
    (runBodyO o c env [⟨[(d, .int 256)], .cmp .lt sc (.imm 256 k)⟩] >>=
      fun e => runTerm e (.br (.var d) lo hi)) =
      pure (.goto (env.insert d (.int 256 (if v < k then 1 else 0))) (if v < k then lo else hi)) := by
  have h1 : evalInt env sc = pure (256, v) := by rw [evalInt_eq, hs]; rfl
  have h2 : evalInt env (.imm 256 k) = pure (256, k) := rfl
  have h3 : ∀ x, evalInt (env.insert d (.int 256 x)) (.var d) = pure (256, x) := fun x => by
    rw [evalInt_eq]; simp [intVal, opVal]; rfl
  have hb : (bool (decide (v < k))).as (.int 256) = .int 256 (if v < k then 1 else 0) := by
    by_cases hvk : v < k <;> simp [hvk, bool, Val.as, Ty.bits]
  simp only [runBodyO, runStmtO, runInst, evalPair, h1, h2, pure_bind, beq_self_eq_true,
    ↓reduceIte, CmpOp.eval, Fe.Sonatina.bind, List.length_cons, List.length_nil,
    List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil, hb, runTerm, h3,
    map_pure, bind_pure_comp]
  by_cases hvk : v < k <;> simp [hvk]

/-- An internal node steps to the side of its pivot that holds the scrutinee, its `lt` bound. -/
theorem stepBlock_node {o : Oracle} {c : Ctx} {f' : Func} {env : Env} {prev : Option Nat}
    {n : Nat} {nb : Block} (hnb : f'.block? n = some nb) (hph : nb.phis = []) {d : Nat}
    {sc : Operand} {k : Nat} (hbo : nb.body = [⟨[(d, .int 256)], .cmp .lt sc (.imm 256 k)⟩])
    {lo hi : Nat} (htm : nb.term = .br (.var d) lo hi) {v : Nat}
    (hs : intVal env sc = some (256, v)) :
    stepBlock o c f' env prev n =
      pure (.goto (env.insert d (.int 256 (if v < k then 1 else 0))) (if v < k then lo else hi)) := by
  simp only [stepBlock, hnb, enter_nil hph, pure_bind, hbo, htm]
  exact lt_br_run o c env d sc k lo hi v hs

/-! ## The simulation -/

namespace LSCtx

/-- The simulation relation: the output at an input block, entered from a block standing for
    the input's predecessor; or the output at a tree node, on an interval holding the input's
    scrutinee, where the input enters the table's target from the switch's block. -/
def R (X : LSCtx) (s' s : BState) : Prop :=
  X.Agree s'.1 s.1 ∧
  ((X.orig s'.2.2 = true ∧ s.2.2 = s'.2.2 ∧ s'.2.1.bind X.lab = s.2.1) ∨
   (∃ r sc D cs fuel a b v, X.nodeOk r sc D cs fuel a b s'.2.2 = true ∧ s.2.1 = some r ∧
     X.inV sc ∧ intVal s.1 sc = some (256, v) ∧ a ≤ v ∧ v < b ∧ s.2.2 = (look cs v).getD D))

end LSCtx

/-- A switch lowering is sound: the output function, its calls run by an oracle that
    approximates itself and returns integers on integers, approximates the well-formed input
    function on integers. -/
theorem lowerSwitches_sound {sig : Sigs} {syms : List String} {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    (hwf : f.wf sig syms = true) (h : checkLowerSwitches f ids s = true) :
    FuncRef o c (some s.func) (some f) := by
  let f' := s.func
  let X := LSCtx.of f f'
  let T := domTree f
  have hm := Func.wf_machine hwf
  unfold checkLowerSwitches at h
  rcases ids with _ | ids
  · simp at h
  rcases he : f.blocks.head? with _ | e
  · simp [he] at h
  rcases he' : s.func.blocks.head? with _ | e'
  · simp [he, he'] at h
  simp only [he, he', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hparams⟩, hentry⟩, hv⟩, hs⟩, hblocks⟩, _⟩, _⟩ := h
  change ∀ b' ∈ f'.blocks, X.blockOk b' = true at hblocks
  change T.valid f = true at hv
  change ssa f T = true at hs
  -- The input's operands are values it mentions.
  have hinStmt : ∀ {b : Block}, b ∈ f.blocks → ∀ st ∈ b.body,
      st.inst.machine = true ∧ ∀ a ∈ st.inst.args, X.inV a := fun hb st hst =>
    ⟨Func.machine_of_mem hm hb st hst, fun a ha u hu => LSCtx.of_V (vars_stmt hb hst ha hu)⟩
  have hinTerm : ∀ {b : Block}, b ∈ f.blocks → ∀ a ∈ b.term.args, X.inV a :=
    fun hb a ha u hu => LSCtx.of_V (vars_term hb ha hu)
  have hinPhi : ∀ {b : Block}, b ∈ f.blocks → ∀ φ ∈ b.phis, ∀ p ∈ φ.incoming, X.inV p.1 :=
    fun hb φ hφ p hp u hu => LSCtx.of_V (vars_phi hb hφ hp hu)
  -- The simulation, with the invariant of the input's state.
  let R : BState → BState → Prop := fun s' s => X.R s' s ∧ BlockInv f T s
  -- An input block of the output steps with the input's.
  have lock : ∀ env' env prev' b, X.orig b = true → X.Agree env' env →
      BlockInv f T (env, prev'.bind X.lab, b) →
      Approx (NextRel R b b) (stepBlock o c f' env' prev' b)
        (stepBlock o c f env (prev'.bind X.lab) b) := by
    intro env' env prev' b horig ha hinv
    refine Approx.mono (Approx.strengthen (S := NextRel X.R b b) ?_
      (stepBlock_inv hwf hv hoi c hinv)) fun n' n ⟨hn, hni⟩ => ?_
    · unfold stepBlock
      cases h' : f'.block? b with
      | none => exact Approx.stuck _
      | some b' =>
        have hb'id : b'.id = b := by simpa using List.find?_some h'
        have hok := hblocks b' (List.mem_of_find?_eq_some h')
        obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.mp horig
        have hbb' : f.block? b = some bb := by rw [← LSCtx.of_B f f']; exact hbb
        have hbbm := List.mem_of_find?_eq_some hbb'
        have hbbid : bb.id = b := by simpa using List.find?_some hbb'
        have hreach : (T.reach.find? b).isSome = true := hinv.2.2.1
        simp only [LSCtx.blockOk, hb'id] at hok
        rw [show X.B.find? b = some bb from hbb] at hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨hphis, hrest⟩ := hok
        rw [hbb']
        dsimp only
        refine Approx.bind (Approx.strengthen (LSCtx.approx_enter hphis (hinPhi hbbm) ha prev')
          (point_zero hwf hv hinv hbb')) fun env₁' env₁ ⟨ha₁, h₀⟩ => ?_
        have htake := point_take hwf hoi c hbb' h₀ bb.body.length le_rfl
        rw [List.take_length] at htake
        split at hrest
        · -- An unchanged block.
          next hterm =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrest
          obtain ⟨hbody, hsuccs⟩ := hrest
          rw [hbody]
          refine Approx.bind (Approx.strengthen (LSCtx.approx_runBodyO ho hoi c bb.body env₁' env₁
            ha₁ h₀.1.int (hinStmt hbbm)) htake) fun env₂' env₂ ⟨ha₂, hpi⟩ => ?_
          rw [hterm]
          refine Approx.mono (approx_runTerm_agree (fun a hx => ha₂.opVal (hinTerm hbbm a hx))
            hpi.1.int) fun n' n hn => ?_
          cases n' <;> cases n <;> simp only [NextRel] at hn ⊢
          · obtain ⟨rfl, rfl, rfl, hd⟩ := hn
            refine ⟨ha₂, Or.inl ⟨hsuccs _ (hterm ▸ hd), rfl, ?_⟩⟩
            simp [LSCtx.lab, horig]
          · exact hn
        · -- A lowered switch.
          next hterm =>
          unfold LSCtx.rootOk at hrest
          split at hrest
          · next sc D cs st cnd lo hi hbt hlast hbt' =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrest
            obtain ⟨⟨⟨hcs, hD⟩, hbody⟩, hrest⟩ := hrest
            split at hrest
            · next k hpiv =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
              obtain ⟨⟨⟨hk0, hk1⟩, hlo⟩, hhi⟩ := hrest
              obtain ⟨d, rfl, rfl, hfresh⟩ := LSCtx.pivot?_spec hpiv
              rw [hbody, runBodyO_append, bind_assoc]
              refine Approx.bind (Approx.strengthen (LSCtx.approx_runBodyO ho hoi c bb.body env₁'
                env₁ ha₁ h₀.1.int (hinStmt hbbm)) htake) fun env₂' env₂ ⟨ha₂, hpi⟩ => ?_
              have hsc : sc ∈ bb.term.args := by rw [hbt]; exact List.mem_cons_self ..
              obtain ⟨v, hvv⟩ := term_defined hwf hs hbb' hreach hpi sc hsc
              have hvlt : v < 2 ^ 256 :=
                intVal_lt hpi.1 ((Func.wf_operands hwf hbbm).2.2 sc hsc) hvv
              have hv' : intVal env₂' sc = some (256, v) := by
                unfold intVal; rw [ha₂.opVal (hinTerm hbbm sc hsc)]; exact hvv
              have hkeys : ∀ c ∈ cs, c.1.immVal?.isSome = true := fun c hc => (hcs c hc).2
              rw [hbt, hbt', runTerm_table hvv hkeys (t := (look cs v).getD D)
                (by cases look cs v <;> rfl)]
              -- The output's `lt` and `br`.
              have hout := lt_br_run o c env₂' d sc k lo hi v hv'
              rw [hout]
              refine Approx.pure ⟨ha₂.insert_fresh hfresh _, Or.inr ?_⟩
              by_cases hvk : v < k
              · simp only [hvk, ↓reduceIte]
                exact ⟨b, sc, D, cs, X.fuel, 0, k, v, hb'id ▸ hlo, rfl,
                  hinTerm hbbm sc hsc, hvv, Nat.zero_le _, hvk, rfl⟩
              · simp only [hvk, ↓reduceIte]
                exact ⟨b, sc, D, cs, X.fuel, k, 2 ^ 256, v, hb'id ▸ hhi, rfl,
                  hinTerm hbbm sc hsc, hvv, Nat.le_of_not_lt hvk, hvlt, rfl⟩
            · cases hrest
          · cases hrest
    · cases n' <;> cases n <;> simp only [NextRel, NextInv] at hn hni ⊢
      · exact ⟨hn, hni⟩
      · exact hn
  have sim : Sim o c f' f R := by
    refine Sim.of_steps_env fun s' s hR => ?_
    rcases s' with ⟨env', prev', b'⟩
    rcases s with ⟨env, prev, b⟩
    obtain ⟨⟨ha, hR⟩, hinv⟩ := hR
    simp only at ha hR
    rcases hR with ⟨horig, rfl, hprev⟩ | ⟨r, sc, D, cs, fuel, a, bnd, v, hnode, hprev, hsc, hvv,
      hav, hvb, ht⟩
    · left; subst hprev; exact lock env' env prev' _ horig ha hinv
    · right
      have hv' : intVal env' sc = some (256, v) := by unfold intVal; rw [ha.opVal hsc]; exact hvv
      cases fuel with
      | zero => simp [LSCtx.nodeOk] at hnode
      | succ fuel =>
      unfold LSCtx.nodeOk at hnode
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnode
      obtain ⟨hnew, hnode⟩ := hnode
      rcases hfind : X.B'.find? b' with _ | nb
      · rw [hfind] at hnode; cases hnode
      rw [hfind] at hnode
      have hnb : f'.block? b' = some nb := by rw [← LSCtx.of_B' f f']; exact hfind
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hnode
      obtain ⟨hph, hnode⟩ := hnode
      split at hnode
      · -- A leaf.
        next sc' D' cs' hbo htm =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hnode
        obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hD⟩, hcs'⟩, hlab⟩, hleaf⟩, _⟩ := hnode
        have hsel := leafOk_sel hleaf hav hvb D'
        have hkeys : ∀ c ∈ cs', c.1.immVal?.isSome = true := fun c hc => by
          simp only [leafOk, Bool.and_eq_true, List.all_eq_true] at hleaf
          have := hleaf.1 c hc
          revert this; cases c.1.immVal? <;> simp
        refine ⟨env', (look cs v).getD D', fun I w => ?_, ?_⟩
        · rw [stepBlock_leaf hnb hph hbo htm hv' hkeys hsel]; rfl
        · refine ⟨⟨ha, Or.inl ⟨?_, ht, ?_⟩⟩, hinv⟩
          · show X.orig ((look cs v).getD D') = true
            rcases hl' : look cs' v with _ | t'
            · rw [hl'] at hsel
              have e : some D' = some ((look cs v).getD D') := hsel
              rw [← Option.some.inj e]; exact hD
            · rw [hl'] at hsel
              have e : some t' = some ((look cs v).getD D') := hsel
              obtain ⟨cc, hcc, _, hc2⟩ := look_some hl'
              rw [← Option.some.inj e, ← hc2]; exact hcs' cc hcc
          · simp only [Option.bind_some]; rw [hlab, hprev]
      · -- An internal node.
        next st cnd lo hi hbo htm =>
        split at hnode
        · next k hpiv =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hnode
          obtain ⟨⟨_, hlo⟩, hhi⟩ := hnode
          obtain ⟨d, rfl, rfl, hfresh⟩ := LSCtx.pivot?_spec hpiv
          refine ⟨env'.insert d (.int 256 (if v < k then 1 else 0)), if v < k then lo else hi,
            fun I w => ?_, ?_⟩
          · rw [stepBlock_node hnb hph hbo htm hv']; rfl
          · refine ⟨⟨ha.insert_fresh hfresh _, Or.inr ?_⟩, hinv⟩
            by_cases hvk : v < k
            · simp only [hvk, ↓reduceIte]
              exact ⟨r, sc, D, cs, fuel, a, k, v, hlo, hprev, hsc, hvv, hav, hvk, ht⟩
            · simp only [hvk, ↓reduceIte]
              exact ⟨r, sc, D, cs, fuel, k, bnd, v, hhi, hprev, hsc, hvv, Nat.le_of_not_lt hvk,
                hvb, ht⟩
        · cases hnode
      · cases hnode
  intro args hargs
  unfold runFuncO
  dsimp only
  rw [he, he']
  dsimp only
  rw [hparams]
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _) (entry_inv hwf hv he hargs))
    fun env env₀ ⟨e₁, hi⟩ => ?_
  cases e₁
  have horig : X.orig e.id = true := by
    show ((LSCtx.of f f').B.find? e.id).isSome = true
    rw [LSCtx.of_B]
    unfold Func.block?
    exact List.find?_isSome.mpr ⟨e, List.mem_of_mem_head? he, by simp⟩
  exact Sim.approx sim (env, none, e'.id) (env, none, e.id)
    ⟨⟨fun _ _ => rfl, Or.inl ⟨hentry ▸ horig, hentry.symm, rfl⟩⟩, hi⟩

theorem lowerSwitches_stepSound : StepSound .lowerSwitches :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    lowerSwitches_sound ho hoi c hw (by simp only [checkFunc, Bool.and_eq_true] at h; exact h.2)

end Fe.Sonatina.Steps
