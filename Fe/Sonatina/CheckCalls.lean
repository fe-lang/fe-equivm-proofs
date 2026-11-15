import Fe.Sonatina.CheckSection

/-!
# Internal calls

The soundness of the checker for sections with several functions.  A block's statements are
segments of events between calls (`Ctx.segments`).

`body_calls`, the IR side: the interpreter runs a block's statements, calls included, as `Segs`
says under any valuation `ρ` of the values they define: each segment's events trace the world,
and each call runs its callee on the words of its arguments, which either ends the block (it is
stuck, or fails), or returns the words the call's results have under `ρ`, where the next
segment goes on, or returns other values, after which the IR's run is no concern of the bytes'
(the callee's bytes then never return).
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

variable {K : Bool} {M : List Made}

/-- How the IR's run of a block's statements goes, from the world `w`, under the valuation `ρ`,
    up to the result `r` of the statements: the events `evs` trace the world up to the first
    of the calls `cls`, and each call runs its callee on its arguments' words. -/
inductive Segs (ee : ExecutionEnv) (g : Guard) (m : Module) (ic : Fe.Sonatina.Ctx) (inh : List Nat)
    (ρ : Nat → UInt256) :
    List Event → List CallSeg → World → Option (Except (Fe.Exit World) World) → Prop
  /-- No call is left: the events end the statements. -/
  | last {evs : List Event} {w : World} {r : Option (Except (Fe.Exit World) World)}
      (h : Trace ee ρ evs w r) : Segs ee g m ic inh ρ evs [] w r
  /-- An event fails before the next call. -/
  | fail {evs : List Event} {cls : List CallSeg} {w : World} {e : Fe.Exit World}
      (h : Trace ee ρ evs w (some (.error e))) : Segs ee g m ic inh ρ evs cls w (some (.error e))
  /-- An event is stuck before the next call. -/
  | stuck {evs : List Event} {cls : List CallSeg} {w : World}
      (h : Trace ee ρ evs w none) : Segs ee g m ic inh ρ evs cls w none
  /-- The callee's run is stuck. -/
  | callNone {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ : World}
      {ws : List UInt256} (h : Trace ee ρ evs w (some (.ok w₁)))
      (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        none) :
      Segs ee g m ic inh ρ evs (cs :: more) w none
  /-- The callee's run fails. -/
  | callErr {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ : World}
      {ws : List UInt256} {e : Fe.Exit World} (h : Trace ee ρ evs w (some (.ok w₁)))
      (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        some (.error e)) (hp : ∀ c, e ≠ .panic c) :
      Segs ee g m ic inh ρ evs (cs :: more) w (some (.error e))
  /-- The callee returns the words of the call's results, and the next segment goes on. -/
  | callOk {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ w₂ : World}
      {ws : List UInt256} {r : Option (Except (Fe.Exit World) World)}
      (h : Trace ee ρ evs w (some (.ok w₁))) (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        some (.ok ((cs.dsts.map ρ).map Fe.Sonatina.word, w₂)))
      (hk : ∀ a ∈ cs.keep, w₂.memory.readWithPadding a 32 = w₁.memory.readWithPadding a 32)
      (rest : Segs ee g m ic inh ρ cs.events more w₂ r) : Segs ee g m ic inh ρ evs (cs :: more) w r
  /-- The callee returns other than as many words as the call has results. -/
  | callOther {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ w₂ : World}
      {ws : List UInt256} {vals : List Val} {r : Option (Except (Fe.Exit World) World)}
      (h : Trace ee ρ evs w (some (.ok w₁))) (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        some (.ok (vals, w₂)))
      (hv : ∀ ws' : List UInt256, vals = ws'.map Fe.Sonatina.word → ws'.length ≠ cs.dsts.length) :
      Segs ee g m ic inh ρ evs (cs :: more) w r

/-- A guard list one statement on. -/
theorem drop_succ_tail {α : Type} (l : List α) (n : Nat) : l.drop (n + 1) = l.tail.drop n := by
  cases l <;> simp

/-- A block's statements up to the first call, and the rest after it. -/
theorem segments_call {c : Ctx} : ∀ {ps : List (List Nat)} {k : Nat} {stmts : List Stmt}
    {evs : List Event} {cs : CallSeg} {more : List CallSeg},
    c.segments ps k stmts = some (evs, cs :: more) →
    ∃ pre s q args ce, stmts = pre ++ s :: q ∧ (∀ t ∈ pre, ∀ g a, t.inst ≠ .call g a) ∧
      c.events ps k pre = some evs ∧ s.inst = .call cs.callee args ∧
      args.mapM (c.operand) = some cs.args ∧ cs.dsts = s.dsts.map (·.1) ∧
      c.frame.callee cs.callee = some ce ∧ cs.args.length = ce.params ∧
      s.dsts.length = (if ce.returns then ce.rets else 0) ∧
      cs.keep = (ps.drop pre.length).headD [] ∧
      c.segments (ps.drop pre.length).tail (k + pre.length + 1) q = some (cs.events, more)
  | _, _, [], evs, cs, more, h => by simp [Ctx.segments] at h
  | ps, k, s :: rest, evs, cs, more, h => by
    unfold Ctx.segments at h
    cases hr : c.segments ps.tail (k + 1) rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · next g args hg =>
        cases hce : c.frame.callee g with
        | none => simp [hce] at h
        | some ce =>
          cases hes : args.mapM (c.operand) with
          | none => simp [hce, hes] at h
          | some es =>
            simp only [hce, hes, Option.bind_some] at h
            by_cases hk : (es.length == ce.params &&
                s.dsts.length == (if ce.returns then ce.rets else 0)) = true
            · rw [if_pos hk] at h
              simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp only [Bool.and_eq_true, beq_iff_eq] at hk
              exact ⟨[], s, rest, args, ce, rfl, by simp, rfl, hg, hes, rfl, hce, hk.1, hk.2,
                rfl, by simpa using hr⟩
            · rw [if_neg hk] at h
              cases h
      · next hnc =>
        have hnc' : ∀ g a, s.inst ≠ .call g a := fun g a h' => hnc g a h'
        cases he : c.eventOfStmt s with
        | none => simp [he] at h
        | some o =>
          obtain ⟨hevs, hcl⟩ : evs = (o.map (c.annotate ps k s)).toList ++ evs' ∧
              calls' = cs :: more := by
            cases o <;> simp [he] at h <;> exact ⟨by simp [h.1], h.2⟩
          subst hcl
          obtain ⟨pre, s', q, args, ce, rfl, hpre, hev, h1, h2, h3, h4, h5, h6, hkeep, hq⟩ :=
            segments_call hr
          refine ⟨s :: pre, s', q, args, ce, rfl, ?_, ?_, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hnc'
            · exact hpre t ht
          · simp only [Ctx.events, hev, he, Option.bind_some, hevs]
            cases o <;> rfl
          · rw [List.length_cons, drop_succ_tail]; exact hkeep
          · rw [List.length_cons, drop_succ_tail, show k + (pre.length + 1) + 1 =
              k + 1 + pre.length + 1 by omega]
            exact hq

/-- A block's statements without a call left. -/
theorem segments_last {c : Ctx} : ∀ {ps : List (List Nat)} {k : Nat} {stmts : List Stmt}
    {evs : List Event}, c.segments ps k stmts = some (evs, []) →
      (∀ t ∈ stmts, ∀ g a, t.inst ≠ .call g a) ∧ c.events ps k stmts = some evs
  | _, _, [], evs, h => by
    simp only [Ctx.segments, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Ctx.events]
  | ps, k, s :: rest, evs, h => by
    unfold Ctx.segments at h
    cases hr : c.segments ps.tail (k + 1) rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · next g args hg =>
        cases hce : c.frame.callee g with
        | none => simp [hce] at h
        | some ce =>
          cases hes : args.mapM (c.operand) with
          | none => simp [hce, hes] at h
          | some es =>
            simp only [hce, hes, Option.bind_some] at h
            by_cases hk : (es.length == ce.params &&
                s.dsts.length == (if ce.returns then ce.rets else 0)) = true
            · rw [if_pos hk] at h; simp at h
            · rw [if_neg hk] at h; cases h
      · next hnc =>
        cases he : c.eventOfStmt s with
        | none => simp [he] at h
        | some o =>
          obtain ⟨hevs, hcl⟩ : evs = (o.map (c.annotate ps k s)).toList ++ evs' ∧
              calls' = [] := by
            cases o <;> simp [he] at h <;> exact ⟨by simp [h.1], h.2⟩
          subst hcl
          obtain ⟨h1, h2⟩ := segments_last hr
          refine ⟨fun t ht => ?_, ?_⟩
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact fun g a h' => hnc g a h'
            · exact h1 t ht
          · simp only [Ctx.events, h2, he, Option.bind_some, hevs]
            cases o <;> rfl

/-- A message call among a statement's events is the statement's. -/
theorem eventOfStmt_messages {c : Ctx} {s : Stmt} {e : Event}
    (h : c.eventOfStmt s = some (some e)) (hm : messageOps.contains e.op = true) :
    s.inst.messages = true := by
  unfold Ctx.eventOfStmt at h
  split at h
  · split at h <;> simp at h
  · next op args _ hev =>
    have he : e.op = op := by
      split_ifs at h
      split at h <;> first | (simp only [Option.some.injEq] at h; rw [← h]) | cases h
    rw [he] at hm
    rcases eventWith_cases (expand := c.expand) hev with ⟨op', os, hi, ho, -⟩ |
      ⟨a, e', hi, rfl, -, -⟩
    swap
    · simp [messageOps] at hm
    rw [hi]
    cases op'
    case log n =>
      rcases n with _ | _ | _ | _ | _ | n <;> simp only [evmEventOpcode, reduceCtorEq,
        Option.some.injEq] at ho <;> subst ho <;> simp [messageOps] at hm
    all_goals first
      | rfl
      | (simp only [evmEventOpcode, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;>
          simp [messageOps] at hm)
  · cases h

/-- A message call among a block's events is one of its statements'. -/
theorem segments_messages {c : Ctx} : ∀ {ps : List (List Nat)} {k : Nat} {stmts : List Stmt}
    {evs : List Event} {calls : List CallSeg}, c.segments ps k stmts = some (evs, calls) →
    ∀ ev ∈ evs ++ calls.flatMap (·.events), messageOps.contains ev.op = true →
      ∃ s ∈ stmts, s.inst.messages = true
  | _, _, [], evs, calls, h => by
    simp only [Ctx.segments, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | ps, k, s :: rest, evs, calls, h => by
    unfold Ctx.segments at h
    cases hr : c.segments ps.tail (k + 1) rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      have ih : ∀ ev ∈ evs' ++ calls'.flatMap (·.events), messageOps.contains ev.op = true →
          ∃ t ∈ s :: rest, t.inst.messages = true := fun ev hev hm => by
        obtain ⟨t, ht, htm⟩ := segments_messages hr ev hev hm
        exact ⟨t, List.mem_cons_of_mem _ ht, htm⟩
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      intro ev hev hm
      split at h
      · next g args hg =>
        cases hce : c.frame.callee g with
        | none => simp [hce] at h
        | some ce =>
          cases hes : args.mapM (c.operand) with
          | none => simp [hce, hes] at h
          | some es =>
            simp only [hce, hes, Option.bind_some] at h
            by_cases hk : (es.length == ce.params &&
                s.dsts.length == (if ce.returns then ce.rets else 0)) = true
            · rw [if_pos hk] at h
              simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ih ev (by simpa using hev) hm
            · rw [if_neg hk] at h
              cases h
      · cases he : c.eventOfStmt s with
        | none => simp [he] at h
        | some o =>
          cases o with
          | none =>
            simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ih ev hev hm
          | some e =>
            simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases List.mem_append.mp hev with hev | hev
            · rcases List.mem_cons.mp hev with rfl | hev
              · exact ⟨s, .head _, eventOfStmt_messages he (e := e) hm⟩
              · exact ih ev (List.mem_append_left _ hev) hm
            · exact ih ev (List.mem_append_right _ hev) hm

theorem runBodyG_append {g : Guard} {m : Module} {ic : Fe.Sonatina.Ctx} {inh : List Nat} :
    ∀ (ps : List (List Nat)) (env : Env) (p q : List Stmt),
      runBodyG g m ic inh ps env (p ++ q) = runBodyG g m ic inh ps env p >>= fun env' =>
        runBodyG g m ic inh (ps.drop p.length) env' q
  | ps, env, [], q => by rw [runBodyG_nil]; simp
  | ps, env, s :: p, q => by
    have ih := fun env' => runBodyG_append (g := g) (m := m) (ic := ic) (inh := inh) ps.tail env' p q
    rw [List.cons_append, runBodyG.eq_2, runBodyG.eq_2, List.length_cons, drop_succ_tail]
    simp only [ih, bind_assoc]

theorem definedAfter_append : ∀ (D : List Nat) (p q : List Stmt),
    definedAfter D (p ++ q) = (definedAfter D p).bind fun D₁ => definedAfter D₁ q
  | D, [], q => by simp [definedAfter]
  | D, s :: p, q => by
    simp only [List.cons_append, definedAfter]
    split_ifs
    · exact definedAfter_append _ p q
    · rfl

/-- A value that only calls define is not expanded. -/
theorem lookup_none_calls {stmts : List Stmt} {id : Nat}
    (h : ∀ s ∈ stmts, (∀ g a, s.inst ≠ .call g a) → ∀ d ∈ s.dsts, d.1 ≠ id) :
    (stmts.filterMap Stmt.local?).lookup id = none := by
  induction stmts with
  | nil => rfl
  | cons t rest ih =>
    have ih' := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    cases ht : t.local? with
    | none => simpa [List.filterMap_cons, ht] using ih'
    | some p =>
      have hnc : ∀ g a, t.inst ≠ .call g a := by
        intro g a hc
        simp [Stmt.local?, hc] at ht
      have hp : p.1 ≠ id := by
        have ht := local_def ht
        unfold Stmt.def? at ht
        split at ht
        · next id' ty' hd => cases ht; exact h t (by simp) hnc (id', ty') (by simp [hd])
        · cases ht
      have hb : (id == p.1) = false := by simpa using Ne.symm hp
      rw [List.filterMap_cons, ht]
      simp only [List.lookup, hb]
      exact ih'

/-- A call's arguments: their words under any valuation of the values before it, which the
    interpreter passes as words. -/
theorem args_words {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D : List Nat}
    {env : Env} (hc : Cons ee ρ c D) (hw : WordsOf env ρ D) :
    ∀ {args : List Operand} {es : List Expr}, reads D args = true →
      args.mapM (c.operand) = some es →
      ∃ ws, es.mapM (·.eval ee ρ) = some ws ∧
        args.mapM (evalOperand env) = pure (ws.map Fe.Sonatina.word)
  | [], es, _, h => by
    simp at h; subst h; exact ⟨[], rfl, rfl⟩
  | a :: args, es, hr, h => by
    simp only [reads, List.all_cons, Bool.and_eq_true] at hr
    rw [List.mapM_cons] at h
    cases he : c.operand a with
    | none => simp [he] at h
    | some e =>
    cases hes : args.mapM (c.operand) with
    | none => simp [he, hes] at h
    | some es' =>
    simp only [he, hes, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    subst h
    obtain ⟨v, hv, -, hev⟩ := operand_words hc hw (by simpa [reads] using hr.1) he
    obtain ⟨ws, hws, hargs⟩ := args_words hc hw (by simpa [reads] using hr.2) hes
    refine ⟨v :: ws, by simp [List.mapM_cons, hv, hws], ?_⟩
    rw [List.mapM_cons, hev, hargs]
    rfl

/-- Binding words to values defined once: each has its word, the others are kept. -/
theorem foldl_words : ∀ {dsts : List (Nat × Ty)} {ws : List UInt256} (env : Env),
    ws.length = dsts.length → (dsts.map (·.1)).Nodup → (∀ d ∈ dsts, d.2.bits = 256) →
    let env' := (dsts.zip (ws.map Fe.Sonatina.word)).foldl
      (fun env ((id, ty), v) => env.insert id (v.as ty)) env
    (∀ id, id ∉ dsts.map (·.1) → env'[id]? = env[id]?) ∧
      List.Forall₂ (fun d w => env'[d.1]? = some (.int 256 w.toNat)) dsts ws
  | [], [], env, _, _, _ => by simp
  | d :: dsts, w :: ws, env, hl, hnd, hb => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hd := hb d (by simp)
    have ih := foldl_words (env.insert d.1 ((Fe.Sonatina.word w).as d.2)) hl hnd.2
      fun d' h => hb d' (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    refine ⟨fun id hid => ?_, .cons ?_ ih.2⟩
    · simp only [List.mem_cons, not_or] at hid
      rw [ih.1 id hid.2, insert_get, if_neg (Ne.symm hid.1)]
    · rw [ih.1 d.1 hnd.1, insert_get, if_pos rfl]
      simp only [Fe.Sonatina.word, as_word _ hd, Reasoning.Theory.u256_ofNat_toNat]

/-- Values bound to words, which a valuation gives them: it gives them those words. -/
theorem forall₂_words {env : Env} {ρ : Nat → UInt256} :
    ∀ {dsts : List (Nat × Ty)} {ws : List UInt256},
    List.Forall₂ (fun d w => env[d.1]? = some (.int 256 w.toNat)) dsts ws →
    (∀ d ∈ dsts, env[d.1]? = some (.int 256 (ρ d.1).toNat)) → (dsts.map (·.1)).map ρ = ws
  | [], [], .nil, _ => rfl
  | d :: _, _ :: _, .cons h hr, hρ => by
    have := word_inj (Option.some.inj ((hρ d (by simp)).symm.trans h))
    simp [this, forall₂_words hr fun d' h' => hρ d' (List.mem_cons_of_mem _ h')]

theorem forall₂_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b, R a b
  | [], [], .nil, _, h => by cases h
  | _ :: _, b :: _, .cons h hr, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, h⟩
    · exact forall₂_left hr a ha

/-- A value defined before or by the statements is one `definedAfter` collects. -/
theorem definedAfter_dsts : ∀ {stmts : List Stmt} {D D' : List Nat},
    definedAfter D stmts = some D' → ∀ t ∈ stmts, ∀ d ∈ t.dsts, d.1 ∈ D'
  | [], _, _, _, t, ht, _, _ => by cases ht
  | s :: rest, D, D', h, t, ht, d, hd => by
    simp only [definedAfter] at h
    split_ifs at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact definedAfter_mono h _ (List.mem_append_right _ (List.mem_map_of_mem hd))
    · exact definedAfter_dsts h t ht d hd

theorem map_word_inj : ∀ {a b : List UInt256},
    a.map Fe.Sonatina.word = b.map Fe.Sonatina.word → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [word_inj h.1, map_word_inj h.2]

theorem pure_inj {α : Type} {a b : α} (h : (pure a : FeM α) = pure b) : a = b := by
  have := congrArg (fun x : FeM α => x.exec default (World.init ∅ default)) h
  simpa using this

/-- The interpreter runs a block's statements of the class, calls included, as `Segs` says
    under any valuation of the values they define: up to the end, or, where a callee returns
    other than the call's words, up to that call. -/
theorem body_calls {ee : ExecutionEnv} {g : Guard} {m : Module} {ic : Fe.Sonatina.Ctx}
    {inh : List Nat} {c : Ctx} (hsym : ic.symbol = (c.symbols.lookup ·)) :
    ∀ (calls : List CallSeg) (stmts pre : List Stmt) (ps : List (List Nat)) (k : Nat)
      (D D' : List Nat) (env : Env) (w : World) (evs : List Event),
      c.defs = (pre ++ stmts).filterMap Stmt.local? →
      (∀ t ∈ pre, ∀ d ∈ t.dsts, d.1 ∈ D) →
      definedAfter D stmts = some D' →
      c.segments ps k stmts = some (evs, calls) →
      (∀ s ∈ stmts, ∀ d ∈ s.dsts, d.2.bits = 256) →
      (∀ s ∈ stmts, (s.dsts.map (·.1)).Nodup) →
      (∃ ρ, WordsOf env ρ D) → (∀ ρ, WordsOf env ρ D → Cons ee ρ c D) →
      NoPanicAt ((runBodyG g m ic inh ps env stmts).exec ee w) →
      ∃ x, (runBodyG g m ic inh ps env stmts).exec ee w = x ∧ ∃ envf Df,
        (∀ id ∈ D, envf[id]? = env[id]?) ∧ (∀ id ∈ D, id ∈ Df) ∧ (∀ id ∈ Df, id ∈ D') ∧
        (∃ ρ, WordsOf envf ρ Df) ∧
        (((∀ env' w', x = some (.ok (env', w')) → envf = env' ∧ Df = D') ∧
            ∀ ρ, WordsOf envf ρ Df → Cons ee ρ c Df ∧
              Segs ee g m ic inh ρ evs calls w (x.map (·.map Prod.snd))) ∨
          ∀ ρ, WordsOf envf ρ Df → Cons ee ρ c Df ∧ Segs ee g m ic inh ρ evs calls w none)
  | [], stmts, pre, ps, k, D, D', env, w, evs, hdefs, hpre, hd, hseg, hbits, _, hw, hc, hnp => by
    obtain ⟨-, hev⟩ := segments_last hseg
    obtain ⟨x, hx, hends⟩ := body_run (m := m) hsym stmts pre ps k D D' env w evs []
      (by rw [hdefs, List.append_nil]) hpre hd hev
      hbits hw hc hnp
    refine ⟨x, hx, ?_⟩
    rcases x with _ | _ | ⟨env', w'⟩
    rotate_left 2
    · obtain ⟨h1, h2, h3⟩ := hends
      exact ⟨env', D', h1, definedAfter_mono hd, fun _ h => h, h2, .inl ⟨(fun _ _ h => by
        cases h; exact ⟨rfl, rfl⟩), fun ρ hρ => ⟨(h3 ρ hρ).1, .last (h3 ρ hρ).2⟩⟩⟩
    all_goals
      obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends
      exact ⟨envf, Df, h1, h2, h2', h3, .inl ⟨(fun _ _ h => by cases h),
        fun ρ hρ => ⟨(h4 ρ hρ).1, .last (h4 ρ hρ).2⟩⟩⟩
  | cs :: more, stmts, pre, ps, k, D, D', env, w, evs, hdefs, hpre, hd, hseg, hbits, hndd, hw, hc,
      hnp => by
    obtain ⟨p0, s, q, args, ce, rfl, -, hev, hinst, hargs, hdsts, -, -, hdl, hkp, hq⟩ :=
      segments_call hseg
    rw [definedAfter_append] at hd
    cases hD1 : definedAfter D p0 with
    | none => simp [hD1] at hd
    | some D1 =>
    simp only [hD1, Option.bind_some, definedAfter] at hd
    split_ifs at hd with hok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨hrd, hfr⟩ := hok
    have hrd' : reads D1 args = true := by simpa [hinst, Inst.operands] using hrd
    have hfr' : ∀ d ∈ s.dsts, d.1 ∉ D1 := fun d hd' h => by
      simpa [List.contains_iff_mem, h] using hfr d hd'
    set ps1 := ps.drop p0.length with hps1
    have hx0 : (runBodyG g m ic inh ps env (p0 ++ s :: q)).exec ee w =
        (runBodyG g m ic inh ps env p0 >>= fun env' =>
          runBodyG g m ic inh ps1 env' (s :: q)).exec ee w := by
      rw [runBodyG_append]
    rw [hx0] at hnp
    obtain ⟨hnp0, hnp1⟩ := NoPanicAt.of_bind hnp
    obtain ⟨x1, hx1, hends1⟩ := body_run (m := m) hsym p0 pre ps k D D1 env w evs (s :: q)
      (by rw [hdefs, List.append_assoc]) hpre hD1 hev
      (fun t ht => hbits t (by simp [ht])) hw hc hnp0
    have hD1sub := definedAfter_mono hD1
    rcases x1 with _ | e | ⟨env1, w1⟩
    · have hx : (runBodyG g m ic inh ps env (p0 ++ s :: q)).exec ee w = none := by
        rw [hx0, Fe.M.exec_bind, hx1]
      obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends1
      exact ⟨none, hx, envf, Df, h1, h2,
        fun id h => definedAfter_mono hd id (List.mem_append_left _ (h2' id h)), h3,
        .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h4 ρ hρ).1, .stuck (h4 ρ hρ).2⟩⟩⟩
    · have hx : (runBodyG g m ic inh ps env (p0 ++ s :: q)).exec ee w = some (.error e) := by
        rw [hx0, Fe.M.exec_bind, hx1]
      obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends1
      exact ⟨some (.error e), hx, envf, Df, h1, h2,
        fun id h => definedAfter_mono hd id (List.mem_append_left _ (h2' id h)), h3,
        .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h4 ρ hρ).1, .fail (h4 ρ hρ).2⟩⟩⟩
    have hx : (runBodyG g m ic inh ps env (p0 ++ s :: q)).exec ee w =
        (runBodyG g m ic inh ps1 env1 (s :: q)).exec ee w1 := by
      rw [hx0, Fe.M.exec_bind, hx1]
    have hnpc := hnp1 _ _ hx1
    obtain ⟨h1, ⟨ρ1, hw1⟩, h3⟩ := hends1
    obtain ⟨ws, -, hevargs⟩ := args_words (h3 ρ1 hw1).1 hw1 hrd' hargs
    -- Under any valuation of the values before the call, its arguments have the same words.
    have hws : ∀ ρ, WordsOf env1 ρ D1 → cs.args.mapM (·.eval ee ρ) = some ws := fun ρ hρ => by
      obtain ⟨ws', hm, he⟩ := args_words (h3 ρ hρ).1 hρ hrd' hargs
      rw [hm, map_word_inj (pure_inj (he.symm.trans hevargs))]
    have hcall : runBodyG g m ic inh ps1 env1 (s :: q) =
        guarded (inh ++ cs.keep)
          (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)) >>= fun vals =>
          Fe.Sonatina.bind env1 s.dsts vals >>= fun env' => runBodyG g m ic inh ps1.tail env' q := by
      rw [runBodyG.eq_2]
      simp only [hinst, hevargs, pure_bind, hkp]
    rw [hcall] at hnpc
    obtain ⟨hnpg, hnpk⟩ := NoPanicAt.of_bind hnpc
    obtain ⟨hgx, hkept⟩ := guarded_exec hnpg
    have hD1D' : ∀ id ∈ D1, id ∈ D' := fun id h =>
      definedAfter_mono hd id (List.mem_append_left _ h)
    cases hz : (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec ee w1 with
    | none =>
      refine ⟨none, by rw [hx, hcall, Fe.M.exec_bind, hgx, hz], env1, D1, h1, hD1sub, hD1D',
        ⟨ρ1, hw1⟩, .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩⟩
      exact .callNone (h3 ρ hρ).2 (hws ρ hρ) hz
    | some z =>
    cases z with
    | error e =>
      refine ⟨some (.error e), by rw [hx, hcall, Fe.M.exec_bind, hgx, hz], env1, D1, h1,
        hD1sub, hD1D', ⟨ρ1, hw1⟩, .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩⟩
      exact .callErr (h3 ρ hρ).2 (hws ρ hρ) hz fun c hc => hnpg c (by rw [hgx, hz, hc])
    | ok p =>
    obtain ⟨vals, w2⟩ := p
    by_cases hvw : ∃ ws' : List UInt256, vals = ws'.map Fe.Sonatina.word ∧
      ws'.length = s.dsts.length
    swap
    · refine ⟨_, rfl, env1, D1, h1, hD1sub, hD1D', ⟨ρ1, hw1⟩, .inr fun ρ hρ =>
        ⟨(h3 ρ hρ).1, .callOther (h3 ρ hρ).2 (hws ρ hρ) hz fun ws' hv hl => ?_⟩⟩
      exact hvw ⟨ws', hv, by rw [hl, hdsts, List.length_map]⟩
    obtain ⟨ws', rfl, hlen⟩ := hvw
    have hnds : (s.dsts.map (·.1)).Nodup := hndd s (by simp)
    have hbs : ∀ d ∈ s.dsts, d.2.bits = 256 := hbits s (by simp)
    obtain ⟨hkeep, hfa⟩ := foldl_words env1 hlen hnds hbs
    set env2 := (s.dsts.zip (ws'.map Fe.Sonatina.word)).foldl
      (fun env ((id, ty), v) => env.insert id (v.as ty)) env1 with henv2
    have hbind : Fe.Sonatina.bind env1 s.dsts (ws'.map Fe.Sonatina.word) = pure env2 := by
      simp [Fe.Sonatina.bind, hlen, henv2]
    have hagree2 : ∀ id ∈ D1, env2[id]? = env1[id]? := fun id h =>
      hkeep id fun hm => by
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hm
        exact hfr' d hd' h
    have hdefs2 : c.defs = ((pre ++ p0 ++ [s]) ++ q).filterMap Stmt.local? := by
      rw [hdefs]; simp
    have hpre2 : ∀ t ∈ pre ++ p0 ++ [s], ∀ d ∈ t.dsts, d.1 ∈ D1 ++ s.dsts.map (·.1) := by
      intro t ht d hdt
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact List.mem_append_left _ (hD1sub _ (hpre t ht d hdt))
      · exact List.mem_append_left _ (definedAfter_dsts hD1 t ht d hdt)
      · exact List.mem_append_right _ (List.mem_map_of_mem hdt)
    have hw2 : WordsOf env2 (wordsOf env2) (D1 ++ s.dsts.map (·.1)) :=
      wordsOf_words fun id hid => by
      rcases List.mem_append.mp hid with h | h
      · rw [hagree2 id h, hw1 id h]; exact ⟨_, rfl, (ρ1 id).val.isLt⟩
      · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp h
        obtain ⟨w', hw'⟩ := forall₂_left hfa d hd'
        exact ⟨_, hw', w'.val.isLt⟩
    -- The call's results: no statement but the call defines them.
    have hnone : ∀ id ∈ s.dsts.map (·.1), c.defs.lookup id = none := fun id hid => by
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hid
      rw [hdefs]
      refine lookup_none_calls fun t ht hnc d hdt hdi => ?_
      simp only [List.mem_append, List.mem_cons] at ht
      rcases ht with ht | ht | rfl | ht
      · exact hfr' d0 hd0 (hdi ▸ hD1sub _ (hpre t ht d hdt))
      · exact hfr' d0 hd0 (hdi ▸ definedAfter_dsts hD1 t ht d hdt)
      · exact hnc _ _ hinst
      · exact definedAfter_fresh hd t ht d hdt (hdi ▸ List.mem_append_right _
          (List.mem_map_of_mem hd0))
    have hc2 : ∀ ρ, WordsOf env2 ρ (D1 ++ s.dsts.map (·.1)) →
        Cons ee ρ c (D1 ++ s.dsts.map (·.1)) := fun ρ hρ => by
      have hc1 := (h3 ρ fun id h => (hagree2 id h).symm.trans (hρ id (List.mem_append_left _ h))).1
      refine hc1.mono (fun x hx => List.mem_append_left _ hx) fun id hid hn => ?_
      rcases List.mem_append.mp hid with h | h
      · exact absurd h hn
      · refine ⟨fun inst hl => (by rw [hnone id h] at hl; cases hl), fun e he => ?_⟩
        rw [expand_atom hc1.1 (hnone id h)] at he
        cases he
        rfl
    have hnpq := hnpk _ _ (hgx.trans hz)
    simp only [hbind, pure_bind] at hnpq
    obtain ⟨x, hx2, envf, Df, g1, g2, g3, g4, g5⟩ := body_calls hsym more q (pre ++ p0 ++ [s])
      ps1.tail (k + p0.length + 1) (D1 ++ s.dsts.map (·.1)) D' env2 w2 cs.events hdefs2 hpre2 hd
      hq (fun t ht => hbits t (by simp [ht])) (fun t ht => hndd t (by simp [ht])) ⟨_, hw2⟩ hc2
      hnpq
    have hxe : (runBodyG g m ic inh ps env (p0 ++ s :: q)).exec ee w = x := by
      rw [hx, hcall, Fe.M.exec_bind, hgx, hz]
      simp only [hbind, pure_bind]
      exact hx2
    have hsub2 : ∀ id ∈ D1, id ∈ Df := fun id h => g2 id (List.mem_append_left _ h)
    -- What a valuation of the values after the call gives before it and to its results.
    have hρ1 : ∀ ρ, WordsOf envf ρ Df → WordsOf env1 ρ D1 := fun ρ hρ id h =>
      ((g1 id (List.mem_append_left _ h)).trans (hagree2 id h)).symm.trans (hρ id (hsub2 id h))
    have hres : ∀ ρ, WordsOf envf ρ Df → cs.dsts.map ρ = ws' := fun ρ hρ => by
      rw [hdsts]
      exact forall₂_words hfa fun d hd' =>
        (g1 d.1 (List.mem_append_right _ (List.mem_map_of_mem hd'))).symm.trans
          (hρ d.1 (g2 d.1 (List.mem_append_right _ (List.mem_map_of_mem hd'))))
    have hseg : ∀ ρ, WordsOf envf ρ Df → ∀ r, Segs ee g m ic inh ρ cs.events more w2 r →
        Segs ee g m ic inh ρ evs (cs :: more) w r := fun ρ hρ r hr =>
      .callOk (h3 ρ (hρ1 ρ hρ)).2 (hws ρ (hρ1 ρ hρ)) (by rw [hres ρ hρ]; exact hz)
        (fun a ha => hkept _ _ hz a (List.mem_append_right _ ha)) hr
    refine ⟨x, hxe, envf, Df, fun id h => (g1 id (List.mem_append_left _ (hD1sub id h))).trans
      ((hagree2 id (hD1sub id h)).trans (h1 id h)), fun id h => hsub2 id (hD1sub id h), g3, g4,
      ?_⟩
    rcases g5 with ⟨gok, gs⟩ | gs
    · exact .inl ⟨gok, fun ρ hρ => ⟨(gs ρ hρ).1, hseg ρ hρ _ (gs ρ hρ).2⟩⟩
    · exact .inr fun ρ hρ => ⟨(gs ρ hρ).1, hseg ρ hρ _ (gs ρ hρ).2⟩

/-! ## The bytes of a block with calls -/

theorem Steps.append {D : Array UInt256} {s s₁ : State}
    {r : Except ExecutionException (State × Option (HaltCause × ByteArray))} {n k : Nat}
    (h : Steps K D s (.ok (s₁, none)) n) (h' : Steps K D s₁ r k) : Steps K D s r (n + k) := by
  generalize hx : (Except.ok (s₁, none) : Except ExecutionException _) = x at h
  induction h with
  | step hc hs henv =>
    subst hx
    rw [Nat.add_comm]
    exact .trans hc hs (henv _ rfl) h'
  | trans hc hs henv _ ih =>
    rw [Nat.add_right_comm]
    exact .trans hc hs henv (ih hx)

theorem Steps.gas_lt {D : Array UInt256} {s s' : State} {n : Nat}
    (h : Steps K D s (.ok (s', none)) n) :
    s'.machineState.gasAvailable.toNat < s.machineState.gasAvailable.toNat := by
  generalize hx : (Except.ok (s', none) : Except ExecutionException _) = x at h
  induction h with
  | step _ hs _ =>
    subst hx
    have := Xstep_gas_decreases_of_continues hs
    omega
  | trans _ hs _ _ ih =>
    have := Xstep_gas_decreases_of_continues hs
    have := ih hx
    omega

theorem Steps.env {D : Array UInt256} {s s' : State} {n : Nat}
    (h : Steps K D s (.ok (s', none)) n) : s'.executionEnv = s.executionEnv := by
  generalize hx : (Except.ok (s', none) : Except ExecutionException _) = x at h
  induction h with
  | step _ _ henv => subst hx; exact henv _ rfl
  | trans _ _ henv _ ih => exact (ih hx).trans henv

theorem Final.prepend {D : Array UInt256} {s s₁ : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} {n : Nat}
    (h : Steps K D s (.ok (s₁, none)) n) (hf : Final K M D s₁ r) : Final K M D s r := by
  rcases hf with ⟨k, e, hx, he⟩ | ⟨k, s', out, w', hx, h2⟩ | ⟨k, s', data, hx, h2⟩
  · exact .inl ⟨n + k, e, h.append hx, he⟩
  · exact .inr (.inl ⟨n + k, s', out, w', h.append hx, h2⟩)
  · exact .inr (.inr ⟨n + k, s', data, h.append hx, h2⟩)

theorem Ends.prepend {code : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint} {place : Nat → Option Nat} {b : Nat} {B : List UInt256}
    {e0 ex ex₁ : Exit} {cls : List CallSeg} {s s₁ : State} {r : Except (Fe.Exit World) World}
    {n : Nat} (h : Steps K (D_J I.code 0) s (.ok (s₁, none)) n)
    (he : Ends K M code I ρ c hints place b B e0 ex₁ cls s₁ r) :
    Ends K M code I ρ c hints place b B e0 ex cls s r := by
  generalize hx : (Except.ok (s₁, none) : Except ExecutionException _) = x at h
  induction h generalizing ex with
  | step hc hs henv => subst hx; exact Ends.cons hc hs (henv _ rfl) he
  | trans hc hs henv _ ih => exact Ends.cons (ex₁ := ex) hc hs henv (ih hx)

/-- The bytes end from `st` as the IR's run `r` ends, or return as it does: they reach the
    return address `ret` with the values' words on top of `B`, the world agreeing. -/
def Final' (K : Bool) (M : List Made) (D : Array UInt256) (st : State)
    (r : Option (Except (Fe.Exit World) (List Val × World))) (ret : Option UInt256)
    (B : List UInt256) (nrets : Nat) : Prop :=
  Final K M D st r ∨ ∃ k ws w' n st', ret = some k ∧ r = some (.ok (ws.map Fe.Sonatina.word, w')) ∧
    ws.length = nrets ∧ Steps K D st (.ok (st', none)) n ∧ st'.machineState.pc = k ∧
    st'.machineState.stack = ws ++ B ∧ st'.executionEnv = st.executionEnv ∧ Agree M st' w'

theorem Final'.prepend {D : Array UInt256} {s s₁ : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} {ret : Option UInt256}
    {B : List UInt256} {nrets n : Nat} (h : Steps K D s (.ok (s₁, none)) n)
    (hf : Final' K M D s₁ r ret B nrets) : Final' K M D s r ret B nrets := by
  rcases hf with hf | ⟨k, ws, w', m, st', h1, h2, h3, hx, h4, h5, h6, h7⟩
  · exact .inl (hf.prepend h)
  · exact .inr ⟨k, ws, w', n + m, st', h1, h2, h3, h.append hx, h4, h5, h6.trans h.env, h7⟩

/-- How the bytes end as the IR's run of a block's statements `r` ends, the world only. -/
def FinalW (K : Bool) (M : List Made) (D : Array UInt256) (st : State) (r : Option (Except (Fe.Exit World) World)) :
    Prop :=
  Final K M D st (r.map (·.map fun w => ([], w)))

/-- Out of gas or stack, the bytes end as any run of the IR. -/
theorem Final.exhausted {D : Array UInt256} {st : State} {e : ExecutionException} {n : Nat}
    (h : Steps K D st (.error e) n) (he : e = .OutOfGass ∨ e = .StackOverflow)
    {r : Option (Except (Fe.Exit World) (List Val × World))} : Final K M D st r :=
  .inl ⟨n, e, h, by rcases he with rfl | rfl <;> simp⟩

/-- What the bytes do from where a callee's result is not the IR's: they run out of gas or
    stack. -/
theorem Final.of_ok {D : Array UInt256} {st : State} {vals : List Val} {w : World}
    (h : Final K M D st (some (.ok (vals, w))))
    {r : Option (Except (Fe.Exit World) (List Val × World))} :
    Final K M D st r := by
  rcases h with ⟨n, e, hx, he⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h⟩
  · rcases he with rfl | rfl | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact .exhausted hx (.inl rfl)
    · exact .exhausted hx (.inr rfl)
    · cases h
    · cases h
    · cases h
  · cases h
  · cases h

/-- An event's failure ends the bytes as it ends the IR's run. -/
theorem Final.of_fails {D : Array UInt256} {st : State} {f : Fe.Exit World}
    {e : ExecutionException} {n : Nat} (hx : Steps K D st (.error e) n) (hf : Fails f e) :
    Final K M D st (some (.error f)) := by
  refine .inl ⟨n, e, hx, ?_⟩
  cases f <;> simp only [Fails] at hf <;> subst hf <;> simp

/-- A callee's ending is the block's: its failure, or getting stuck. -/
theorem FinalW.of_callee {D : Array UInt256} {st : State}
    {z : Option (Except (Fe.Exit World) (List Val × World))}
    (h : Final K M D st z) (hz : ∀ vals w, z ≠ some (.ok (vals, w))) :
    FinalW K M D st (z.map (·.map Prod.snd)) := by
  unfold FinalW
  rcases z with _ | _ | ⟨vals, w⟩
  · exact h
  · exact h
  · exact absurd rfl (hz vals w)

theorem validJump_D_J {code tail : ByteArray} {I : ExecutionEnv} {t : Nat}
    (hsize : code.size < UInt256.size) (hI : I.code = code ++ tail)
    (hj : validJump code (jumpdests code) t = true) :
    (D_J I.code 0).contains (UInt256.ofNat t) = true ∧ (UInt256.ofNat t).toNat = t := by
  simp only [validJump, Bool.and_eq_true, decide_eq_true_eq] at hj
  refine ⟨by rw [hI]; exact D_J_append (jumpdests_D_J hj.2), ?_⟩
  rw [toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The calls of a block's segments name callees, with as many arguments as they take and as
    many results as they return. -/
theorem segments_calls {c : Ctx} : ∀ {ps : List (List Nat)} {k : Nat} {stmts : List Stmt}
    {evs : List Event} {calls : List CallSeg}, c.segments ps k stmts = some (evs, calls) →
    ∀ cs ∈ calls, ∃ ce, c.frame.callee cs.callee = some ce ∧ cs.args.length = ce.params ∧
      cs.dsts.length = (if ce.returns then ce.rets else 0)
  | _, _, stmts, evs, [], _, cs, hcs => by cases hcs
  | _, _, stmts, evs, cs' :: more, h, cs, hcs => by
    obtain ⟨pre, s, q, args, ce, -, -, -, -, -, hdsts, hce, hargs, hdl, -, hq⟩ := segments_call h
    rcases List.mem_cons.mp hcs with rfl | hcs
    · exact ⟨ce, hce, hargs, by rw [hdsts, List.length_map]; exact hdl⟩
    · exact segments_calls hq cs hcs

/-- The block lemma with calls: a path of block `b`'s bytes that `run` accepts, from where it
    is, under the valuation whose IR's run of the block's statements is `Segs`, ends as that
    run does, at a callee's failure or getting stuck included, or ends as the block's last
    segment does, given that every callee's bytes from its entry, below the block's gas, end as
    its IR's run does. -/
theorem segs_ends {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint} {place : Nat → Option Nat} {b : Nat} {e0 : Exit} {g : Guard}
    {m : Module} {ic : Fe.Sonatina.Ctx} {inh : List Nat} {G : Nat}
    (hsize : code.size < UInt256.size)
    (hretj : c.frame.returns = true → (D_J I.code 0).contains (ρ c.frame.retId) = true)
    (hcanon : c.canon.Valid I ρ)
    (hcallee : ∀ (cs : CallSeg) (ce : Callee) (ws : List UInt256) (st' : State) (w' : World)
      (ret' : Option UInt256) (B' : List UInt256), c.frame.callee cs.callee = some ce →
      st'.machineState.pc.toNat = ce.offset → st'.executionEnv = I → Agree M st' w' →
      ws.length = ce.params →
      st'.machineState.stack = ws ++ (match ret' with | some k => k :: B' | none => B') →
      (ce.returns = true → ∃ k, ret' = some k ∧ (D_J I.code 0).contains k = true) →
      (ce.returns = false → ret' = none) → st'.machineState.gasAvailable.toNat < G →
      NoPanicAt ((runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec I w') →
      Final' K M (D_J I.code 0) st'
        ((runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec I w')
        ret' B' ce.rets) :
    ∀ (calls : List CallSeg) (fuel : Nat) (p : Path) (s : State) (w : World)
      (r : Option (Except (Fe.Exit World) World)) (B : List UInt256), p.calls = calls →
      (∀ ev ∈ p.events ++ calls.flatMap (·.events), messageOps.contains ev.op = true → K = true) →
      (∀ cs ∈ calls, ∃ ce, c.frame.callee cs.callee = some ce ∧ cs.args.length = ce.params ∧
        cs.dsts.length = (if ce.returns then ce.rets else 0)) →
      run code (codeTree code) (jumpdests code) c hints place b fuel p = true →
      PathRel code tail I ρ B e0 p s → Agree M s w →
      Segs I g m ic inh ρ p.events calls w r → s.machineState.gasAvailable.toNat ≤ G →
      FinalW K M (D_J I.code 0) s r ∨
        ∃ w', r = some (.ok w') ∧ Ends K M code I ρ c hints place b B e0 p.exit [] s (some (.ok w'))
  | calls, fuel, p, s, w, r, B, hcl, hK, har, hrun, hp, hw, hseg, hg => by
    -- The bytes up to the segment's end, as `run_ends` gives them.
    have hends := fun r' (htr : Trace I ρ p.events w r') =>
      run_ends (K := K) (tail := tail) (e0 := e0) hsize hretj hcanon fuel p s w r' B
        (fun ev h => hK ev (List.mem_append_left _ h)) hrun hp hw htr
    -- A path whose next call is `cs`, its events done: the bytes end as the callee's IR run,
    -- or the callee returns its words to the code the run goes on at.
    have hcall : ∀ {cs more w₁ ws}, calls = cs :: more → Trace I ρ p.events w (some (.ok w₁)) →
        cs.args.mapM (·.eval I ρ) = some ws →
        NoPanicAt ((runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec I w₁) →
        Final K M (D_J I.code 0) s
          ((runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec I w₁) ∨
        ∃ (ws₂ : List UInt256) (w₂ : World) (s₂ : State) (n : Nat) (restE : List Expr)
          (restW : List UInt256) (ex' : Exit) (fuel' k : Nat),
          (runFuncG g m ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec I w₁ =
            some (.ok (ws₂.map Fe.Sonatina.word, w₂)) ∧ ws₂.length = cs.dsts.length ∧
          Steps K (D_J I.code 0) s (.ok (s₂, none)) n ∧ s₂.machineState.pc = UInt256.ofNat k ∧
          validJump code (jumpdests code) k = true ∧
          s₂.machineState.stack = ws₂ ++ restW ++ B ∧
          restE.mapM (·.eval I ρ) = some restW ∧
          run code (codeTree code) (jumpdests code) c hints place b fuel'
            ⟨k, cs.dsts.map .atom ++ restE, cs.events, ex', more⟩ = true ∧ ex'.Valid I ρ ∧ ExitRel I ρ e0 ex' ∧ s₂.executionEnv = I ∧ Agree M s₂ w₂ := by
      intro cs more w₁ ws hcs htr hargs hnpz
      obtain ⟨ce, hce, hla, hld⟩ := har cs (by rw [hcs]; simp)
      have hE := hends _ htr
      rw [hcl, hcs] at hE
      have hlw : ws.length = ce.params := by
        rw [← hla]; exact (mapM_some_iff.mp hargs).length_eq.symm
      rcases hE with ⟨n, e, hx, he⟩ | ⟨_, _, _, hr, -⟩ | ⟨w₁', hr, ⟨_, _, _, _, _, _, hc0, -⟩ |
          ⟨_, _, _, hc0, -⟩ | ⟨_, _, _, _, hc0, -⟩ | hret | hnr⟩
      · exact .inl (.exhausted hx he)
      · cases hr
      · cases hc0
      · cases hc0
      · cases hc0
      · obtain ⟨cs', more', ce', n, s', ws', k, restE, restW, ex', fuel', hc', hce', hret', hst,
          hpc, hargs', hrestW, hstk, hkj, hrun', hval, hexr, henv, hag⟩ := hret
        simp only [List.cons.injEq] at hc'
        obtain ⟨rfl, rfl⟩ := hc'
        cases hr
        rw [hce] at hce'; cases hce'
        rw [hargs] at hargs'; cases hargs'
        obtain ⟨hkd, -⟩ := validJump_D_J hsize hp.code hkj
        have hf := hcallee cs ce ws s' w₁ (some (UInt256.ofNat k)) (restW ++ B) hce hpc henv hag
          hlw (by simpa using hstk) (fun _ => ⟨_, rfl, hkd⟩) (fun h => by rw [hret'] at h; cases h)
          (by have := hst.gas_lt; omega) hnpz
        rcases hf with hf | ⟨k', ws₂, w₂, n₂, s₂, hk', hr₂, hl₂, hx₂, hpc₂, hstk₂, henv₂, hag₂⟩
        · exact .inl (hf.prepend hst)
        · simp only [Option.some.injEq] at hk'
          subst hk'
          refine .inr ⟨ws₂, w₂, s₂, n + n₂, restE, restW, ex', fuel', k, hr₂,
            by rw [hl₂, hld, if_pos hret'], hst.append hx₂, hpc₂, hkj,
            by rw [hstk₂, List.append_assoc], hrestW, hrun', hval, hexr, henv₂.trans henv, hag₂⟩
      · obtain ⟨cs', ce', n, s', ws', t, hc', hce', hnr, hst, hpc, hargs', hstk, henv, hag⟩ := hnr
        simp only [List.cons.injEq] at hc'
        obtain ⟨rfl, rfl⟩ := hc'
        cases hr
        rw [hce] at hce'; cases hce'
        rw [hargs] at hargs'; cases hargs'
        have hf := hcallee cs ce ws s' w₁ none t hce hpc henv hag hlw (by simpa using hstk)
          (fun h => by rw [hnr] at h; cases h) (fun _ => rfl) (by have := hst.gas_lt; omega) hnpz
        rcases hf with hf | ⟨_, _, _, _, _, h, -⟩
        · exact .inl (hf.prepend hst)
        · cases h
    cases hseg with
    | last htr =>
      rcases hends _ htr with ⟨n, e, hx, he⟩ | ⟨f, e, n, rfl, hf, hx⟩ | ⟨w', rfl, h⟩
      · exact .inl (.exhausted hx he)
      · exact .inl (.of_fails hx hf)
      · rw [hcl] at h
        exact .inr ⟨w', rfl, .inr (.inr ⟨w', rfl, h⟩)⟩
    | fail htr =>
      rcases hends _ htr with ⟨n, e, hx, he⟩ | ⟨f, e, n, hr, hf, hx⟩ | ⟨w', hr, -⟩
      · exact .inl (.exhausted hx he)
      · cases hr
        exact .inl (.of_fails hx hf)
      · cases hr
    | stuck htr =>
      rcases hends _ htr with ⟨n, e, hx, he⟩ | ⟨f, e, n, hr, hf, hx⟩ | ⟨w', hr, -⟩
      · exact .inl (.exhausted hx he)
      · cases hr
      · cases hr
    | callNone htr ha hz =>
      rcases hcall rfl htr ha (by rw [hz]; intro c h; cases h) with hf | ⟨_, _, _, _, _, _, _, _, _, h, -⟩
      · rw [hz] at hf; exact .inl hf
      · rw [hz] at h; cases h
    | callErr htr ha hz hpe =>
      rcases hcall rfl htr ha (by rw [hz]; intro c h; cases h; exact hpe c rfl) with hf | ⟨_, _, _, _, _, _, _, _, _, h, -⟩
      · rw [hz] at hf; exact .inl hf
      · rw [hz] at h; cases h
    | @callOk _ cs more _ w₁ w₂ ws r htr ha hz hkz hrest =>
      rcases hcall rfl htr ha (by rw [hz]; intro c h; cases h) with hf | ⟨ws₂, w₂', s₂, n, restE, restW, ex', fuel', k, h, hl,
          hx, hpc, hkj, hstk, hrestW, hrun', hval, hexr, henv, hag⟩
      · rw [hz] at hf; exact .inl hf.of_ok
      · rw [hz] at h
        simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, rfl⟩ := h
        have hws₂ := map_word_inj hv
        obtain ⟨hkd, hkn⟩ := validJump_D_J hsize hp.code hkj
        have hp' : PathRel code tail I ρ B e0 ⟨k, cs.dsts.map .atom ++ restE, cs.events, ex', more⟩
            s₂ := ⟨henv, hp.code, by rw [hpc, hkn], ⟨cs.dsts.map ρ ++ restW, by
              simp only [List.mapM_append, hrestW]
              rw [show (cs.dsts.map Expr.atom).mapM (·.eval I ρ) = some (cs.dsts.map ρ) by
                clear * -; induction cs.dsts <;> simp_all [List.mapM_cons, Expr.eval]]
              rfl, by rw [hstk, hws₂, List.append_assoc]⟩, hval, hexr⟩
        have har' := fun cs' (h : cs' ∈ more) => har cs' (.tail _ h)
        have hK' : ∀ ev ∈ cs.events ++ more.flatMap (·.events), messageOps.contains ev.op = true →
            K = true := fun ev hev => hK ev (by
          simp only [List.flatMap_cons, List.mem_append] at hev ⊢; exact .inr hev)
        rcases segs_ends hsize hretj hcanon hcallee more fuel' _ s₂ w₂ r B rfl hK' har' hrun' hp' hag
            hrest
            (by have := hx.gas_lt; omega) with h | ⟨w', hr, h⟩
        · exact .inl (h.prepend hx)
        · exact .inr ⟨w', hr, Ends.prepend hx h⟩
    | callOther htr ha hz hv =>
      rcases hcall rfl htr ha (by rw [hz]; intro c h; cases h) with hf | ⟨ws₂, _, _, _, _, _, _, _, _, h, hl, -⟩
      · rw [hz] at hf; exact .inl hf.of_ok
      · rw [hz] at h
        simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        exact absurd hl (hv ws₂ h.1)

/-- Before a function's entry block, the section entry's code stores the free pointer. -/
def preIf (isRoot : Bool) (low : Lowering) (eb b : Block) : FeM Unit :=
  if isRoot then pre low eb b else pure ()

theorem pre_trace' (isRoot : Bool) (low : Lowering) (eb b : Block) (I : ExecutionEnv)
    (w : World) :
    ∃ w₀, (preIf isRoot low eb b).exec I w = some (.ok ((), w₀)) ∧
      ∀ ρ evs r, Trace I ρ evs w₀ r →
        Trace I ρ (prologue low (isRoot && b.id == eb.id) evs) w r := by
  cases isRoot
  · refine ⟨w, rfl, fun ρ evs r h => ?_⟩
    cases low.entryFreePtr <;> simpa [prologue] using h
  · simpa [preIf] using pre_trace low eb b I w

theorem Segs.pre {ee : ExecutionEnv} {g : Guard} {m : Module} {ic : Fe.Sonatina.Ctx} {inh : List Nat}
    {ρ : Nat → UInt256}
    {evs evs' : List Event} {cls : List CallSeg} {w w₀ : World}
    {r : Option (Except (Fe.Exit World) World)}
    (ht : ∀ r, Trace ee ρ evs w₀ r → Trace ee ρ evs' w r) (h : Segs ee g m ic inh ρ evs cls w₀ r) :
    Segs ee g m ic inh ρ evs' cls w r := by
  cases h with
  | last h => exact .last (ht _ h)
  | fail h => exact .fail (ht _ h)
  | stuck h => exact .stuck (ht _ h)
  | callNone h ha hz => exact .callNone (ht _ h) ha hz
  | callErr h ha hz hp => exact .callErr (ht _ h) ha hz hp
  | callOk h ha hz hk hr => exact .callOk (ht _ h) ha hz hk hr
  | callOther h ha hz hv => exact .callOther (ht _ h) ha hz hv

theorem Final.of_none {D : Array UInt256} {st : State} (h : Final K M D st none)
    {r : Option (Except (Fe.Exit World) (List Val × World))} : Final K M D st r := by
  rcases h with ⟨n, e, hx, he⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h⟩
  · rcases he with rfl | rfl | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact .exhausted hx (.inl rfl)
    · exact .exhausted hx (.inr rfl)
    · cases h
    · cases h
    · cases h
  · cases h
  · cases h

/-- A value of the block after its statements was before them, or a statement defines it. -/
theorem definedAfter_sub : ∀ {stmts : List Stmt} {D D' : List Nat},
    definedAfter D stmts = some D' → ∀ id ∈ D', id ∈ D ∨ ∃ s ∈ stmts, ∃ d ∈ s.dsts, d.1 = id
  | [], D, D', h, id, hid => by simp [definedAfter] at h; exact .inl (h ▸ hid)
  | s :: rest, D, D', h, id, hid => by
    simp only [definedAfter] at h
    split_ifs at h
    rcases definedAfter_sub h id hid with h' | ⟨t, ht, d, hd, rfl⟩
    · rcases List.mem_append.mp h' with h' | h'
      · exact .inl h'
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h'
        exact .inr ⟨s, by simp, d, hd, rfl⟩
    · exact .inr ⟨t, List.mem_cons_of_mem _ ht, d, hd, rfl⟩

/-- A block whose exit is a return ends in `ret`. -/
theorem exitOf_ret_eq {c : Ctx} {t : Term} {vals : List Expr}
    (h : c.exitOf t = some (.ret vals)) :
    ∃ vs, t = .ret vs ∧ vs.mapM (c.operand) = some vals := by
  cases t with
  | ret vs =>
    unfold Ctx.exitOf at h
    split_ifs at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨es, hes, he⟩ := h
    cases he
    exact ⟨vs, rfl, hes⟩
  | brTable sc d cases =>
    cases d with
    | none => simp [Ctx.exitOf] at h
    | some d =>
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, h⟩ := h
      cases h
  | _ => simp [Ctx.exitOf, Option.bind_eq_some_iff] at h

/-- The valuation `ρ` with each value the statements define, if `keep` lacks it and its
    instruction computes a word, set to that word, in order. -/
def complete (ee : ExecutionEnv) (symbols : List (String × Nat × Nat)) (keep : List Nat) :
    List Stmt → (Nat → UInt256) → Nat → UInt256
  | [], ρ => ρ
  | s :: rest, ρ => complete ee symbols keep rest (match s.local? with
    | some (id, inst) => if id ∈ keep then ρ else
      ((instWord ee ρ symbols inst).map (Function.update ρ id)).getD ρ
    | none => ρ)

/-- A value no statement sets keeps its word. -/
theorem complete_same {ee : ExecutionEnv} {symbols : List (String × Nat × Nat)}
    {keep : List Nat} {id : Nat} : ∀ (stmts : List Stmt) (ρ : Nat → UInt256),
      (∀ s ∈ stmts, ∀ p, s.local? = some p → p.1 = id → id ∈ keep) →
      complete ee symbols keep stmts ρ id = ρ id
  | [], _, _ => rfl
  | s :: rest, ρ, h => by
    unfold complete
    rw [complete_same rest _ fun t ht => h t (List.mem_cons_of_mem _ ht)]
    cases hj : s.local? with
    | none => rfl
    | some p =>
      obtain ⟨j, inst⟩ := p
      dsimp only
      split_ifs with hk
      · rfl
      · cases hw : instWord ee ρ symbols inst with
        | none => rfl
        | some v =>
          have hne : id ≠ j := fun he => hk (by subst he; exact h s (by simp) _ hj rfl)
          simp [Function.update_of_ne hne]

theorem local_inst {t : Stmt} {p : Nat × Inst} (h : t.local? = some p) : p.2 = t.inst := by
  have ht := local_def h
  unfold Stmt.def? at ht
  split at ht
  · cases ht; rfl
  · cases ht

/-- Each value the statements set has the word its instruction computes. -/
theorem complete_eqn {ee : ExecutionEnv} {symbols : List (String × Nat × Nat)}
    {keep : List Nat} : ∀ (stmts : List Stmt) (D D' : List Nat) (ρ : Nat → UInt256),
      definedAfter D stmts = some D' →
      (∀ s ∈ stmts, ∀ op args, s.inst = .evm op args →
        (evmPureOpcode op).all fun o => δ o == some args.length) →
      ∀ s ∈ stmts, ∀ id inst, s.local? = some (id, inst) → id ∉ keep →
        Eqn ee (complete ee symbols keep stmts ρ) symbols id inst
  | [], _, _, _, _, _, s, hs, _, _, _, _ => by cases hs
  | s0 :: rest, D, D', ρ, hd, har, s, hs, id, inst, hl, hk => by
    simp only [definedAfter] at hd
    split_ifs at hd with hok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
    unfold complete
    rcases List.mem_cons.mp hs with rfl | hs
    · set ρ1 := (match s.local? with
        | some (id, inst) => if id ∈ keep then ρ else
          ((instWord ee ρ symbols inst).map (Function.update ρ id)).getD ρ
        | none => ρ) with hρ1
      have hinst := local_inst hl
      simp only at hinst
      subst hinst
      obtain ⟨ty, hty⟩ := local_dst hl
      simp only at hty
      have hidD : id ∉ D := fun h => by
        simpa [List.contains_iff_mem, h] using hok.2 (id, ty) hty
      -- The later statements set no value of `D` nor `s`'s.
      have hkeep : ∀ x ∈ D ++ s.dsts.map (·.1),
          complete ee symbols keep rest ρ1 x = ρ1 x := fun x hx =>
        complete_same rest ρ1 fun t ht p hp he => by
          obtain ⟨ty', hty'⟩ := local_dst hp
          exact absurd (he ▸ hx) (definedAfter_fresh hd t ht _ hty')
      intro ex e he
      obtain ⟨v, hv⟩ := instWord_some (ee := ee) (ρ := ρ) he fun op args h => har s (by simp) op args h
      have hρ1 : ρ1 = Function.update ρ id v := by simp [hρ1, hl, hk, hv]
      have hsame : ∀ x ∈ D, complete ee symbols keep rest ρ1 x = ρ x := fun x hx => by
        rw [hkeep x (List.mem_append_left _ hx), hρ1,
          Function.update_of_ne (fun h : x = id => hidD (by rw [← h]; exact hx))]
      have hr : reads D s.inst.operands = true := hok.1
      rw [instWord_congr (ρ' := ρ) hsame hr, hv,
        hkeep id (List.mem_append_right _ (List.mem_map_of_mem hty)), hρ1]
      simp
    · exact complete_eqn rest _ D' _ hd (fun t ht => har t (List.mem_cons_of_mem _ ht)) s hs id
        inst hl hk

/-- Every statement of segments the checker accepts that is an EVM instruction with a word of
    its own has as many operands as its opcode pops. -/
theorem segments_arity {c : Ctx} : ∀ {ps : List (List Nat)} {k : Nat} {stmts : List Stmt}
    {r : List Event × List CallSeg},
    c.segments ps k stmts = some r → ∀ s ∈ stmts, ∀ op args, s.inst = .evm op args →
      (evmPureOpcode op).all fun o => δ o == some args.length
  | _, _, [], _, _, s, hs, _, _, _ => by cases hs
  | ps, k, t :: rest, r, h, s, hs, op, args, hi => by
    unfold Ctx.segments at h
    cases hr : c.segments ps.tail (k + 1) rest with
    | none => simp [hr] at h
    | some r' =>
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [hi] at h
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      cases he : c.eventOfStmt s with
      | none => simp [he] at h
      | some o =>
        unfold Ctx.eventOfStmt at he
        rw [hi] at he
        cases hpe : c.pureExpr (.evm op args) with
        | some e =>
          simp only [hpe] at he
          split_ifs at he with hk
          simp only [Bool.and_eq_true] at hk
          exact hk.2
        | none =>
          cases hev : c.eventOf (.evm op args) with
          | none => simp [hpe, hev] at he
          | some q =>
            obtain ⟨opc, es⟩ := q
            rcases eventWith_cases hev with ⟨op', os, hi', hopc, -⟩ | ⟨a, e, hi', -⟩
            · cases hi'
              simp [evmEvent_not_pure hopc]
            · cases hi'
    · exact segments_arity hr s hs op args hi

set_option maxHeartbeats 2000000 in
/-- One block of a checked function: the bytes end as the IR's run does, return as it does,
    or reach the next block's code where the IR's run goes on there, given that every callee's
    bytes from its entry, below the block's gas, end as its IR's run does. -/
theorem block_run {code : CodeSection} {low : Lowering} {hint : FuncHint} {f : Func}
    {fr : Frame} {sp : FuncSpill} {isRoot : Bool} {eb : Block} {I : ExecutionEnv}
    {tail : ByteArray} {g : Guard} {ic : Fe.Sonatina.Ctx} {inh : List Nat}
    (hI : I.code = code.bytecode ++ tail) (hsize : code.bytecode.size < UInt256.size)
    (hsym : ic.symbol = (code.symbols.lookup ·))
    (hbits : (f.blocks.all fun b => b.phis.all (·.ty.bits == 256) &&
        b.body.all (·.dsts.all (·.2.bits == 256))) = true)
    (hnd : nodup (f.blocks.flatMap fun b =>
        b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) = true)
    (hsg : sp.guard = g.at f.name)
    (hchk : ∀ b ∈ f.blocks, checkBlock code low hint f fr sp isRoot eb
        (placeIn low hint.name) (zeroRank f (placeIn low hint.name) f.blocks.length) b = .ok ())
    (hpred : ∀ x ∈ f.blocks, eb.id ∉ x.term.succs)
    (hexact : ∀ b ∈ f.blocks, fr.exact b.id = false → ∀ s ∈ b.term.succs, fr.exact s = false)
    (hretx : ∀ b ∈ f.blocks, ∀ vs, b.term = .ret vs → fr.exact b.id = true)
    (hexr : ∀ b, fr.exact b = true → fr.returns = true)
    (hrets : ∀ b ∈ f.blocks, ∀ vs, b.term = .ret vs → vs.length = f.rets.length)
    (hfresh : ∀ b ∈ f.blocks, ∀ h ∈ hint.blocks, ∀ id,
      (id ∈ slotValues h.entryStack ∨ id ∈ b.phis.map (·.dst) ∨
        ∃ s ∈ b.body, ∃ d ∈ s.dsts, d.1 = id) → id < fr.retId)
    (hK : ∀ b ∈ f.blocks, ∀ s ∈ b.body, s.inst.messages = true → K = true)
    {b : Block} {prev : Option Nat} {env : Env} {w : World} {st : State} {ret : Option UInt256}
    {B : List UInt256} (hat : AtBlock M low hint f fr I b prev env w st ret B)
    (hretk : fr.returns = true → ∃ k, ret = some k ∧ (D_J I.code 0).contains k = true)
    (hcallee : ∀ (cs : CallSeg) (ce : Callee) (ws : List UInt256) (st' : State) (w' : World)
      (ret' : Option UInt256) (B' : List UInt256), fr.callee cs.callee = some ce →
      st'.machineState.pc.toNat = ce.offset → st'.executionEnv = I → Agree M st' w' →
      ws.length = ce.params →
      st'.machineState.stack = ws ++ (match ret' with | some k => k :: B' | none => B') →
      (ce.returns = true → ∃ k, ret' = some k ∧ (D_J I.code 0).contains k = true) →
      (ce.returns = false → ret' = none) →
      st'.machineState.gasAvailable.toNat < st.machineState.gasAvailable.toNat →
      NoPanicAt ((runFuncG g low.machine ic (inh ++ cs.keep) cs.callee
        (ws.map Fe.Sonatina.word)).exec I w') →
      Final' K M (D_J I.code 0) st'
        ((runFuncG g low.machine ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec
          I w') ret' B' ce.rets)
    (hnp : NoPanicAt ((preIf isRoot low eb b >>= fun _ =>
      runBlocksG g low.machine ic inh f env prev b.id).exec I w)) :
    Final' K M (D_J I.code 0) st
        ((preIf isRoot low eb b >>= fun _ => runBlocksG g low.machine ic inh f env prev b.id).exec I w)
        (if fr.exact b.id then ret else none) B f.rets.length ∨
      ∃ S env' w' st' n B', Reach K (D_J I.code 0) st st' n ∧
        (n = 0 → zeroRank f (placeIn low hint.name) f.blocks.length S.id <
          zeroRank f (placeIn low hint.name) f.blocks.length b.id) ∧
        AtBlock M low hint f fr I S (some b.id) env' w' st' ret B' ∧
        (fr.exact S.id = true → B' = B ∧ fr.exact b.id = true) ∧ S.id ≠ eb.id ∧
        (preIf isRoot low eb b >>= fun _ => runBlocksG g low.machine ic inh f env prev b.id).exec I w =
          (runBlocksG g low.machine ic inh f env' (some b.id) S.id).exec I w' := by
  obtain ⟨hmem, hblk, henv, hw, hb, pc, envB, ws, hhb, hpc, hstpc, henter, hstk, hslots,
    hphis⟩ := hat
  obtain ⟨hb', pc', stack, events, calls, exit, hhb', hpc', hst, hseg, hex, hempty, hdef, hrank,
    hrun⟩ := checkBlock_ok (hchk b hmem)
  rw [hhb] at hhb'; cases hhb'
  rw [hpc] at hpc'; cases hpc'
  replace hdef : defined f hint.blocks b (slotValues hb.entryStack) = true := hdef
  set c := Ctx.ofBlock f b code.symbols fr sp with hc
  unfold defined at hdef
  cases hDA : definedAfter (slotValues hb.entryStack ++ b.phis.map (·.dst)) b.body with
  | none => simp [hDA] at hdef
  | some D' =>
  simp only [hDA, Bool.and_eq_true, List.all_eq_true] at hdef
  set D := slotValues hb.entryStack ++ b.phis.map (·.dst) with hD
  obtain ⟨hterm, hsucc⟩ := hdef
  have hfreshS := definedAfter_fresh hDA
  have hnone : ∀ id ∈ D, c.defs.lookup id = none := fun id hid =>
    lookup_none fun s hs d hd h => hfreshS s hs d hd (h ▸ hid)
  have hwB : WordsOf envB (wordsOf envB) D := wordsOf_words fun id hid => by
    rcases List.mem_append.mp hid with h | h
    · obtain ⟨v, hv⟩ := slot_word hslots (by rw [slotValues_slots]; exact h)
      exact ⟨v.toNat, hv, v.val.isLt⟩
    · obtain ⟨phi, hp, rfl⟩ := List.mem_map.mp h
      exact hphis phi hp
  obtain ⟨w₀, hpre, htrace⟩ := pre_trace' isRoot low eb b I w
  have hbitsb : ∀ s ∈ b.body, ∀ d ∈ s.dsts, d.2.bits = 256 := by
    have := List.all_eq_true.mp hbits b hmem
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
    exact fun s hs d hd => this.2 s hs d hd
  have hndb : ∀ s ∈ b.body, (s.dsts.map (·.1)).Nodup := fun s hs => by
    have h1 := ((List.nodup_flatMap.mp ((nodup_iff _).mp hnd)).1 b hmem).of_append_right
    exact (List.nodup_flatMap.mp h1).1 s hs
  have hhint : hb ∈ hint.blocks := List.mem_of_find?_eq_some hhb
  -- Every value of the block is one its return address is not.
  have hRD' : ∀ id ∈ D', id ≠ fr.retId := fun id hid h => by
    have := hfresh b hmem hb hhint id (by
      rcases definedAfter_sub hDA id hid with h' | h'
      · rcases List.mem_append.mp h' with h' | h'
        · exact .inl h'
        · exact .inr (.inl h')
      · exact .inr (.inr h'))
    omega
  have hR : (preIf isRoot low eb b >>= fun _ =>
      runBlocksG g low.machine ic inh f env prev b.id).exec I w =
      (runBlocksG g low.machine ic inh f env prev b.id).exec I w₀ := by
    rw [Fe.M.exec_bind, hpre]
  have hnpb : NoPanicAt ((runBodyG g low.machine ic inh (sp.guard b.id) envB b.body).exec I w₀) := by
    have h1 := hR ▸ hnp
    rw [runBlocksG.eq_1, hblk] at h1
    simp only [henter, pure_bind] at h1
    rw [hsg]
    exact (NoPanicAt.of_bind h1).1
  obtain ⟨x, hx, envf, Df, hagr, hsub, hDf, ⟨ρ0, hρ0⟩, hcase⟩ :=
    body_calls (ee := I) (m := low.machine) (c := c) hsym calls b.body [] (sp.guard b.id) 0 D D'
      envB w₀ events (by simp [c, Ctx.ofBlock]) (by simp) hDA hseg hbitsb hndb ⟨_, hwB⟩
      (fun ρ _ => ⟨rfl, fun id hid inst hl => (by rw [hnone id hid] at hl; cases hl),
        fun id hid e he => by rw [expand_atom rfl (hnone id hid)] at he; cases he; rfl⟩) hnpb
  -- The valuation: the return address the function's, and each value of the block the word
  -- its instruction computes, those after where the run stops included.
  have hlocal : ∀ s ∈ b.body, ∀ p, s.local? = some p → p.1 ∈ D' := fun s hs p hp => by
    obtain ⟨ty, hty⟩ := local_dst hp
    exact definedAfter_dsts hDA s hs _ hty
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = complete I c.symbols Df b.body
      (Function.update ρ0 fr.retId (ret.getD ⟨0⟩)) := ⟨_, rfl⟩
  have hρR : ρ fr.retId = ret.getD ⟨0⟩ := by
    rw [hρdef, complete_same _ _ fun s hs p hp he => absurd he (hRD' _ (hlocal s hs p hp))]
    simp
  have hρ : WordsOf envf ρ Df := fun id h => by
    rw [hρdef, complete_same _ _ fun _ _ _ _ _ => h, Function.update_of_ne (hRD' id (hDf id h))]
    exact hρ0 id h
  have hcanon : c.canon.Valid I ρ :=
    Canon.valid_ofDefs (symbols := c.symbols) (xs := c.defs) fun j inst hl => by
      by_cases hj : j ∈ Df
      · rcases hcase with ⟨-, hall⟩ | hall <;> exact ((hall ρ hρ).1.2.1 j hj inst hl).2
      · obtain ⟨t, ht, htl⟩ := List.mem_filterMap.mp
          (show (j, inst) ∈ b.body.filterMap Stmt.local? from mem_of_lookup hl)
        rw [hρdef]
        exact complete_eqn b.body D D' _ hDA (segments_arity hseg) t ht j inst htl hj
  rw [hR]
  have hρD : WordsOf envB ρ D := fun id hid => (hagr id hid).symm.trans (hρ id (hsub id hid))
  have hpath : PathRel code.bytecode tail I ρ B exit
      ⟨pc, stack, prologue low (isRoot && b.id == eb.id) events, exit, calls⟩ st :=
    ⟨henv, hI, hstpc, ⟨ws,
      entryStack_rel (fun v h => by show ρ fr.retId = v; rw [hρR, h]; rfl) rfl
        (fun id hid => hnone id (List.mem_append_left _ (by rwa [slotValues_slots] at hid)))
        (fun id hid => hρD id (List.mem_append_left _ (by rwa [slotValues_slots] at hid))) hslots
        hst, hstk⟩,
      exitOf_valid hex I ρ, .inl rfl⟩
  have hretj : c.frame.returns = true → (D_J I.code 0).contains (ρ c.frame.retId) = true :=
    fun h => by
      obtain ⟨k, hk, hkj⟩ := hretk h
      simpa [c, Ctx.ofBlock, hρR, hk] using hkj
  have har := segments_calls hseg
  -- A message call among the path's events is one of the block's.
  have hKp : ∀ ev ∈ prologue low (isRoot && b.id == eb.id) events ++ calls.flatMap (·.events),
      messageOps.contains ev.op = true → K = true := by
    intro ev hev hm
    have hev' : ev ∈ events ++ calls.flatMap (·.events) := by
      unfold prologue at hev
      split at hev
      · rcases List.mem_append.mp hev with hev | hev
        · rcases List.mem_cons.mp hev with rfl | hev
          · simp [messageOps] at hm
          · exact List.mem_append_left _ hev
        · exact List.mem_append_right _ hev
      · exact hev
    obtain ⟨t, ht, htm⟩ := segments_messages hseg ev hev' hm
    exact hK b hmem t ht htm
  -- Where a callee's result is not the IR's, the bytes run out of gas or stack.
  rcases hcase with ⟨hok, hall⟩ | hall
  swap
  · left; left
    rcases segs_ends (m := low.machine) (ic := ic) (G := st.machineState.gasAvailable.toNat)
        hsize hretj hcanon hcallee calls _ _ st w none B rfl hKp har hrun hpath hw
        (Segs.pre (htrace ρ _) (hall ρ hρ).2) (le_refl _) with h | ⟨_, h, -⟩
    · exact Final.of_none h
    · cases h
  have hE := segs_ends (m := low.machine) (ic := ic) (G := st.machineState.gasAvailable.toNat)
    hsize hretj hcanon hcallee calls _ _ st w _ B rfl hKp har hrun hpath hw
    (Segs.pre (htrace ρ _) (hall ρ hρ).2) (le_refl _)
  rw [hsg] at hx
  rw [runBlocksG.eq_1, hblk]
  simp only [henter, pure_bind, Fe.M.exec_bind, hx]
  rcases hE with hE | ⟨w', hxw, hE⟩
  · left; left
    cases x with
    | none => exact hE
    | some x => cases x with
      | error e => exact hE
      | ok p => exact Final.of_ok hE
  cases x with
  | none => cases hxw
  | some x =>
  cases x with
  | error e => cases hxw
  | ok p =>
  obtain ⟨env', w₁⟩ := p
  simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at hxw
  subst w₁
  obtain ⟨h1, h2⟩ := hok env' w' rfl
  subst envf
  subst Df
  have hcons := (hall ρ hρ).1
  rcases hE with ⟨n, e', hxs, he'⟩ | ⟨_, _, _, hr, -⟩ |
    ⟨w'', hr, harr | ⟨op, args, hws, -, hex0, hargs, hh⟩ |
    ⟨vals, wsv, nv, sv, -, hex0, hwsv, hstv, hpcv, hstkv, henvv, hagv⟩ |
    ⟨cs, more, -, -, -, -, -, -, -, -, -, hcl, -⟩ | ⟨cs, -, -, -, -, -, hcl, -⟩⟩
  · left; left; exact .exhausted hxs he'
  · cases hr
  · cases hr
    obtain ⟨S, n, st', pc', exprs, B', -, hnh, hjmp, hzero, hreach, hnext, hplS, hpcS, harr, hrel,
      hBS, henvS, hagS⟩ := harr
    simp only [Ctx.arrival, Option.bind_eq_bind, Option.bind_eq_some_iff] at harr
    obtain ⟨hbS, hhbS, Sb, hSb, hmapS⟩ := harr
    change f.block? S = some Sb at hSb
    have hSbmem : Sb ∈ f.blocks := List.mem_of_find?_eq_some hSb
    have hSid : Sb.id = S := by simpa using List.find?_some hSb
    -- The successor, entered from `b`, is where the bytes are.
    have key : ∀ d, exit.next I ρ = some d →
        AtBlock M low hint f fr I Sb (some b.id) env' w' st' ret B' ∧
        d = Sb.id := by
      intro d hd
      have hdS := hnext d hd
      subst hdS
      refine ⟨?_, hSid.symm⟩
      have hsuccS := hsucc _ (exitOf_succ hex hd)
      rw [hSb] at hsuccS
      simp only [Bool.and_eq_true, List.all_eq_true] at hsuccS
      obtain ⟨hphisS, hslotsS⟩ := hsuccS
      have hndS : (Sb.phis.map (·.dst)).Nodup := by
        have := (nodup_iff _).mp hnd
        exact ((List.nodup_flatMap.mp this).1 Sb hSbmem).of_append_left
      have hbitsS := List.all_eq_true.mp hbits Sb hSbmem
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hbitsS
      have hin : ∀ phi ∈ Sb.phis, ∃ o d, phi.incoming.find? (·.2 == b.id) = some (o, d) ∧
          reads D' [o] = true ∧ ∀ ty, o ≠ .undef ty := fun phi hp => by
        have := hphisS phi hp
        rcases hf : phi.incoming.find? (fun x => x.2 == b.id) with _ | ⟨o, d⟩
        · simp [hf] at this
        · refine ⟨o, d, hf, ?_⟩
          rw [hf] at this
          cases o <;> simp_all
      obtain ⟨envS, henterS, hphiS, hkeepS⟩ := enter_run (fun phi hp => by
        obtain ⟨o, d, hf, hr, -⟩ := hin phi hp; exact ⟨o, d, hf, hr⟩) hρ hndS
      obtain ⟨ws', hws', hstk'⟩ := hrel
      refine ⟨hSbmem, by rw [hSid]; exact hSb, henvS, hagS, hbS, pc', envS, ws',
        by rw [hSid]; exact hhbS, by rw [hSid]; exact hplS, hpcS, henterS, hstk', ?_, ?_⟩
      · have hall : (fr.slots hbS).all (slotDefined D' Sb) = true := by
          have := hslotsS
          rw [hhbS] at this
          simp only [Option.all_some] at this
          exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp this x (slots_sub hx)
        exact arrival_rel hcons hρ (ret := ret) (fun phi hp => by
          obtain ⟨o, d, val, hf, hev, hS⟩ := hphiS phi hp
          obtain ⟨o', d', hf', hr', -⟩ := hin phi hp
          rw [hf] at hf'; cases hf'
          exact ⟨hbitsS.1 phi hp, o, d, val, hf, hr', hev, hS⟩) hkeepS
          (fun h => by
            obtain ⟨k, hk, -⟩ := hretk h
            show ret = some (ρ fr.retId)
            rw [hρR, hk]; rfl) hall hmapS hws'
      · intro phi hp
        obtain ⟨o, d, val, hf, hev, hS⟩ := hphiS phi hp
        obtain ⟨o', d', hf', hr', hnu⟩ := hin phi hp
        rw [hf] at hf'; cases hf'
        have hval : ∃ bits k, val = .int bits k := by
          have hex' : ∀ {a b : FeM Val}, a = b →
              a.exec I (World.init ∅ default) = b.exec I (World.init ∅ default) :=
            fun h => h ▸ rfl
          cases o with
          | var id =>
            have hid : id ∈ D' := by simpa [reads, Operand.var?] using hr'
            have := hex' hev
            simp [evalOperand, hρ id hid] at this
            exact ⟨_, _, this.symm⟩
          | imm bits k =>
            have := hex' hev
            simp [evalOperand] at this
            exact ⟨_, _, this.symm⟩
          | undef ty => exact absurd rfl (hnu ty)
        obtain ⟨bits, k, rfl⟩ := hval
        exact ⟨_, by rw [hS, as_int _ _ (hbitsS.1 phi hp)]; rfl, (UInt256.ofNat k).val.isLt⟩
    -- In no step the exit selected the successor: its code is at `b`'s, so it is lower.
    have hlow : n = 0 → zeroRank f (placeIn low hint.name) f.blocks.length Sb.id <
        zeroRank f (placeIn low hint.name) f.blocks.length b.id := fun hn => by
      have hsel := hzero hn
      have honly := exitOf_only hex hsel
      rw [honly] at hrank
      simp only [Option.all_some, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hrank
      rcases hreach with ⟨-, rfl⟩ | hx
      · rcases hrank with h | h
        · exact absurd (by rw [hplS, ← hpcS, hstpc]) h
        · rw [hSid]; exact h
      · subst hn; cases hx
    have hfin : ∀ d, exit.next I ρ = some d →
        ∃ S' env'' w'' st'' n' B'', Reach K (D_J I.code 0) st st'' n' ∧
          (n' = 0 → zeroRank f (placeIn low hint.name) f.blocks.length S'.id <
            zeroRank f (placeIn low hint.name) f.blocks.length b.id) ∧
          AtBlock M low hint f fr I S' (some b.id) env'' w'' st'' ret B'' ∧
          (fr.exact S'.id = true → B'' = B ∧ fr.exact b.id = true) ∧ S'.id ≠ eb.id ∧
          (runBlocksG g low.machine ic inh f env' (some b.id) d).exec I w' =
            (runBlocksG g low.machine ic inh f env'' (some b.id) S'.id).exec I w'' := fun d hd => by
      obtain ⟨hat', hdS⟩ := key d hd
      have hSs : Sb.id ∈ b.term.succs := hdS ▸ exitOf_succ hex hd
      exact ⟨Sb, env', w', st', n, B', hreach, hlow, hat', fun hx => by
        refine ⟨hBS (by rw [← hSid]; exact hx), ?_⟩
        by_contra hb
        exact absurd hx (by simp [hexact b hmem (by simpa using hb) Sb.id hSs]),
        fun h => hpred b hmem (h ▸ hSs), by rw [hdS]⟩
    right
    cases ht : b.term with
    | jump d =>
      rw [ht] at hex; simp only [Ctx.exitOf, Option.some.injEq] at hex; subst hex
      simpa using hfin d rfl
    | br cond nz z =>
      rw [ht] at hex hterm
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hex
      obtain ⟨ce, hce, rfl⟩ := hex
      obtain ⟨v, hv, -, hev⟩ := operand_words hcons hρ (by simpa [Term.operands] using hterm) hce
      have := hfin (if v.toNat != 0 then nz else z) (by simp [Exit.next, hv])
      simpa [evalInt, hev] using this
    | brTable sc def? cases =>
      cases def? with
      | none => rw [ht] at hex; simp [Ctx.exitOf] at hex
      | some dd =>
      rw [ht] at hex hterm
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hex
      obtain ⟨cs, hcs, ce, hce, rfl⟩ := hex
      simp only [Term.operands, reads, List.all_cons, Bool.and_eq_true] at hterm
      obtain ⟨v, hv, -, hev⟩ := operand_words hcons hρ (by simpa [reads] using hterm.1) hce
      have hlt : ∀ kd ∈ cs, kd.1 < UInt256.size := mapM_forall hcs fun x y hxy => by
        obtain ⟨o, dest⟩ := x
        simp only at hxy
        split at hxy
        · split_ifs at hxy with hv'; cases hxy; exact hv'
        · cases hxy
      have := hfin (((cs.find? (UInt256.ofNat ·.1 == v)).map (·.2)).getD dd)
        (by simp [Exit.next, hv])
      have hei : evalInt env' sc = pure (256, v.toNat) := by simp [evalInt, hev]
      simp only [hei, pure_bind]
      rw [table_vals (env := env') hcs]
      simp only [pure_bind]
      rw [← find_table hlt] at this
      cases hf : cs.find? (·.1 == v.toNat) with
      | none => simpa [hf] using this
      | some kd => simpa [hf] using this
    | evmReturn a l | evmRevert a l =>
      rw [ht] at hex
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hex
      obtain ⟨_, _, _, _, rfl⟩ := hex
      exact absurd rfl (hnh _ _)
    | evmStop | evmInvalid =>
      rw [ht] at hex
      simp only [Ctx.exitOf, Option.some.injEq] at hex
      subst hex
      exact absurd rfl (hnh _ _)
    | ret vs =>
      rw [ht] at hex
      unfold Ctx.exitOf at hex
      split_ifs at hex
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hex
      obtain ⟨_, _, rfl⟩ := hex
      exact hjmp.elim
    | unreachable =>
      rw [ht] at hex
      simp only [Ctx.exitOf, Option.some.injEq] at hex
      subst hex
      exact hjmp.elim
  · cases hr
    left; left
    subst hex0
    have hw2 : ∀ {a l : Operand} {ea el : Expr}, reads D' [a, l] = true →
        c.operand a = some ea → c.operand l = some el →
        [ea, el].mapM (·.eval I ρ) = some hws → ∃ va vl, hws = [va, vl] ∧
          evalWord env' a = pure va ∧ evalWord env' l = pure vl := by
      intro a l ea el hr ha hl hm
      simp only [reads, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hr
      obtain ⟨va, hva, -, hea⟩ := operand_words hcons hρ (by simpa [reads] using hr.1) ha
      obtain ⟨vl, hvl, -, hel⟩ := operand_words hcons hρ (by simpa [reads] using hr.2) hl
      refine ⟨va, vl, by simpa [List.mapM_cons, hva, hvl] using hm.symm, ?_, ?_⟩
      · simp [evalWord, evalInt, hea, Reasoning.Theory.u256_ofNat_toNat]
      · simp [evalWord, evalInt, hel, Reasoning.Theory.u256_ofNat_toNat]
    rcases exitOf_halt hex with ⟨a, l, ea, el, ht, rfl, rfl, hea, hel⟩ |
      ⟨a, l, ea, el, ht, rfl, rfl, hea, hel⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩
    · rw [ht] at hterm
      obtain ⟨va, vl, rfl, hva, hvl⟩ := hw2 hterm hea hel hargs
      obtain ⟨n, s', hxs, ha, hl⟩ := hh
      exact .inr (.inl ⟨n, s', _, w', hxs, by simp [ht, hva, hvl, returnData], ha, hl⟩)
    · rw [ht] at hterm
      obtain ⟨va, vl, rfl, hva, hvl⟩ := hw2 hterm hea hel hargs
      obtain ⟨n, s', hxs⟩ := hh
      exact .inr (.inr ⟨n, s', _, hxs, by simp [ht, hva, hvl, revertData]⟩)
    · simp at hargs; subst hargs
      obtain ⟨n, s', hxs, ha, hl⟩ := hh
      exact .inr (.inl ⟨n, s', _, w', hxs, by simp [ht, stopCall], ha, hl⟩)
    · simp at hargs; subst hargs
      obtain ⟨n, hxs⟩ := hh
      exact .inl ⟨n, _, hxs, .inr (.inr (.inr (.inl ⟨rfl, by simp [ht, trap]⟩)))⟩

  · -- A return.
    cases hr
    left; right
    subst hex0
    obtain ⟨vs, hvs, hmv⟩ := exitOf_ret_eq hex
    have hexb := hretx b hmem vs hvs
    obtain ⟨k, hk, -⟩ := hretk (hexr b.id hexb)
    rw [hvs] at hterm
    obtain ⟨ws', hws', hev'⟩ := args_words hcons hρ (by simpa [Term.operands] using hterm) hmv
    rw [hwsv] at hws'; cases hws'
    refine ⟨k, wsv, w', nv, sv, by rw [if_pos hexb, hk], ?_, ?_, hstv, ?_, hstkv,
      henvv.trans henv.symm, hagv⟩
    · simp only [hvs, hev']; rfl
    · rw [(mapM_some_iff.mp hwsv).length_eq.symm, (mapM_some_iff.mp hmv).length_eq.symm]
      exact hrets b hmem vs hvs
    · rw [hpcv]; show ρ fr.retId = k; rw [hρR, hk]; rfl
  · cases hcl
  · cases hcl


/-! ## A function -/

theorem foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_refl _, fun _ h => by cases h⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem lt_fresh {f : Func} {id : Nat} (h : id ∈ f.defs) : id < f.fresh := by
  have := (foldl_max f.defs 0).2 id h
  unfold Func.fresh; omega

/-- A block of a function that does not return has no `ret`. -/
theorem exitOf_ret_term {c : Ctx} {vs : List Operand} {e : Exit}
    (h : c.exitOf (.ret vs) = some e) : c.frame.returns = true := by
  unfold Ctx.exitOf at h
  split_ifs at h with hr
  · exact hr

/-- What a function the checker accepts is, as `block_run` asks it. -/
theorem func_facts {code : CodeSection} {low : Lowering} {plan : SpillPlan} {G : Guard}
    {entry : String} {hint : FuncHint} (h : checkFunc code low plan G entry hint = .ok ()) :
    ∃ f eb, low.machine.func? hint.name = some f ∧ f.blocks.head? = some eb ∧
      (f.blocks.all fun b => b.phis.all (·.ty.bits == 256) &&
        b.body.all (·.dsts.all (·.2.bits == 256))) = true ∧
      nodup (f.blocks.flatMap fun b =>
        b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) = true ∧
      (∃ sp : FuncSpill, sp.guard = G.at f.name ∧ ∀ b ∈ f.blocks, checkBlock code low hint f
        (frameOf low entry f) sp (hint.name == entry) eb (placeIn low hint.name)
        (zeroRank f (placeIn low hint.name) f.blocks.length) b = .ok ()) ∧
      (∀ x ∈ f.blocks, eb.id ∉ x.term.succs) ∧
      (∀ b ∈ f.blocks, (frameOf low entry f).exact b.id = false →
        ∀ s ∈ b.term.succs, (frameOf low entry f).exact s = false) ∧
      (∀ b ∈ f.blocks, ∀ vs, b.term = .ret vs → (frameOf low entry f).exact b.id = true) ∧
      (∀ b, (frameOf low entry f).exact b = true → (frameOf low entry f).returns = true) ∧
      (∀ b ∈ f.blocks, ∀ vs, b.term = .ret vs → vs.length = f.rets.length) ∧
      (∀ b ∈ f.blocks, ∀ h ∈ hint.blocks, ∀ id,
        (id ∈ slotValues h.entryStack ∨ id ∈ b.phis.map (·.dst) ∨
          ∃ s ∈ b.body, ∃ d ∈ s.dsts, d.1 = id) → id < (frameOf low entry f).retId) ∧
      (f.params.all (·.2.bits == 256)) = true ∧ (f.params.map (·.1)).Nodup ∧
      (hint.name = entry → f.params = [] ∧ (frameOf low entry f).returns = false ∧
        placeIn low hint.name eb.id = some 0) ∧
      (hint.blocks.find? (·.block == eb.id)).map (·.entryStack) =
        some (f.params.map (.value ·.1) ++
          if (frameOf low entry f).returns then [.funcReturn] else []) ∧
      eb.phis = [] := by
  obtain ⟨f, eb, hf, he, hchecks, sp, hsp, hchk⟩ := checkFunc_ok h
  have hname : f.name = hint.name := by
    simpa using List.find?_some (show low.machine.funcs.find? (·.name == hint.name) = some f from hf)
  simp only [funcChecks, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at hchecks
  obtain ⟨-, ⟨⟨hbits, hpb⟩, -⟩, hnd, ⟨hephi, hpreds⟩, hroot, hclosed, hretn, -, hslotids,
    hentry⟩ := hchecks
  have hnd' := (nodup_iff _).mp hnd
  unfold Func.defs at hnd'
  have hfr : ∀ id ∈ f.defs, id < (frameOf low entry f).retId := fun id h => lt_fresh h
  refine ⟨f, eb, hf, he, hbits, (nodup_iff _).mpr hnd'.of_append_right,
    ⟨sp, by rw [hsp, hname], hchk⟩,
    fun x hx hin => by
      have := List.all_eq_true.mp hpreds x hx
      simp [hin] at this,
    fun b hb hx s hs => ?_, fun b hb vs ht => ?_, fun b hx => ?_, fun b hb vs ht => ?_,
    fun b hb h hh id hid => ?_, hpb, (nodup_iff _).mp hnd |>.of_append_left |> fun h => by
      simpa using h, fun hr => ?_, by simpa using hentry, by simpa using hephi⟩
  · simp only [frameOf, Bool.and_eq_false_iff] at hx ⊢
    rcases hx with hx | hx
    · exact .inl hx
    · right
      have := List.all_eq_true.mp hclosed b hb
      simp only [hx, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
        Bool.not_eq_true] at this
      simpa using this.2 s hs
  · obtain ⟨-, -, -, -, -, exit, -, -, -, -, hex, -⟩ := checkBlock_ok (hchk b hb)
    rw [ht] at hex
    have hr := exitOf_ret_term hex
    simp only [Ctx.ofBlock] at hr
    have := List.all_eq_true.mp hclosed b hb
    simp only [frameOf, Bool.and_eq_true] at hr ⊢
    refine ⟨hr, ?_⟩
    simp only [ht, Bool.or_eq_true] at this
    rcases this with h | h
    · exact h
    · simp at h
  · simp only [frameOf, Bool.and_eq_true] at hx ⊢
    exact hx.1
  · have := List.all_eq_true.mp hretn b hb
    rw [ht] at this
    simpa using this
  · show id < f.fresh
    rcases hid with h1 | h1 | ⟨s, hs, d, hd, rfl⟩
    · obtain ⟨sl, hsl, he'⟩ := List.mem_filterMap.mp h1
      cases sl <;> simp at he'
      subst he'
      have := List.all_eq_true.mp (List.all_eq_true.mp hslotids h hh) _ hsl
      simpa using this
    · exact lt_fresh (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb,
        List.mem_append_left _ h1⟩))
    · exact lt_fresh (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb,
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_map_of_mem hd⟩)⟩))
  · rcases hroot with h | h
    · exact absurd hr h
    · exact ⟨by simpa using h.1.1, by simpa using h.1.2, h.2⟩

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List α} {l₄ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h hr, h' => .cons h (forall₂_append hr h')

theorem forall₂_slots {env : Env} {ret : Option UInt256} :
    ∀ {ps : List (Nat × Ty)} {ws : List UInt256},
    List.Forall₂ (fun d w => env[d.1]? = some (.int 256 w.toNat)) ps ws →
    List.Forall₂ (SlotWord env ret) (ps.map (.value ·.1)) ws
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons h (forall₂_slots hr)

theorem callees_some {low : Lowering} {entry g : String} {ce : Callee}
    (h : callees low entry g = some ce) :
    g ≠ entry ∧ ∃ hint f eb, low.funcs.find? (·.name == g) = some hint ∧
      low.machine.func? g = some f ∧ f.blocks.head? = some eb ∧
      placeIn low g eb.id = some ce.offset ∧ ce.params = f.params.length ∧
      ce.rets = f.rets.length ∧ ce.returns = returns f := by
  unfold callees at h
  by_cases hg : (g == entry) = true
  · simp [hg] at h
  · simp only [hg, Bool.false_eq_true, if_false] at h
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, hint, hh, f, hf, eb, he, o, ho, hce⟩ := h
    cases hce
    exact ⟨by simpa using hg, hint, f, eb, hh, hf, he, ho, rfl, rfl, rfl⟩

theorem preIf_succ {isRoot : Bool} {low : Lowering} {eb S : Block} (h : S.id ≠ eb.id) {β : Type}
    (k : FeM β) : (preIf isRoot low eb S >>= fun _ => k) = k := by
  cases isRoot <;> simp [preIf, pre, h]

theorem Final'.of_none {D : Array UInt256} {st : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} {B B' : List UInt256} {n n' : Nat}
    (h : Final' K M D st r none B n) {ret : Option UInt256} : Final' K M D st r ret B' n' := by
  rcases h with h | ⟨_, _, _, _, _, h, -⟩
  · exact .inl h
  · cases h

/-- Where the function cannot return, the bytes end as the IR's run does. -/
theorem Final'.final {D : Array UInt256} {st : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} {B : List UInt256} {n : Nat}
    (h : Final' K M D st r none B n) : Final K M D st r := by
  rcases h with h | ⟨_, _, _, _, _, h, -⟩
  · exact h
  · cases h

theorem Final'.reach {D : Array UInt256} {s s₁ : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} {ret : Option UInt256}
    {B : List UInt256} {nrets n : Nat} (h : Reach K D s s₁ n) (hf : Final' K M D s₁ r ret B nrets) :
    Final' K M D s r ret B nrets := by
  rcases h with ⟨-, rfl⟩ | hx
  · exact hf
  · exact hf.prepend hx

theorem head_block {f : Func} {eb : Block} (he : f.blocks.head? = some eb) :
    eb ∈ f.blocks ∧ f.block? eb.id = some eb := by
  cases hb : f.blocks with
  | nil => simp [hb] at he
  | cons b bs =>
    rw [hb] at he
    cases he
    exact ⟨by simp, by simp [Func.block?, hb]⟩

set_option maxHeartbeats 1000000 in
/-- The function theorem: from a block's start of a function of a checked section, below the
    fuel's gas, the bytes end as the IR's run of the function from that block does, or return
    as it does where the function may return from the block, at profile `P1`. -/
theorem func_run {code : CodeSection} {low : Lowering} {plan : SpillPlan} {G : Guard}
    {entry : String} {I : ExecutionEnv} {tail : ByteArray} {ic : Fe.Sonatina.Ctx}
    (hI : I.code = code.bytecode ++ tail) (hsize : code.bytecode.size < UInt256.size)
    (hsym : ic.symbol = (code.symbols.lookup ·))
    (hfs : ∀ hint ∈ low.funcs, checkFunc code low plan G entry hint = .ok ())
    (hK : low.machine.hasCalls = true → K = true) :
    ∀ fuel (hint : FuncHint) (f : Func) (eb b : Block) prev env w st ret B inh,
      hint ∈ low.funcs → low.machine.func? hint.name = some f → f.blocks.head? = some eb →
      st.machineState.gasAvailable.toNat < fuel →
      AtBlock M low hint f (frameOf low entry f) I b prev env w st ret B →
      ((frameOf low entry f).returns = true →
        ∃ k, ret = some k ∧ (D_J I.code 0).contains k = true) →
      NoPanicAt ((preIf (hint.name == entry) low eb b >>= fun _ =>
          runBlocksG G low.machine ic inh f env prev b.id).exec I w) →
      Final' K M (D_J I.code 0) st
        ((preIf (hint.name == entry) low eb b >>= fun _ =>
          runBlocksG G low.machine ic inh f env prev b.id).exec I w)
        (if (frameOf low entry f).exact b.id then ret else none) B f.rets.length := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
  intro hint f eb b
  generalize hr : zeroRank f (placeIn low hint.name) f.blocks.length b.id = r
  induction r using Nat.strong_induction_on generalizing b with
  | _ r ihr =>
  intro prev env w st ret B inh hmem hf he hg hat hretk hnp
  obtain ⟨f', eb', hf', he', hbits, hnd, ⟨sp, hsg, hchk⟩, hpred, hexact, hretx, hexr, hrets, hfresh, -, -, -,
    -, -⟩ := func_facts (hfs hint hmem)
  rw [hf] at hf'; cases hf'
  rw [he] at he'; cases he'
  -- A callee's bytes from its entry, below this block's gas, end as its IR's run.
  have hcallee : ∀ (cs : CallSeg) (ce : Callee) (ws : List UInt256) (st' : State) (w' : World)
      (ret' : Option UInt256) (B' : List UInt256),
      (frameOf low entry f).callee cs.callee = some ce →
      st'.machineState.pc.toNat = ce.offset → st'.executionEnv = I → Agree M st' w' →
      ws.length = ce.params →
      st'.machineState.stack = ws ++ (match ret' with | some k => k :: B' | none => B') →
      (ce.returns = true → ∃ k, ret' = some k ∧ (D_J I.code 0).contains k = true) →
      (ce.returns = false → ret' = none) →
      st'.machineState.gasAvailable.toNat < st.machineState.gasAvailable.toNat →
      NoPanicAt ((runFuncG G low.machine ic (inh ++ cs.keep) cs.callee
        (ws.map Fe.Sonatina.word)).exec I w') →
      Final' K M (D_J I.code 0) st'
        ((runFuncG G low.machine ic (inh ++ cs.keep) cs.callee (ws.map Fe.Sonatina.word)).exec
          I w') ret' B' ce.rets := by
    intro cs ce ws st' w' ret' B' hce hpc henv' hag hlen hstk hrk hnr hg' hnpz
    obtain ⟨hne, hint', f', eb', hh, hf', he', hpl, hpar, hrt, hrr⟩ := callees_some hce
    have hmem' := List.mem_of_find?_eq_some hh
    have hname : hint'.name = cs.callee := by simpa using List.find?_some hh
    obtain ⟨f'', eb'', hf'', he'', -, -, -, -, -, -, -, -, -, hpb, hpnd, -, hent, hephi⟩ :=
      func_facts (hfs hint' hmem')
    rw [hname, hf'] at hf''; cases hf''
    rw [he'] at he''; cases he''
    have hlen' : ws.length = f'.params.length := hlen.trans hpar
    have hpb' : ∀ d ∈ f'.params, d.2.bits = 256 := fun d hd => by
      simpa using List.all_eq_true.mp hpb d hd
    obtain ⟨-, hfa⟩ := foldl_words {} hlen' hpnd hpb'
    set env0 := (f'.params.zip (ws.map Fe.Sonatina.word)).foldl
      (fun env ((id, ty), v) => env.insert id (v.as ty)) ({} : Env) with henv0
    have hbind : Fe.Sonatina.bind {} f'.params (ws.map Fe.Sonatina.word) = pure env0 := by
      simp [Fe.Sonatina.bind, hlen', henv0]
    have hrun : (runFuncG G low.machine ic (inh ++ cs.keep) cs.callee
        (ws.map Fe.Sonatina.word)).exec I w' =
        (preIf (hint'.name == entry) low eb' eb' >>= fun _ =>
          runBlocksG G low.machine ic (inh ++ cs.keep) f' env0 none eb'.id).exec I w' := by
      rw [runFuncG.eq_1] at hnpz ⊢
      rw [(guarded_exec hnpz).1]
      have : (hint'.name == entry) = false := by rw [hname]; simpa using hne
      simp [hf', he', hbind, preIf, this]
    obtain ⟨hebm, hblk⟩ := head_block he'
    obtain ⟨hbE, hfind, hentry⟩ : ∃ hbE, hint'.blocks.find? (·.block == eb'.id) = some hbE ∧
        hbE.entryStack = f'.params.map (.value ·.1) ++
          if (frameOf low entry f').returns then [.funcReturn] else [] := by
      cases hfe : hint'.blocks.find? (·.block == eb'.id) with
      | none => rw [hfe] at hent; cases hent
      | some hbE => rw [hfe] at hent; exact ⟨hbE, rfl, Option.some.inj hent⟩
    have hbid : hbE.block = eb'.id := by simpa using List.find?_some hfind
    have hexE : (frameOf low entry f').exact eb'.id = returns f' := by
      simp only [frameOf, returns, he', Option.map_some, Option.getD_some, Bool.and_self]
    -- The callee's words on its entry stack.
    have hvals : List.Forall₂ (SlotWord env0 ret') (f'.params.map (.value ·.1)) ws :=
      forall₂_slots hfa
    have hat' : AtBlock M low hint' f' (frameOf low entry f') I eb' none env0 w' st' ret' B' := by
      have hmk : ∀ wsE, st'.machineState.stack = wsE ++ B' →
          List.Forall₂ (SlotWord env0 ret') ((frameOf low entry f').slots hbE) wsE →
          AtBlock M low hint' f' (frameOf low entry f') I eb' none env0 w' st' ret' B' :=
        fun wsE h1 h2 => ⟨hebm, hblk, henv', hag, hbE, ce.offset, env0, wsE, hfind,
          by rw [hname]; exact hpl, hpc, by simp [enter, hephi, Fe.Sonatina.bind], h1, h2,
          by simp [hephi]⟩
      have hret0 : (frameOf low entry f').returns = returns f' := rfl
      cases hR : returns f'
      · have hret' : ret' = none := hnr (hrr.trans hR)
        subst hret'
        refine hmk ws (by simpa using hstk) ?_
        unfold Frame.slots
        rw [hbid, hexE, hR, hentry, hret0, hR]
        simp only [Bool.false_eq_true, if_false, List.append_nil]
        rw [List.filter_eq_self.mpr fun x hx => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx; rfl]
        exact hvals
      · obtain ⟨k, rfl, -⟩ := hrk (hrr.trans hR)
        refine hmk (ws ++ [k]) (by simpa using hstk) ?_
        unfold Frame.slots
        rw [hbid, hexE, hR, hentry, hret0, hR]
        simp only [if_true]
        exact forall₂_append hvals (.cons rfl .nil)
    have hrk' : (frameOf low entry f').returns = true →
        ∃ k, ret' = some k ∧ (D_J I.code 0).contains k = true := fun h => hrk (hrr.trans h)
    have hf2 := ihf st.machineState.gasAvailable.toNat hg hint' f' eb' eb' none env0 w' st' ret' B'
      (inh ++ cs.keep) hmem' (by rw [hname]; exact hf') he' hg' hat' hrk' (hrun ▸ hnpz)
    rw [hrun, hrt]
    rw [hexE] at hf2
    cases hR : returns f'
    · rw [hR] at hf2
      exact hf2.of_none
    · rw [hR] at hf2
      exact hf2
  have hKf : ∀ b ∈ f.blocks, ∀ s ∈ b.body, s.inst.messages = true → K = true :=
    fun b hb s hs hm => hK (List.any_eq_true.mpr ⟨f, List.mem_of_find?_eq_some hf,
      List.any_eq_true.mpr ⟨b, hb, List.any_eq_true.mpr ⟨s, hs, hm⟩⟩⟩)
  rcases block_run hI hsize hsym hbits hnd hsg hchk hpred hexact hretx hexr hrets hfresh hKf hat
      hretk hcallee hnp with hfin | ⟨S, env', w', st', n, B', hreach, hlow, hat', hBB, hne, hIR⟩
  · exact hfin
  rw [hIR] at hnp ⊢
  have hnpS : NoPanicAt ((preIf (hint.name == entry) low eb S >>= fun _ =>
      runBlocksG G low.machine ic inh f env' (some b.id) S.id).exec I w') := by
    rw [preIf_succ hne]; exact hnp
  have key : Final' K M (D_J I.code 0) st'
      ((preIf (hint.name == entry) low eb S >>= fun _ =>
        runBlocksG G low.machine ic inh f env' (some b.id) S.id).exec I w')
      (if (frameOf low entry f).exact S.id then ret else none) B' f.rets.length := by
    rcases hreach with ⟨rfl, rfl⟩ | hx
    · exact ihr _ (hr ▸ hlow rfl) S rfl (some b.id) env' w' st' ret B' inh hmem hf he hg hat'
        hretk hnpS
    · exact ihf st.machineState.gasAvailable.toNat hg hint f eb S (some b.id) env' w' st' ret B'
        inh hmem hf he hx.gas_lt hat' hretk hnpS
  rw [preIf_succ hne] at key
  cases hS : (frameOf low entry f).exact S.id
  · rw [hS] at key
    exact Final'.reach hreach key.of_none
  · rw [hS] at key
    obtain ⟨rfl, hb⟩ := hBB hS
    rw [hb]
    exact Final'.reach hreach key

end Fe.Sonatina.Check
