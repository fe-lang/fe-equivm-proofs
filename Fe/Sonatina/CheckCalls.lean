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

/-- How the IR's run of a block's statements goes, from the world `w`, under the valuation `ρ`,
    up to the result `r` of the statements: the events `evs` trace the world up to the first
    of the calls `cls`, and each call runs its callee on its arguments' words. -/
inductive Segs (ee : ExecutionEnv) (m : Module) (ic : Fe.Sonatina.Ctx) (ρ : Nat → UInt256) :
    List Event → List CallSeg → World → Option (Except (Fe.Exit World) World) → Prop
  /-- No call is left: the events end the statements. -/
  | last {evs : List Event} {w : World} {r : Except (Fe.Exit World) World}
      (h : Trace ee ρ evs w r) : Segs ee m ic ρ evs [] w (some r)
  /-- An event fails before the next call. -/
  | fail {evs : List Event} {cls : List CallSeg} {w : World} {e : Fe.Exit World}
      (h : Trace ee ρ evs w (.error e)) : Segs ee m ic ρ evs cls w (some (.error e))
  /-- The callee's run is stuck. -/
  | callNone {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ : World}
      {ws : List UInt256} (h : Trace ee ρ evs w (.ok w₁))
      (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFunc m ic cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ = none) :
      Segs ee m ic ρ evs (cs :: more) w none
  /-- The callee's run fails. -/
  | callErr {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ : World}
      {ws : List UInt256} {e : Fe.Exit World} (h : Trace ee ρ evs w (.ok w₁))
      (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFunc m ic cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ = some (.error e)) :
      Segs ee m ic ρ evs (cs :: more) w (some (.error e))
  /-- The callee returns the words of the call's results, and the next segment goes on. -/
  | callOk {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ w₂ : World}
      {ws : List UInt256} {r : Option (Except (Fe.Exit World) World)}
      (h : Trace ee ρ evs w (.ok w₁)) (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFunc m ic cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        some (.ok ((cs.dsts.map ρ).map Fe.Sonatina.word, w₂)))
      (rest : Segs ee m ic ρ cs.events more w₂ r) : Segs ee m ic ρ evs (cs :: more) w r
  /-- The callee returns other than as many words as the call has results. -/
  | callOther {evs : List Event} {cs : CallSeg} {more : List CallSeg} {w w₁ w₂ : World}
      {ws : List UInt256} {vals : List Val} {r : Option (Except (Fe.Exit World) World)}
      (h : Trace ee ρ evs w (.ok w₁)) (ha : cs.args.mapM (·.eval ee ρ) = some ws)
      (hz : (runFunc m ic cs.callee (ws.map Fe.Sonatina.word)).exec ee w₁ =
        some (.ok (vals, w₂)))
      (hv : ∀ ws' : List UInt256, vals = ws'.map Fe.Sonatina.word → ws'.length ≠ cs.dsts.length) :
      Segs ee m ic ρ evs (cs :: more) w r

/-- A block's statements up to the first call, and the rest after it. -/
theorem segments_call {c : Ctx} : ∀ {stmts : List Stmt} {evs : List Event} {cs : CallSeg}
    {more : List CallSeg}, c.segments stmts = some (evs, cs :: more) →
    ∃ pre s q args ce, stmts = pre ++ s :: q ∧ (∀ t ∈ pre, ∀ g a, t.inst ≠ .call g a) ∧
      pre.filterMapM c.eventOfStmt = some evs ∧ s.inst = .call cs.callee args ∧
      args.mapM (c.operand depth) = some cs.args ∧ cs.dsts = s.dsts.map (·.1) ∧
      c.frame.callee cs.callee = some ce ∧ cs.args.length = ce.params ∧
      s.dsts.length = (if ce.returns then ce.rets else 0) ∧ c.segments q = some (cs.events, more)
  | [], evs, cs, more, h => by simp [Ctx.segments] at h
  | s :: rest, evs, cs, more, h => by
    unfold Ctx.segments at h
    cases hr : c.segments rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · next g args hg =>
        cases hce : c.frame.callee g with
        | none => simp [hce] at h
        | some ce =>
          cases hes : args.mapM (c.operand depth) with
          | none => simp [hce, hes] at h
          | some es =>
            simp only [hce, hes, Option.bind_some] at h
            by_cases hk : (es.length == ce.params &&
                s.dsts.length == (if ce.returns then ce.rets else 0)) = true
            · rw [if_pos hk] at h
              simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp only [Bool.and_eq_true, beq_iff_eq] at hk
              exact ⟨[], s, rest, args, ce, rfl, by simp, rfl, hg, hes, rfl, hce, hk.1, hk.2, hr⟩
            · rw [if_neg hk] at h
              cases h
      · next hnc =>
        have hnc' : ∀ g a, s.inst ≠ .call g a := fun g a h' => hnc g a h'
        cases he : c.eventOfStmt s with
        | none => simp [he] at h
        | some o =>
          obtain ⟨hevs, hcl⟩ : evs = o.toList ++ evs' ∧ calls' = cs :: more := by
            cases o <;> simp [he] at h <;> exact ⟨by simp [h.1], h.2⟩
          subst hcl
          obtain ⟨pre, s', q, args, ce, rfl, hpre, hev, h1⟩ := segments_call hr
          refine ⟨s :: pre, s', q, args, ce, rfl, ?_, ?_, h1⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hnc'
            · exact hpre t ht
          · rw [List.filterMapM_cons, he, hev, hevs]
            cases o <;> rfl

/-- A block's statements without a call left. -/
theorem segments_last {c : Ctx} : ∀ {stmts : List Stmt} {evs : List Event},
    c.segments stmts = some (evs, []) →
      (∀ t ∈ stmts, ∀ g a, t.inst ≠ .call g a) ∧ stmts.filterMapM c.eventOfStmt = some evs
  | [], evs, h => by
    simp only [Ctx.segments, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | s :: rest, evs, h => by
    unfold Ctx.segments at h
    cases hr : c.segments rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · next g args hg =>
        cases hce : c.frame.callee g with
        | none => simp [hce] at h
        | some ce =>
          cases hes : args.mapM (c.operand depth) with
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
          obtain ⟨hevs, hcl⟩ : evs = o.toList ++ evs' ∧ calls' = [] := by
            cases o <;> simp [he] at h <;> exact ⟨by simp [h.1], h.2⟩
          subst hcl
          obtain ⟨h1, h2⟩ := segments_last hr
          refine ⟨fun t ht => ?_, ?_⟩
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact fun g a h' => hnc g a h'
            · exact h1 t ht
          · rw [List.filterMapM_cons, he, h2, hevs]
            cases o <;> rfl

theorem runBody_append {m : Module} {ic : Fe.Sonatina.Ctx} :
    ∀ (env : Env) (p q : List Stmt),
      runBody m ic env (p ++ q) = runBody m ic env p >>= fun env' => runBody m ic env' q
  | env, [], q => by rw [runBody.eq_1]; simp
  | env, s :: p, q => by
    have ih := fun env' => runBody_append (m := m) (ic := ic) env' p q
    rw [List.cons_append, runBody.eq_2, runBody.eq_2]
    simp only [ih]
    split <;> simp only [bind_assoc]

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
      args.mapM (c.operand depth) = some es →
      ∃ ws, es.mapM (·.eval ee ρ) = some ws ∧
        args.mapM (evalOperand env) = pure (ws.map Fe.Sonatina.word)
  | [], es, _, h => by
    simp at h; subst h; exact ⟨[], rfl, rfl⟩
  | a :: args, es, hr, h => by
    simp only [reads, List.all_cons, Bool.and_eq_true] at hr
    rw [List.mapM_cons] at h
    cases he : c.operand depth a with
    | none => simp [he] at h
    | some e =>
    cases hes : args.mapM (c.operand depth) with
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
theorem body_calls {ee : ExecutionEnv} {m : Module} {ic : Fe.Sonatina.Ctx} {c : Ctx}
    (hsym : ic.symbol = (c.symbols.lookup ·)) :
    ∀ (calls : List CallSeg) (stmts pre : List Stmt) (D D' : List Nat) (env : Env) (w : World)
      (evs : List Event),
      c.defs = (pre ++ stmts).filterMap Stmt.local? →
      (∀ t ∈ pre, ∀ d ∈ t.dsts, d.1 ∈ D) →
      definedAfter D stmts = some D' →
      c.segments stmts = some (evs, calls) →
      (∀ s ∈ stmts, ∀ d ∈ s.dsts, d.2.bits = 256) →
      (∀ s ∈ stmts, (s.dsts.map (·.1)).Nodup) →
      (∃ ρ, WordsOf env ρ D) → (∀ ρ, WordsOf env ρ D → Cons ee ρ c D) →
      ∃ x, (runBody m ic env stmts).exec ee w = x ∧ ∃ envf Df,
        (∀ id ∈ D, envf[id]? = env[id]?) ∧ (∀ id ∈ D, id ∈ Df) ∧ (∀ id ∈ Df, id ∈ D') ∧
        (∃ ρ, WordsOf envf ρ Df) ∧
        (((∀ env' w', x = some (.ok (env', w')) → envf = env' ∧ Df = D') ∧
            ∀ ρ, WordsOf envf ρ Df → Cons ee ρ c Df ∧
              Segs ee m ic ρ evs calls w (x.map (·.map Prod.snd))) ∨
          ∀ ρ, WordsOf envf ρ Df → Cons ee ρ c Df ∧ Segs ee m ic ρ evs calls w none)
  | [], stmts, pre, D, D', env, w, evs, hdefs, hpre, hd, hseg, hbits, _, hw, hc => by
    obtain ⟨-, hev⟩ := segments_last hseg
    obtain ⟨x, hx, hends⟩ := body_run (m := m) hsym stmts pre D D' env w evs []
      (by rw [hdefs, List.append_nil]) hpre hd hev
      hbits hw hc
    refine ⟨some x, hx, ?_⟩
    cases x with
    | ok p =>
      obtain ⟨env', w'⟩ := p
      obtain ⟨h1, h2, h3⟩ := hends
      exact ⟨env', D', h1, definedAfter_mono hd, fun _ h => h, h2, .inl ⟨(fun _ _ h => by
        cases h; exact ⟨rfl, rfl⟩), fun ρ hρ => ⟨(h3 ρ hρ).1, .last (h3 ρ hρ).2⟩⟩⟩
    | error e =>
      obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends
      exact ⟨envf, Df, h1, h2, h2', h3, .inl ⟨(fun _ _ h => by cases h),
        fun ρ hρ => ⟨(h4 ρ hρ).1, .last (h4 ρ hρ).2⟩⟩⟩
  | cs :: more, stmts, pre, D, D', env, w, evs, hdefs, hpre, hd, hseg, hbits, hndd, hw, hc => by
    obtain ⟨p0, s, q, args, ce, rfl, -, hev, hinst, hargs, hdsts, -, -, hdl, hq⟩ :=
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
    obtain ⟨x1, hx1, hends1⟩ := body_run (m := m) hsym p0 pre D D1 env w evs (s :: q)
      (by rw [hdefs, List.append_assoc]) hpre hD1 hev
      (fun t ht => hbits t (by simp [ht])) hw hc
    have hD1sub := definedAfter_mono hD1
    have hx0 : (runBody m ic env (p0 ++ s :: q)).exec ee w =
        (runBody m ic env p0 >>= fun env' => runBody m ic env' (s :: q)).exec ee w := by
      rw [runBody_append]
    cases x1 with
    | error e =>
      have hx : (runBody m ic env (p0 ++ s :: q)).exec ee w = some (.error e) := by
        rw [hx0, Fe.M.exec_bind, hx1]
      obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends1
      exact ⟨some (.error e), hx, envf, Df, h1, h2,
        fun id h => definedAfter_mono hd id (List.mem_append_left _ (h2' id h)), h3,
        .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h4 ρ hρ).1, .fail (h4 ρ hρ).2⟩⟩⟩
    | ok p =>
    obtain ⟨env1, w1⟩ := p
    have hx : (runBody m ic env (p0 ++ s :: q)).exec ee w =
        (runBody m ic env1 (s :: q)).exec ee w1 := by
      rw [hx0, Fe.M.exec_bind, hx1]
    obtain ⟨h1, ⟨ρ1, hw1⟩, h3⟩ := hends1
    obtain ⟨ws, -, hevargs⟩ := args_words (h3 ρ1 hw1).1 hw1 hrd' hargs
    -- Under any valuation of the values before the call, its arguments have the same words.
    have hws : ∀ ρ, WordsOf env1 ρ D1 → cs.args.mapM (·.eval ee ρ) = some ws := fun ρ hρ => by
      obtain ⟨ws', hm, he⟩ := args_words (h3 ρ hρ).1 hρ hrd' hargs
      rw [hm, map_word_inj (pure_inj (he.symm.trans hevargs))]
    have hcall : runBody m ic env1 (s :: q) =
        runFunc m ic cs.callee (ws.map Fe.Sonatina.word) >>= fun vals =>
          Fe.Sonatina.bind env1 s.dsts vals >>= fun env' => runBody m ic env' q := by
      rw [runBody.eq_2]
      simp only [hinst, hevargs, pure_bind]
    have hD1D' : ∀ id ∈ D1, id ∈ D' := fun id h =>
      definedAfter_mono hd id (List.mem_append_left _ h)
    cases hz : (runFunc m ic cs.callee (ws.map Fe.Sonatina.word)).exec ee w1 with
    | none =>
      refine ⟨none, by rw [hx]; simp [hcall, Fe.M.exec_bind, hz], env1, D1, h1, hD1sub, hD1D',
        ⟨ρ1, hw1⟩, .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩⟩
      exact .callNone (h3 ρ hρ).2 (hws ρ hρ) hz
    | some z =>
    cases z with
    | error e =>
      refine ⟨some (.error e), by rw [hx]; simp [hcall, Fe.M.exec_bind, hz], env1, D1, h1,
        hD1sub, hD1D', ⟨ρ1, hw1⟩, .inl ⟨(fun _ _ h => by cases h), fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩⟩
      exact .callErr (h3 ρ hρ).2 (hws ρ hρ) hz
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
        Cons ee ρ c (D1 ++ s.dsts.map (·.1)) := fun ρ hρ =>
      ((h3 ρ fun id h => (hagree2 id h).symm.trans (hρ id (List.mem_append_left _ h))).1).mono
        (fun x hx => List.mem_append_left _ hx) fun id hid hn inst hl => by
          rcases List.mem_append.mp hid with h | h
          · exact absurd h hn
          · rw [hnone id h] at hl; cases hl
    obtain ⟨x, hx2, envf, Df, g1, g2, g3, g4, g5⟩ := body_calls hsym more q (pre ++ p0 ++ [s])
      (D1 ++ s.dsts.map (·.1)) D' env2 w2 cs.events hdefs2 hpre2 hd hq
      (fun t ht => hbits t (by simp [ht])) (fun t ht => hndd t (by simp [ht])) ⟨_, hw2⟩ hc2
    have hxe : (runBody m ic env (p0 ++ s :: q)).exec ee w = x := by
      rw [hx, hcall, Fe.M.exec_bind, hz]
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
    have hseg : ∀ ρ, WordsOf envf ρ Df → ∀ r, Segs ee m ic ρ cs.events more w2 r →
        Segs ee m ic ρ evs (cs :: more) w r := fun ρ hρ r hr =>
      .callOk (h3 ρ (hρ1 ρ hρ)).2 (hws ρ (hρ1 ρ hρ)) (by rw [hres ρ hρ]; exact hz) hr
    refine ⟨x, hxe, envf, Df, fun id h => (g1 id (List.mem_append_left _ (hD1sub id h))).trans
      ((hagree2 id (hD1sub id h)).trans (h1 id h)), fun id h => hsub2 id (hD1sub id h), g3, g4,
      ?_⟩
    rcases g5 with ⟨gok, gs⟩ | gs
    · exact .inl ⟨gok, fun ρ hρ => ⟨(gs ρ hρ).1, hseg ρ hρ _ (gs ρ hρ).2⟩⟩
    · exact .inr fun ρ hρ => ⟨(gs ρ hρ).1, hseg ρ hρ _ (gs ρ hρ).2⟩

end Fe.Sonatina.Check
