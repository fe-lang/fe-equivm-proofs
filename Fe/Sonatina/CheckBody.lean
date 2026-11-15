import Fe.Sonatina.CheckIR

/-!
# The machine IR's run of a block's statements

`body_run`: the interpreter runs a block's statements that the checker accepts (each defined
before it is read, each defining fresh values, each pure or an event of the class) without
diverging, and ends as `BodyEnds` says: returning or failing at an event, with the values it
defined words, and under any valuation `ρ` of them the block's events tracing the world
(`Trace`) and the checker's expressions having their words (`Cons`).
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- What a statement defines locally, it defines. -/
theorem local_def {t : Stmt} {p : Nat × Inst} (h : t.local? = some p) : t.def? = some p := by
  unfold Stmt.local? at h
  split at h
  · cases h
  · exact h

theorem lookup_def {pre rest : List Stmt} {s : Stmt} {id : Nat} {ty : Ty}
    (hs : s.dsts = [(id, ty)]) (hnc : ∀ callee args, s.inst ≠ .call callee args)
    (hpre : ∀ t ∈ pre, ∀ d ∈ t.dsts, d.1 ≠ id) :
    ((pre ++ s :: rest).filterMap Stmt.local?).lookup id = some s.inst := by
  induction pre with
  | nil =>
    have : s.local? = some (id, s.inst) := by
      unfold Stmt.local?
      split
      · next h => obtain ⟨g, a, he⟩ : ∃ g a, s.inst = .call g a := by
                    revert h; cases s.inst <;> simp
                  exact absurd he (hnc g a)
      · simp [Stmt.def?, hs]
    simp [this]
  | cons t pre ih =>
    have ih' := ih fun t' h => hpre t' (List.mem_cons_of_mem _ h)
    cases ht : t.local? with
    | none => simpa [List.filterMap_cons, ht] using ih'
    | some p =>
      have hp : p.1 ≠ id := by
        have ht := local_def ht
        unfold Stmt.def? at ht
        split at ht
        · next id' ty' hd =>
          cases ht
          exact hpre t (by simp) (id', ty') (by simp [hd])
        · cases ht
      have hb : (id == p.1) = false := by simpa using Ne.symm hp
      rw [List.cons_append, List.filterMap_cons, ht]
      simp only [List.lookup, hb]
      exact ih'

theorem opWord_congr {ρ ρ' : Nat → UInt256} {D : List Nat} (h : ∀ id ∈ D, ρ id = ρ' id) :
    ∀ {o : Operand}, reads D [o] = true → opWord ρ o = opWord ρ' o
  | .var id, hr => by
    simp only [opWord, h id (by simpa [reads, Operand.var?] using hr)]
  | .imm _ _, _ => rfl
  | .undef _, _ => rfl

theorem opWords_congr {ρ ρ' : Nat → UInt256} {D : List Nat} (h : ∀ id ∈ D, ρ id = ρ' id) :
    ∀ {os : List Operand}, reads D os = true → os.mapM (opWord ρ) = os.mapM (opWord ρ')
  | [], _ => rfl
  | o :: os, hr => by
    simp only [reads, List.all_cons, Bool.and_eq_true] at hr
    simp only [List.mapM_cons, opWord_congr h (o := o) (by simpa [reads] using hr.1),
      opWords_congr h hr.2]

/-- A pure instruction's word depends on its operands' words only. -/
theorem instWord_congr {ee : ExecutionEnv} {ρ ρ' : Nat → UInt256} {D : List Nat}
    {symbols : List (String × Nat × Nat)} {inst : Inst} (h : ∀ id ∈ D, ρ id = ρ' id)
    (hr : reads D inst.operands = true) :
    instWord ee ρ symbols inst = instWord ee ρ' symbols inst := by
  cases inst <;>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hr <;>
    simp only [instWord]
  · rw [opWord_congr h (by simpa [reads] using hr.1), opWord_congr h (by simpa [reads] using hr.2)]
  · rw [opWord_congr h (by simpa [reads] using hr.1), opWord_congr h (by simpa [reads] using hr.2)]
  · rw [opWord_congr h (by simpa [reads] using hr)]
  · rw [opWord_congr h (by simpa [reads] using hr)]
  · rw [opWords_congr h hr]

theorem opWord_some {ρ : Nat → UInt256} {expand : Nat → Option Expr} {o : Operand} {e : Expr}
    (h : operandWith expand o = some e) : ∃ v, opWord ρ o = some v := by
  cases o with
  | var id => exact ⟨_, rfl⟩
  | imm bits x =>
    simp only [operandWith] at h
    split_ifs at h with hb
    exact ⟨.ofNat x, by rw [opWord, if_pos hb]⟩
  | undef _ => cases h

theorem opWords_some {ρ : Nat → UInt256} {expand : Nat → Option Expr} :
    ∀ {os : List Operand} {es : List Expr}, os.mapM (operandWith expand) = some es →
      ∃ ws, os.mapM (opWord ρ) = some ws ∧ ws.length = es.length
  | [], es, h => by simp at h; subst h; exact ⟨[], rfl, rfl⟩
  | o :: os, es, h => by
    cases ho : operandWith expand o with
    | none => simp [ho] at h
    | some e =>
      cases hos : os.mapM (operandWith expand) with
      | none => simp [ho, hos] at h
      | some es' =>
        simp only [List.mapM_cons, ho, hos, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨v, hv⟩ := opWord_some (ρ := ρ) ho
        obtain ⟨ws, hws, hl⟩ := opWords_some (ρ := ρ) hos
        exact ⟨v :: ws, by simp [List.mapM_cons, hv, hws], by simp [hl]⟩

theorem binOpcode_pure {op : BinOp} {opc : Operation} (h : binOpcode op = some opc) :
    pureOps.contains opc = true ∧ δ opc = some 2 := by
  cases op <;> simp only [binOpcode, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

theorem cmpOpcode_pure {op : CmpOp} {opc : Operation} (h : cmpOpcode op = some opc) :
    pureOps.contains opc = true ∧ δ opc = some 2 := by
  cases op <;> simp only [cmpOpcode, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

theorem evmPureOpcode_pure {op : EvmOp} {opc : Operation} (h : evmPureOpcode op = some opc) :
    pureOps.contains opc = true := by
  cases op <;> simp only [evmPureOpcode, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    decide

/-- A pure instruction of the class has a word, its EVM instructions on as many operands as
    they pop. -/
theorem instWord_some {ee : ExecutionEnv} {ρ : Nat → UInt256} {expand : Nat → Option Expr}
    {symbols : List (String × Nat × Nat)} {inst : Inst} {e : Expr}
    (h : pureWith expand symbols inst = some e)
    (harity : ∀ op args, inst = .evm op args →
      (evmPureOpcode op).all fun o => δ o == some args.length) :
    ∃ v, instWord ee ρ symbols inst = some v := by
  cases inst with
  | bin op a b =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : binOpcode op <;> cases ha : operandWith expand a <;>
      cases hb : operandWith expand b <;> simp [hc, ha, hb] at h
    obtain ⟨va, hva⟩ := opWord_some (ρ := ρ) ha
    obtain ⟨vb, hvb⟩ := opWord_some (ρ := ρ) hb
    obtain ⟨r, hr⟩ := opEval_total (ee := ee) (ws := [va, vb]) (binOpcode_pure hc).1
      (binOpcode_pure hc).2
    exact ⟨r, by simp [instWord, hc, hva, hvb, hr]⟩
  | cmp op a b =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : cmpOpcode op <;> cases ha : operandWith expand a <;>
      cases hb : operandWith expand b <;> simp [hc, ha, hb] at h
    obtain ⟨va, hva⟩ := opWord_some (ρ := ρ) ha
    obtain ⟨vb, hvb⟩ := opWord_some (ρ := ρ) hb
    obtain ⟨r, hr⟩ := opEval_total (ee := ee) (ws := [va, vb]) (cmpOpcode_pure hc).1
      (cmpOpcode_pure hc).2
    exact ⟨r, by simp [instWord, hc, hva, hvb, hr]⟩
  | isZero a =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases ha : operandWith expand a <;> simp [ha] at h
    obtain ⟨va, hva⟩ := opWord_some (ρ := ρ) ha
    exact ⟨_, by simp [instWord, hva, opEval, evalOp]; rfl⟩
  | not a =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases ha : operandWith expand a <;> simp [ha] at h
    obtain ⟨va, hva⟩ := opWord_some (ρ := ρ) ha
    exact ⟨_, by simp [instWord, hva, opEval, evalOp]; rfl⟩
  | evm op args =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : evmPureOpcode op <;> cases has : args.mapM (operandWith expand) <;>
      simp [hc, has] at h
    next opc es =>
    obtain ⟨ws, hws, hl⟩ := opWords_some (ρ := ρ) has
    have hk := harity op args rfl
    simp only [hc, Option.all_some, beq_iff_eq] at hk
    have hal : args.length = es.length := by
      have := (mapM_some_iff.mp has).length_eq; omega
    obtain ⟨r, hr⟩ := opEval_total (ee := ee) (ws := ws) (evmPureOpcode_pure hc)
      (by rw [hk, hl, hal])
    exact ⟨r, by simp [instWord, hc, hws, hr]⟩
  | symAddr sym =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hs : symbols.lookup sym <;> simp [hs] at h
    rename_i p
    exact ⟨.ofNat p.1, by simp [instWord, hs]⟩
  | symSize sym =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hs : symbols.lookup sym <;> simp [hs] at h
    rename_i p
    exact ⟨.ofNat p.2, by simp [instWord, hs]⟩
  | _ => simp [pureWith] at h

theorem reads_mono {D D₂ : List Nat} (h : ∀ x ∈ D, x ∈ D₂) {os : List Operand}
    (hr : reads D os = true) : reads D₂ os = true := by
  simp only [reads, List.all_eq_true] at hr ⊢
  intro o ho
  have := hr o ho
  cases hv : o.var? <;> simp_all

theorem runBody_cons {m : Module} {ic : Fe.Sonatina.Ctx} {env : Env} {s : Stmt}
    {rest : List Stmt} (h : ∀ callee args, s.inst ≠ .call callee args) :
    runBody m ic env (s :: rest) =
      runInst ic env s.inst >>= fun vals => Fe.Sonatina.bind env s.dsts vals >>= fun env' =>
        runBody m ic env' rest := by
  rw [runBody.eq_2]
  split
  · next callee args hc => exact absurd hc (h callee args)
  · rfl

theorem bind_one (env : Env) (id : Nat) (ty : Ty) (v : Val) :
    Fe.Sonatina.bind env [(id, ty)] [v] = pure (env.insert id (v.as ty)) := rfl

theorem bind_nil (env : Env) : Fe.Sonatina.bind env [] [] = pure env := rfl

/-- A read gives a word, a write none. -/
theorem evRun_result {ee : ExecutionEnv} {opc : Operation} {args : List UInt256} {w w' : World}
    {r : Option UInt256} (h : (evRun opc args).exec ee w = some (.ok (r, w'))) :
    r.isSome = readOps.contains opc := by
  unfold evRun at h
  split at h
  -- A message call's word or a creation's.
  case h_9 | h_10 | h_11 | h_12 | h_13 =>
    simp only [Fe.M.exec_map] at h
    split at h <;> simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq,
      reduceCtorEq] at h
    rw [← h.1]; rfl
  all_goals
    by_cases hp : ee.perm = true <;> cases hf : w.feed <;>
      simp [Fe.EVM.sstore, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.sload, Fe.EVM.mload,
        Fe.EVM.keccak256, Fe.EVM.mstore, Fe.EVM.mstore8, Fe.EVM.codecopy, Fe.EVM.calldatacopy,
        Fe.EVM.mcopy, Fe.EVM.selfbalance, Fe.EVM.balance, Fe.EVM.extcodesize,
        Fe.EVM.returndatasize, Fe.EVM.gas, Fe.EVM.tload, Fe.EVM.tstore, Fe.EVM.next, exec_returndatacopy, hp, hf] at h
  all_goals (try split_ifs at h) <;> (try simp at h); rw [← h.1]; rfl

theorem eventWith_evm {expand : Nat → Option Expr} {inst : Inst} {opc : Operation}
    {es : List Expr} (h : eventWith expand inst = some (opc, es)) :
    ∃ op os, inst = .evm op os ∧ evmEventOpcode op = some opc ∧
      os.mapM (operandWith expand) = some es := by
  cases inst with
  | evm op os =>
    simp only [eventWith, Option.bind_eq_bind] at h
    cases hc : evmEventOpcode op <;> cases hos : os.mapM (operandWith expand) <;>
      simp [hc, hos] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨op, os, rfl, hc, hos⟩
  | _ => simp [eventWith] at h

theorem evmEvent_not_pure {op : EvmOp} {opc : Operation} (h : evmEventOpcode op = some opc) :
    evmPureOpcode op = none := by
  cases op <;> simp_all [evmEventOpcode, evmPureOpcode]

/-- How a block's statements end from `env`, the values `D` defined before them and `D'` after:
    returning, `D` kept and `D'` words, the events tracing and the values consistent under any
    valuation of them; or failing or stuck at an event, likewise up to it. -/
def BodyEnds (ee : ExecutionEnv) (c : Ctx) (env : Env) (D D' : List Nat) (evs : List Event)
    (w : World) : Option (Except (Fe.Exit World) (Env × World)) → Prop
  | some (.ok (env', w')) => (∀ id ∈ D, env'[id]? = env[id]?) ∧ (∃ ρ, WordsOf env' ρ D') ∧
      ∀ ρ, WordsOf env' ρ D' → Cons ee ρ c D' ∧ Trace ee ρ evs w (some (.ok w'))
  | x => ∃ envf Df, (∀ id ∈ D, envf[id]? = env[id]?) ∧ (∀ id ∈ D, id ∈ Df) ∧
      (∀ id ∈ Df, id ∈ D') ∧ (∃ ρ, WordsOf envf ρ Df) ∧
        ∀ ρ, WordsOf envf ρ Df → Cons ee ρ c Df ∧ Trace ee ρ evs w (x.map (·.map Prod.snd))

theorem word_inj {a b : UInt256} (h : Val.int 256 a.toNat = Val.int 256 b.toNat) : a = b :=
  eq_of_toNat (by injection h)

theorem WordsOf.agree {env env' : Env} {ρ : Nat → UInt256} {D : List Nat}
    (h : ∀ id ∈ D, env'[id]? = env[id]?) (hw : WordsOf env' ρ D) : WordsOf env ρ D :=
  fun id hid => (h id hid).symm.trans (hw id hid)

theorem WordsOf.same {env : Env} {ρ ρ' : Nat → UInt256} {D : List Nat} (hw : WordsOf env ρ D)
    (hw' : WordsOf env ρ' D) : ∀ id ∈ D, ρ id = ρ' id := fun id hid =>
  word_inj (Option.some.inj ((hw id hid).symm.trans (hw' id hid)))

theorem Cons.mono {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D D₂ : List Nat}
    (hc : Cons ee ρ c D) (h : ∀ x ∈ D, x ∈ D₂) (hn : ∀ id ∈ D₂, id ∉ D → ∀ inst,
      c.defs.lookup id = some inst → reads D₂ inst.operands = true ∧
      ∀ d e, pureWith (c.expand d) c.symbols inst = some e →
        instWord ee ρ c.symbols inst = some (ρ id)) : Cons ee ρ c D₂ := by
  intro id hid inst hl
  by_cases hd : id ∈ D
  · obtain ⟨hr, hp⟩ := hc id hd inst hl
    exact ⟨reads_mono h hr, hp⟩
  · exact hn id hid hd inst hl

theorem definedAfter_mono : ∀ {stmts : List Stmt} {D D' : List Nat},
    definedAfter D stmts = some D' → ∀ x ∈ D, x ∈ D'
  | [], D, D', h, x, hx => by simp [definedAfter] at h; exact h ▸ hx
  | s :: rest, D, D', h, x, hx => by
    simp only [definedAfter] at h
    split_ifs at h
    exact definedAfter_mono h x (List.mem_append_left _ hx)

/-- The IR runs a block's statements of the class as the events say. -/
theorem body_run {ee : ExecutionEnv} {m : Module} {ic : Fe.Sonatina.Ctx} {c : Ctx}
    (hsym : ic.symbol = (c.symbols.lookup ·)) :
    ∀ (stmts pre : List Stmt) (D D' : List Nat) (env : Env) (w : World) (evs : List Event)
      (post : List Stmt),
      c.defs = (pre ++ stmts ++ post).filterMap Stmt.local? →
      (∀ t ∈ pre, ∀ d ∈ t.dsts, d.1 ∈ D) →
      definedAfter D stmts = some D' →
      stmts.filterMapM c.eventOfStmt = some evs →
      (∀ s ∈ stmts, ∀ d ∈ s.dsts, d.2.bits = 256) →
      (∃ ρ, WordsOf env ρ D) → (∀ ρ, WordsOf env ρ D → Cons ee ρ c D) →
      ∃ x, (runBody m ic env stmts).exec ee w = x ∧ BodyEnds ee c env D D' evs w x
  | [], pre, D, D', env, w, evs, _, _, _, hd, he, _, hw, hc => by
    simp only [definedAfter, Option.some.injEq] at hd
    simp only [List.filterMapM_nil, Option.pure_def, Option.some.injEq] at he
    subst hd he
    refine ⟨some (.ok (env, w)), by rw [runBody.eq_1]; rfl, fun _ _ => rfl, hw, fun ρ hρ =>
      ⟨hc ρ hρ, .nil w⟩⟩
  | s :: rest, pre, D, D', env, w, evs, post, hdefs, hpre, hd, he, hbits, ⟨ρ₁, hw₁⟩, hc => by
    simp only [definedAfter] at hd
    split_ifs at hd with hok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨hr, hfresh⟩ := hok
    have hfresh' : ∀ d ∈ s.dsts, d.1 ∉ D := fun d hd' h =>
      by simpa [List.contains_iff_mem, h] using hfresh d hd'
    rw [List.filterMapM_cons] at he
    cases hes : c.eventOfStmt s with
    | none => simp [hes] at he
    | some o =>
    simp only [hes, Option.bind_eq_bind, Option.bind_some] at he
    have hdefs' : c.defs = ((pre ++ [s]) ++ rest ++ post).filterMap Stmt.local? := by
      rw [hdefs]; simp
    have hpre' : ∀ t ∈ pre ++ [s], ∀ d ∈ t.dsts, d.1 ∈ D ++ s.dsts.map (·.1) := by
      intro t ht d hdt
      rcases List.mem_append.mp ht with ht | ht
      · exact List.mem_append_left _ (hpre t ht d hdt)
      · simp only [List.mem_singleton] at ht; subst ht
        exact List.mem_append_right _ (List.mem_map_of_mem hdt)
    have hbits' : ∀ s' ∈ rest, ∀ d ∈ s'.dsts, d.2.bits = 256 :=
      fun s' hs' => hbits s' (List.mem_cons_of_mem _ hs')
    unfold Ctx.eventOfStmt at hes
    split at hes
    · next e hpe =>
      simp only at hes
      split_ifs at hes with hk
      cases hes
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨hlen, harity⟩ := hk
      obtain ⟨⟨id, ty⟩, hds⟩ : ∃ d, s.dsts = [d] := by
        match h : s.dsts, hlen with
        | [d], _ => exact ⟨d, rfl⟩
      have hty : ty.bits = 256 := hbits s (by simp) (id, ty) (by simp [hds])
      have hid : id ∉ D := hfresh' (id, ty) (by simp [hds])
      have hnc : ∀ callee args, s.inst ≠ .call callee args := by
        intro callee args h; rw [h] at hpe; simp [Ctx.pureExpr, pureWith] at hpe
      obtain ⟨v, hv⟩ := instWord_some (ee := ee) (ρ := ρ₁) hpe fun op args h => by
        simpa [h] using harity
      obtain ⟨val, hrun, has⟩ := pure_run hsym hw₁ hr hpe hv
      set env₁ := env.insert id (Val.int 256 v.toNat)
      have hagree : ∀ id' ∈ D, env₁[id']? = env[id']? := fun id' h' => by
        have hne : ¬compare id id' = .eq := by
          rw [compare_eq_iff_eq]; rintro rfl; exact hid h'
        simp only [env₁, Std.TreeMap.getElem?_insert, hne, if_false]
      have hD : D ++ s.dsts.map (·.1) = D ++ [id] := by simp [hds]
      rw [hD] at hd hpre'
      have hw₁' : WordsOf env₁ (Function.update ρ₁ id v) (D ++ [id]) := by
        intro id' h'
        by_cases he' : id' = id
        · subst he'; simp [env₁]
        · rw [List.mem_append, List.mem_singleton] at h'
          rcases h' with h' | h'
          · rw [hagree id' h', Function.update_of_ne he']; exact hw₁ id' h'
          · exact absurd h' he'
      have hc' : ∀ ρ, WordsOf env₁ ρ (D ++ [id]) → Cons ee ρ c (D ++ [id]) := by
        intro ρ hρ
        refine (hc ρ (WordsOf.agree hagree (fun id' h' => hρ id' (List.mem_append_left _ h')))).mono
          (fun x hx => List.mem_append_left _ hx) fun id' h' hn inst hl => ?_
        have : id' = id := by simpa [hn] using h'
        subst this
        rw [hdefs, List.append_assoc, List.cons_append,
          lookup_def hds hnc (fun t ht d hdt h => hid (h ▸ hpre t ht d hdt))] at hl
        cases hl
        refine ⟨reads_mono (fun x hx => List.mem_append_left _ hx) hr, fun _ _ _ => ?_⟩
        have hsame := WordsOf.same (WordsOf.agree hagree (fun x hx => hρ x
          (List.mem_append_left _ hx))) hw₁
        rw [instWord_congr hsame hr, hv]
        congr 1
        exact word_inj (Option.some.inj ((show env₁[id']? = some (Val.int 256 v.toNat) by
          simp [env₁]).symm.trans (hρ id' (by simp))))
      obtain ⟨x, hx, hends⟩ := body_run hsym rest (pre ++ [s]) (D ++ [id]) D' env₁ w evs post
        hdefs' hpre' hd he hbits' ⟨_, hw₁'⟩ hc'
      refine ⟨x, ?_, ?_⟩
      · rw [runBody_cons hnc, Fe.M.exec_bind, hrun w]
        simp only [hds, bind_one, has ty hty, Fe.M.exec_bind, Fe.M.exec_pure]
        exact hx
      · rcases x with _ | _ | ⟨env', w'⟩
        rotate_left 2
        · obtain ⟨h1, h2, h3⟩ := hends
          exact ⟨fun id' h' => (h1 id' (List.mem_append_left _ h')).trans (hagree id' h'), h2, h3⟩
        all_goals
          obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends
          exact ⟨envf, Df, fun id' h' => (h1 id' (List.mem_append_left _ h')).trans
            (hagree id' h'), fun id' h' => h2 id' (List.mem_append_left _ h'), h2', h3, h4⟩
    · next opc es hpe hev =>
      split_ifs at hes with hk
      simp only [bne_iff_ne, ne_eq, not_not] at hk
      obtain ⟨op, os, hinst, hopc, hos⟩ := eventWith_evm hev
      have hnc : ∀ callee args, s.inst ≠ .call callee args := by
        intro callee args h; rw [hinst] at h; cases h
      obtain ⟨args, hargs, hal⟩ := opWords_some (ρ := ρ₁) hos
      have hr' : reads D os = true := by simpa [hinst, Inst.operands] using hr
      have hrunI : runInst ic env s.inst = op.run args := by
        rw [hinst]; simp only [runInst, evalWords_word hw₁ hr' hargs, pure_bind]
      have hk' : δ opc = some args.length := by rw [hk, hal]
      -- The event's operands under any valuation of the values defined before it.
      have hevargs : ∀ ρ, WordsOf env ρ D → es.mapM (·.eval ee ρ) = some args := fun ρ hρ => by
        rw [operands_eval (fun id' e' h' he' => expand_eval (hc ρ hρ) depth id' e' h' he') hr' hos,
          opWords_congr (WordsOf.same hρ hw₁) hr', hargs]
      have hrun := evm_run (ee := ee) hopc hk' w
      obtain ⟨res, rfl, hres⟩ : ∃ res, o = some ⟨opc, es, res⟩ ∧
          ((s.dsts = [] ∧ res = none ∧ readOps.contains opc = false) ∨
            ∃ id ty, s.dsts = [(id, ty)] ∧ res = some id ∧ readOps.contains opc = true) := by
        split at hes <;> simp only [Option.some.injEq, reduceCtorEq] at hes
        · next h1 h2 => exact ⟨none, hes.symm, .inl ⟨h1, rfl, h2⟩⟩
        · next id ty h1 h2 => exact ⟨some id, hes.symm, .inr ⟨id, ty, h1, rfl, h2⟩⟩
      cases hrest : rest.filterMapM c.eventOfStmt with
      | none => simp [hrest] at he
      | some evs' =>
      simp only [hrest, Option.bind_some, Option.pure_def, Option.some.injEq] at he
      subst he
      cases hE : (evRun opc args).exec ee w with
      | none =>
        rw [hE] at hrun
        refine ⟨none, ?_, env, D, fun _ _ => rfl, fun _ h => h, fun id h' => ?_, ⟨ρ₁, hw₁⟩,
          fun ρ hρ => ⟨hc ρ hρ, ?_⟩⟩
        · rw [runBody_cons hnc, Fe.M.exec_bind, hrunI, hrun]
        · exact definedAfter_mono hd id (List.mem_append_left _ h')
        · exact .stuck (hevargs ρ hρ) hE
      | some x =>
      cases x with
      | error e =>
        rw [hE] at hrun
        refine ⟨some (.error e), ?_, env, D, fun _ _ => rfl, fun _ h => h, fun id h' => ?_, ⟨ρ₁, hw₁⟩,
          fun ρ hρ => ⟨hc ρ hρ, ?_⟩⟩
        · rw [runBody_cons hnc, Fe.M.exec_bind, hrunI, hrun]
        · exact definedAfter_mono hd id (List.mem_append_left _ h')
        · exact .fail (hevargs ρ hρ) hE
      | ok p =>
        obtain ⟨r, w₁⟩ := p
        rw [hE] at hrun
        have hrs := evRun_result hE
        have hnp : evmPureOpcode op = none := evmEvent_not_pure hopc
        rcases hres with ⟨hds, rfl, hrd⟩ | ⟨id, ty, hds, rfl, hrd⟩
        · obtain rfl : r = none := by cases r <;> simp_all
          have hD : D ++ s.dsts.map (·.1) = D ++ [] := by simp [hds]
          rw [hD] at hd hpre'
          have hsub : ∀ x ∈ D, x ∈ D ++ [] := fun x hx => List.mem_append_left _ hx
          obtain ⟨x, hx, hends⟩ := body_run hsym rest (pre ++ [s]) (D ++ []) D' env w₁ evs' post
            hdefs' hpre' hd hrest hbits' ⟨ρ₁, by simpa using hw₁⟩ fun ρ hρ =>
              (hc ρ (by simpa using hρ)).mono hsub fun id' h' hn => by simp_all
          refine ⟨x, ?_, ?_⟩
          · rw [runBody_cons hnc, Fe.M.exec_bind, hrunI, hrun]
            simp only [hds, Option.toList_none, List.map_nil, bind_nil, Fe.M.exec_bind,
              Fe.M.exec_pure]
            exact hx
          · rcases x with _ | _ | ⟨env', w'⟩
            rotate_left 2
            · obtain ⟨h1, h2, h3⟩ := hends
              refine ⟨fun id' h' => h1 id' (hsub id' h'), h2, fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩
              have hρD : WordsOf env ρ D := fun id' h' =>
                (h1 id' (hsub id' h')).symm.trans (hρ id' (definedAfter_mono hd id' (hsub id' h')))
              exact .ok (hevargs ρ hρD) hE (h3 ρ hρ).2
            all_goals
              obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends
              refine ⟨envf, Df, fun id' h' => h1 id' (hsub id' h'),
                fun id' h' => h2 id' (hsub id' h'), h2',
                h3, fun ρ hρ => ⟨(h4 ρ hρ).1, .ok (hevargs ρ fun id' h' =>
                  (h1 id' (hsub id' h')).symm.trans (hρ id' (h2 id' (hsub id' h')))) hE
                  (h4 ρ hρ).2⟩⟩
        · obtain ⟨v, rfl⟩ : ∃ v, r = some v := by cases r <;> simp_all
          have hty : ty.bits = 256 := hbits s (by simp) (id, ty) (by simp [hds])
          have hid : id ∉ D := hfresh' (id, ty) (by simp [hds])
          set env₁ := env.insert id (Val.int 256 v.toNat)
          have hagree : ∀ id' ∈ D, env₁[id']? = env[id']? := fun id' h' => by
            have hne : ¬compare id id' = .eq := by
              rw [compare_eq_iff_eq]; rintro rfl; exact hid h'
            simp only [env₁, Std.TreeMap.getElem?_insert, hne, if_false]
          have hD : D ++ s.dsts.map (·.1) = D ++ [id] := by simp [hds]
          rw [hD] at hd hpre'
          have hsub : ∀ x ∈ D, x ∈ D ++ [id] := fun x hx => List.mem_append_left _ hx
          have hw₁' : WordsOf env₁ (Function.update ρ₁ id v) (D ++ [id]) := by
            intro id' h'
            by_cases he' : id' = id
            · subst he'; simp [env₁]
            · rw [List.mem_append, List.mem_singleton] at h'
              rcases h' with h' | h'
              · rw [hagree id' h', Function.update_of_ne he']; exact hw₁ id' h'
              · exact absurd h' he'
          have hc' : ∀ ρ, WordsOf env₁ ρ (D ++ [id]) → Cons ee ρ c (D ++ [id]) := by
            intro ρ hρ
            refine (hc ρ (WordsOf.agree hagree fun id' h' => hρ id' (hsub id' h'))).mono hsub
              fun id' h' hn inst hl => ?_
            have : id' = id := by simpa [hn] using h'
            subst this
            rw [hdefs, List.append_assoc, List.cons_append,
          lookup_def hds hnc (fun t ht d hdt h => hid (h ▸ hpre t ht d hdt))] at hl
            cases hl
            refine ⟨reads_mono hsub hr, fun d e he' => ?_⟩
            rw [hinst] at he'
            simp [pureWith, hnp] at he'
          obtain ⟨x, hx, hends⟩ := body_run hsym rest (pre ++ [s]) (D ++ [id]) D' env₁ w₁ evs' post
            hdefs' hpre' hd hrest hbits' ⟨_, hw₁'⟩ hc'
          -- The word the read gives is the valuation's.
          have hval : ∀ (env' : Env) ρ, env'[id]? = env₁[id]? → WordsOf env' ρ (D ++ [id]) →
              ρ id = v := fun env' ρ he' hρ =>
            (word_inj (Option.some.inj ((show env₁[id]? = some (Val.int 256 v.toNat) by
              simp [env₁]).symm.trans (he'.symm.trans (hρ id (by simp)))))).symm
          refine ⟨x, ?_, ?_⟩
          · rw [runBody_cons hnc, Fe.M.exec_bind, hrunI, hrun]
            simp only [hds, Option.toList_some, List.map_cons, List.map_nil, bind_one,
              word, as_word _ hty, Reasoning.Theory.u256_ofNat_toNat, Fe.M.exec_bind,
              Fe.M.exec_pure]
            exact hx
          · rcases x with _ | _ | ⟨env', w'⟩
            rotate_left 2
            · obtain ⟨h1, h2, h3⟩ := hends
              refine ⟨fun id' h' => (h1 id' (hsub id' h')).trans (hagree id' h'), h2,
                fun ρ hρ => ⟨(h3 ρ hρ).1, ?_⟩⟩
              have hρ₁ : WordsOf env' ρ (D ++ [id]) := fun id' h' =>
                hρ id' (definedAfter_mono hd id' h')
              have hρD : WordsOf env ρ D := fun id' h' =>
                ((h1 id' (hsub id' h')).trans (hagree id' h')).symm.trans (hρ₁ id' (hsub id' h'))
              refine .ok (hevargs ρ hρD) ?_ (h3 ρ hρ).2
              rw [hE]
              simp only [Option.map_some, hval env' ρ (h1 id (by simp)) hρ₁]
            all_goals
              obtain ⟨envf, Df, h1, h2, h2', h3, h4⟩ := hends
              refine ⟨envf, Df, fun id' h' => (h1 id' (hsub id' h')).trans (hagree id' h'),
                fun id' h' => h2 id' (hsub id' h'), h2', h3, fun ρ hρ => ⟨(h4 ρ hρ).1, ?_⟩⟩
              have hρ₁ : WordsOf envf ρ (D ++ [id]) := fun id' h' => hρ id' (h2 id' h')
              have hρD : WordsOf env ρ D := fun id' h' =>
                ((h1 id' (hsub id' h')).trans (hagree id' h')).symm.trans (hρ₁ id' (hsub id' h'))
              refine .ok (hevargs ρ hρD) ?_ (h4 ρ hρ).2
              rw [hE]
              simp only [Option.map_some, hval envf ρ (h1 id (by simp)) hρ₁]
    · cases hes

end Fe.Sonatina.Check
