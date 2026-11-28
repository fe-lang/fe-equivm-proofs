import Fe.Sonatina.Stage3.Place.Sim
import Fe.Sonatina.Stage3.Place.InstEvm

/-!
# The call pattern (`lower_structural` of `call`)

A source `call g args` is the machine `call g args'` on the mapped arguments, its results the
machine values of the source results.  With calls by an oracle that satisfies the call contract
(`CallP`), H's `call` rule runs the callee's `ExecFunc` to an outcome the contract relates to the
oracle's result (`inst_call`).  What the caller gives the callee is rule S7's A2 at the call
(every argument and every value live after the call points into no range of the callee's
footprint, unless into the heap), the origin flags (an argument with origins goes to a parameter
flagged as receiving one) and footprints (the callee's are the caller's), and S8's derived
parameters.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

theorem stmt_call {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {g : String} {args : List Operand}
    (hi : s.inst = .base (.call g args))
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ kg callee tas args' ds', callee? = some kg ∧ c.src.funcs[kg]? = some callee ∧
      callee.name = g ∧ args.mapM c.tyOf = some tas ∧
      (tas.length == callee.params.length && (tas.zip callee.params).all (fun (t, p) => sameW t p.2) &&
        s.dsts.length == callee.rets.length &&
        (s.dsts.zip callee.rets).all (fun (d, t) => sameW d.2 t)) = true ∧
      args.mapM (mop vm) = some args' ∧ ms = ⟨ds', .call g args'⟩ :: ms' ∧
      ds'.length = s.dsts.length ∧ (∀ d ∈ ds', d.2 = .int 256) ∧ ds = ds'.map (·.1) ∧
      (∀ p ∈ s.dsts.zip (ds'.map (·.1)), vm.find? p.1.1 = some (.var p.2)) ∧ vm' = vm ∧
      mb' = mb := by
  simp only [stmt, hi, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨kg, hkg, callee, hcal, hname, tas, htas, hc, args', hargs', ⟨rs, rest⟩, htk, vm2, hfold,
    rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨ds', hms, hlen, hty, rfl⟩ := takeN_some htk
  obtain ⟨rfl, hvmx⟩ := foldlM_bindV hfold
  exact ⟨kg, callee, tas, args', ds', hkg, hcal, hname, htas, hc, hargs', hms, hlen, hty, rfl,
    hvmx, rfl, rfl⟩

theorem mval_evalOperand {env : Env} {a : Operand} {m : Nat} (h : mval env a = some m) :
    evalOperand env a = pure (.int 256 m) := by
  cases a with
  | var r =>
    simp only [mval] at h
    split at h
    · next v hv => cases h; simp only [evalOperand, hv]
    · cases h
  | imm bits v =>
    simp only [mval] at h
    split at h
    · next hb => cases h; subst hb; rfl
    · cases h

theorem mapM_evalOperand {env : Env} :
    ∀ {args' : List Operand} {mws : List Nat},
      List.Forall₂ (fun a' m => mval env a' = some m) args' mws →
      args'.mapM (evalOperand env) = pure (mws.map (Val.int 256 ·))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.mapM_cons, mval_evalOperand h, pure_bind, mapM_evalOperand hs]
    rfl

/-- The arguments of a call, live, against the machine's: their H values and machine words,
    related place by place. -/
theorem call_args {z : Bool} {F : Frame} {g : Ghost} {hst : H.State} {envH : HEnv} {envM : Env}
    {L : List Nat} {c : FCtx} (hE : EnvRel z F g hst envH envM L) (hdecl : F.decls = c.decls) :
    ∀ {args : List Operand} {tas : List Ty} {args' : List Operand},
    (∀ y, Operand.var y ∈ args → y ∈ L) → args.mapM c.tyOf = some tas →
    args.mapM (mop F.vm) = some args' →
    ∃ (vs : List H.Val) (mws : List Nat), args.mapM (evalOp envH) = some vs ∧
      List.Forall₂ (fun a' m => mval envM a' = some m) args' mws ∧
      vs.length = args.length ∧ mws.length = args.length ∧ tas.length = args.length ∧
      ∀ (j : Nat) (a : Operand) (v : H.Val) (m : Nat) (t : Ty), args[j]? = some a → vs[j]? = some v → mws[j]? = some m → tas[j]? = some t →
        v.fits t = true ∧ VRel g z (F.dOp a) v m ∧ ValOk hst v ∧
          OrigOk g hst F.R F.fpf (origOf F.O a) v
  | [], tas, args', _, ht, hm => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ht hm
    subst ht hm
    exact ⟨[], [], rfl, .nil, rfl, rfl, rfl, fun j a v m t h => by simp at h⟩
  | a :: as, tas, args', hl, ht, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht hm
    obtain ⟨ta, hta, tas', htas', rfl⟩ := ht
    obtain ⟨a', ha', as', has', rfl⟩ := hm
    obtain ⟨v, m, hv, hf, hmv, hr, ho, hor⟩ := opnd_rel hE hdecl rfl
      (fun y hy => hl y (by rw [← hy]; exact List.mem_cons_self ..)) hta ha'
    obtain ⟨vs, mws, hvs, hmws, hl1, hl2, hl3, hrel⟩ := call_args hE hdecl
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) htas' has'
    refine ⟨v :: vs, m :: mws, by simp [List.mapM_cons, hv, hvs], .cons hmv hmws, by simp [hl1],
      by simp [hl2], by simp [hl3], fun j b u n t hb hu hn ht => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hu hn ht
      subst hb hu hn ht
      exact ⟨hf, hr, ho, hor⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb hu hn ht
      exact hrel j b u n t hb hu hn ht

/-- An argument's origins, for the callee's parameter: a pointer into a block of the caller's
    frame is one into a block that misses the callee's footprint (A2, footprints), and the
    parameter is flagged as receiving one. -/
theorem origOk_arg {g : Ghost} {hst : H.State} {R R' : NatMap Range} {fpf fpf' : List Range}
    {os os' : List Nat} {v : H.Val} (h : OrigOk g hst R fpf os v) (h0 : os ≠ [] → 0 ∈ os')
    (hfp : ∀ r ∈ fpf', r ∈ fpf)
    (hA2 : ∀ o ∈ os, o = 0 ∨ ∃ rr, R.find? (o - 1) = some rr ∧ ∀ r ∈ fpf', Disj rr r) :
    OrigOk g hst R' fpf' os' v := by
  cases v with
  | int => trivial
  | ptr b o =>
    rcases h with h | ⟨hl, ⟨s, hs1, hs2⟩ | ⟨hp0, hd⟩⟩
    · exact Or.inl h
    · rcases hA2 (s + 1) hs1 with h | ⟨rr, hrr, hdis⟩
      · cases h
      · simp only [Nat.add_sub_cancel] at hrr
        rw [hs2] at hrr
        cases hrr
        exact Or.inr ⟨hl, Or.inr ⟨h0 (List.ne_nil_of_mem hs1), fun r hr => (hdis r hr).symm⟩⟩
    · exact Or.inr ⟨hl, Or.inr ⟨h0 (List.ne_nil_of_mem hp0), fun r hr => hd r (hfp r hr)⟩⟩

/-- A value live across a call keeps its origins' consequence after it: its block stays live
    (A2 for a frame block, footprints for a parameter's), with its range. -/
theorem origOk_after {g g' : Ghost} {hst hst' : H.State} {R : NatMap Range} {fpf fpf' : List Range}
    {os : List Nat} {v : H.Val} (h : OrigOk g hst R fpf os v) (hv : ValOk hst v)
    (hle : GhostLe fpf' g g' hst hst') (hfp : ∀ r ∈ fpf', r ∈ fpf)
    (hA2 : ∀ o ∈ os, o = 0 ∨ ∃ rr, R.find? (o - 1) = some rr ∧ ∀ r ∈ fpf', Disj rr r) :
    OrigOk g' hst' R fpf os v := by
  cases v with
  | int => trivial
  | ptr b o =>
    have hrg := hle.rg hv.1
    rcases h with h | ⟨hl, ⟨s, hs1, hs2⟩ | ⟨hp0, hd⟩⟩
    · exact Or.inl (hle.heap b h)
    · rcases hA2 (s + 1) hs1 with h | ⟨rr, hrr, hdis⟩
      · cases h
      · simp only [Nat.add_sub_cancel] at hrr
        rw [hs2] at hrr
        cases hrr
        exact Or.inr ⟨hle.live b hl fun r hr => (hdis r hr).symm, Or.inl ⟨s, hs1, by rw [hrg]; exact hs2⟩⟩
    · exact Or.inr ⟨hle.live b hl fun r hr => hd r (hfp r hr), Or.inr ⟨hp0, by rw [hrg]; exact hd⟩⟩

theorem GhostLe.mono_fp {fp fp' : List Range} {g g' : Ghost} {hst hst' : H.State}
    (h : GhostLe fp' g g' hst hst') (hfp : ∀ r ∈ fp', r ∈ fp) : GhostLe fp g g' hst hst' :=
  ⟨h.size, h.j, h.bsize, h.addr, h.heap, fun b hb hd => h.live b hb fun r hr => hd r (hfp r hr)⟩

theorem vrel_after {g g' : Ghost} {hst hst' : H.State} {fp : List Range} {z dx : Bool} {v : H.Val}
    {m : Nat} (hle : GhostLe fp g g' hst hst') (hr : VRel g z dx v m) (hv : ValOk hst v) :
    VRel g' z dx v m := by
  cases v with
  | int => exact hr
  | ptr b o => exact ⟨by rw [hle.j b hv.1]; exact hr.1, hr.2⟩

theorem valOk_after {g g' : Ghost} {hst hst' : H.State} {fp : List Range} {v : H.Val}
    (hle : GhostLe fp g g' hst hst') (hv : ValOk hst v) : ValOk hst' v := by
  cases v with
  | int => trivial
  | ptr b o => exact ⟨lt_of_lt_of_le hv.1 hle.size, hv.2⟩

theorem foldl_insert_away {α β : Type} (key : α → Nat) (val : α → β) :
    ∀ (l : List α) (env : Std.TreeMap Nat β compare) {x : Nat}, (∀ p ∈ l, key p ≠ x) →
      (l.foldl (fun env q => env.insert (key q) (val q)) env)[x]? = env[x]?
  | [], _, _, _ => rfl
  | p :: l, env, x, h => by
    rw [List.foldl_cons, foldl_insert_away key val l _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rw [Std.TreeMap.getElem?_insert]
    have := h p (List.mem_cons_self ..)
    simp [compare_eq_iff_eq, this]

/-- A fold of inserts with distinct keys: each key has its value. -/
theorem foldl_insert_get {α β : Type} (key : α → Nat) (val : α → β) :
    ∀ (l : List α) (env : Std.TreeMap Nat β compare), (l.map key).Nodup → ∀ a ∈ l,
      (l.foldl (fun env q => env.insert (key q) (val q)) env)[key a]? = some (val a)
  | [], _, _, a, ha => by cases ha
  | q :: l, env, hnd, a, ha => by
    rw [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [foldl_insert_away key val l _ (fun p hp e => hnd.1 (by rw [← e]; exact List.mem_map_of_mem hp))]
      simp
    · exact foldl_insert_get key val l _ hnd.2 a ha

theorem mem_zip_of {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat} {a : α} {b : β}
    (h1 : l₁[i]? = some a) (h2 : l₂[i]? = some b) : (a, b) ∈ l₁.zip l₂ :=
  List.mem_of_getElem? (by rw [List.getElem?_zip_eq_some]; exact ⟨h1, h2⟩)

theorem map_fst_zip_key {α β γ : Type} (f : α → γ) (l₁ : List α) (l₂ : List β)
    (h : l₁.length = l₂.length) : (l₁.zip l₂).map (fun q => f q.1) = l₁.map f := by
  rw [show (fun q : α × β => f q.1) = f ∘ Prod.fst from rfl, ← List.map_map,
    List.map_fst_zip (by omega)]

theorem get_of_len {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat} {a : α}
    (h : l₁[i]? = some a) (hl : l₁.length = l₂.length) : ∃ b, l₂[i]? = some b := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  exact ⟨l₂[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩

theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α} {b : β}, l₁[i]? = some a →
      l₂[i]? = some b → R a b
  | [], [], .nil, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, .cons hr hs, i, a, b, h1, h2 => by
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1 h2; exact hr
    | succ i => simp only [List.getElem?_cons_succ] at h1 h2; exact forall₂_get hs h1 h2

/-- A call (`lower_structural`): the machine calls the callee on the mapped arguments, by an
    oracle that satisfies the call contract; H's `call` rule runs the callee to an outcome the
    contract relates to the oracle's, and binds its results. -/
theorem inst_call {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {Dr : Derived}
    {fns : Nat → Option Fn} {O : Oracle} (hO : CallP P I S Dr fns O)
    {F : Frame} {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    {L L' : List Nat} {c : FCtx} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {gn : String} {args : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) (hnd : (defsOf ms).Nodup)
    (hi : s.inst = .base (.call gn args))
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds))
    (hfg : ∀ kg, callee? = some kg → ∃ fg, fns kg = some fg ∧ c.src.funcs[kg]? = some fg.f ∧
      fg.k = kg ∧
      (∀ (j : Nat) (a : Operand) (p : Nat × Ty), args[j]? = some a → fg.f.params[j]? = some p →
        (Dr.op k a = true → fg.F.D p.1 = true) ∧
        (origOf F.O a ≠ [] → 0 ∈ origOf fg.F.O (.var p.1))) ∧
      (∀ r ∈ fg.F.fpf, r ∈ F.fpf) ∧
      (∀ y, ((y ∈ L' ∧ y ∉ s.defs) ∨ Operand.var y ∈ args) → ∀ o ∈ origOf F.O (.var y),
        o = 0 ∨ ∃ rr, F.R.find? (o - 1) = some rr ∧ ∀ r ∈ fg.F.fpf, Disj rr r)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOkC P I cM S O F g hst w envH envM s L' pre := by
  obtain ⟨kg, callee, tas, args', ds', rfl, hcal, hname, htas, hc, hargs', hms, hlen, hty, rfl, hvmx,
    rfl, rfl⟩ := stmt_call hi h
  obtain ⟨fg, hfns, hfgf, hfk, harg, hfp, hA2⟩ := hfg kg rfl
  rw [hfgf] at hcal
  obtain rfl : fg.f = callee := Option.some.inj hcal
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hl1, hl2⟩, hl3⟩, hl4⟩ := hc
  have hargs : s.inst.args = args := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vs, mws, hvs, hmws, hvl, hml, htl, hrel⟩ := call_args hE hA.decls
    (fun y hy => hA.uses y (by rw [hargs]; exact hy)) htas hargs'
  have hdnd : (ds'.map (·.1)).Nodup := by
    rw [hms] at hnd
    simp only [defsOf, List.flatMap_cons, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).1
  have hArg : ArgRel S fg g hst vs (mws.map (Val.int 256 ·)) := by
    refine ⟨by rw [hvl, ← htl, hl1], by rw [List.length_map, hml, ← htl, hl1],
      fun j p v a hp hv ha => ?_⟩
    rw [List.getElem?_map] at ha
    cases hmj : mws[j]? with
    | none => rw [hmj] at ha; cases ha
    | some m =>
      rw [hmj] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      subst ha
      obtain ⟨aj, haj⟩ := get_of_len hv hvl
      obtain ⟨tj, htj⟩ := get_of_len haj htl.symm
      obtain ⟨hf, hr, ho, hor⟩ := hrel j aj v m tj haj hv hmj htj
      obtain ⟨hd, h0⟩ := harg j aj p haj hp
      have hsw : sameW tj p.2 = true := hl2 (tj, p) (mem_zip_of htj hp)
      refine ⟨m, rfl, fits_sameW (sameW_symm hsw) hf, ?_, ho, ?_⟩
      · cases v with
        | int => exact hr
        | ptr b o => exact ⟨hr.1, fun hz => hd (by rw [← hA.dOp aj]; exact hr.2 hz)⟩
      · refine origOk_arg hor h0 hfp fun o ho' => ?_
        cases aj with
        | var y => exact hA2 y (Or.inr (List.mem_of_getElem? haj)) o ho'
        | imm => simp [origOf] at ho'
  refine ⟨[_], hms, rfl, fun res hres => ?_⟩
  simp only [runBodyO, runStmtO, mapM_evalOperand hmws, pure_bind, bind_pure] at hres
  rcases exec_bind_some hres with ⟨e, h1, rfl⟩ | ⟨vals, w', h1, h2⟩
  · obtain ⟨fo, hex, hfr⟩ := hO kg fg hfns _ vs g hst w hI hArg _ (by rw [hname]; exact h1)
    rw [hname] at hex
    rcases hfr with ⟨o, rfl, hx⟩ | ⟨_, _, _, _, _, heq, _⟩
    · exact Or.inl ⟨o, fun rest => ExecBody.callHalt hi hvs hex, Excuses.of_error hx⟩
    · cases heq
  · obtain ⟨fo, hex, hfr⟩ := hO kg fg hfns _ vs g hst w hI hArg _ (by rw [hname]; exact h1)
    rw [hname] at hex
    rcases hfr with ⟨o, rfl, hx⟩ | ⟨vals₁, w₁, valsH, hst', g', heq, rfl, hI', hle, hrr⟩
    · exact Or.inl ⟨o, fun rest => ExecBody.callHalt hi hvs hex, Excuses.of_ok hx _⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨h5, h6⟩ := heq
      subst vals₁ w₁
      obtain ⟨hrv, hrf⟩ := hrr
      have hlv : valsH.length = vals.length := hrv.length_eq
      have hlr : valsH.length = fg.f.rets.length := hrf.length_eq
      -- The machine binds the results.
      have hbl : ds'.length = vals.length := by rw [hlen, hl3, ← hlr, hlv]
      simp only [Fe.Sonatina.bind, hbl, beq_self_eq_true, if_true, Fe.M.exec_pure,
        Option.some.injEq] at h2
      subst h2
      -- H binds them.
      have hfit : ∀ (i : Nat) (d : Nat × Ty) (v : H.Val), s.dsts[i]? = some d → valsH[i]? = some v →
          v.fits d.2 = true := by
        intro i d v hd hv
        obtain ⟨t, ht⟩ := get_of_len (l₂ := fg.f.rets) hd hl3
        have hsw := hl4 (d, t) (mem_zip_of hd ht)
        exact fits_sameW hsw (forall₂_get hrf hv ht)
      have hbv : bindVals envH s.dsts valsH = some ((s.dsts.zip valsH).foldl
          (fun env (q : (Nat × Ty) × H.Val) => env.insert q.1.1 q.2) envH) := by
        unfold bindVals
        rw [if_pos]
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨by rw [hl3, hlr], fun q hq => ?_⟩
        obtain ⟨i, hqi⟩ := List.mem_iff_getElem?.mp hq
        rw [List.getElem?_zip_eq_some] at hqi
        exact hfit i q.1 q.2 hqi.1 hqi.2
      have hdl : s.dsts.length = valsH.length := by rw [hl3, hlr]
      refine Or.inr ⟨_, w', rfl, _, hst', g', hI', ?_, hle.mono_fp hfp,
        fun rest o hr => ExecBody.call hi hvs hex hbv hr⟩
      have hdefs : s.defs = s.dsts.map (·.1) := rfl
      refine envRel_step' hE (fun y hy hn => hA.keep y hy (by rw [hdefs]; exact hn)) hbv ?_
        (fun y hy hn => hA.clob y (Or.inr hy) (by rw [hdefs]; exact hn)) ?_ ?_
      · intro r hr
        refine foldl_insert_away (fun q : (Nat × Ty) × Val => q.1.1) (fun q => q.2.as q.1.2) _ _
          fun q hq e => hr ?_
        rw [← e]
        exact List.mem_map_of_mem (List.of_mem_zip hq).1
      · intro y hy hn v m hv hvr hvo hor
        exact ⟨vrel_after hle hvr hvo, valOk_after hle hvo,
          origOk_after hor hvo hle hfp (hA2 y (Or.inl ⟨hy, by rw [hdefs]; exact hn⟩))⟩
      · intro x hx _
        obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, hdi⟩ := List.mem_iff_getElem?.mp hdm
        obtain ⟨v, hvi⟩ := get_of_len hdi hdl
        obtain ⟨mv, hmvi⟩ := get_of_len hvi hlv
        obtain ⟨q, hqi⟩ := get_of_len hdi hlen.symm
        obtain ⟨m, rfl, hvr, hvo, hheap⟩ := forall₂_get hrv hvi hmvi
        have hdt : F.decls.find? d.1 = some d.2 := hA.dsts d hdm
        have hfv := hfit i d v hdi hvi
        have hval : Ty.value d.2 = true := by
          obtain ⟨t, ht⟩ := get_of_len (l₂ := fg.f.rets) hdi hl3
          have := hl4 (d, t) (mem_zip_of hdi ht)
          simp only [sameW, Bool.and_eq_true] at this
          exact this.1.1
        have hmW : m < W := vrel_lt hvr hfv hval
        have hx' : F.vm.find? d.1 = some (.var q.1) :=
          hvmx (d, q.1) (mem_zip_of hdi (by rw [List.getElem?_map, hqi]; rfl))
        refine ⟨v, m, ?_, ⟨d.2, hdt, hfv⟩, ?_, ?_, hvo, ?_⟩
        · have := foldl_insert_get (fun q : (Nat × Ty) × H.Val => q.1.1) (fun q => q.2)
            (s.dsts.zip valsH) envH (by rw [map_fst_zip_key (·.1) _ _ hdl]; exact hA.nodup) (d, v)
            (mem_zip_of hdi hvi)
          exact this
        · rw [hx']
          simp only [Option.bind_some, mval]
          have := foldl_insert_get (fun q : (Nat × Ty) × Val => q.1.1) (fun q => q.2.as q.1.2)
            (ds'.zip vals) envM (by rw [map_fst_zip_key (·.1) _ _ hbl]; exact hdnd) (q, .int 256 m)
            (mem_zip_of hqi hmvi)
          simp only at this
          rw [this, hty q (List.mem_of_getElem? hqi)]
          simp only [W] at hmW
          simpa [Val.as, Ty.bits] using hmW
        · cases v with
          | int => exact hvr
          | ptr b o =>
            refine ⟨hvr.1, fun hz => ?_⟩
            have hs : stmtDerived Dr k s (some kg) = true := by
              simp only [stmtDerived, hi, Option.any_some]
              have := hvr.2 hz
              simpa [Fn.dret, hfk] using this
            rw [hA.D]
            exact hA.der hz hs d.1 (by rw [hdefs]; exact hx)
        · cases v with
          | int => trivial
          | ptr b o => exact Or.inl (hheap b o rfl)

end Fe.Sonatina.Stage3.Place
