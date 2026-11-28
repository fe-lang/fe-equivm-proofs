import Fe.Sonatina.Stage3.Place.InstAlloc

/-!
# EVM operations that touch no memory

`evm_*` of `EvmOp.memFree` (`lower_structural`): the same operation on the operands' words.
The model library's operation ignores memory (`memFree_ignoresMemory`), so H, which runs it on
its own world (`evmH`, `liftFe`), gets the machine's result and world but for memory
(`IgnoresMemory.onH`), and the invariant holds of the changed world (`inv_world`).  Its results
are words (`returns_words`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- Every result of an EVM operation of the machine IR is a word. -/
theorem returns_words (op : EvmOp) (xs : List Ethereum.UInt256) :
    Returns (fun vals : List Val => ∀ v ∈ vals, ∃ u : Ethereum.UInt256, v = word u) (op.run xs) := by
  unfold EvmOp.run
  dsimp only
  split <;> first
    | exact Returns.stuck _
    | exact Returns.pure (by simp)
    | exact Returns.bind_any fun _ => Returns.pure (by simp)

theorem mapM_evalWord {env : Env} :
    ∀ {os : List Operand} {ms : List Nat}, List.Forall₂ (fun o m => mval env o = some m) os ms →
      os.mapM (evalWord env) = pure (ms.map Ethereum.UInt256.ofNat)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.mapM_cons, mval_evalWord h, mapM_evalWord hs]; rfl

/-- The checking walk's bindings of several results: each result's machine value is its
    statement's. -/
theorem foldlM_bindV {vm vm' : VM} :
    ∀ {l : List ((Nat × Ty) × Nat)},
      l.foldlM (fun vm x => if vm.find? x.1.1 = some (.var x.2) then some vm else none) vm =
        some vm' → vm' = vm ∧ ∀ p ∈ l, vm.find? p.1.1 = some (.var p.2)
  | [], h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; exact ⟨h.symm, by simp⟩
  | p :: l, h => by
    rw [List.foldlM_cons] at h
    split at h
    · next he =>
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨rfl, hl⟩ := foldlM_bindV h
      refine ⟨rfl, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact he
      · exact hl q hq
    · simp at h

theorem args_rel {vm : VM} {envH : HEnv} {envM : Env} {st : H.State} :
    ∀ {args args' : List Operand}, args.mapM (mop vm) = some args' →
    (∀ a ∈ args, ∀ a', mop vm a = some a' → ∃ v m, evalOp envH a = some v ∧
      mval envM a' = some m ∧ st.word v = m) →
    ∃ vs mws, args.mapM (evalOp envH) = some vs ∧
      List.Forall₂ (fun a' m => mval envM a' = some m) args' mws ∧
      vs.map st.uword = mws.map Ethereum.UInt256.ofNat ∧ vs.length = args.length
  | [], args', h, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨[], [], rfl, .nil, rfl, rfl⟩
  | a :: as, args', h, hok => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a', ha', as', has', rfl⟩ := h
    obtain ⟨v, m, hv, hm, hw⟩ := hok a (List.mem_cons_self ..) a' ha'
    obtain ⟨vs, mws, hvs, hf, hmap, hl⟩ := args_rel has' (fun b hb => hok b (List.mem_cons_of_mem _ hb))
    refine ⟨v :: vs, m :: mws, by simp [List.mapM_cons, hv, hvs], .cons hm hf, ?_, by simp [hl]⟩
    simp [State.uword, hw, hmap]

theorem len1 {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem addrPos_memFree {op : EvmOp} (h : op.memFree = true) : op.addrPos = [] := by
  cases op <;> simp_all [EvmOp.memFree, EvmOp.addrPos]

theorem arity_memFree {op : EvmOp} {a b : Nat} (h : op.memFree = true)
    (ha : op.arity = some (a, b)) : b ≤ 1 := by
  cases op <;> simp_all [EvmOp.memFree, EvmOp.arity] <;> omega

/-- A statement that gives one value and changes H's world only, related by `Inv` to the
    machine's: the step goes on. -/
theorem stepOk_st1 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst hst' : H.State} {w w' : World} {envH : HEnv} {envM envM' : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)])
    {v : H.Val} (hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst')
    (hI' : Inv S hst' w' g) (hbl : hst'.blocks = hst.blocks) (hfit : v.fits tx = true)
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {m : Nat}
    (hm : (F.vm.find? x).bind (mval envM') = some m) (hv : VRel g S.z (F.D x) v m)
    (hok : ValOk hst' v) (horig : OrigOk g hst' F.R F.fpf (origOf F.O (.var x)) v) :
    StepOk P I S F g hst envH s L' (.ok (envM', w')) := by
  have hb : bindVals envH s.dsts [v] = some (envH.insert x v) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  have hbs : ∀ b, hst'.bsize b = hst.bsize b := fun b => by simp [State.bsize, hbl]
  have had : ∀ b, hst'.addrOf b = hst.addrOf b := fun b => by simp [State.addrOf, hbl]
  refine Or.inr ⟨envM', w', rfl, envH.insert x v, hst', g, hI', ?_,
    ⟨by rw [hbl], fun _ _ => rfl, fun b _ => hbs b, fun b _ => had b, fun _ h => h,
      fun _ h _ => h⟩, fun rest o hr => ExecBody.step hstep hb hr⟩
  refine envRel_step hE (fun y hy hn => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn)) hb hkeep
    (fun y hy hn => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn))
    (fun v h => h.state (by rw [hbl])) (fun _ _ h => h.state hI.live_lt fun b _ => hbs b) ?_
  intro y hy _
  simp only [hd, List.map_cons, List.map_nil, List.mem_singleton] at hy
  subst hy
  exact ⟨v, m, by simp, ⟨tx, hdt, hfit⟩, hm, hv, hok, horig⟩

/-- An EVM operation that touches no memory: H runs the model library's operation on its world
    as the machine does on its own; both end alike, or give the same words, the worlds equal but
    for memory. -/
theorem inst_evmFree {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : EvmOp} {args : List Operand}
    (hfree : op.memFree = true)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.evm op args))
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨⟨nA, nR⟩, har, hc, args', hargs', ⟨rs, rest⟩, htk, vm2, hfold, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨ds', hms, hlen, hty, rfl⟩ := takeN_some htk
  obtain ⟨-, hvmx⟩ := foldlM_bindV hfold
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨_, hnA⟩, hnR⟩, hdw⟩, harg⟩ := hc
  have hargs : s.inst.args = args := by simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : nonObserving Dr k s = [] := by simp [nonObserving, hi, addrPos_memFree hfree]
  obtain ⟨vs, mws, hvs, hmws, hmap, hvl⟩ := args_rel (st := hst) (envH := envH) (envM := envM)
    hargs' (fun a ha a' ha' => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
      obtain ⟨t, ht, hvt⟩ := tyOf_any (harg a ha)
      obtain ⟨v, m, hv, _, hm, hw, _⟩ := opnd_word hI hE hA (i := j) (by rw [hargs]; exact hj)
        (by rw [hno]; simp) ht ha' hvt
      exact ⟨v, m, hv, hm, hw⟩)
  have hR1 := arity_memFree hfree har
  refine ⟨[_], hms, rfl, fun O res hres => ?_⟩
  rw [runBodyO_plain O cM envM _ (by simp)] at hres
  simp only [runPlain, runInst, Fe.M.exec_bind, mapM_evalWord hmws, Fe.M.exec_pure] at hres
  rw [← hmap] at hres
  -- H runs the same operation on its world.
  have hon := IgnoresMemory.onH (memFree_ignoresMemory hfree (vs.map hst.uword)) hI I
  have hstepE : ∀ e, ((op.run (vs.map hst.uword)).exec I w = some (.error e)) →
      stepInst P.ctx I envH hst s.inst = .exit e := fun e he => by
    simp only [stepInst, hi, hvs, evmH, har, Option.map_some, hvl, hnA, bne_self_eq_false,
      Bool.false_eq_true, if_false, hfree, if_true, liftFe, hon, he, withMemory]
  cases hrun : (op.run (vs.map hst.uword)).exec I w with
  | none => rw [hrun] at hres; cases hres
  | some r =>
    rw [hrun] at hres
    cases r with
    | error e =>
      cases hres
      exact Or.inl ⟨_, fun _ => ExecBody.exit (hstepE e hrun),
        Or.inr (Or.inr ⟨e, rfl, Or.inr (Or.inr ⟨.error e, rfl, EndsAs.exit e⟩)⟩)⟩
    | ok p =>
      obtain ⟨vals, w'⟩ := p
      have hwords := returns_words op _ I w vals w' hrun
      have hmem := IgnoresMemory.keeps (memFree_ignoresMemory hfree (vs.map hst.uword)) hrun
      have hI' := inv_world hI hmem
      by_cases hlv' : ds'.length = vals.length
      swap
      · simp [Fe.Sonatina.bind, hlv', stuck] at hres
      simp only [Fe.Sonatina.bind, hlv', beq_self_eq_true, if_true, Fe.M.exec_bind,
        Fe.M.exec_pure, runPlain, Option.some.injEq] at hres
      subst hres
      have hvsH : vals.mapM ofSonatina = some (vals.map fun v => match v with
          | .int b n => H.Val.int b n
          | .agg _ => H.Val.int 0 0) := by
        clear hrun hlv' hmws
        induction vals with
        | nil => rfl
        | cons v vals ih =>
          obtain ⟨u, rfl⟩ := hwords v (List.mem_cons_self ..)
          rw [List.mapM_cons, ih (fun v hv => hwords v (List.mem_cons_of_mem _ hv))]
          rfl
      have hstep : stepInst P.ctx I envH hst s.inst = .ok (vals.map fun v => match v with
          | .int b n => H.Val.int b n
          | .agg _ => H.Val.int 0 0) { hst with world := { w' with memory := hst.world.memory } } := by
        simp only [stepInst, hi, hvs, evmH, har, Option.map_some, hvl, hnA, bne_self_eq_false,
          Bool.false_eq_true, if_false, hfree, if_true, liftFe, hon, hrun, withMemory, hvsH]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hnR ▸ hR1) with h0 | h1
      · have hd : s.dsts = [] := List.eq_nil_of_length_eq_zero h0
        have hds' : ds' = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hvals : vals = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hds' hvals
        exact stepOk_st0 hI hE hA hd (by simpa using hstep) hI' rfl (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ _ => rfl)
      · obtain ⟨⟨x, tx⟩, hd⟩ := len1 h1
        obtain ⟨⟨r, tr⟩, rfl⟩ := len1 (show ds'.length = 1 by omega)
        obtain ⟨v, rfl⟩ := len1 (show vals.length = 1 by omega)
        obtain ⟨u, rfl⟩ := hwords _ (List.mem_singleton_self _)
        have htr : tr = .int 256 := hty (r, tr) (by simp)
        subst htr
        have hu : u.toNat < W := toNat_lt' u
        have hx : F.vm.find? x = some (.var r) := hvmx ((x, tx), r) (by simp [hd])
        have hwx : isWord tx = true := hdw (x, tx) (by simp [hd])
        have hM : mval (envM.insert r ((word u).as (.int 256))) (.var r) = some u.toNat := by
          simp only [mval, Std.TreeMap.getElem?_insert_self, word, Val.as, Ty.bits]
          rw [Nat.mod_eq_of_lt hu]
        exact stepOk_st1 (m := u.toNat) (v := .int 256 u.toNat) hI hE hA hd
          (by simpa [word] using hstep) hI' rfl (fits_word hwx hu)
          (fun r' hr' => insert_other fun e => hr' (by simp at e ⊢; simp [e])) (by rw [hx]; exact hM) rfl
          trivial trivial

end Fe.Sonatina.Stage3.Place
