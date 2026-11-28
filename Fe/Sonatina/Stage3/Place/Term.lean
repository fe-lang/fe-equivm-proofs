import Fe.Sonatina.Stage3.Place.Obl

/-!
# The terminator obligation of a placed function

`FnUnp.termObl`: every source terminator, against the machine terminator `termOk` matched with
it (and, for `evm_return_code`, the code copy before it; for `evm_revert_word`, the two stores
before it, `run_revertWord`), ends alike: H halts in an outcome that
excuses the machine's result, or both go to related blocks, or both return related values.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

theorem foldr_chain_last {α : Type} (h : α → List Nat → List Nat) (x : List Nat) :
    ∀ (l : List α), (l.foldr (fun s acc => h s (acc.headD []) :: acc) [x])[l.length]? = some x
  | [] => rfl
  | a :: l => by
    simp only [List.foldr_cons, List.length_cons, List.getElem?_cons_succ]
    exact foldr_chain_last h x l

theorem forall₂_of_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ x ∈ l₁.zip l₂, R x.1 x.2) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h => .cons (h (a, b) (List.mem_cons_self ..))
      (forall₂_of_zip (by simpa using hl) fun x hx => h x (List.mem_cons_of_mem _ hx))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The values of a `return`, operand by operand. -/
theorem ret_lists {envH : HEnv} {envM : Env} {vm : VM} {tyOf : Operand → Option Ty}
    (P : Operand → H.Val → Nat → Prop) :
    ∀ (vs : List Operand) (ts rets : List Ty) (vs' : List Operand),
      vs.mapM tyOf = some ts → List.Forall₂ (fun t r => sameW t r = true) ts rets →
      vs.mapM (mop vm) = some vs' →
      (∀ a ∈ vs, ∀ t a', tyOf a = some t → mop vm a = some a' → ∃ v m, evalOp envH a = some v ∧
        mval envM a' = some m ∧ v.fits t = true ∧ P a v m) →
      ∃ valsH mws, vs.mapM (evalOp envH) = some valsH ∧
        List.Forall₂ (fun a' m => mval envM a' = some m) vs' mws ∧
        List.Forall₂ (fun v m => ∃ a ∈ vs, P a v m) valsH mws ∧
        List.Forall₂ (fun (v : H.Val) t => v.fits t = true) valsH rets
  | [], ts, rets, vs', h1, h2, h3, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h1 h3
    subst h1 h3
    cases h2
    exact ⟨[], [], rfl, .nil, .nil, .nil⟩
  | a :: vs, ts, rets, vs', h1, h2, h3, h4 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h1 h3
    obtain ⟨t, ht, ts', hts', rfl⟩ := h1
    obtain ⟨a', ha', vs'', hvs'', rfl⟩ := h3
    cases h2 with
    | cons hr h2 =>
      obtain ⟨v, m, hv, hm, hf, hP⟩ := h4 a (List.mem_cons_self ..) t a' ht ha'
      obtain ⟨valsH, mws, e1, e2, e3, e4⟩ := ret_lists P vs ts' _ vs'' hts' h2 hvs''
        fun x hx => h4 x (List.mem_cons_of_mem _ hx)
      refine ⟨v :: valsH, m :: mws, by simp [List.mapM_cons, hv, e1], .cons hm e2,
        .cons ⟨a, List.mem_cons_self .., hP⟩ (e3.imp fun _ _ ⟨x, hx, hp⟩ =>
          ⟨x, List.mem_cons_of_mem _ hx, hp⟩), .cons (fits_sameW (sameW_symm hr) hf) e4⟩


theorem find_rel {bm : NatMap Nat} (k : Nat) :
    ∀ {l₁ l₂ : List (Nat × Nat)},
      List.Forall₂ (fun p q => p.1 = q.1 ∧ bm.find? p.2 = some q.2) l₁ l₂ →
      (∃ p q, l₁.find? (·.1 == k) = some p ∧ l₂.find? (·.1 == k) = some q ∧ bm.find? p.2 = some q.2) ∨
        (l₁.find? (·.1 == k) = none ∧ l₂.find? (·.1 == k) = none)
  | [], [], .nil => Or.inr ⟨rfl, rfl⟩
  | p :: l₁, q :: l₂, .cons ⟨h1, h2⟩ hs => by
    by_cases hk : p.1 = k
    · exact Or.inl ⟨p, q, by simp [List.find?_cons, hk], by simp [List.find?_cons, ← h1, hk], h2⟩
    · have e1 : (p.1 == k) = false := by simpa using hk
      have e2 : (q.1 == k) = false := by rw [← h1]; exact e1
      simp only [List.find?_cons, e1, e2]
      exact find_rel k hs

/-- The cases of a `br_table`, against the machine's. -/
theorem table_lists {envH : HEnv} {envM : Env} {vm : VM} {bm : NatMap Nat} {word : H.Val → Nat} :
    ∀ (cases cases' : List (Operand × Nat)),
      (∀ x ∈ cases, ∀ o', mop vm x.1 = some o' → ∃ v m, evalOp envH x.1 = some v ∧
        mval envM o' = some m ∧ word v = m) →
      cases.mapM (fun x => (mop vm x.1).bind fun a => (bm.find? x.2).bind fun b => some (a, b)) =
        some cases' →
      ∃ valsH valsM, cases.mapM (fun x => (evalOp envH x.1).map (word ·, x.2)) = some valsH ∧
        cases'.mapM (fun (x : Operand × Nat) => do return ((← evalInt envM x.1).2, x.2)) =
          pure valsM ∧
        List.Forall₂ (fun p q => p.1 = q.1 ∧ bm.find? p.2 = some q.2) valsH valsM ∧
        ∀ p ∈ valsH, p.2 ∈ cases.map (·.2)
  | [], cases', _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], [], rfl, rfl, .nil, fun p hp => by cases hp⟩
  | x :: cases, cases', hop, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨o', b'⟩, hx, rest, hrest, rfl⟩ := h
    obtain ⟨o'', ho'', b'', hb'', hxe⟩ := hx
    cases hxe
    obtain ⟨v, m, hv, hm, hw⟩ := hop x (List.mem_cons_self ..) o' ho''
    obtain ⟨valsH, valsM, e1, e2, e3, e4⟩ := table_lists cases rest
      (fun y hy => hop y (List.mem_cons_of_mem _ hy)) hrest
    refine ⟨(word v, x.2) :: valsH, (m, b') :: valsM, by simp [List.mapM_cons, hv, e1], ?_,
      .cons ⟨by simp [hw], hb''⟩ e3, fun p hp => ?_⟩
    · simp only [List.mapM_cons, mval_evalInt hm, e2, pure_bind]
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (e4 p hp)

/-- A copy of `len` bytes to address 0 read back from 0 is the source's bytes. -/
theorem read_write_zero (src m : ByteArray) (so len : Nat) :
    (src.write so m 0 len).readWithPadding 0 len = src.readWithPadding so len := by
  rw [readWithPadding_of_mem (l := (List.range len).map fun i => src.data.getD (so + i) 0)
      (by simp) fun i hi => by simp [mem_write, hi],
    readWithPadding_of_mem (l := (List.range len).map fun i => src.data.getD (so + i) 0)
      (by simp) fun i hi => by simp [mem]]

/-! ## `evm_revert_word`: the bytes of its expansion -/

theorem toByteArray_list_length (w : Ethereum.UInt256) :
    (Ethereum.UInt256.toByteArray w).toList.length = 32 := by
  rw [Reasoning.Theory.byteArray_toList_eq]; exact Reasoning.Theory.toByteArray_size w

theorem toList_extract_toByteArray (w : Ethereum.UInt256) (a b : Nat) :
    ((Ethereum.UInt256.toByteArray w).extract a b).toList =
      ((Ethereum.UInt256.toByteArray w).toList.take b).drop a := by
  rw [Reasoning.Theory.byteArray_toList_eq, Reasoning.Theory.byteArray_toList_eq,
    ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, List.drop_take]

/-- The last four bytes of a word are its value modulo `2 ^ 32`. -/
theorem fromBE_toByteArray_extract28 (w : Ethereum.UInt256) :
    Ethereum.fromByteArrayBigEndian ((Ethereum.UInt256.toByteArray w).extract 28 32) =
      w.toNat % 2 ^ 32 := by
  have hl := toByteArray_list_length w
  have hfull := Reasoning.Theory.fromByteArrayBigEndian_toByteArray w
  unfold Ethereum.fromByteArrayBigEndian at hfull ⊢
  rw [toList_extract_toByteArray, List.take_of_length_le (by omega)]
  have hb := Reasoning.Theory.fromBytesBigEndian_bound ((Ethereum.UInt256.toByteArray w).toList.drop 28)
  rw [List.length_drop, hl] at hb
  rw [← List.take_append_drop 28 (Ethereum.UInt256.toByteArray w).toList,
    Reasoning.Theory.fromBytesBigEndian_append, List.length_drop, hl] at hfull
  rw [← hfull, Nat.mul_add_mod_of_lt hb]

theorem toNat_ofNat_mod (m : Nat) : (Ethereum.UInt256.ofNat m).toNat = m % W := by
  simp only [Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat]; rfl

/-- The first four bytes of the word `n · 2 ^ 224` (`shl 224 n`) are `be4(n)`, the last four of
    `n`'s word. -/
theorem sel_bytes {c : Ethereum.UInt256} {n : Nat} (hc : c.toNat = n % 2 ^ 32 * 2 ^ 224) :
    c.toByteArray.extract 0 4 = (Ethereum.UInt256.ofNat n).toByteArray.extract 28 32 := by
  have h1 := Reasoning.Theory.fromByteArrayBigEndian_toByteArray_extract0_4 c
  have h2 := fromBE_toByteArray_extract28 (Ethereum.UInt256.ofNat n)
  rw [hc, Nat.mul_div_cancel _ (by norm_num)] at h1
  rw [toNat_ofNat_mod, Nat.mod_mod_of_dvd n (by norm_num)] at h2
  have hlen : ∀ (w : Ethereum.UInt256) (a b : Nat), b ≤ 32 →
      ((Ethereum.UInt256.toByteArray w).extract a b).toList.length = b - a := by
    intro w a b hb
    rw [toList_extract_toByteArray, List.length_drop, List.length_take, toByteArray_list_length]
    omega
  have := Reasoning.Theory.fromBytesBigEndian_inj_of_length
    (xs := (c.toByteArray.extract 0 4).toList)
    (ys := ((Ethereum.UInt256.ofNat n).toByteArray.extract 28 32).toList)
    (by rw [hlen _ _ _ (by norm_num), hlen _ _ _ (by norm_num)])
    (by unfold Ethereum.fromByteArrayBigEndian at h1 h2; rw [h1, h2])
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← Reasoning.Theory.byteArray_toList_eq, ← Reasoning.Theory.byteArray_toList_eq]
  exact this

theorem shl224_toNat (n : Nat) :
    (Ethereum.UInt256.ofNat (n * 2 ^ 224)).toNat = n % 2 ^ 32 * 2 ^ 224 := by
  rw [toNat_ofNat_mod, show W = 2 ^ 32 * 2 ^ 224 by norm_num, Nat.mul_mod_mul_right]

/-- Two words stored at 0 and 4, read back at `[0, 36)`: the first one's first four bytes and the
    second one. -/
theorem read_two_words (m : ByteArray) (c x : Ethereum.UInt256) :
    (x.toByteArray.write 0 (c.toByteArray.write 0 m 0 32) 4 32).readWithPadding 0 36 =
      c.toByteArray.extract 0 4 ++ x.toByteArray := by
  have hc := Reasoning.Theory.toByteArray_size c
  have hx := Reasoning.Theory.toByteArray_size x
  have hs : (c.toByteArray.extract 0 4 ++ x.toByteArray).data.toList.length = 36 := by
    simp [hc, hx]
  refine (readWithPadding_of_mem hs fun i hi => ?_).trans rfl
  have hc' : c.toByteArray.data.size = 32 := hc
  have hx' : x.toByteArray.data.size = 32 := hx
  rw [mem_write, mem_write]
  simp only [Array.getElem_toList, ByteArray.data_append]
  by_cases h4 : i < 4
  · rw [ite_eq_right_iff.mpr (fun h => absurd h.1 (by omega)),
      ite_cond_eq_true _ _ (eq_true (by omega)), Array.getElem_append_left (by simp [hc]; omega)]
    simp [ByteArray.data_extract, Array.getElem_extract, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show i < c.toByteArray.data.size by omega)]
  · rw [ite_cond_eq_true _ _ (eq_true (by omega)), Array.getElem_append_right (by simp [hc]; omega)]
    simp [ByteArray.data_extract, Array.getD_eq_getD_getElem?, hc,
      Array.getElem?_eq_getElem (show i - 4 < x.toByteArray.data.size by omega)]

/-- What `revertWordOk` accepts: the machine operand of `word`, the revert of `[0, 36)`, the types,
    and the two stores, the first of the immediate selector word or of a `shl` just before. -/
theorem revertWordOk_some {c : FCtx} {vm : VM} {s wd : Operand} {ms : List Stmt} {mt : Term}
    (h : revertWordOk c vm s wd ms mt = true) :
    ∃ w', mop vm wd = some w' ∧ mt = .evmRevert (imm 0) (imm 36) ∧
      (c.tyOf s).any (sameW · (.int 32)) = true ∧ (c.tyOf wd).any isWord = true ∧
      ((∃ b v, s = .imm b v ∧
          ms = [⟨[], .evm .mstore [imm 0, imm (v * 2 ^ 224)]⟩, ⟨[], .evm .mstore [imm 4, w']⟩]) ∨
       (∃ x s' t, s = .var x ∧ mop vm s = some s' ∧ w' ≠ .var t ∧
          ms = [⟨[(t, .int 256)], .bin .shl (imm 224) s'⟩, ⟨[], .evm .mstore [imm 0, .var t]⟩,
            ⟨[], .evm .mstore [imm 4, w']⟩])) := by
  unfold revertWordOk at h
  cases hc : ((c.tyOf s).any (sameW · (.int 32)) && (c.tyOf wd).any isWord) with
  | false => simp [hc] at h
  | true =>
  simp only [Bool.and_eq_true] at hc
  cases hw' : mop vm wd with
  | none => simp [hc, hw'] at h
  | some w' =>
  refine ⟨w', rfl, ?_⟩
  cases s with
  | imm b v =>
    cases h1 : take0 (.evm .mstore [imm 0, imm (v * 2 ^ 224)]) ms with
    | none => simp [hc, hw', h1, -Nat.reducePow] at h
    | some rest =>
    cases h2 : take0 (.evm .mstore [imm 4, w']) rest with
    | none => simp [hc, hw', h1, h2, -Nat.reducePow] at h
    | some rest2 =>
    simp [hc, hw', h1, h2, -Nat.reducePow] at h
    obtain ⟨rfl, rfl⟩ := h
    have e1 := take0_some h1
    have e2 := take0_some h2
    subst e1 e2
    exact ⟨rfl, hc.1, hc.2, Or.inl ⟨b, v, rfl, rfl⟩⟩
  | var x =>
    cases hs' : mop vm (.var x) with
    | none => simp [hc, hw', hs'] at h
    | some s' =>
    cases h0 : take1 (.bin .shl (imm 224) s') ms with
    | none => simp [hc, hw', hs', h0] at h
    | some p =>
    obtain ⟨t, ms1⟩ := p
    by_cases hne : w' = Operand.var t
    · simp [hc, hw', hs', h0, hne] at h
    cases h1 : take0 (.evm .mstore [imm 0, Operand.var t]) ms1 with
    | none => simp [hc, hw', hs', h0, hne, h1] at h
    | some rest =>
    cases h2 : take0 (.evm .mstore [imm 4, w']) rest with
    | none => simp [hc, hw', hs', h0, hne, h1, h2] at h
    | some rest2 =>
    simp [hc, hw', hs', h0, hne, h1, h2] at h
    obtain ⟨rfl, rfl⟩ := h
    have e0 := take1_some h0
    have e1 := take0_some h1
    have e2 := take0_some h2
    subst e0 e1 e2
    exact ⟨rfl, hc.1, hc.2, Or.inr ⟨x, s', t, rfl, rfl, hne, rfl⟩⟩

theorem eval_shl224 (n : Nat) : BinOp.eval .shl 256 224 n % W = n % 2 ^ 32 * 2 ^ 224 := by
  simp only [BinOp.eval, show ¬ (224 ≥ 256) by omega, if_false]
  rw [wrap_nat, Nat.shiftLeft_eq, Nat.mod_mod, show 2 ^ 256 = 2 ^ 32 * 2 ^ 224 by norm_num,
    Nat.mul_mod_mul_right]

/-- The machine run of `evm_revert_word`'s expansion (`revertWordOk`): it reverts with H's data of
    the selector's and the word's machine words. -/
theorem run_revertWord {c : FCtx} {vm : VM} {s wd : Operand} {ms : List Stmt} {mt : Term}
    (hto : revertWordOk c vm s wd ms mt = true) (O : Oracle) (cM : Ctx) (I : Fe.EVM.Env)
    {envM : Env} {w : World} {ns nw : Nat}
    (hs : ∀ s', mop vm s = some s' → mval envM s' = some ns)
    (hw : ∀ w', mop vm wd = some w' → mval envM w' = some nw)
    {res : Except (Exit World) (Next × World)}
    (hres : (runBodyO O cM envM ms >>= fun e => runTerm e mt).exec I w = some res) :
    res = .error (.revert (revertWordData ns nw)) := by
  obtain ⟨w', hw', rfl, -, -, h⟩ := revertWordOk_some hto
  have hmw := hw w' hw'
  have hi : ∀ (env : Env) n, evalWord env (imm n) = pure (Ethereum.UInt256.ofNat n) := fun _ _ =>
    mval_evalWord (by simp [imm, mval])
  have h0' : (Ethereum.UInt256.ofNat 0).toNat = 0 := toNat_ofNat_lt (by unfold W; norm_num)
  have h4' : (Ethereum.UInt256.ofNat 4).toNat = 4 := toNat_ofNat_lt (by unfold W; norm_num)
  have h36' : (Ethereum.UInt256.ofNat 36).toNat = 36 := toNat_ofNat_lt (by unfold W; norm_num)
  rcases h with ⟨b, v, rfl, rfl⟩ | ⟨x, s', t, rfl, hs', hne, rfl⟩
  · have hv : ns = v := by
      have := hs _ rfl
      simp only [mop, mval, if_true, Option.some.injEq] at this
      exact this.symm
    subst hv
    rw [runBodyO_plain O cM envM _ (by simp)] at hres
    simp [runPlain, runInst, EvmOp.run, Fe.EVM.mstore, hi, mval_evalWord hmw, Fe.Sonatina.bind,
      runTerm, revertData, Fe.M.revert, h0', h4', h36', -Nat.reducePow] at hres
    rw [read_two_words, sel_bytes (shl224_toNat ns)] at hres
    exact hres.symm
  · have hms' := hs s' hs'
    rw [runBodyO_plain O cM envM _ (by simp),
      runPlain_bin cM (show mval envM (imm 224) = some 224 by simp [imm, mval]) hms'] at hres
    have hne' : ∀ q, w' = .var q → q ≠ t := fun q hq he => hne (he ▸ hq)
    simp [runPlain, runInst, EvmOp.run, Fe.EVM.mstore, hi, mval_evalWord (mval_insert_self envM t _),
      mval_evalWord ((mval_insert_other hne').trans hmw), Fe.Sonatina.bind, runTerm, revertData,
      Fe.M.revert, h0', h4', h36', -Nat.reducePow] at hres
    rw [read_two_words, sel_bytes (by rw [toNat_ofNat_mod, Nat.mod_mod, eval_shl224])] at hres
    exact hres.symm

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.liveEnd (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    fn.live b b.body.length = nset (b.term.uses ++ liveOut fn.f fn.L b) := by
  rw [U.live hb]
  unfold livePoints
  rw [foldr_chain_last]
  rfl

theorem FnUnp.dOp (U : FnUnp src low r fn fr fl e me be rs) (a : Operand) :
    fn.F.dOp a = (secX src r).derived.op fn.k a := by
  cases a <;> simp [Frame.dOp, Derived.op, U.hF, frameOf]

/-- A source terminator's successor: a block of the function, whose region starts where the
    block map says, entered on a related edge. -/
theorem FnUnp.gotoOk {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {g : Ghost} {hst : H.State} {envH : HEnv} {envM : Env}
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length)) {d d' : Nat}
    (hd : d ∈ b.term.succs) (hbm : fn.c.bm.find? d = some d') :
    ∃ db dblk, db.id = d ∧ db ∈ fn.f.blocks ∧ fn.start db = some (d', dblk) ∧
      EdgeRel (secS src r efp) fn g hst (some b.id) db envH envM := by
  obtain ⟨db, hdb, hid⟩ := U.shape'.2.2.2.2.2.2.2.2.2.2.2 b hb d hd
  obtain ⟨mb₀, mblk₀, _, _, _, _, _, hst0, -⟩ := U.walkOk hdb
  have hst1 := hst0
  simp only [Fn.start, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at hst1
  obtain ⟨mb', hmb', mblk', -, rfl, rfl⟩ := hst1
  rw [hid, hbm] at hmb'
  cases hmb'
  refine ⟨db, mblk', hid, hdb, hst0, b, hb, rfl, by rw [hid]; exact hd, hE.mono fun x hx => ?_⟩
  rw [U.liveEnd hb, mem_nset]
  exact List.mem_append_right _ hx

/-- A terminator operand of a function: its H value, and its machine operand's word. -/
theorem FnUnp.topnd {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {g : Ghost} {hst : H.State} {envH : HEnv} {envM : Env}
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length))
    {a : Operand} (ha : a ∈ b.term.skel.args) {ta : Ty} (ht : fn.c.tyOf a = some ta)
    (hval : Ty.value ta = true) {a' : Operand} (hm : mop fn.F.vm a = some a') :
    ∃ v m, evalOp envH a = some v ∧ v.fits ta = true ∧ mval envM a' = some m ∧ m < W ∧
      VRel g (secS src r efp).z (fn.F.dOp a) v m ∧ ValOk hst v ∧
      OrigOk g hst fn.F.R fn.F.fpf (origOf fn.F.O a) v := by
  have hdecl : fn.F.decls = fn.c.decls := by rw [U.hF, U.hc]; rfl
  obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := opnd_rel hE hdecl rfl (fun y hy => by
    rw [U.liveEnd hb, mem_nset]
    refine List.mem_append_left _ ?_
    unfold HTerm.uses varsOf
    exact List.mem_filterMap.mpr ⟨a, ha, by rw [hy]⟩) ht hm
  exact ⟨v, m, h1, h2, h3, vrel_lt h4 h2 hval, h4, h5, h6⟩

/-- The function's terminator conclusion, for block `b` with H terminator `t`. -/
def TermGoal (I : Fe.EVM.Env) (S : SecFacts) (Dr : Derived) (fn : Fn) (b : HBlock) (t : HTerm)
    (g : Ghost) (hst : H.State) (w : World) (envH : HEnv)
    (r : Except (Exit World) (Next × World)) : Prop :=
  (∃ o, stepTerm I envH hst t = .halt o ∧ Excuses o r) ∨
  (∃ envM' d' db dblk, r = .ok (.goto envM' d', w) ∧ stepTerm I envH hst t = .goto db.id ∧
    db ∈ fn.f.blocks ∧ fn.start db = some (d', dblk) ∧ EdgeRel S fn g hst (some b.id) db envH envM') ∨
  (∃ vals w' valsH, r = .ok (.done vals, w') ∧ stepTerm I envH hst t = .ret valsH ∧
    Inv S hst w' g ∧ RetRel S g hst (fn.dret Dr) fn.f.rets valsH vals)

/-- An exit of the machine that H's halt in the same exit excuses. -/
theorem excuses_exit {e : Exit World} {α : Type} : Excuses (.ends (.error e))
    (.error e : Except (Exit World) α) :=
  Or.inr (Or.inr ⟨e, rfl, Or.inr (Or.inr ⟨.error e, rfl, EndsAs.exit e⟩)⟩)

/-- A stop of the machine that H's stop with the same data and a world equal but for memory
    excuses. -/
theorem excuses_stop {d : ByteArray} {w w' : World} {α : Type}
    (h : { w with memory := w'.memory } = w') :
    Excuses (.ends (.error (.stop d w'))) (.error (.stop d w) : Except (Exit World) α) := by
  refine Or.inr (Or.inr ⟨.stop d w, rfl, Or.inr (Or.inr ⟨.error (.stop d w'), rfl, ?_⟩)⟩)
  rw [← h]
  exact EndsAs.stop_stop rfl rfl rfl

/-- `selfdestruct` on a world that differs only in memory ends in the same exit, its world's
    memory aside. -/
theorem selfdestruct_mem (a : Ethereum.UInt256) (I : Fe.EVM.Env) (w : World) (m : ByteArray)
    {e : Exit World} (h : (Fe.EVM.selfdestruct a).exec I w = some (.error e)) :
    ∃ e', (Fe.EVM.selfdestruct a).exec I { w with memory := m } = some (.error e') ∧
      ∀ {α : Type}, Excuses (.ends (.error e')) (.error e : Except (Exit World) α) := by
  unfold Fe.EVM.selfdestruct next at h ⊢
  simp only [Fe.M.exec_bind, Fe.M.exec_read, Fe.M.exec_get] at h ⊢
  split at h
  · next hp =>
    simp only [hp, ite_true, Fe.M.exec_fail, Option.some.injEq, Except.error.injEq] at h ⊢
    subst h
    exact ⟨_, rfl, excuses_exit⟩
  · next hp =>
    simp only [hp, Bool.false_eq_true, ite_false] at h ⊢
    simp only [Fe.M.exec_bind, Fe.M.exec_get] at h ⊢
    cases hf : w.feed with
    | nil => simp [hf, Fe.M.exec_diverge] at h
    | cons sp rest =>
      simp [hf, Fe.M.stop] at h ⊢
      subst h
      exact fun {α} => excuses_stop rfl

/-- The data of `evm_return`/`evm_revert`: the machine reads, at its address, the bytes H's
    range of the operands holds. -/
theorem FnUnp.dataOk {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hI : Inv (secS src r efp) hst w g)
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length))
    {a l : Operand} (ha : a ∈ b.term.skel.args) (hl : l ∈ b.term.skel.args)
    (hta : (fn.c.tyOf a).any Ty.value = true) (htl : (fn.c.tyOf l).any Ty.value = true)
    (hlobs : (secS src r efp).z = true → fn.F.dOp l = false) {a' l' : Operand}
    (hma : mop fn.F.vm a = some a') (hml : mop fn.F.vm l = some l') :
    ∃ x n ma ml, evalOp envH a = some x ∧ evalOp envH l = some n ∧ mval envM a' = some ma ∧
      mval envM l' = some ml ∧ ma < W ∧ ml < W ∧ hst.word n = ml ∧
      ∀ rr, hst.range x ml = some rr → hst.bytes rr ml = w.memory.readWithPadding ma ml := by
  obtain ⟨ta, hta', hva⟩ := tyOf_any hta
  obtain ⟨tl, htl', hvl⟩ := tyOf_any htl
  obtain ⟨x, ma, hx, -, hmx, hmaW, hvx, hox, horx⟩ := U.topnd hb hE ha hta' hva hma
  obtain ⟨n, ml, hn, -, hmn, hmlW, hvn, hon, -⟩ := U.topnd hb hE hl htl' hvl hml
  refine ⟨x, n, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, vrel_exact hI hvn hon hlobs, fun rr hr => ?_⟩
  by_cases h0 : ml = 0
  · subst h0
    simp only [State.range, if_true, Option.some.injEq] at hr
    subst hr
    rw [readWithPadding_of_mem (l := []) (n := 0) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))]
    rfl
  · obtain ⟨bk, o, rfl, rfl, ho, -⟩ := range_ptr hr h0
    have hlive := live_of_orig hI horx
    rw [addr_of_vrel hI hvx hlive ho, inv_bytes hI hlive ho]

/-- Rule S8's certificate at a `return`: a derived returned value makes the function's results
    derived. -/
theorem FnUnp.derRet {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (hz : secZ src r = true) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {vs : List Operand} (ht : b.term = .base (.ret vs)) {a : Operand} (ha : a ∈ vs)
    (hd : (secX src r).derived.op fn.k a = true) : (secX src r).derived.rets.contains fn.k = true := by
  have h := hS.der hz
  unfold derivedOk at h
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have hf : (fn.k, fn.f, withCallees fr fn.f) ∈ derivedInput (secP src r) := by
    have := mem_placed (r := r) U.hf
    rw [← U.hfr] at this
    exact List.mem_map.mpr ⟨_, this, rfl⟩
  have hwj : (withCallees fr fn.f)[j]? = some (withCallees.go b.body ((fr.calls[j]?).getD [])) := by
    unfold withCallees
    rw [List.getElem?_map, List.getElem?_zipIdx, hj]; simp
  have h1 := ((h _ hf).2 _ (mem_zip_of hj hwj)).2
  rw [ht] at h1
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · have : vs.any ((secX src r).derived.op fn.k) = true := List.any_eq_true.mpr ⟨a, ha, hd⟩
    rw [this] at h1; cases h1
  · exact h1

theorem FnUnp.termBase {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {t : Term} (ht : b.term = .base t) {mt : Term}
    (hmt : mapTerm fn.c fn.F.vm fn.f.rets t = some mt) {g : Ghost} {hst : H.State} {w : World}
    {envH : HEnv} {envM : Env} (hI : Inv (secS src r efp) hst w g)
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length))
    {res : Except (Exit World) (Next × World)} (hres : (runTerm envM mt).exec I w = some res) :
    TermGoal I (secS src r efp) (secX src r).derived fn b b.term g hst w envH res := by
  have hobs : (secS src r efp).z = true → ∀ a ∈ t.args,
      (∀ a' l', t ≠ .evmReturn a' l' ∧ t ≠ .evmRevert a' l') → (∀ vs, t ≠ .ret vs) →
      fn.F.dOp a = false := by
    intro hz a ha hnr hnret
    have h := U.rules.s8 hz
    simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
    have h1 := (h b hb).2
    rw [U.dOp]
    rw [ht] at h1
    cases t
    all_goals first
      | (exact absurd rfl (hnret _))
      | (exact absurd rfl (hnr _ _).1)
      | (exact absurd rfl (hnr _ _).2)
      | (simp only [List.any_eq_false, Bool.not_eq_true', Bool.not_eq_true] at h1
         simpa using h1 a ha)
  unfold TermGoal
  rw [ht]
  cases t with
  | jump d =>
    simp only [mapTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hmt
    obtain ⟨d', hd', rfl⟩ := hmt
    simp only [runTerm, Fe.M.exec_pure, Option.some.injEq] at hres
    subst hres
    obtain ⟨db, dblk, hid, hdb, hst0, hedge⟩ := U.gotoOk hb hE (d := d)
      (by rw [ht]; simp [HTerm.succs, Term.succs]) hd'
    exact Or.inr (Or.inl ⟨envM, d', db, dblk, rfl, by simp [stepTerm, hid], hdb, hst0, hedge⟩)
  | evmStop =>
    simp only [mapTerm, Option.pure_def, Option.some.injEq] at hmt
    subst hmt
    simp only [runTerm, stopCall, Fe.M.stop, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_fail] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    exact Or.inl ⟨_, rfl, excuses_stop hI.world⟩
  | evmInvalid =>
    simp only [mapTerm, Option.pure_def, Option.some.injEq] at hmt
    subst hmt
    simp only [runTerm, trap, Fe.M.exec_bind, Fe.M.exec_fail, Option.some.injEq] at hres
    subst hres
    exact Or.inl ⟨_, rfl, excuses_exit⟩
  | unreachable =>
    simp only [mapTerm, Option.pure_def, Option.some.injEq] at hmt
    subst hmt
    simp only [runTerm, trap, Fe.M.exec_bind, Fe.M.exec_fail, Option.some.injEq] at hres
    subst hres
    exact Or.inl ⟨_, rfl, excuses_exit⟩
  | br cnd nz z =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨hty, c', hc', nz', hnz, z', hz, rfl⟩ := hmt
    obtain ⟨ta, hta, hval⟩ := tyOf_any hty
    obtain ⟨v, m, hev, -, hmv, -, hvr, hvo, -⟩ := U.topnd hb hE (a := cnd)
      (by rw [ht]; simp [HTerm.skel, Term.args]) hta hval hc'
    have hw : hst.word v = m := vrel_exact hI hvr hvo fun hz =>
      hobs hz cnd (by simp [Term.args]) (by intro a' l'; simp) (by intro vs; simp)
    simp only [runTerm, mval_evalInt hmv, pure_bind, Fe.M.exec_pure, Option.some.injEq] at hres
    subst hres
    by_cases hm0 : m = 0
    · obtain ⟨db, dblk, hid, hdb, hst0, hedge⟩ := U.gotoOk hb hE (d := z)
        (by rw [ht]; simp [HTerm.succs, Term.succs]) hz
      refine Or.inr (Or.inl ⟨envM, _, db, dblk, by simp [hm0], ?_, hdb, hst0, hedge⟩)
      simp [stepTerm, hev, hw, hm0, hid]
    · obtain ⟨db, dblk, hid, hdb, hst0, hedge⟩ := U.gotoOk hb hE (d := nz)
        (by rw [ht]; simp [HTerm.succs, Term.succs]) hnz
      refine Or.inr (Or.inl ⟨envM, _, db, dblk, by simp [hm0], ?_, hdb, hst0, hedge⟩)
      simp [stepTerm, hev, hw, hm0, hid]
  | brTable sc d cases =>
    cases d with
    | none => simp [mapTerm] at hmt
    | some d =>
    simp only [mapTerm, Option.bind_eq_bind] at hmt
    split at hmt
    · next hc =>
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      obtain ⟨d', hd', hmt⟩ := Option.bind_eq_some_iff.mp hmt
      obtain ⟨cases', hcases', hmt⟩ := Option.bind_eq_some_iff.mp hmt
      obtain ⟨dbd, dblkd, hidd, hdbd, hstd, hedd⟩ := U.gotoOk hb hE (d := d)
        (by rw [ht]; simp [HTerm.succs, Term.succs]) hd'
      have hcase : ∀ x ∈ cases, ∀ o', mop fn.F.vm x.1 = some o' → ∃ v m, evalOp envH x.1 = some v ∧
          mval envM o' = some m ∧ hst.word v = m := by
        intro x hx o' ho'
        obtain ⟨tx, htx, hvx⟩ := tyOf_any (hc.2 x hx)
        have hxa : x.1 ∈ (Term.brTable sc (some d) cases).args := by
          simp only [Term.args]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hx)
        obtain ⟨v, m, hev, -, hmv, -, hvr, hvo, -⟩ := U.topnd hb hE (a := x.1)
          (by rw [ht]; exact hxa) htx hvx ho'
        exact ⟨v, m, hev, hmv, vrel_exact hI hvr hvo fun hz =>
          hobs hz x.1 hxa (by intro a' l'; simp) (by intro vs; simp)⟩
      obtain ⟨valsH, valsM, hvH, hvM, hrel, hmem⟩ := table_lists (word := hst.word) cases cases'
        hcase hcases'
      split at hmt
      · next hemp =>
        obtain rfl : Term.jump d' = mt := by simpa using hmt
        have hc0 : cases' = [] := List.isEmpty_iff.mp hemp
        subst hc0
        have hc1 : cases = [] := by
          have := (mapM_some_forall₂ hcases').length_eq
          simpa using this
        subst hc1
        simp only [runTerm, Fe.M.exec_pure, Option.some.injEq] at hres
        subst hres
        obtain ⟨ts, hts, hvts⟩ := tyOf_any hc.1
        obtain ⟨sc', hsc'⟩ : ∃ sc', mop fn.F.vm sc = some sc' := by
          cases sc with
          | imm => exact ⟨_, rfl⟩
          | var y =>
            obtain ⟨_, _, _, _, h3, _⟩ := hE y (by
              rw [U.liveEnd hb, mem_nset]
              refine List.mem_append_left _ ?_
              rw [ht]; simp [HTerm.uses, HTerm.skel, Term.args, varsOf])
            cases e : fn.F.vm.find? y with
            | none => rw [e] at h3; cases h3
            | some o => exact ⟨o, e⟩
        obtain ⟨v, m, hev, -, -, -, -, -, -⟩ := U.topnd hb hE (a := sc)
          (by rw [ht]; simp [HTerm.skel, Term.args]) hts hvts hsc'
        refine Or.inr (Or.inl ⟨envM, d', dbd, dblkd, rfl, ?_, hdbd, hstd, hedd⟩)
        simp [stepTerm, hev, hidd]
      · obtain ⟨sc', hsc', hmt⟩ := Option.bind_eq_some_iff.mp hmt
        obtain rfl : Term.brTable sc' (some d') cases' = mt := by simpa using hmt
        obtain ⟨ts, hts, hvts⟩ := tyOf_any hc.1
        obtain ⟨v, m, hev, -, hmv, -, hvr, hvo, -⟩ := U.topnd hb hE (a := sc)
          (by rw [ht]; simp [HTerm.skel, Term.args]) hts hvts hsc'
        have hw : hst.word v = m := vrel_exact hI hvr hvo fun hz =>
          hobs hz sc (by simp [Term.args]) (by intro a' l'; simp) (by intro vs; simp)
        simp only [runTerm, mval_evalInt hmv, hvM, pure_bind] at hres
        rcases find_rel m hrel with ⟨p, q, hp, hq, hpq⟩ | ⟨hp, hq⟩
        · rw [hq] at hres
          have hres' : (pure (Next.goto envM q.2) : FeM Next).exec I w = some res := hres
          simp only [Fe.M.exec_pure, Option.some.injEq] at hres'
          subst hres'
          obtain ⟨db, dblk, hid, hdb, hst0, hedge⟩ := U.gotoOk hb hE (d := p.2)
            (by rw [ht]; simp only [HTerm.succs, Term.succs]
                exact List.mem_append_right _ (hmem p (List.mem_of_find?_eq_some hp))) hpq
          refine Or.inr (Or.inl ⟨envM, q.2, db, dblk, rfl, ?_, hdb, hst0, hedge⟩)
          simp [stepTerm, hev, hvH, hw, hp, hid]
        · rw [hq] at hres
          have hres' : (pure (Next.goto envM d') : FeM Next).exec I w = some res := hres
          simp only [Fe.M.exec_pure, Option.some.injEq] at hres'
          subst hres'
          refine Or.inr (Or.inl ⟨envM, d', dbd, dblkd, rfl, ?_, hdbd, hstd, hedd⟩)
          simp [stepTerm, hev, hvH, hw, hp, hidd]
    · cases hmt
  | ret vs =>
    simp only [mapTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmt
    obtain ⟨ts, hts, hmt⟩ := hmt
    split at hmt
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨vs', hvs', hmt⟩ := Option.bind_eq_some_iff.mp hmt
      obtain rfl : Term.ret vs' = mt := by simpa using hmt
      have hs3 := U.rules.s3
      simp only [s3Uses, List.all_eq_true, Bool.and_eq_true] at hs3
      have hs3b := (hs3 b hb).2
      rw [ht] at hs3b
      simp only [List.all_eq_true, List.isEmpty_iff] at hs3b
      obtain ⟨valsH, mws, hvals, hmws, hrel, hfits⟩ := ret_lists (envH := envH) (envM := envM)
        (vm := fn.F.vm) (tyOf := fn.c.tyOf)
        (fun a v m => VRel g (secS src r efp).z (fn.dret (secX src r).derived) v m ∧ ValOk hst v ∧
          ∀ b o, v = .ptr b o → g.heap b) vs ts fn.f.rets vs' hts (forall₂_of_zip hc.1 hc.2) hvs'
        (fun a ha t a' hta hma => by
          have hval : Ty.value t = true := by
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
            obtain ⟨tj, htj⟩ : ∃ tj, ts[i]? = some tj := get_of_len hi
              (mapM_some_forall₂ hts).length_eq
            obtain ⟨rt, hrt⟩ := get_of_len htj hc.1
            have := hc.2 (tj, rt) (mem_zip_of htj hrt)
            have e : tj = t := by
              have := forall₂_get (mapM_some_forall₂ hts) hi htj
              rw [hta] at this; exact (Option.some.inj this).symm
            subst e
            simp only [sameW, Bool.and_eq_true] at this
            exact this.1.1
          obtain ⟨v, m, hev, hfit, hmv, -, hvr, hvo, hor⟩ := U.topnd hb hE (a := a)
            (by rw [ht]; simpa [HTerm.skel, Term.args] using ha) hta hval hma
          refine ⟨v, m, hev, hmv, hfit, ?_, hvo, ?_⟩
          · cases v with
            | int => exact hvr
            | ptr b' o' =>
              exact ⟨hvr.1, fun hz => U.derRet hS hz hb ht ha (by rw [← U.dOp]; exact hvr.2 hz)⟩
          · intro b' o' hv
            subst hv
            have ho : origOf fn.F.O a = [] := by rw [U.hF]; exact hs3b a ha
            rw [ho] at hor
            rcases hor with h | ⟨-, ⟨s, hs, -⟩ | ⟨h0, -⟩⟩
            · exact h
            · cases hs
            · cases h0)
      simp only [runTerm, mapM_evalOperand hmws, pure_bind, Fe.M.exec_pure, Option.some.injEq] at hres
      subst hres
      refine Or.inr (Or.inr ⟨_, w, valsH, rfl, by simp [stepTerm, hvals], hI, ?_, hfits⟩)
      rw [List.forall₂_map_right_iff]
      exact hrel.imp fun v m ⟨_, _, h1, h2, h3⟩ => ⟨m, rfl, h1, h2, h3⟩
    · cases hmt
  | evmReturn a l =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨⟨hta, htl⟩, a', ha', l', hl', rfl⟩ := hmt
    have hlobs : (secS src r efp).z = true → fn.F.dOp l = false := by
      intro hz
      have h := U.rules.s8 hz
      simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
      have h1 := (h b hb).2
      rw [ht] at h1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      rw [U.dOp]; exact h1.1
    obtain ⟨x, n, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, hwn, hdat⟩ := U.dataOk hb hI hE
      (by rw [ht]; simp [HTerm.skel, Term.args]) (by rw [ht]; simp [HTerm.skel, Term.args]) hta htl
      hlobs ha' hl'
    simp only [runTerm, mval_evalWord hmx, mval_evalWord hmn, pure_bind, returnData, Fe.M.stop,
      Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_fail, toNat_ofNat_lt hmaW, toNat_ofNat_lt hmlW,
      Option.some.injEq] at hres
    subst hres
    left
    cases hr : hst.range x ml with
    | none => exact ⟨.ub, by simp [stepTerm, hx, hn, hwn, hr], Or.inl rfl⟩
    | some rr =>
      refine ⟨.ends (.error (.stop (hst.bytes rr ml) hst.world)), by simp [stepTerm, hx, hn, hwn, hr], ?_⟩
      rw [hdat rr hr]
      exact excuses_stop hI.world
  | evmRevert a l =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨⟨hta, htl⟩, a', ha', l', hl', rfl⟩ := hmt
    have hlobs : (secS src r efp).z = true → fn.F.dOp l = false := by
      intro hz
      have h := U.rules.s8 hz
      simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
      have h1 := (h b hb).2
      rw [ht] at h1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      rw [U.dOp]; exact h1.1
    obtain ⟨x, n, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, hwn, hdat⟩ := U.dataOk hb hI hE
      (by rw [ht]; simp [HTerm.skel, Term.args]) (by rw [ht]; simp [HTerm.skel, Term.args]) hta htl
      hlobs ha' hl'
    simp only [runTerm, mval_evalWord hmx, mval_evalWord hmn, pure_bind, revertData, Fe.M.revert,
      Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_fail, toNat_ofNat_lt hmaW, toNat_ofNat_lt hmlW,
      Option.some.injEq] at hres
    subst hres
    left
    cases hr : hst.range x ml with
    | none => exact ⟨.ub, by simp [stepTerm, hx, hn, hwn, hr], Or.inl rfl⟩
    | some rr =>
      refine ⟨.ends (.error (.revert (hst.bytes rr ml))), by simp [stepTerm, hx, hn, hwn, hr], ?_⟩
      rw [hdat rr hr]
      exact excuses_exit
  | evmSelfDestruct a =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨hty, a', ha', rfl⟩ := hmt
    obtain ⟨ta, hta, hval⟩ := tyOf_any hty
    obtain ⟨v, m, hev, -, hmv, hmW, hvr, hvo, -⟩ := U.topnd hb hE (a := a)
      (by rw [ht]; simp [HTerm.skel, Term.args]) hta hval ha'
    have hw : hst.word v = m := vrel_exact hI hvr hvo fun hz =>
      hobs hz a (by simp [Term.args]) (by intro a' l'; simp) (by intro vs; simp)
    simp only [runTerm, mval_evalWord hmv, pure_bind] at hres
    rcases exec_bind_some hres with ⟨e, h1, rfl⟩ | ⟨x, _, _, _⟩
    · obtain ⟨e', h2, hx⟩ := selfdestruct_mem _ I w hst.world.memory h1
      rw [hI.world] at h2
      left
      refine ⟨.ends (.error e'), ?_, hx⟩
      simp [stepTerm, hev, State.uword, hw, h2]
    · exact x.elim

theorem FnUnp.termCode {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) (cM : Ctx) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {o l : Operand} (ht : b.term = .returnCode o l) {ms : List Stmt} {mt : Term}
    (hto : termOk fn.c fn.F.vm fn.f.rets b.term ms mt = true) (O : Oracle) {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env} (hI : Inv (secS src r efp) hst w g)
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length))
    {res : Except (Exit World) (Next × World)}
    (hres : (runBodyO O cM envM ms >>= fun e => runTerm e mt).exec I w = some res) :
    TermGoal I (secS src r efp) (secX src r).derived fn b b.term g hst w envH res := by
  rw [ht] at hto
  simp only [termOk, Option.isSome_iff_exists, Option.bind_eq_bind, Option.bind_eq_some_iff] at hto
  obtain ⟨_, hto⟩ := hto
  split at hto
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨o', ho', hto⟩ := Option.bind_eq_some_iff.mp hto
    obtain ⟨l', hl', hto⟩ := Option.bind_eq_some_iff.mp hto
    obtain ⟨rest, hrest, hto⟩ := Option.bind_eq_some_iff.mp hto
    split at hto
    · next hc2 =>
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hc2
      obtain ⟨rfl, rfl⟩ := hc2
      have hms := take0_some hrest
      subst hms
      have hobs : (secS src r efp).z = true → ∀ a ∈ [o, l], fn.F.dOp a = false := by
        intro hz a ha
        have h := U.rules.s8 hz
        simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
        have h1 := (h b hb).2
        rw [ht] at h1
        simp only [HTerm.skel, Term.args, List.any_eq_false, Bool.not_eq_true'] at h1
        rw [U.dOp]
        simpa using h1 a ha
      obtain ⟨tO, hto', hvo⟩ := tyOf_any hc.1
      obtain ⟨tl, htl', hvl⟩ := tyOf_any hc.2
      obtain ⟨x, mo, hx, -, hmo, hmoW, hvx, hox, -⟩ := U.topnd hb hE (a := o)
        (by rw [ht]; simp [HTerm.skel, Term.args]) hto' hvo ho'
      obtain ⟨n, ml, hn, -, hml, hmlW, hvn, hon, -⟩ := U.topnd hb hE (a := l)
        (by rw [ht]; simp [HTerm.skel, Term.args]) htl' hvl hl'
      have hwx : hst.word x = mo := vrel_exact hI hvx hox fun hz => hobs hz o (by simp)
      have hwn : hst.word n = ml := vrel_exact hI hvn hon fun hz => hobs hz l (by simp)
      rw [runBodyO_plain O cM envM _ (by simp)] at hres
      have h0 : evalWord envM (Operand.imm 256 0) = pure (Ethereum.UInt256.ofNat 0) :=
        mval_evalWord (by simp [mval])
      have h0' : (Ethereum.UInt256.ofNat 0).toNat = 0 := toNat_ofNat_lt (by unfold W; norm_num)
      simp [h0, h0', runPlain, runInst, EvmOp.run, Fe.EVM.codecopy, mval_evalWord hmo, mval_evalWord hml,
        toNat_ofNat_lt hmoW, toNat_ofNat_lt hmlW, Fe.Sonatina.bind, runTerm, returnData, Fe.M.stop,
        imm, mval, read_write_zero] at hres
      subst hres
      refine Or.inl ⟨.ends (.error (.stop (I.code.readWithPadding mo ml) hst.world)),
        by simp [stepTerm, ht, hx, hn, hwx, hwn], ?_⟩
      exact excuses_stop hI.world
    · simp at hto
  · simp at hto

/-- A selector of type `i32` and a word: their declared types, value types. -/
theorem revertWord_types {c : FCtx} {s wd : Operand}
    (hts : (c.tyOf s).any (sameW · (.int 32)) = true) (htw : (c.tyOf wd).any isWord = true) :
    (∃ t, c.tyOf s = some t ∧ Ty.value t = true) ∧ ∃ t, c.tyOf wd = some t ∧ Ty.value t = true := by
  constructor
  · cases e : c.tyOf s with
    | none => rw [e] at hts; cases hts
    | some t =>
      rw [e] at hts
      simp only [Option.any_some, sameW, Bool.and_eq_true] at hts
      exact ⟨t, rfl, hts.1.1⟩
  · cases e : c.tyOf wd with
    | none => rw [e] at htw; cases htw
    | some t =>
      rw [e] at htw
      simp only [Option.any_some, isWord, Bool.and_eq_true] at htw
      exact ⟨t, rfl, htw.1⟩

/-- The selector's machine operand, which `revertWordOk` takes or which is an immediate. -/
theorem revertWord_mop {vm : VM} {s : Operand} {ms : List Stmt} {w' : Operand}
    (h : (∃ b v, s = .imm b v ∧
          ms = [⟨[], .evm .mstore [imm 0, imm (v * 2 ^ 224)]⟩, ⟨[], .evm .mstore [imm 4, w']⟩]) ∨
       (∃ x s' t, s = .var x ∧ mop vm s = some s' ∧ w' ≠ .var t ∧
          ms = [⟨[(t, .int 256)], .bin .shl (imm 224) s'⟩, ⟨[], .evm .mstore [imm 0, .var t]⟩,
            ⟨[], .evm .mstore [imm 4, w']⟩])) : ∃ s', mop vm s = some s' := by
  rcases h with ⟨b, v, rfl, -⟩ | ⟨-, s', -, -, hs', -, -⟩
  · exact ⟨_, rfl⟩
  · exact ⟨s', hs'⟩

/-- Rule S8 at `evm_revert_word`: in address-0 mode neither operand is derived (both are
    observed, `notObserved`'s last case). -/
theorem FnUnp.obsWord {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {s wd : Operand} (ht : b.term = .revertWord s wd)
    (hz : (secS src r efp).z = true) : fn.F.dOp s = false ∧ fn.F.dOp wd = false := by
  have h := U.rules.s8 hz
  simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h b hb).2
  rw [ht] at h1
  simp only [HTerm.skel, Term.args, List.any_eq_false, Bool.not_eq_true'] at h1
  rw [U.dOp, U.dOp]
  exact ⟨by simpa using h1 s (by simp), by simpa using h1 wd (by simp)⟩

/-- `evm_revert_word`: the machine stores the selector word at 0 and the word at 4 and reverts
    with `[0, 36)`; H reverts with the same 36 bytes and touches no memory. -/
theorem FnUnp.termWord {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) (cM : Ctx) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {s wd : Operand} (ht : b.term = .revertWord s wd) {ms : List Stmt} {mt : Term}
    (hto : termOk fn.c fn.F.vm fn.f.rets b.term ms mt = true) (O : Oracle) {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env} (hI : Inv (secS src r efp) hst w g)
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b b.body.length))
    {res : Except (Exit World) (Next × World)}
    (hres : (runBodyO O cM envM ms >>= fun e => runTerm e mt).exec I w = some res) :
    TermGoal I (secS src r efp) (secX src r).derived fn b b.term g hst w envH res := by
  rw [ht] at hto
  have hto' : revertWordOk fn.c fn.F.vm s wd ms mt = true := hto
  obtain ⟨w', hw', -, hts, htw, hsel⟩ := revertWordOk_some hto'
  obtain ⟨⟨tS, htS, hvS⟩, tW, htW, hvW⟩ := revertWord_types hts htw
  obtain ⟨s', hs'⟩ := revertWord_mop hsel
  obtain ⟨x, mx, hx, -, hmx, -, hvx, hox, -⟩ := U.topnd hb hE (a := s)
    (by rw [ht]; simp [HTerm.skel, Term.args]) htS hvS hs'
  obtain ⟨y, my, hy, -, hmy, -, hvy, hoy, -⟩ := U.topnd hb hE (a := wd)
    (by rw [ht]; simp [HTerm.skel, Term.args]) htW hvW hw'
  have hwx : hst.word x = mx := vrel_exact hI hvx hox fun hz => (U.obsWord hb ht hz).1
  have hwy : hst.word y = my := vrel_exact hI hvy hoy fun hz => (U.obsWord hb ht hz).2
  have hr := run_revertWord hto' O cM I (ns := mx) (nw := my)
    (fun s'' h => by rw [hs'] at h; cases h; exact hmx)
    (fun w'' h => by rw [hw'] at h; cases h; exact hmy) hres
  subst hr
  exact Or.inl ⟨_, by simp [stepTerm, ht, hx, hy, hwx, hwy], excuses_exit⟩

/-- Every block's terminator. -/
theorem FnUnp.termObl {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (I : Fe.EVM.Env) (cM : Ctx) :
    TermObl I cM (secS src r efp) (secX src r).derived fn := by
  intro b hb mb ms cs hp
  obtain ⟨mb₀, mblk₀, tbk, ms₀, cs₀, dss, tblk, -, hpos, htb, -, htblk, hto, -⟩ := U.walkOk hb
  rw [hpos] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  refine ⟨htb, fun mblk hmblk O g hst w envH envM hI hE res hres => ?_⟩
  rw [htblk] at hmblk
  cases hmblk
  have hG : TermGoal I (secS src r efp) (secX src r).derived fn b b.term g hst w envH res := by
    cases ht : b.term with
    | returnCode o l =>
      rw [← ht]; exact U.termCode I cM hb ht hto O hI hE hres
    | revertWord s wd =>
      rw [← ht]; exact U.termWord I cM hb ht hto O hI hE hres
    | base t =>
      rw [ht] at hto
      simp only [termOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hto
      obtain ⟨rfl, hmt⟩ := hto
      simp only [runBodyO, pure_bind] at hres
      rw [← ht]
      exact U.termBase hS I hb ht hmt hI hE hres
  exact hG

end unp

end Fe.Sonatina.Stage3.Place
