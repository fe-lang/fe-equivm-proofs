import Fe.Sonatina.Stage3.Place.InstPure

/-!
# `gep`

Machine lowering folds a `gep`'s constant offsets and emits `mul i size; add addr _` for each
dynamic index of an element of nonzero size (`gepWalk`).  `gepWalk_shape`: the walk consumes a
prefix of the statements, `add`s and `mul`s, defining what it reports.  `gepWalk_run`: run on the
machine, the prefix computes the base's word plus the offset H's `gepOffset` gives (modulo
`2 ^ 256`), on the indices' words, when the statements define distinct values none of which is
the base's or an index's machine value.  `inst_gep`: the simulation lemma.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The values machine statements define. -/
def defsOf (ms : List Stmt) : List Nat := (ms.flatMap (·.dsts)).map (·.1)

theorem defsOf_append (a b : List Stmt) : defsOf (a ++ b) = defsOf a ++ defsOf b := by
  simp [defsOf]

theorem defsOf_one (r : Nat) (i : Inst) : defsOf [⟨[(r, .int 256)], i⟩] = [r] := by
  simp [defsOf]

/-- `gepWalk`'s statements: a prefix of `ms`, of `add`s and `mul`s, defining `ds`. -/
theorem gepWalk_shape {c : FCtx} {vm : VM} :
    ∀ (idxs : List Operand) (addr : Operand) (k : Nat) (ty : Ty) (ms : List Stmt)
      (res : Operand) (ms' : List Stmt) (ds : List Nat),
    gepWalk c vm addr k ty idxs ms = some (res, ms', ds) →
    ∃ pre, ms = pre ++ ms' ∧ ds = defsOf pre ∧ ∀ st ∈ pre, ∀ g a, st.inst ≠ .call g a
  | [], addr, k, ty, ms, res, ms', ds, h => by
    simp only [gepWalk] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], rfl, rfl, by simp⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨r, rest⟩, ht, rfl, rfl, rfl⟩ := h
      exact ⟨[_], take1_some ht, (defsOf_one _ _).symm, by simp⟩
  | i :: idxs, addr, k, ty, ms, res, ms', ds, h => by
    have ih := gepWalk_shape (c := c) (vm := vm) idxs
    cases ty with
    | struct name =>
      cases i with
      | imm bits idx =>
        simp only [gepWalk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, _, _, _, _, _, h⟩ := h
        exact ih _ _ _ _ _ _ _ h
      | var y => simp [gepWalk] at h
    | int _ => simp [gepWalk] at h
    | unit => simp [gepWalk] at h
    | objRef _ => simp [gepWalk] at h
    | constRef _ => simp [gepWalk] at h
    | ptr elem => ?_
    | array elem n => ?_
    all_goals
      simp only [gepWalk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨size, _, h⟩ := h
      cases i with
      | imm bits v => exact ih _ _ _ _ _ _ _ h
      | var y =>
        simp only at h
        split at h
        · exact ih _ _ _ _ _ _ _ h
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨⟨addr1, ms1, d1⟩, h1, i', _, ⟨s, ms2⟩, hs, ⟨a2, ms3⟩, ha2, ⟨r4, ms4, d4⟩, h4,
            rfl, rfl, rfl⟩ := h
          obtain ⟨pre4, rfl, rfl, hc4⟩ := ih _ _ _ _ _ _ _ h4
          have hms2 := take1_some hs
          have hms3 := take1_some ha2
          simp only at hms2 hms3
          have hpre1 : ∃ pre1, ms = pre1 ++ ms1 ∧ d1 = defsOf pre1 ∧
              ∀ st ∈ pre1, ∀ g a, st.inst ≠ .call g a := by
            split at h1
            · simp only [Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl, rfl⟩ := h1
              exact ⟨[], rfl, rfl, by simp⟩
            · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
                Prod.mk.injEq] at h1
              obtain ⟨⟨r, rest⟩, ht, rfl, rfl, rfl⟩ := h1
              exact ⟨[_], take1_some ht, (defsOf_one _ _).symm, by simp⟩
          obtain ⟨pre1, rfl, rfl, hc1⟩ := hpre1
          refine ⟨pre1 ++ [⟨[(s, .int 256)], .bin .mul i' (imm size)⟩,
            ⟨[(a2, .int 256)], .bin .add addr1 (.var s)⟩] ++ pre4, by rw [hms2, hms3]; simp, ?_, ?_⟩
          · simp [defsOf]
          · intro st hst g a
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hst
            rcases hst with (hst | rfl | rfl) | hst
            · exact hc1 st hst g a
            · simp
            · simp
            · exact hc4 st hst g a

theorem eval_add (x y : Nat) : BinOp.eval .add 256 x y = (x + y) % W := by
  simp only [BinOp.eval]; rw [← Nat.cast_add, wrap_nat]

theorem eval_mul (x y : Nat) : BinOp.eval .mul 256 x y = (x * y) % W := by
  simp only [BinOp.eval]; rw [← Nat.cast_mul, wrap_nat]

theorem mval_insert_self (env : Env) (r m : Nat) : mval (env.insert r (.int 256 m)) (.var r) = some m := by
  simp [mval]

theorem mval_insert_other {env : Env} {r : Nat} {v : Val} {o : Operand}
    (h : ∀ q, o = .var q → q ≠ r) : mval (env.insert r v) o = mval env o := by
  cases o with
  | var q => simp only [mval]; rw [insert_other (Ne.symm (h q rfl))]
  | imm => rfl

theorem gep_mod (A k P off : Nat) :
    (((A + k) % W + P % W % W) % W % W + 0 + off) % W = (A + k + (P + off)) % W := by
  simp only [W]; omega

/-- The machine's run of `gepWalk`'s statements: the base's word plus the offset H's `gepOffset`
    gives on the indices' words, modulo `2 ^ 256`, in a machine value or immediate that is the
    walk's result; the statements change only the values they define. -/
theorem gepWalk_run {c : FCtx} {vm : VM} (cM : Ctx) (word : H.Val → Nat) :
    ∀ (idxs : List Operand) (is : List H.Val) (addr : Operand) (k : Nat) (ty : Ty)
      (ms : List Stmt) (res : Operand) (ms' : List Stmt) (ds : List Nat) (E : Env) (A : Nat),
    gepWalk c vm addr k ty idxs ms = some (res, ms', ds) → ds.Nodup →
    mval E addr = some A → A < W → (∀ q, addr = .var q → q ∉ ds) →
    List.Forall₂ (fun i v => ∃ i', mop vm i = some i' ∧ mval E i' = some (word v) ∧
      word v < W ∧ (∀ q, i' = .var q → q ∉ ds) ∧ (∀ bits n, i = .imm bits n → word v = n))
      idxs is →
    ∃ pre off E', ms = pre ++ ms' ∧ gepOffset c.src.structs word ty is = some off ∧
      runPlain cM E pre = pure E' ∧ mval E' res = some ((A + k + off) % W) ∧
      ∀ r, r ∉ ds → E'[r]? = E[r]?
  | [], [], addr, k, ty, ms, res, ms', ds, E, A, h, hnd, hA, hAW, hq, _ => by
    simp only [gepWalk] at h
    split at h
    · next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨[], 0, E, rfl, by simp [gepOffset], rfl, ?_, fun _ _ => rfl⟩
      rw [beq_iff_eq.mp hk, hA]; simp only [Nat.add_zero, Nat.mod_eq_of_lt hAW]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨r, rest⟩, ht, rfl, rfl, rfl⟩ := h
      have hk : mval E (imm k) = some k := by simp [mval, imm]
      refine ⟨[_], 0, _, take1_some ht, by simp [gepOffset], (runPlain_bin cM hA hk []).trans rfl,
        ?_, fun r' hr' => insert_other (fun e => hr' (by simp [e]))⟩
      rw [mval_insert_self, eval_add, Nat.mod_mod, Nat.add_zero]
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hiv => by cases hiv
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, hiv => by cases hiv
  | i :: idxs, v :: is, addr, k, ty, ms, res, ms', ds, E, A, h, hnd, hA, hAW, hq, hiv => by
    obtain ⟨⟨i', hmi, hmv, hwl, hiq, himm⟩, hrest⟩ := List.forall₂_cons.mp hiv
    have ih := gepWalk_run (c := c) (vm := vm) cM word idxs is
    cases ty with
    | struct name =>
      cases i with
      | imm bits idx =>
        simp only [gepWalk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨fields, hf, field, hfi, before, hb, h⟩ := h
        obtain ⟨pre, off, E', hms, hoff, hrun, hres, hag⟩ := ih _ _ _ _ _ _ _ _ _ h hnd hA hAW hq
          hrest
        have hw := himm bits idx rfl
        refine ⟨pre, before + off, E', hms, ?_, hrun, ?_, hag⟩
        · unfold gepOffset
          simp only [hf, hw, hfi, hb, hoff, Option.bind_eq_bind, Option.bind_some, bind,
            Option.bind]
          rfl
        · rw [hres]; congr 2; omega
      | var y => simp [gepWalk] at h
    | int _ => simp [gepWalk] at h
    | unit => simp [gepWalk] at h
    | objRef _ => simp [gepWalk] at h
    | constRef _ => simp [gepWalk] at h
    | ptr elem => ?_
    | array elem n => ?_
    all_goals
      simp only [gepWalk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨size, hsize, h⟩ := h
      cases i with
      | imm bits n =>
        obtain ⟨pre, off, E', hms, hoff, hrun, hres, hag⟩ := ih _ _ _ _ _ _ _ _ _ h hnd hA hAW hq
          hrest
        have hw := himm bits n rfl
        refine ⟨pre, n * size + off, E', hms, ?_, hrun, ?_, hag⟩
        · simp [gepOffset, hsize, hoff, hw]
        · rw [hres]; congr 2; rw [Nat.mul_comm]; omega
      | var y =>
        simp only at h
        split at h
        · next hs0 =>
          obtain ⟨pre, off, E', hms, hoff, hrun, hres, hag⟩ := ih _ _ _ _ _ _ _ _ _ h hnd hA hAW
            hq hrest
          refine ⟨pre, off, E', hms, ?_, hrun, by rw [hres], hag⟩
          simp [gepOffset, hsize, hoff, beq_iff_eq.mp hs0]
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨⟨addr1, ms1, d1⟩, h1, i'', hi'', ⟨s, ms2⟩, hs, ⟨a2, ms3⟩, ha2, ⟨r4, ms4, d4⟩,
            h4, rfl, rfl, rfl⟩ := h
          rw [hmi] at hi''
          cases hi''
          have hms2 := take1_some hs
          have hms3 := take1_some ha2
          simp only at hms2 hms3
          -- The pending constant, if any.
          obtain ⟨pre1, E1, A1, hms1, hrun1, hA1, hA1v, hag1, hq1⟩ : ∃ pre1 E1 A1,
              ms = pre1 ++ ms1 ∧ runPlain cM E pre1 = pure E1 ∧ mval E1 addr1 = some A1 ∧
              A1 = (A + k) % W ∧ (∀ r, r ∉ d1 → E1[r]? = E[r]?) ∧
              ∀ q, addr1 = .var q → q ∉ [s, a2] ++ d4 := by
            split at h1
            · next hk =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl, rfl⟩ := h1
              refine ⟨[], E, A, rfl, rfl, hA, ?_, fun _ _ => rfl, fun q hq' hm => hq q hq' ?_⟩
              · rw [beq_iff_eq.mp hk, Nat.add_zero, Nat.mod_eq_of_lt hAW]
              · simpa using hm
            · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
                Prod.mk.injEq] at h1
              obtain ⟨⟨r, rest⟩, ht, rfl, rfl, rfl⟩ := h1
              have hk : mval E (imm k) = some k := by simp [mval, imm]
              refine ⟨[_], _, _, take1_some ht, (runPlain_bin cM hA hk []).trans rfl,
                mval_insert_self _ _ _, by rw [eval_add, Nat.mod_mod],
                fun r' hr' => insert_other (fun e => hr' (by simp [e])), ?_⟩
              intro q hq' hm
              cases hq'
              simp only [List.singleton_append, List.cons_append] at hnd
              exact (List.nodup_cons.mp hnd).1 (by simpa using hm)
          have hd1 : ∀ q, q ∈ d1 → q ∈ d1 ++ [s, a2] ++ d4 := fun q h => by simp [h]
          have hsd : s ∈ d1 ++ [s, a2] ++ d4 := by simp
          have ha2d : a2 ∈ d1 ++ [s, a2] ++ d4 := by simp
          -- The index's word, the scaled index, the address.
          have hmi1 : mval E1 i' = some (word v) := by
            cases i' with
            | var q =>
              simp only [mval]
              rw [hag1 q (fun h => hiq q rfl (hd1 q h))]
              exact hmv
            | imm => exact hmv
          have hsz : mval E1 (imm size) = some size := by simp [mval, imm]
          set E2 := E1.insert s (.int 256 (BinOp.eval .mul 256 (word v) size % W)) with hE2
          have hA2 : mval E2 addr1 = some A1 := by
            rw [hE2, mval_insert_other fun q hq' e => hq1 q hq' (by simp [e])]; exact hA1
          have hs2 : mval E2 (.var s) = some (BinOp.eval .mul 256 (word v) size % W) :=
            mval_insert_self _ _ _
          set A2 := BinOp.eval .add 256 A1 (BinOp.eval .mul 256 (word v) size % W) % W with hA2v
          set E3 := E2.insert a2 (.int 256 A2) with hE3
          have hnd4 : d4.Nodup := (List.nodup_append.mp hnd).2.1
          have ha2n : a2 ∉ d4 := by
            have := List.nodup_append.mp hnd
            exact fun h => this.2.2 a2 (by simp) a2 h rfl
          have hsa2 : s ≠ a2 := by
            have := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
            simpa using this
          -- Values outside the step's definitions keep their machine values.
          have hkeep3 : ∀ q, q ∉ d1 ++ [s, a2] ++ d4 → E3[q]? = E[q]? := by
            intro q hq'
            rw [hE3, insert_other (fun e => hq' (by simp [← e])), hE2,
              insert_other (fun e => hq' (by simp [← e])), hag1 q (fun h => hq' (by simp [h]))]
          have hrest3 : List.Forall₂ (fun i v => ∃ i', mop vm i = some i' ∧
              mval E3 i' = some (word v) ∧ word v < W ∧ (∀ q, i' = .var q → q ∉ d4) ∧
              (∀ bits n, i = .imm bits n → word v = n)) idxs is := by
            refine List.Forall₂.imp (fun i v ⟨j', h1, h2, h3, h4, h5⟩ => ⟨j', h1, ?_, h3,
              fun q hq' hm => h4 q hq' (by simp [hm]), h5⟩) hrest
            cases j' with
            | var q => simp only [mval]; rw [hkeep3 q (h4 q rfl)]; exact h2
            | imm => exact h2
          obtain ⟨pre4, off, E4, hms4, hoff, hrun4, hres, hag4⟩ := ih _ _ _ _ _ _ _ _ _ h4 hnd4
            (mval_insert_self _ _ _) (Nat.mod_lt _ (by positivity)) (fun q hq' => by cases hq'; exact ha2n)
            hrest3
          simp only at hms4 hres
          refine ⟨pre1 ++ [⟨[(s, .int 256)], .bin .mul i' (imm size)⟩,
              ⟨[(a2, .int 256)], .bin .add addr1 (.var s)⟩] ++ pre4, word v * size + off, E4,
              by rw [hms1, hms2, hms3, hms4]; simp, ?_, ?_, ?_, ?_⟩
          · simp [gepOffset, hsize, hoff]
          · rw [runPlain_append, runPlain_append, hrun1]
            simp only [pure_bind]
            rw [runPlain_bin cM hmi1 hsz, runPlain_bin cM hA2 hs2]
            exact hrun4
          · rw [hres, eval_add, eval_mul, hA1v]
            exact congrArg some (gep_mod _ _ _ _)
          · intro r hr
            rw [hag4 r (fun h => hr (by simp [h])), hkeep3 r hr]

theorem mapM_forall₂ {α β : Type} {f : α → Option β} {P : α → β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = some b ∧ P a b) →
      ∃ bs, l.mapM f = some bs ∧ List.Forall₂ P l bs
  | [], _ => ⟨[], rfl, .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb, hp⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs, hf⟩ := mapM_forall₂ l (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs], .cons hp hf⟩

theorem OrigOk.ptr_off {g : Ghost} {st : H.State} {R : NatMap Range} {fpf : List Range}
    {os : List Nat} {b o : Nat} (h : OrigOk g st R fpf os (.ptr b o)) (o' : Nat) :
    OrigOk g st R fpf os (.ptr b o') := h

/-- An operand of the statement that is a value: its machine value is none the template
    defines (`clobberOk`, and no statement reads its own result). -/
theorem At.opnd {S : SecFacts} {F : Frame} {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt}
    {callee? : Option Nat} {L L' ds : List Nat} (hA : At S F c Dr k s callee? L L' ds)
    {a a' : Operand} (ha : a ∈ s.inst.args) (hm : mop F.vm a = some a') :
    ∀ q, a' = .var q → q ∉ ds := by
  intro q hq hqd
  cases a with
  | var y =>
    simp only [mop] at hm
    exact hA.clob y (Or.inl (hA.uses y ha)) (hA.self y ha) q hqd (by rw [hm, hq])
  | imm => simp only [mop, Option.some.injEq] at hm; rw [← hm] at hq; cases hq

theorem gep_mod2 (J o off : Nat) : (J + (o + off) % W) % W = ((J + o) % W + 0 + off) % W := by
  simp only [W]; omega

/-- A `gep` (`lower_gep`): H's step adds `gepOffset` to the base, keeping a pointer's block; the
    machine's statements compute the base's word plus the offset. -/
theorem inst_gep {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {bt : Ty} {base : Operand}
    {idxs : List Operand} {x : Nat} {tx : Ty} (hstr : c.src.structs = P.module.structs)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) (hnd : (defsOf ms).Nodup)
    (hi : s.inst = .gep bt base idxs) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, base', hb', ⟨res, ms2, ds2⟩, hw, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨hbt, hwx⟩, hbw⟩, hidx⟩ := hc
  obtain ⟨elem, rfl⟩ : ∃ e, bt = .ptr e := by cases bt <;> simp at hbt ⊢
  have hargs : s.inst.args = base :: idxs := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨tb, htb, hbw'⟩ : ∃ tb, c.tyOf base = some tb ∧ isWord tb = true := by
    cases h : c.tyOf base with
    | none => rw [h] at hbw; cases hbw
    | some tb => rw [h] at hbw; exact ⟨tb, rfl, hbw⟩
  have hvb : Ty.value tb = true := by simp only [isWord, Bool.and_eq_true] at hbw'; exact hbw'.1
  obtain ⟨vb, mbs, hvb', hfb, hmb, hrb, hob, hgb⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) htb hb'
  have hlb := vrel_lt hrb hfb hvb
  -- The statements and their definitions.
  obtain ⟨pre, hms, hds, hcall⟩ := gepWalk_shape _ _ _ _ _ _ _ _ hw
  have hndd : ds2.Nodup := by
    rw [hds]; rw [hms, defsOf_append] at hnd; exact (List.nodup_append.mp hnd).1
  -- The indices: their values and words.
  obtain ⟨is, his, hf2⟩ := mapM_forall₂ (f := evalOp envH) (P := fun i v => ∃ i', mop F.vm i = some i' ∧
      mval envM i' = some (hst.word v) ∧ hst.word v < W ∧ (∀ q, i' = .var q → q ∉ ds2) ∧
      (∀ bits n, i = .imm bits n → hst.word v = n)) idxs (by
    intro i hi'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hi'
    obtain ⟨ti, hti, hvi⟩ : ∃ ti, c.tyOf i = some ti ∧ Ty.value ti = true := by
      have := hidx i hi'
      cases h : c.tyOf i with
      | none => rw [h] at this; cases this
      | some ti => rw [h] at this; exact ⟨ti, rfl, this⟩
    obtain ⟨i', hmi⟩ : ∃ i', mop F.vm i = some i' := by
      cases i with
      | imm bits n => exact ⟨_, rfl⟩
      | var y =>
        obtain ⟨_, m, _, _, h3, _⟩ := hE y (hA.uses y (by rw [hargs]; exact List.mem_cons_of_mem _ hi'))
        cases h : F.vm.find? y with
        | none => rw [h] at h3; cases h3
        | some o => exact ⟨o, h⟩
    obtain ⟨v, m, hv, _, hm, hwv, hlt⟩ := opnd_word hI hE hA (i := j + 1)
      (by rw [hargs]; simpa using hj) (by simp [nonObserving, hi]) hti hmi hvi
    refine ⟨v, hv, i', hmi, by rw [hwv]; exact hm, by rw [hwv]; exact hlt,
      hA.opnd (by rw [hargs]; exact List.mem_cons_of_mem _ hi') hmi, ?_⟩
    intro bits n hin
    subst hin
    simp only [evalOp, Option.some.injEq] at hv
    subst hv
    rfl)
  obtain ⟨pre2, off, E', hms2, hoff, hrun, hres, hag⟩ := gepWalk_run cM hst.word idxs is base' 0
    (.ptr elem) ms res ms2 ds2 envM mbs hw hndd hmb hlb
    (hA.opnd (by rw [hargs]; simp) hb') hf2
  obtain rfl : pre = pre2 := by
    rw [hms] at hms2; exact List.append_cancel_right hms2
  rw [hstr] at hoff
  -- H's step.
  have hstep : stepInst P.ctx I envH hst s.inst =
      .ok [match vb with
        | .ptr blk o => .ptr blk ((o + off) % 2 ^ 256)
        | .int _ n => .int 256 ((n + off) % 2 ^ 256)] hst := by
    simp only [stepInst, hi, hvb', his, HSection.ctx, hoff]
    cases vb <;> rfl
  refine ⟨pre, hms, rfl, fun O r hr => ?_⟩
  rw [runBodyO_plain O cM envM pre hcall, hrun] at hr
  simp only [Fe.M.exec_pure, Option.some.injEq] at hr
  subst hr
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  refine stepOk_pure1 (m := (mbs + 0 + off) % W) hI hE hA hd hstep ?_ hag (by rw [hx]; exact hres) ?_ ?_ ?_
  · cases vb with
    | ptr blk o => rw [fits_iff hwx'.1]; exact ⟨hwx'.2, Nat.mod_lt _ (by positivity)⟩
    | int bits n => exact fits_word hwx (Nat.mod_lt _ (by positivity))
  · cases vb with
    | ptr blk o =>
      refine ⟨by rw [← hrb.1]; exact gep_mod2 _ _ _, fun hz => ?_⟩
      rw [hA.D]
      have hda := hrb.2 hz
      rw [hA.dOp] at hda
      exact hA.der hz (by simp [stmtDerived, hi, hda]) x (by simp [HStmt.defs, hd])
    | int bits n =>
      have e : n = mbs := hrb
      subst e
      show (n + off) % 2 ^ 256 = (n + 0 + off) % W
      rw [Nat.add_zero]
  · cases vb with
    | ptr blk o => exact ⟨hob.1, Nat.mod_lt _ (by positivity)⟩
    | int => trivial
  · cases vb with
    | ptr blk o =>
      exact OrigOk.mono (hgb.ptr_off _) fun o' ho => hA.orig x tx hd o' (by simp [stmtOrig, hi, ho])
    | int => trivial

end Fe.Sonatina.Stage3.Place
