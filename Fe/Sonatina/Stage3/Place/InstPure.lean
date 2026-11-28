import Fe.Sonatina.Stage3.Place.Inst

/-!
# Statements that touch neither memory nor the world

The simulation lemmas (`TemplOk`) of the patterns of `stmt` whose H step changes no state:
comparisons (`inst_cmp`, with the inverted forms machine lowering emits for `le`, `ge`, `sle`,
`sge`, `ne`), `is_zero`, `not`, `neg`, `clz`, `ctz`, the saturating and overflowing operations,
casts (`inst_cast`: an alias or a mask), `black_box`, `sym_addr`, `sym_size` and `trunc_nuw`.

Each reads its operands' words where it observes them (`opnd_word`): outside address-0 mode
every related value's H word is its machine word; in it, rule S8 puts no derived value at such a
position, and a value that is not derived is an integer (`VRel`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Operands whose word is observed -/

theorem vrel_exact {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {dx : Bool} {v : H.Val} {m : Nat} (hv : VRel g S.z dx v m) (hok : ValOk hst v)
    (hd : S.z = true → dx = false) : hst.word v = m := by
  cases v with
  | int => exact hv
  | ptr b o =>
    cases hz : S.z
    · exact vrel_word hI hv hok (Or.inl hz)
    · have h1 := hv.2 hz; rw [hd hz] at h1; cases h1

theorem fits_bits {v : H.Val} {t : Ty} (h : v.fits t = true) (ht : Ty.value t = true) :
    v.bits = t.bits := by
  rw [fits_iff ht] at h
  cases v with
  | int bits n => exact h.1
  | ptr _ _ => exact h.1.symm

/-- An operand at a position where the statement observes its word: its H value, of its type,
    has its machine word as H word. -/
theorem opnd_word {S : SecFacts} {F : Frame} {g : Ghost} {hst : H.State} {w : World}
    {envH : HEnv} {envM : Env} {L L' : List Nat} {c : FCtx} {Dr : Derived} {k : Nat}
    {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {i : Nat} {a a' : Operand} {ta : Ty}
    (hai : s.inst.args[i]? = some a) (hni : i ∉ nonObserving Dr k s)
    (ht : c.tyOf a = some ta) (hm : mop F.vm a = some a') (hval : Ty.value ta = true) :
    ∃ v m, evalOp envH a = some v ∧ v.fits ta = true ∧ mval envM a' = some m ∧
      hst.word v = m ∧ m < W := by
  obtain ⟨v, m, h1, h2, h3, h4, h5, _⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [← hy]; exact List.mem_of_getElem? hai)) ht hm
  refine ⟨v, m, h1, h2, h3, vrel_exact hI h4 h5 fun hz => ?_, vrel_lt h4 h2 hval⟩
  rw [hA.dOp]
  cases hd : Dr.op k a
  · rfl
  · exact absurd (hA.obs hz i a hai hd) hni

/-- One machine statement binding a value as a word. -/
theorem runPlain_one (c : Ctx) {env : Env} {r : Nat} {inst : Inst} {v : Val}
    (hrun : runInst c env inst = pure [v]) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], inst⟩ :: rest) =
      runPlain c (env.insert r (v.as (.int 256))) rest := by
  simp [runPlain, hrun, Fe.Sonatina.bind]

theorem insert_other {env : Env} {r r' : Nat} {v : Val} (h : r ≠ r') :
    (env.insert r v)[r']? = env[r']? := by
  rw [Std.TreeMap.getElem?_insert]; simp [h]

/-- A template of one machine statement binding a word `M`, against an H step that gives one
    value related to it and changes nothing. -/
theorem templ_one {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {x r M bits : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)])
    (hx : F.vm.find? x = some (.var r)) {inst : Inst} (hinst : ∀ g a, inst ≠ .call g a)
    (hrun : (runInst cM envM inst).exec I w = some (.ok ([.int bits M], w))) (hM : M < W)
    {v : H.Val} (hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst) (hfit : v.fits tx = true)
    (hv : VRel g S.z (F.D x) v M) (hok : ValOk hst v)
    (horig : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v) :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], inst⟩] := by
  intro O res hres
  have hM' : M % 2 ^ 256 = M := Nat.mod_eq_of_lt hM
  rw [runBodyO_plain O cM envM _ (by simpa using hinst)] at hres
  simp only [runPlain, Fe.M.exec_bind, hrun] at hres
  simp [Fe.Sonatina.bind] at hres
  subst hres
  refine stepOk_pure1 (m := M) hI hE hA hd hstep hfit
    (fun r' hr' => insert_other fun e => hr' (by simp [e])) ?_ hv hok horig
  rw [hx]; simp only [Option.bind_some, mval]
  rw [Std.TreeMap.getElem?_insert_self]
  simp only [Val.as, Ty.bits, hM']

/-- A pattern with no machine statement: the result's machine operand is an operand's, whose word
    `M` is related to H's value. -/
theorem templ_alias {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {x M : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [(x, tx)]) {a' : Operand}
    (hx : F.vm.find? x = some a') (hM : mval envM a' = some M)
    {v : H.Val} (hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst) (hfit : v.fits tx = true)
    (hv : VRel g S.z (F.D x) v M) (hok : ValOk hst v)
    (horig : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v) :
    TemplOk P I cM S F g hst w envH envM s L' [] := by
  intro O res hres
  simp only [runBodyO, Fe.M.exec_pure, Option.some.injEq] at hres
  subst hres
  exact stepOk_pure1 (m := M) hI hE hA hd hstep hfit (fun _ _ => rfl) (by rw [hx]; exact hM) hv
    hok horig

/-- A statement H finds undefined: whatever the machine does, H halts in `ub`. -/
theorem templ_ub {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L' : List Nat}
    {s : HStmt} (pre : List Stmt) (hstep : stepInst P.ctx I envH hst s.inst = .ub) :
    TemplOk P I cM S F g hst w envH envM s L' pre :=
  fun _ _ _ => Or.inl ⟨.ub, fun _ => ExecBody.ub hstep, Or.inl rfl⟩

/-- A statement H exits with `e`, as the machine's run of its template does. -/
theorem templ_exit {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L' : List Nat}
    {s : HStmt} {pre : List Stmt} {e : Exit World}
    (hstep : stepInst P.ctx I envH hst s.inst = .exit e)
    (hrun : ∀ O, (runBodyO O cM envM pre).exec I w = some (.error e)) :
    TemplOk P I cM S F g hst w envH envM s L' pre := by
  intro O res hres
  rw [hrun O] at hres
  cases hres
  exact Or.inl ⟨_, fun _ => ExecBody.exit hstep, Or.inr (Or.inr ⟨e, rfl, Or.inr (Or.inr
    ⟨.error e, rfl, EndsAs.exit e⟩)⟩)⟩

/-! ## Comparisons -/

theorem CmpOp.inverse_eval {op inv : CmpOp} (h : op.inverse = some inv) (n a b : Nat) :
    op.eval n a b = !inv.eval n a b := by
  cases op <;> cases inv <;> simp [CmpOp.inverse] at h <;> simp only [CmpOp.eval] <;>
    first | rfl | simp [← decide_not, Nat.not_lt, Int.not_lt, Nat.not_le, Int.not_le]

theorem cmp_word {op : CmpOp} {bits : Nat} (hb : bits = 256 ∨ (bits = 1 ∧ op.okI1 = true))
    (a b : Nat) : op.eval bits a b = op.eval 256 a b := by
  rcases hb with rfl | ⟨rfl, h⟩
  · rfl
  · exact CmpOp.okI1_eval h 1 256 a b

theorem ite_lt (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) < W := by
  split <;> norm_num [W]

/-- A comparison: H's step gives the `i1` of the comparison of the operands' words, as the
    machine's `cmp` does, or `is_zero` of the inverse comparison. -/
theorem inst_cmp {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : CmpOp} {a b : Operand} {x : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.cmp op a b)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, tb, htb, hok, a', ha', b', hb', h⟩ := h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hsw, hbits⟩, rfl⟩ := hok
  have hargs : s.inst.args = [a, b] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  have hsw' := hsw
  simp only [sameW, Bool.and_eq_true, beq_iff_eq] at hsw'
  obtain ⟨⟨hva', hvb'⟩, hbab⟩ := hsw'
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta ha' hva'
  obtain ⟨vb, mb0, hvb, hfb, hmb, hwb, hlb⟩ := opnd_word hI hE hA (i := 1) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) htb hb' hvb'
  have hba : va.bits = ta.bits := fits_bits hfa hva'
  have hbb : vb.bits = ta.bits := by rw [fits_bits hfb hvb', hbab]
  have hbits' : va.bits = 256 ∨ (va.bits = 1 ∧ op.okI1 = true) := by rw [hba]; exact hbits
  have hstep : stepInst P.ctx I envH hst s.inst =
      .ok [.int 1 (if op.eval 256 ma mb0 then 1 else 0)] hst := by
    simp only [stepInst, hi, hva, hvb, hba, hbb, beq_self_eq_true, if_true]
    rw [← hba, cmp_word hbits', hwa, hwb]
  have hfit : (H.Val.int 1 (if op.eval 256 ma mb0 then 1 else 0)).fits (.int 1) = true := by
    simp only [H.Val.fits]; split <;> decide
  cases hinv : op.inverse with
  | none =>
    simp only [hinv, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨[_], take1_some ht, rfl, templ_one (bits := 1) hI hE hA hd hx (by simp)
      (by simp [runInst, evalPair, mval_evalInt hma, mval_evalInt hmb, Fe.Sonatina.bool])
      (ite_lt _) hstep hfit rfl trivial trivial⟩
  | some inv =>
    simp only [hinv, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨t, rest1⟩, ht1, ⟨r, rest⟩, ht2, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    have hms := take1_some ht1
    have hms2 := take1_some ht2
    simp only at hms hms2
    refine ⟨[_, _], by rw [hms, hms2]; rfl, rfl, fun O res hres => ?_⟩
    have ht0 : mval (envM.insert t (.int 256 (if inv.eval 256 ma mb0 then 1 else 0))) (.var t) =
        some (if inv.eval 256 ma mb0 then 1 else 0) := by simp [mval]
    rw [runBodyO_plain O cM envM _ (by simp), runPlain_cmp cM hma hmb, runPlain_isZero cM ht0]
      at hres
    simp only [runPlain, Fe.M.exec_pure, Option.some.injEq] at hres
    subst hres
    refine stepOk_pure1 (m := if (if inv.eval 256 ma mb0 then 1 else 0) = 0 then 1 else 0) hI hE
      hA hd hstep hfit (fun r' hr' => ?_) ?_ ?_ trivial trivial
    · simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, or_false] at hr'
      rw [insert_other (Ne.symm hr'.2), insert_other (Ne.symm hr'.1)]
    · rw [hx]; simp [mval]
    · show (if op.eval 256 ma mb0 then 1 else 0) = _
      rw [CmpOp.inverse_eval hinv]
      cases inv.eval 256 ma mb0 <;> rfl

/-! ## Unary operations -/

/-- `is_zero`: H's step gives the `i1` of whether the operand's word is zero. -/
theorem inst_isZero {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {x : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.isZero a)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, hval, a', ha', rfl, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta ha' hval
  have hstep : stepInst P.ctx I envH hst s.inst = .ok [.int 1 (if ma = 0 then 1 else 0)] hst := by
    simp only [stepInst, hi, hva, hwa]; simp
  refine ⟨[_], take1_some ht, rfl, templ_one (bits := 1) hI hE hA hd hx (by simp)
    (by simp [runInst, mval_evalInt hma, Fe.Sonatina.bool]) (ite_lt _) hstep
    (by simp only [H.Val.fits]; split <;> decide) rfl trivial trivial⟩

/-- `not`, `neg`, `clz` (on Osaka), `ctz` of a word: H's step and the machine's agree on the
    operand's word. -/
theorem inst_unary {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty}
    {mk : Operand → Inst} (hmk : mk = .not ∨ mk = .neg ∨ mk = .clz ∨ mk = .ctz)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (mk a)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  have hargs : s.inst.args = [a] := by
    rcases hmk with rfl | rfl | rfl | rfl <;> simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : 0 ∉ nonObserving Dr k s := by
    rcases hmk with rfl | rfl | rfl | rfl <;> simp [nonObserving, hi]
  have hst' : ∀ {f : Operand → Inst}, f = mk →
      stmt c true F.vm s mb ms callee? = (do
        let a' ← mop F.vm a
        let ta ← c.tyOf a
        unless isWord ta && isWord tx do none
        let (r, ms) ← take1 (f a') ms
        let vm ← bindV true F.vm x (.var r)
        some (vm, mb, ms, [r])) := by
    intro f hf; subst hf
    rcases hmk with rfl | rfl | rfl | rfl <;> simp only [stmt, hi, hd] <;> rfl
  rw [hst' rfl] at h
  simp only [bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨a', ha', ta, hta, hok, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hwt, hwx⟩ := hok
  have hval : Ty.value ta = true := by simp only [isWord, Bool.and_eq_true] at hwt; exact hwt.1
  have h256 : ta.bits = 256 := by simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwt; exact hwt.2
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    hno hta ha' hval
  have hbv : va.bits = 256 := by rw [fits_bits hfa hval, h256]
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  have hfit : ∀ n, n < W → (H.Val.int 256 n).fits tx = true := fun n hn => by
    rw [fits_iff hwx'.1]; exact ⟨hwx'.2.symm, by rw [hwx'.2]; exact hn⟩
  refine ⟨[_], take1_some ht, rfl, ?_⟩
  rcases hmk with rfl | rfl | rfl | rfl
  · exact templ_one (bits := 256) (M := 2 ^ 256 - 1 - ma) hI hE hA hd hx (by simp)
      (by simp [runInst, mval_evalInt hma]) (by unfold W; omega)
      (by simp only [stepInst, hi, hva, hbv, hwa]) (hfit _ (by unfold W; omega)) rfl trivial trivial
  · exact templ_one (bits := 256) (M := wrap 256 (-(ma : Int))) hI hE hA hd hx (by simp)
      (by simp [runInst, mval_evalInt hma]) (wrap_lt _ _)
      (by simp only [stepInst, hi, hva, hbv, hwa]) (hfit _ (wrap_lt _ _)) rfl trivial trivial
  · by_cases hos : I.header.fork = .Osaka
    · have hlt : (if ma = 0 then 256 else 256 - 1 - ma.log2) < W := by
        split <;> unfold W <;> omega
      exact templ_one (bits := 256) (M := if ma = 0 then 256 else 256 - 1 - ma.log2) hI hE hA hd
        hx (by simp) (by simp [runInst, mval_evalInt hma, hos]) hlt
        (by simp only [stepInst, hi, hva, hbv, hwa, hos, if_true]) (hfit _ hlt) rfl trivial trivial
    · refine templ_exit (e := .trap) (by simp only [stepInst, hi, hva, hos, if_false]) fun O => ?_
      rw [runBodyO_plain O cM envM _ (by simp)]
      simp [runPlain, runInst, mval_evalInt hma, hos, trap]
  · have hlt : ((List.range 256).find? ma.testBit).getD 256 < W := by
      cases h : (List.range 256).find? ma.testBit with
      | none => unfold W; simp
      | some n =>
        have := List.mem_range.mp (List.mem_of_find?_eq_some h)
        simp only [Option.getD_some]; unfold W; omega
    exact templ_one (bits := 256) (M := ((List.range 256).find? ma.testBit).getD 256) hI hE hA hd hx
      (by simp) (by simp [runInst, mval_evalInt hma]) hlt
      (by simp only [stepInst, hi, hva, hbv, hwa]) (hfit _ hlt) rfl trivial trivial

/-! ## Saturating and overflowing operations, `black_box`, symbols -/

theorem fits_word {t : Ty} (h : isWord t = true) {n : Nat} (hn : n < W) :
    (H.Val.int 256 n).fits t = true := by
  simp only [isWord, Bool.and_eq_true, beq_iff_eq] at h
  rw [fits_iff h.1]; exact ⟨h.2.symm, by rw [h.2]; exact hn⟩

theorem sameW_symm {t u : Ty} (h : sameW t u = true) : sameW u t = true := by
  simp only [sameW, Bool.and_eq_true, beq_iff_eq] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, h.2.symm⟩

theorem VRel.mono {g : Ghost} {z da db : Bool} {v : H.Val} {m : Nat} (h : VRel g z da v m)
    (hd : z = true → da = true → db = true) : VRel g z db v m := by
  cases v with
  | int => exact h
  | ptr b o => exact ⟨h.1, fun hz => hd hz (h.2 hz)⟩

theorem sat_lt (op : SatOp) {bits : Nat} (hb : bits ≤ 256) (x y : Nat) : op.eval bits x y < W := by
  have h1 : 2 ^ bits ≤ W := Nat.pow_le_pow_right (by norm_num) hb
  have hp : 0 < 2 ^ bits := Nat.two_pow_pos _
  have h2 : 2 ^ bits - 1 < W := lt_of_lt_of_le (Nat.sub_lt hp Nat.one_pos) h1
  cases op <;> simp only [SatOp.eval]
  all_goals first
    | exact wrap_lt _ _
    | (split
       · exact Nat.two_pow_pos 256
       · exact lt_of_le_of_lt (Nat.min_le_right _ _) h2)

/-- A saturating operation at an integer type: H and the machine compute it on the operands'
    words. -/
theorem inst_sat {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : SatOp} {a b : Operand} {t : Ty}
    {x : Nat} {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.sat op a b t)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, tb, htb, hc, a', ha', b', hb', hwx, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl,
    rfl, rfl⟩ := h
  have hargs : s.inst.args = [a, b] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨n, rfl⟩ : ∃ n, t = .int n := by cases t <;> simp at hc ⊢
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hva', hvb'⟩, -⟩, hvt⟩ := hc
  obtain ⟨va, ma, hva, -, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta ha' hva'
  obtain ⟨vb, mb0, hvb, -, hmb, hwb, hlb⟩ := opnd_word hI hE hA (i := 1) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) htb hb' hvb'
  have hn : n ≤ 256 := by simpa [Ty.bits] using (value_bits hvt).2
  have hlt := sat_lt op hn ma mb0
  exact ⟨[_], take1_some ht, rfl, templ_one (bits := 256) (M := op.eval n ma mb0) hI hE hA hd hx
    (by simp) (by simp [runInst, mval_evalInt hma, mval_evalInt hmb, Ty.bits]) hlt
    (by simp [stepInst, hi, hva, hvb, hwa, hwb, hvt, Ty.bits]) (fits_word hwx hlt) rfl trivial
    trivial⟩

theorem take0_some {inst : Inst} {ms rest : List Stmt} (h : take0 inst ms = some rest) :
    ms = ⟨[], inst⟩ :: rest := by
  unfold take0 at h
  split at h
  · next i rest' =>
    split at h
    · next he => cases h; rw [beq_iff_eq.mp he]
    · cases h
  · cases h

theorem takeN_some {inst : Inst} {n : Nat} {ms rest : List Stmt} {rs : List Nat}
    (h : takeN inst n ms = some (rs, rest)) :
    ∃ ds', ms = ⟨ds', inst⟩ :: rest ∧ ds'.length = n ∧ (∀ d ∈ ds', d.2 = .int 256) ∧
      rs = ds'.map (·.1) := by
  unfold takeN at h
  split at h
  · next ds' i rest' =>
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ds', by rw [hc.1.1], hc.1.2, fun d hd => by simpa [w256] using hc.2 d hd, rfl⟩
    · cases h
  · cases h

theorem ovf_lt (op : OvfOp) (x y : Nat) : (op.eval 256 x y).1 < W := by
  cases op <;> simp only [OvfOp.eval] <;> exact wrap_lt _ _

/-- A statement H steps without changing its state, to two values related to the machine values
    its template binds. -/
theorem stepOk_pure2 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM envM' : Env} {L L' : List Nat} {c : FCtx}
    {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {x y : Nat} {tx ty : Ty}
    (hd : s.dsts = [(x, tx), (y, ty)]) {v1 v2 : H.Val}
    (hstep : stepInst P.ctx I envH hst s.inst = .ok [v1, v2] hst) (hf1 : v1.fits tx = true)
    (hf2 : v2.fits ty = true) (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {m1 m2 : Nat}
    (hm1 : (F.vm.find? x).bind (mval envM') = some m1)
    (hm2 : (F.vm.find? y).bind (mval envM') = some m2)
    (hv1 : VRel g S.z (F.D x) v1 m1) (hv2 : VRel g S.z (F.D y) v2 m2)
    (ho1 : ValOk hst v1) (ho2 : ValOk hst v2)
    (hg1 : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v1)
    (hg2 : OrigOk g hst F.R F.fpf (origOf F.O (.var y)) v2) :
    StepOk P I S F g hst envH s L' (.ok (envM', w)) := by
  have hxy : x ≠ y := by have := hA.nodup; rw [hd] at this; simpa using this
  have hb : bindVals envH s.dsts [v1, v2] = some ((envH.insert x v1).insert y v2) := by
    simp [bindVals, hd, hf1, hf2]
  have hdefs : s.defs = [x, y] := by simp [HStmt.defs, hd]
  have hdt1 : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  have hdt2 : F.decls.find? y = some ty := hA.dsts (y, ty) (by simp [hd])
  refine Or.inr ⟨envM', w, rfl, _, hst, g, hI, ?_, GhostLe.refl _ _ _,
    fun rest o hr => ExecBody.step hstep hb hr⟩
  refine envRel_step hE (fun z hz hn => hA.keep z hz (by rw [hdefs]; rwa [hd] at hn)) hb hkeep
    (fun z hz hn => hA.clob z (Or.inr hz) (by rw [hdefs]; rwa [hd] at hn)) (fun _ h => h)
    (fun _ _ h => h) ?_
  intro z hz _
  simp only [hd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact ⟨v1, m1, by rw [Std.TreeMap.getElem?_insert]; simp [Ne.symm hxy], ⟨tx, hdt1, hf1⟩, hm1,
      hv1, ho1, hg1⟩
  · exact ⟨v2, m2, by simp, ⟨ty, hdt2, hf2⟩, hm2, hv2, ho2, hg2⟩

/-- An overflowing operation on words: the wrapped result and the flag, on the operands'
    words. -/
theorem inst_ovf {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : OvfOp} {a b : Operand}
    {x y : Nat} {tx ty : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hnd : ((ms.flatMap (·.dsts)).map (·.1)).Nodup)
    (hi : s.inst = .base (.ovf op a b)) (hd : s.dsts = [(x, tx), (y, ty)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, tb, htb, hc, a', ha', b', hb', ⟨rs, rest⟩, htk, h⟩ := h
  obtain ⟨ds', hms, hlen, hty, rfl⟩ := takeN_some htk
  obtain ⟨⟨r1, t1⟩, ⟨r2, t2⟩, rfl⟩ : ∃ d1 d2, ds' = [d1, d2] := by
    match ds', hlen with
    | [d1, d2], _ => exact ⟨d1, d2, rfl⟩
  have e1 : t1 = .int 256 := hty (r1, t1) (by simp)
  have e2 : t2 = .int 256 := hty (r2, t2) (by simp)
  subst e1 e2
  simp only [List.map_cons, List.map_nil, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, ⟨hx, rfl⟩, _, ⟨hy, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  have hr12 : r1 ≠ r2 := by
    rw [hms] at hnd; simp at hnd; exact hnd.1.1
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hwa', hwb'⟩, hwx⟩, rfl⟩ := hc
  have hargs : s.inst.args = [a, b] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  have hva' : Ty.value ta = true := by simp only [isWord, Bool.and_eq_true] at hwa'; exact hwa'.1
  have hvb' : Ty.value tb = true := by simp only [isWord, Bool.and_eq_true] at hwb'; exact hwb'.1
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta ha' hva'
  obtain ⟨vb, mb0, hvb, hfb, hmb, hwb, hlb⟩ := opnd_word hI hE hA (i := 1) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) htb hb' hvb'
  have hba : va.bits = 256 := by
    rw [fits_bits hfa hva']; simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwa'; exact hwa'.2
  have hbb : vb.bits = 256 := by
    rw [fits_bits hfb hvb']; simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwb'; exact hwb'.2
  refine ⟨[_], hms, rfl, fun O res hres => ?_⟩
  rw [runBodyO_plain O cM envM _ (by simp)] at hres
  simp [runPlain, runInst, evalPair, mval_evalInt hma, mval_evalInt hmb, Fe.Sonatina.bind,
    Fe.Sonatina.bool, Val.as, Ty.bits] at hres
  subst hres
  have hR := ovf_lt op ma mb0
  refine stepOk_pure2 (m1 := (op.eval 256 ma mb0).1)
    (m2 := if (op.eval 256 ma mb0).2 then 1 else 0) (v1 := .int 256 (op.eval 256 ma mb0).1)
    (v2 := .int 1 (if (op.eval 256 ma mb0).2 then 1 else 0)) hI hE hA hd
    (by simp [stepInst, hi, hva, hvb, hba, hbb, hwa, hwb]) (fits_word hwx hR)
    (by simp only [H.Val.fits]; split <;> decide) (fun r' hr' => ?_) ?_ ?_ rfl rfl trivial trivial
    trivial trivial
  · simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, or_false] at hr'
    rw [insert_other (Ne.symm hr'.2), insert_other (Ne.symm hr'.1)]
  · have hR' : (op.eval 256 ma mb0).1 %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        (op.eval 256 ma mb0).1 := Nat.mod_eq_of_lt hR
    rw [hx]; simp only [Option.bind_some, mval]
    rw [insert_other (Ne.symm hr12), Std.TreeMap.getElem?_insert_self]
    simp [hR']
  · rw [hy]; simp only [Option.bind_some, mval]
    rw [Std.TreeMap.getElem?_insert_self]
    cases hf : (op.eval 256 ma mb0).2 <;> simp

/-- `black_box v`: H's value is `v` itself, origin included (I7); the machine's its word. -/
theorem inst_blackBox {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.blackBox a)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨a', ha', ta, hta, hsw, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) hta ha'
  have hval : Ty.value ta = true := by simp only [sameW, Bool.and_eq_true] at hsw; exact hsw.1.1
  have hlt := vrel_lt hra hfa hval
  refine ⟨[_], take1_some ht, rfl, templ_one (bits := 256) (M := ma) hI hE hA hd hx (by simp)
    (by simp [runInst, mval_eval hma]) hlt (by simp [stepInst, hi, hva])
    (fits_sameW (sameW_symm hsw) hfa) ?_ hoa ?_⟩
  · refine VRel.mono hra fun hz hda => ?_
    rw [hA.D]
    refine hA.der hz ?_ x (by simp [HStmt.defs, hd])
    rw [hA.dOp] at hda
    simp [stmtDerived, hi, hda]
  · exact OrigOk.mono hga fun o ho => hA.orig x tx hd o (by simp [stmtOrig, hi, ho])

/-- `sym_addr`: the section's symbol table, which H and the machine read alike. -/
theorem inst_symAddr {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {sym : String} {x : Nat} {tx : Ty}
    (hsym : c.symbols = P.symbols) (hcM : cM.symbol = fun s => P.symbols.lookup s)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.symAddr sym)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨⟨off, sz⟩, hl, hc, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [hsym] at hl
  exact ⟨[_], take1_some ht, rfl, templ_one (bits := 256) (M := off) hI hE hA hd hx (by simp)
    (by simp [runInst, hcM, hl]) hc.2 (by simp [stepInst, hi, HSection.ctx, hl])
    (fits_word hc.1 hc.2) rfl trivial trivial⟩

/-- `sym_size`: as `sym_addr`. -/
theorem inst_symSize {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {sym : String} {x : Nat} {tx : Ty}
    (hsym : c.symbols = P.symbols) (hcM : cM.symbol = fun s => P.symbols.lookup s)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.symSize sym)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨⟨off, sz⟩, hl, hc, ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [hsym] at hl
  exact ⟨[_], take1_some ht, rfl, templ_one (bits := 256) (M := sz) hI hE hA hd hx (by simp)
    (by simp [runInst, hcM, hl]) hc.2 (by simp [stepInst, hi, HSection.ctx, hl])
    (fits_word hc.1 hc.2) rfl trivial trivial⟩

/-- `trunc_nuw a T`: an alias of `a`'s machine value; H gives the word at `T` if it fits, else
    `ub`. -/
theorem inst_truncNuw {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {t : Ty} {x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .truncNuw a t) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, hc, a', ha', _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, t = .int n := by cases t <;> simp at hc ⊢
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hva', -⟩, hvt⟩, hsw⟩ := hc
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta ha' hva'
  refine ⟨[], rfl, rfl, ?_⟩
  by_cases hlt : ma < 2 ^ n
  · exact templ_alias (M := ma) (v := .int n ma) hI hE hA hd hx hma
      (by simp [stepInst, hi, hva, hwa, hvt, hlt, Ty.bits])
      (fits_sameW hsw (by simp [H.Val.fits, hlt])) rfl trivial trivial
  · exact templ_ub [] (by simp [stepInst, hi, hva, hwa, hvt, hlt, Ty.bits])

/-! ## Casts -/

theorem castVal_ptr {st : H.State} {op : CastOp} {x : H.Val} {t : Ty} {b o : Nat}
    (h : castVal st op x t = some (.ptr b o)) : x = .ptr b o ∧ keepsPtr op t = true := by
  unfold castVal at h
  split at h
  · cases h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq, H.Val.ptr.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

theorem castVal_keep (st : H.State) {op : CastOp} {b o : Nat} {t : Ty}
    (h : keepsPtr op t = true) : castVal st op (.ptr b o) t = some (.ptr b o) := by
  cases op <;> cases t <;> simp_all [keepsPtr, castVal, Ty.value, widths]
  all_goals (split at h <;> simp_all)

theorem keepsPtr_bits {op : CastOp} {t : Ty} (h : keepsPtr op t = true) : t.bits = 256 := by
  cases op <;> cases t <;> simp_all [keepsPtr, Ty.bits]
  all_goals (split at h <;> simp_all)

theorem castKeep_256 {op : CastOp} {ta t : Ty} {k : Nat} (h : castKeep op ta t = some k)
    (ha : ta.bits = 256) (ht : t.bits = 256) : k = 256 := by
  unfold castKeep at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [hc.1] at ha; simp [Ty.bits] at ha
    · simp only [Option.some.injEq] at h; rw [← h, ha, ht]; rfl

theorem stmtDerived_cast {D : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat}
    {op : CastOp} {a : Operand} {t : Ty} (hi : s.inst = .base (.cast op a t))
    (hk : keepsPtr op t = true) (hd : D.op k a = true) : stmtDerived D k s callee? = true := by
  simp only [stmtDerived, hi]
  cases op <;> cases t <;> simp_all [keepsPtr, isWord, Ty.value, Ty.bits, widths]
  all_goals (split at hk <;> simp_all)

theorem stmtOrig_cast {fr : FuncRec} {O : Orig} {s : HStmt} {op : CastOp} {a : Operand} {t : Ty}
    (hi : s.inst = .base (.cast op a t)) (hk : keepsPtr op t = true) :
    stmtOrig fr O s = origOf O a := by
  simp only [stmtOrig, hi]
  cases op <;> cases t <;> simp_all [keepsPtr]
  all_goals (split at hk <;> simp_all)

/-- A cast (`castKeep`): an alias of the operand's machine value, or its low `k` bits by an
    `and`.  H's value is the operand itself when the cast keeps a pointer, else an integer whose
    word is the operand's low `k` bits. -/
theorem inst_cast {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : CastOp} {a : Operand} {t : Ty}
    {x : Nat} {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.cast op a t)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨ta, hta, hc, kk, hk, a', ha', h⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hva', hvt⟩, hsw⟩ := hc
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) hta ha'
  have hla := vrel_lt hra hfa hva'
  -- H's step.
  have hval : ∃ v, castVal hst op va t = some v := by
    unfold castVal; rw [show (!Ty.value t) = false by simp [hvt]]; simp only [Bool.false_eq_true,
      if_false]; split <;> exact ⟨_, rfl⟩
  obtain ⟨v, hcv⟩ := hval
  obtain ⟨hwv, hfv⟩ := castVal_word hcv hk hfa hva'
  have hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst := by simp [stepInst, hi, hva, hcv]
  -- The value is related to the operand's low `kk` bits.
  have hrel : VRel g S.z (F.D x) v (ma % 2 ^ kk) := by
    cases v with
    | int bits n =>
      show n = ma % 2 ^ kk
      rw [word_int] at hwv
      rw [hwv]
      congr 1
      cases va with
      | int => exact hra
      | ptr b o =>
        cases hz : S.z
        · exact vrel_word hI hra hoa (Or.inl hz)
        · exfalso
          have hda := hra.2 hz
          rw [hA.dOp] at hda
          have h0 := hA.obs hz 0 a (by rw [hargs]; rfl) hda
          simp only [nonObserving, hi] at h0
          split at h0
          · next hkp => rw [castVal_keep hst hkp] at hcv; cases hcv
          · simp at h0
    | ptr b' o' =>
      obtain ⟨rfl, hkp⟩ := castVal_ptr hcv
      have hk256 : kk = 256 := castKeep_256 hk (fits_ptr hfa).2 (keepsPtr_bits hkp)
      subst hk256
      refine ⟨by rw [hra.1, Nat.mod_eq_of_lt hla], fun hz => ?_⟩
      rw [hA.D]
      have hda := hra.2 hz
      rw [hA.dOp] at hda
      exact hA.der hz (stmtDerived_cast hi hkp hda) x (by simp [HStmt.defs, hd])
  have hok : ValOk hst v := by
    cases v with
    | int => trivial
    | ptr b' o' => obtain ⟨rfl, _⟩ := castVal_ptr hcv; exact hoa
  have horig : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v := by
    cases v with
    | int => trivial
    | ptr b' o' =>
      obtain ⟨rfl, hkp⟩ := castVal_ptr hcv
      exact OrigOk.mono hga fun o ho => hA.orig x tx hd o (by rw [stmtOrig_cast hi hkp]; exact ho)
  have hfx : v.fits tx = true := fits_sameW hsw hfv
  split at h
  · next hk256 =>
    subst hk256
    simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨_, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨[], rfl, rfl, templ_alias (M := ma) hI hE hA hd hx hma hstep hfx ?_ hok horig⟩
    rwa [Nat.mod_eq_of_lt hla] at hrel
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    have hlt : ma % 2 ^ kk < W := lt_of_le_of_lt (Nat.mod_le _ _) hla
    refine ⟨[_], take1_some ht, rfl, templ_one (bits := 256) (M := ma % 2 ^ kk) hI hE hA hd hx
      (by simp) ?_ hlt hstep hfx hrel hok horig⟩
    have hm2 : mval envM (imm (2 ^ kk - 1)) = some (2 ^ kk - 1) := by simp [mval, imm]
    simp [runInst, evalPair, mval_evalInt hma, mval_evalInt hm2, BinOp.eval,
      Nat.and_two_pow_sub_one_eq_mod]

end Fe.Sonatina.Stage3.Place
