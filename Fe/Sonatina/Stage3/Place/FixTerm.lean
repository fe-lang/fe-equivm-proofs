import Fe.Sonatina.Stage3.Place.FixSite

/-!
# After a terminal fixed buffer: terminators

Rule S6 allows after the site only jumps and branches (to blocks after the site), halts without
data, the memory-free terminals `evm_return_code` and `evm_revert_word`, and
`evm_return`/`evm_revert` of the buffer or of nothing.  Each ends as H's (`FnUnp.sfxTermBase`,
`FnUnp.sfxTermCode`, `FnUnp.sfxTermWord`): H halts in an outcome that excuses the machine's
result, or both go to the same successor.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- A terminator operand after the site: its H value and its machine word, related. -/
theorem FnUnp.sfxOpnd {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {kt base n t : Nat} {g : Ghost} {hst : H.State} {w : World} {envH : HEnv}
    {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b b.body.length (fn.live b b.body.length) g hst w envH envM)
    {a : Operand} (ha : a ∈ b.term.skel.args) {ta : Ty} (ht : fn.c.tyOf a = some ta)
    (hval : Ty.value ta = true) {a' : Operand} (hm : mop fn.F.vm a = some a') :
    ∃ v m, evalOp envH a = some v ∧ mval envM a' = some m ∧ m < W ∧
      VRel (vG g hst) (secS src r efp).z (fn.F.dOp a) v m ∧ ValOk (vSt hst w kt n base) v ∧
      (((secS src r efp).z = true → fn.F.dOp a = false) → hst.word v = m) := by
  have hdecl : (vF fn.F (fn.live b b.body.length)).decls = fn.c.decls := by rw [U.hF, U.hc]; rfl
  obtain ⟨v, m, h1, h2, h3, h4, h5, -⟩ := opnd_rel (hR.envRel (fun x hx => hx)) hdecl rfl
    (fun y hy => by
      rw [U.liveEnd hb, mem_nset]
      refine List.mem_append_left _ ?_
      unfold HTerm.uses varsOf
      exact List.mem_filterMap.mpr ⟨a, ha, by rw [hy]⟩) ht hm
  refine ⟨v, m, h1, h3, vrel_lt h4 h2 hval, h4, h5, fun hobs => ?_⟩
  have := vrel_exact hR.inv h4 h5 hobs
  rwa [vSt_word] at this

/-- Rule S8 at a terminator: in address-0 mode no derived operand of a terminator other than
    `return`, `evm_return` and `evm_revert` is observed; of those two, the length. -/
theorem FnUnp.termObs {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) (hz : (secS src r efp).z = true) :
    (∀ t, b.term = .base t → (∀ a' l', t ≠ .evmReturn a' l' ∧ t ≠ .evmRevert a' l') →
      (∀ vs, t ≠ .ret vs) → ∀ a ∈ t.args, fn.F.dOp a = false) ∧
    (∀ a l, (b.term = .base (.evmReturn a l) ∨ b.term = .base (.evmRevert a l)) →
      fn.F.dOp l = false) ∧
    (∀ o l, b.term = .returnCode o l → fn.F.dOp o = false ∧ fn.F.dOp l = false) := by
  have h := U.rules.s8 hz
  simp only [notObserved, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h b hb).2
  refine ⟨fun t ht hnr hnret a ha => ?_, fun a l hal => ?_, fun o l ht => ?_⟩
  · rw [U.dOp]
    rw [ht] at h1
    cases t
    all_goals first
      | (exact absurd rfl (hnret _))
      | (exact absurd rfl (hnr _ _).1)
      | (exact absurd rfl (hnr _ _).2)
      | (simp only [List.any_eq_false, Bool.not_eq_true', Bool.not_eq_true] at h1
         simpa using h1 a ha)
  · rw [U.dOp]
    rcases hal with ht | ht <;> rw [ht] at h1 <;>
      (simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1; exact h1.1)
  · rw [ht] at h1
    simp only [HTerm.skel, Term.args, List.any_eq_false, Bool.not_eq_true'] at h1
    rw [U.dOp, U.dOp]
    exact ⟨by simpa using h1 o (by simp), by simpa using h1 l (by simp)⟩

/-- How a terminator after the site ends against the machine's: H halts excusing it, or both go
    to the same successor (the machine to the block map's image). -/
def TGoal (I : Fe.EVM.Env) (fn : Fn) (b : HBlock) (envH : HEnv) (hst : H.State) (envM : Env)
    (w : World) (res : Except (Exit World) (Next × World)) : Prop :=
  (∃ o, stepTerm I envH hst b.term = .halt o ∧ Excuses o res) ∨
  ∃ d d', res = .ok (.goto envM d', w) ∧ stepTerm I envH hst b.term = .goto d ∧
    fn.c.bm.find? d = some d' ∧ d ∈ b.term.succs

/-- The data `evm_return`/`evm_revert` of the buffer, or of nothing, read: the machine's bytes
    are H's, or H is `ub`. -/
theorem FnUnp.sfxData {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {kt base n t : Nat} {g : Ghost} {hst : H.State} {w : World} {envH : HEnv}
    {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b b.body.length (fn.live b b.body.length) g hst w envH envM)
    {a l : Operand} (ha : a ∈ b.term.skel.args) (hl : l ∈ b.term.skel.args)
    (hta : (fn.c.tyOf a).any Ty.value = true) (htl : (fn.c.tyOf l).any Ty.value = true)
    (hlobs : (secS src r efp).z = true → fn.F.dOp l = false)
    (hok : fixInM (fixM fn.f t) a = true ∨ isZeroImm l = true) {a' l' : Operand}
    (hma : mop fn.F.vm a = some a') (hml : mop fn.F.vm l = some l') :
    ∃ x nv ma ml, evalOp envH a = some x ∧ evalOp envH l = some nv ∧ mval envM a' = some ma ∧
      mval envM l' = some ml ∧ ma < W ∧ ml < W ∧ hst.word nv = ml ∧
      ∀ rr, hst.range x ml = some rr → hst.bytes rr ml = w.memory.readWithPadding ma ml := by
  obtain ⟨ta, hta', hva⟩ := tyOf_any hta
  obtain ⟨tl, htl', hvl⟩ := tyOf_any htl
  obtain ⟨x, ma, hx, hmx, hmaW, hvx, -, -⟩ := U.sfxOpnd hb hR ha hta' hva hma
  obtain ⟨nv, ml, hn, hmn, hmlW, -, -, hwn⟩ := U.sfxOpnd hb hR hl htl' hvl hml
  refine ⟨x, nv, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, hwn hlobs, fun rr hr => ?_⟩
  by_cases h0 : ml = 0
  · subst h0
    simp only [State.range, if_true, Option.some.injEq] at hr
    subst hr
    rw [readWithPadding_of_mem (l := []) (n := 0) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))]
    rfl
  · have hinM : fixInM (fixM fn.f t) a = true := by
      rcases hok with h | h
      · exact h
      · exfalso
        cases l with
        | var => simp [isZeroImm] at h
        | imm bits v =>
          cases v with
          | succ => simp [isZeroImm] at h
          | zero =>
            simp only [mop, Option.some.injEq] at hml
            subst hml
            simp [mval] at hmn
            exact h0 hmn.symm
    obtain ⟨y, rfl⟩ : ∃ y, a = .var y := by
      cases a with
      | var y => exact ⟨y, rfl⟩
      | imm => simp [fixInM] at hinM
    obtain ⟨o, rfl⟩ := hR.must y (by simpa [fixInM] using hinM) x hx
    rw [hR.range h0] at hr
    split at hr
    · next hw =>
      simp only [Option.some.injEq] at hr
      subst hr
      have hma' : (base + o) % W = ma := by have := hvx.1; simp only [vG] at this; rwa [hR.jt] at this
      have hbn := hR.bn
      rw [← hma', Nat.mod_eq_of_lt (by omega)]
      refine (bytes_of_agree hR.hkt fun i hi => ?_).symm
      rw [show base + o + i = base + (o + i) by omega]
      exact hR.buf (o + i) (by omega)
    · cases hr

theorem FnUnp.sfxTermBase {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks) {tm : Term} (ht : b.term = .base tm)
    {mt : Term} (hmt : mapTerm fn.c fn.F.vm fn.f.rets tm = some mt) {t : Nat} {O' : Orig}
    (htm : fixTermOk O' (fixM fn.f t) t b.term = true) {kt base n : Nat} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b b.body.length (fn.live b b.body.length) g hst w envH envM)
    {res : Except (Exit World) (Next × World)} (hres : (runTerm envM mt).exec I w = some res) :
    TGoal I fn b envH hst envM w res := by
  have hobs : (secS src r efp).z = true → ∀ a ∈ tm.args,
      (∀ a' l', tm ≠ .evmReturn a' l' ∧ tm ≠ .evmRevert a' l') → (∀ vs, tm ≠ .ret vs) →
      fn.F.dOp a = false := fun hz a ha h1 h2 => (U.termObs hb hz).1 tm ht h1 h2 a ha
  unfold TGoal
  rw [ht]
  cases tm with
  | jump d =>
    simp only [mapTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hmt
    obtain ⟨d', hd', rfl⟩ := hmt
    simp only [runTerm, Fe.M.exec_pure, Option.some.injEq] at hres
    subst hres
    exact Or.inr ⟨d, d', rfl, by simp [stepTerm], hd', by simp [HTerm.succs, Term.succs]⟩
  | evmStop =>
    simp only [mapTerm, Option.pure_def, Option.some.injEq] at hmt
    subst hmt
    simp only [runTerm, stopCall, Fe.M.stop, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_fail] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    exact Or.inl ⟨_, rfl, excuses_stop hR.world⟩
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
    obtain ⟨v, m, hev, hmv, -, -, -, hw⟩ := U.sfxOpnd hb hR (a := cnd)
      (by rw [ht]; simp [HTerm.skel, Term.args]) hta hval hc'
    have hw := hw fun hz => hobs hz cnd (by simp [Term.args]) (by intro a' l'; simp) (by intro vs; simp)
    simp only [runTerm, mval_evalInt hmv, pure_bind, Fe.M.exec_pure, Option.some.injEq] at hres
    subst hres
    by_cases hm0 : m = 0
    · exact Or.inr ⟨z, z', by simp [hm0], by simp [stepTerm, hev, hw, hm0], hz,
        by simp [HTerm.succs, Term.succs]⟩
    · exact Or.inr ⟨nz, nz', by simp [hm0], by simp [stepTerm, hev, hw, hm0], hnz,
        by simp [HTerm.succs, Term.succs]⟩
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
      have hcase : ∀ x ∈ cases, ∀ o', mop fn.F.vm x.1 = some o' → ∃ v m, evalOp envH x.1 = some v ∧
          mval envM o' = some m ∧ hst.word v = m := by
        intro x hx o' ho'
        obtain ⟨tx, htx, hvx⟩ := tyOf_any (hc.2 x hx)
        have hxa : x.1 ∈ (Term.brTable sc (some d) cases).args := by
          simp only [Term.args]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hx)
        obtain ⟨v, m, hev, hmv, -, -, -, hw⟩ := U.sfxOpnd hb hR (a := x.1)
          (by rw [ht]; exact hxa) htx hvx ho'
        exact ⟨v, m, hev, hmv, hw fun hz =>
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
            obtain ⟨_, _, _, _, h3, _⟩ := hR.vals y (by
              rw [U.liveEnd hb, mem_nset]
              refine List.mem_append_left _ ?_
              rw [ht]; simp [HTerm.uses, HTerm.skel, Term.args, varsOf])
            cases e : fn.F.vm.find? y with
            | none => rw [e] at h3; cases h3
            | some o => exact ⟨o, e⟩
        obtain ⟨v, m, hev, -, -, -, -, -⟩ := U.sfxOpnd hb hR (a := sc)
          (by rw [ht]; simp [HTerm.skel, Term.args]) hts hvts hsc'
        exact Or.inr ⟨d, d', rfl, by simp [stepTerm, hev], hd', by simp [HTerm.succs, Term.succs]⟩
      · obtain ⟨sc', hsc', hmt⟩ := Option.bind_eq_some_iff.mp hmt
        obtain rfl : Term.brTable sc' (some d') cases' = mt := by simpa using hmt
        obtain ⟨ts, hts, hvts⟩ := tyOf_any hc.1
        obtain ⟨v, m, hev, hmv, -, -, -, hw⟩ := U.sfxOpnd hb hR (a := sc)
          (by rw [ht]; simp [HTerm.skel, Term.args]) hts hvts hsc'
        have hw := hw fun hz =>
          hobs hz sc (by simp [Term.args]) (by intro a' l'; simp) (by intro vs; simp)
        simp only [runTerm, mval_evalInt hmv, hvM, pure_bind] at hres
        rcases find_rel m hrel with ⟨p, q, hp, hq, hpq⟩ | ⟨hp, hq⟩
        · rw [hq] at hres
          have hres' : (pure (Next.goto envM q.2) : FeM Next).exec I w = some res := hres
          simp only [Fe.M.exec_pure, Option.some.injEq] at hres'
          subst hres'
          exact Or.inr ⟨p.2, q.2, rfl, by simp [stepTerm, hev, hvH, hw, hp], hpq,
            by simp only [HTerm.succs, Term.succs]
               exact List.mem_append_right _ (hmem p (List.mem_of_find?_eq_some hp))⟩
        · rw [hq] at hres
          have hres' : (pure (Next.goto envM d') : FeM Next).exec I w = some res := hres
          simp only [Fe.M.exec_pure, Option.some.injEq] at hres'
          subst hres'
          exact Or.inr ⟨d, d', rfl, by simp [stepTerm, hev, hvH, hw, hp], hd',
            by simp [HTerm.succs, Term.succs]⟩
    · cases hmt
  | ret vs => simp [fixTermOk, ht] at htm
  | evmSelfDestruct a => simp [fixTermOk, ht] at htm
  | evmReturn a l =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨⟨hta, htl⟩, a', ha', l', hl', rfl⟩ := hmt
    have hok : fixInM (fixM fn.f t) a = true ∨ isZeroImm l = true := by
      simpa [fixTermOk, ht] using htm
    obtain ⟨x, nv, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, hwn, hdat⟩ := U.sfxData hb hR
      (by rw [ht]; simp [HTerm.skel, Term.args]) (by rw [ht]; simp [HTerm.skel, Term.args]) hta htl
      (fun hz => (U.termObs hb hz).2.1 a l (Or.inl ht)) hok ha' hl'
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
      exact excuses_stop hR.world
  | evmRevert a l =>
    simp [mapTerm, Option.bind_eq_some_iff] at hmt
    obtain ⟨⟨hta, htl⟩, a', ha', l', hl', rfl⟩ := hmt
    have hok : fixInM (fixM fn.f t) a = true ∨ isZeroImm l = true := by
      simpa [fixTermOk, ht] using htm
    obtain ⟨x, nv, ma, ml, hx, hn, hmx, hmn, hmaW, hmlW, hwn, hdat⟩ := U.sfxData hb hR
      (by rw [ht]; simp [HTerm.skel, Term.args]) (by rw [ht]; simp [HTerm.skel, Term.args]) hta htl
      (fun hz => (U.termObs hb hz).2.1 a l (Or.inr ht)) hok ha' hl'
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

/-- `evm_return_code` after the site: the machine copies the code to 0 and returns it; H
    returns the code. -/
theorem FnUnp.sfxTermCode {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) (cM : Ctx) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {o l : Operand} (ht : b.term = .returnCode o l) {ms : List Stmt} {mt : Term}
    (hto : termOk fn.c fn.F.vm fn.f.rets b.term ms mt = true) (O : Oracle) {kt base n t : Nat}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b b.body.length (fn.live b b.body.length) g hst w envH envM)
    {res : Except (Exit World) (Next × World)}
    (hres : (runBodyO O cM envM ms >>= fun e => runTerm e mt).exec I w = some res) :
    ∃ o', stepTerm I envH hst b.term = .halt o' ∧ Excuses o' res := by
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
      obtain ⟨tO, hto', hvo⟩ := tyOf_any hc.1
      obtain ⟨tl, htl', hvl⟩ := tyOf_any hc.2
      obtain ⟨x, mo, hx, hmo, hmoW, -, -, hwx⟩ := U.sfxOpnd hb hR (a := o)
        (by rw [ht]; simp [HTerm.skel, Term.args]) hto' hvo ho'
      obtain ⟨nv, ml, hn, hml, hmlW, -, -, hwn⟩ := U.sfxOpnd hb hR (a := l)
        (by rw [ht]; simp [HTerm.skel, Term.args]) htl' hvl hl'
      have hwx := hwx fun hz => ((U.termObs hb hz).2.2 o l ht).1
      have hwn := hwn fun hz => ((U.termObs hb hz).2.2 o l ht).2
      rw [runBodyO_plain O cM envM _ (by simp)] at hres
      have h0 : evalWord envM (Operand.imm 256 0) = pure (Ethereum.UInt256.ofNat 0) :=
        mval_evalWord (by simp [mval])
      have h0' : (Ethereum.UInt256.ofNat 0).toNat = 0 := toNat_ofNat_lt (by unfold W; norm_num)
      simp [h0, h0', runPlain, runInst, EvmOp.run, Fe.EVM.codecopy, mval_evalWord hmo,
        mval_evalWord hml, toNat_ofNat_lt hmoW, toNat_ofNat_lt hmlW, Fe.Sonatina.bind, runTerm,
        returnData, Fe.M.stop, imm, mval, read_write_zero] at hres
      subst hres
      refine ⟨.ends (.error (.stop (I.code.readWithPadding mo ml) hst.world)),
        by simp [stepTerm, ht, hx, hn, hwx, hwn], ?_⟩
      exact excuses_stop hR.world
    · simp at hto
  · simp at hto

/-- `evm_revert_word` after the site: the machine stores the selector word at 0 and the word at
    4 and reverts with them; H reverts with the same 36 bytes. -/
theorem FnUnp.sfxTermWord {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) (cM : Ctx) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {s wd : Operand} (ht : b.term = .revertWord s wd) {ms : List Stmt} {mt : Term}
    (hto : termOk fn.c fn.F.vm fn.f.rets b.term ms mt = true) (O : Oracle) {kt base n t : Nat}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b b.body.length (fn.live b b.body.length) g hst w envH envM)
    {res : Except (Exit World) (Next × World)}
    (hres : (runBodyO O cM envM ms >>= fun e => runTerm e mt).exec I w = some res) :
    ∃ o', stepTerm I envH hst b.term = .halt o' ∧ Excuses o' res := by
  rw [ht] at hto
  have hto' : revertWordOk fn.c fn.F.vm s wd ms mt = true := hto
  obtain ⟨w', hw', -, hts, htw, hsel⟩ := revertWordOk_some hto'
  obtain ⟨⟨tS, htS, hvS⟩, tW, htW, hvW⟩ := revertWord_types hts htw
  obtain ⟨s', hs'⟩ := revertWord_mop hsel
  obtain ⟨x, mx, hx, hmx, -, -, -, hwx⟩ := U.sfxOpnd hb hR (a := s)
    (by rw [ht]; simp [HTerm.skel, Term.args]) htS hvS hs'
  obtain ⟨y, my, hy, hmy, -, -, -, hwy⟩ := U.sfxOpnd hb hR (a := wd)
    (by rw [ht]; simp [HTerm.skel, Term.args]) htW hvW hw'
  have hwx := hwx fun hz => (U.obsWord hb ht hz).1
  have hwy := hwy fun hz => (U.obsWord hb ht hz).2
  have hr := run_revertWord hto' O cM I (ns := mx) (nw := my)
    (fun s'' h => by rw [hs'] at h; cases h; exact hmx)
    (fun w'' h => by rw [hw'] at h; cases h; exact hmy) hres
  subst hr
  exact ⟨_, by simp [stepTerm, ht, hx, hy, hwx, hwy], excuses_exit⟩

end unp

end Fe.Sonatina.Stage3.Place
