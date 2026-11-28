import Fe.Sonatina.Stage3.Place.FixStore

/-!
# A terminal fixed buffer's site

`FnUnp.fixSiteStep`: at the site H allocates the buffer (or ends `exhausted` past its budget),
at the record's base (1 for a base 0, in address-0 mode), holding the machine's bytes there;
the machine does nothing; `SR` holds after it.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- What `stmt` accepts at a terminal fixed buffer: the buffer's base as the result's operand,
    no machine statement. -/
theorem stmt_fixed {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty} {base : Nat}
    {rule : FixedRule} (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)])
    (hl : c.frec.mallocs.lookup x = some (.fixed base rule))
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    isWord tx = true ∧ (c.tyOf a).any Ty.value = true ∧ vm.find? x = some (imm base) ∧
      mb' = mb ∧ ms' = ms ∧ ds = [] := by
  simp only [stmt, hi, hd, hl, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.bind_none, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq,
    reduceCtorEq, false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte,
    Option.bind_some] at h
  obtain ⟨hc, _, ⟨he, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hc
  exact ⟨hc.1, hc.2, he, rfl, rfl, rfl⟩

theorem s45_bases {P : List (Nat × HFunc × FuncRec)} {rs : List Range} {efp : Option Nat}
    (h : ruleS45 P rs efp = none) {q : Nat × HFunc × FuncRec} (hq : q ∈ P) {xm : Nat × Malloc}
    (hxm : xm ∈ q.2.2.mallocs) {base : Nat} {rule : FixedRule} (hf : xm.2 = .fixed base rule) :
    base < 2 ^ 32 := by
  unfold ruleS45 at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · next h2 =>
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.not_eq_false, List.all_eq_true,
        decide_eq_true_eq, not_or, Bool.and_eq_true] at h2
      have := h2.1.2 base (List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨xm, hxm, by rw [hf]⟩⟩)
      exact this

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.mplaced (U : FnUnp src low r fn fr fl e me be rs) : (fn.k, fn.f, fr) ∈ placed src r := by
  have := mem_placed (r := r) U.hf
  rw [← U.hfr] at this
  exact this

/-- The site: H allocates the buffer, or ends `exhausted`; `SR` holds after it. -/
theorem FnUnp.fixSiteStep {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat}
    {s : HStmt} (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {a : Operand} {x : Nat} {tx : Ty}
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)]) {base : Nat} {rule : FixedRule}
    (hl : fr.mallocs.lookup x = some (.fixed base rule)) {vm' : VM} {mb' : Nat} {ms' : List Stmt}
    {ds : List Nat} (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds))
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hI : Inv (secS src r efp) hst w g)
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (fn.live b i)) (hQ : FixInv fn b i envH) :
    FixSite fn b i x ∧ mb' = mb ∧ ms' = ms ∧
      ((∀ rest, ExecBody src I envH (s :: rest) hst (.halt .exhausted)) ∨
      ∃ n g' hst' envH', SR (secS src r efp) fn hst.blocks.size base n x b (i + 1) (fn.live b (i + 1))
        g' hst' w envH' envM ∧
        ∀ rest o, ExecBody src I envH' rest hst' o → ExecBody src I envH (s :: rest) hst o) := by
  have hnd := U.defsNodup
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have hA := U.at hS hb hs hp hstm
  have hl' : fn.c.frec.mallocs.lookup x = some (.fixed base rule) := by rw [U.frec]; exact hl
  obtain ⟨hwx, hta, hvx, rfl, rfl, rfl⟩ := stmt_fixed hi hd hl' hstm
  have hmem : (x, Malloc.fixed base rule) ∈ fr.mallocs := lookup_mem hl
  have hF : FixSite fn b i x :=
    ⟨hb, s, a, tx, hs, hi, hd, by rw [U.frec]; simp [FuncRec.isFixed]; exact ⟨_, hmem, rfl⟩⟩
  refine ⟨hF, rfl, rfl, ?_⟩
  have hbase : base < 2 ^ 32 := s45_bases hS.s45 U.mplaced hmem rfl
  -- The size operand.
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨v, hv⟩ : ∃ v, evalOp envH a = some v := by
    cases a with
    | imm => exact ⟨_, rfl⟩
    | var y =>
      obtain ⟨v, -, h1, -⟩ := hE y (hA.uses y (by rw [hargs]; simp))
      exact ⟨v, h1⟩
  by_cases hbud : hst.heapReq + align32 (hst.word v) < heapBudget
  swap
  · exact Or.inl fun rest => ExecBody.exhausted hi hv (by omega)
  set n := hst.word v with hn
  have hn' : n < 2 ^ 255 := by
    have := align32_ge n; unfold heapBudget at hbud; omega
  set kt := hst.blocks.size with hkt
  set addr := if base = 0 then 1 else base with haddr
  have hAok : AddrOk addr n := by
    refine ⟨by rw [haddr]; split <;> omega, ?_⟩
    rw [haddr]; split <;> omega
  set fresh := freshAt w.memory base n
  set hst' : H.State := { hst.alloc .malloc n addr fresh with heapReq := hst.heapReq + align32 n }
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  have hfit : (H.Val.ptr kt 0).fits tx = true := by
    rw [fits_iff hwx'.1]; exact ⟨hwx'.2, by positivity⟩
  have hbv : bindVals envH s.dsts [.ptr kt 0] = some (envH.insert x (.ptr kt 0)) := by
    simp [bindVals, hd, hfit]
  have hexec : ∀ rest o, ExecBody src I (envH.insert x (.ptr kt 0)) rest hst' o →
      ExecBody src I envH (s :: rest) hst o := fun rest o hr =>
    ExecBody.malloc hi hv hbud hAok (freshAt_length _ _ _) hbv hr
  set g' : Ghost := { g with j := fun bb => if bb = kt then base else g.j bb }
  have hsz' : hst'.blocks.size = kt + 1 := alloc_size ..
  have hgj : ∀ bb, bb < kt → g'.j bb = g.j bb := fun bb hbb => by simp [g', show bb ≠ kt by omega]
  have hbW : base < W := lt_of_lt_of_le hbase (by unfold W; norm_num)
  -- The site's result is not bound before it.
  have hxun : envH[x]? = none := by
    cases hxv : envH[x]? with
    | none => rfl
    | some _ =>
      rcases (hQ.2 b i x hF).1 (by simp [hxv]) with hR | ⟨j, hj, s', hs', hxs'⟩
      · exact absurd hR (U.notR hF)
      · have := stmt_index hnd hb hs' hs hxs' (by simp [HStmt.defs, hd])
        omega
  have hMun := (hQ.2 b i x hF).2 hxun
  refine Or.inr ⟨n, g', hst', envH.insert x (.ptr kt 0), ?_, hexec⟩
  refine ⟨hI.world, fun bb blk hblk => ?_, fun bb hbb hj => ?_, fun bb hbb hj => ?_, fun y hy => ?_,
    by rw [hsz']; omega, ?_, by simp [g'], by unfold W; omega, fun k hk => ?_,
    U.fixStep I b hb i s hs envH hst _ hst' hQ (hexec [] _ ExecBody.nil), fun y hy v hvy => ?_⟩
  · show blk.bytes.size = blk.size
    change (hst.alloc .malloc n addr fresh).blocks[bb]? = some blk at hblk
    rw [alloc_get?] at hblk
    split at hblk
    · simp only [Option.some.injEq] at hblk; subst hblk; simp [fresh, freshAt_length]
    · exact hI.bytes_size bb blk hblk
  · change (hst.alloc .malloc n addr fresh).addrOf bb = g'.j bb
    rw [addrOf_alloc]
    by_cases h : bb = kt
    · rw [if_pos h]
      have hj' : base ≠ 0 := by simpa [g', h] using hj
      show addr = (if bb = kt then base else g.j bb)
      rw [if_pos h, haddr, if_neg hj']
    · rw [if_neg h, hgj bb (by omega)]
      exact hI.exact bb (by omega) (by rwa [hgj bb (by omega)] at hj)
  · by_cases h : bb = kt
    · subst h
      simp only [g', ite_true] at hj
      subst hj
      show zeroMode (placed src r) (secRs src r) = true
      simp only [zeroMode, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨_, U.mplaced, _, hmem, rfl⟩
    · exact hI.zero bb (by omega) (by rwa [hgj bb (by omega)] at hj)
  · by_cases hyx : y = x
    · subst hyx
      have hdt : fn.F.decls.find? y = some tx := hA.dsts (y, tx) (by simp [hd])
      refine ⟨.ptr kt 0, base, by simp, ⟨tx, hdt, hfit⟩, by rw [hvx]; simp [mval, imm], ?_,
        ⟨by show kt < (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega, by positivity⟩,
        fun bb o h => by cases h; simp [g']; exact hbW⟩
      refine ⟨by simp [g', Nat.mod_eq_of_lt hbW], fun hz => ?_⟩
      rw [hA.D]; exact hA.der hz (by simp [stmtDerived, hi]) y (by simp [HStmt.defs, hd])
    · have hyL := hA.keep y hy (by simp [HStmt.defs, hd, hyx])
      obtain ⟨v', m, e1, e2, e3, e4, e5, e6⟩ := hE y hyL
      refine ⟨v', m, by rw [Std.TreeMap.getElem?_insert]; simp [compare_eq_iff_eq, Ne.symm hyx, e1],
        e2, e3, ?_, ?_, ?_⟩
      · cases v' with
        | int => exact e4
        | ptr bb o => exact ⟨by rw [hgj bb e5.1]; exact e4.1, e4.2⟩
      · cases v' with
        | int => trivial
        | ptr bb o => exact ⟨by show bb < (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; have := e5.1; omega, e5.2⟩
      · intro bb o hvo
        subst hvo
        rw [hgj bb e5.1]
        have hl : g.live bb := by
          rcases e6 with hh | ⟨hl, -⟩
          · exact hI.heap_live bb hh
          · exact hl
        have := hI.bound bb hl
        omega
  · show (hst.alloc .malloc n addr fresh).bsize kt = n
    rw [bsize_alloc, if_pos rfl]
  · show mem w.memory (base + k) = ((hst.alloc .malloc n addr fresh).cell kt k).val
      (hst.alloc .malloc n addr fresh).addrOf
    rw [cell_alloc, if_pos rfl, dif_pos (by simp [fresh, freshAt_length]; exact hk)]
    simp [fresh, freshAt, MByte.val]
  · by_cases hyx : x = y
    · subst hyx
      rw [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at hvy
      exact ⟨0, hvy.symm⟩
    · rw [Std.TreeMap.getElem?_insert] at hvy
      simp only [compare_eq_iff_eq, hyx, ↓reduceIte] at hvy
      rw [hMun y hy] at hvy; cases hvy

end unp

end Fe.Sonatina.Stage3.Place
