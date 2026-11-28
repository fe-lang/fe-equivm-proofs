import Fe.Sonatina.Stage3.Place.Dia

/-!
# The heap base clamp

A heap `evm_malloc` whose clamp lowering kept (`emit_word_max_with_compare`) is a diamond: block
`mb` reads the free pointer `b0` and compares it with `minBase - 1`; the arms jump to the join,
whose phi takes `b0` or `minBase`, so the base is `max(fp, minBase)`; the join's body goes on
with the aligned size, the bump and the free-pointer store.  `heap_tail` is the part after the
base, for any base at or above the free pointer and at most `F0 + heapReq` (`inv_heap`);
`inst_clamp` is the diamond (`DiaOk`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

theorem mallocSize_defs {vm : VM} {a szo : Operand} {ms ms2 : List Stmt} {dsz : List Nat}
    (h : mallocSize vm a ms = some (szo, ms2, dsz)) : ∃ pre, ms = pre ++ ms2 ∧ dsz = defsOf pre := by
  have dyn : mallocSize.dyn vm a ms = some (szo, ms2, dsz) → ∃ pre, ms = pre ++ ms2 ∧
      dsz = defsOf pre := by
    intro h
    simp only [mallocSize.dyn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨a'', -, ⟨t, r1⟩, ht, ⟨sz, r2⟩, hs, rfl, rfl, rfl⟩ := h
    have hm1 := take1_some ht
    have hm2 := take1_some hs
    simp only at hm1 hm2
    exact ⟨[_, _], by rw [hm1, hm2]; rfl, by simp [defsOf]⟩
  cases a with
  | imm bits n =>
    simp only [mallocSize] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], rfl, rfl⟩
    · exact dyn h
  | var y => exact dyn h

/-- A heap malloc's statements after its base: from a machine environment `E` that agrees with
    `envM` but on `D` and has the base `B`, at or above the free pointer and at most
    `F0 + heapReq`, the size, the bump and the store end as H's step does. -/
theorem heap_tail {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {ms' : List Stmt} {callee? : Option Nat}
    {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty} {base szo : Operand} {E : Env} {B : Nat}
    {D : List Nat} {ms1 ms2 ms3 pre : List Stmt} {dsz : List Nat} {nf : Nat}
    (hheap : S.hasHeap = true) (hF0 : S.F0 < 2 ^ 32)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hta : (c.tyOf a).any Ty.value = true)
    (hB : mval E base = some B) (hq : ∀ q, base = .var q → q ∉ dsz ∧ q ≠ nf)
    (hfpB : fpWord w.memory ≤ B) (hBF : B ≤ S.F0 + hst.heapReq)
    (hEag : ∀ r, r ∉ D → E[r]? = envM[r]?)
    (hsz : mallocSize F.vm a ms1 = some (szo, ms2, dsz))
    (hms2 : ms2 = ⟨[(nf, .int 256)], .bin .add base szo⟩ :: ms3)
    (hms3 : ms3 = ⟨[], .evm .mstore [imm 64, .var nf]⟩ :: ms')
    (hx : F.vm.find? x = some base) (hds : ds = D ++ dsz ++ [nf]) (hpre : ms1 = pre ++ ms') :
    ∀ (O : Oracle) res, (runBodyO O cM E pre).exec I w = some res →
      StepOk P I S F g hst envH s L' res := by
  intro O res hres
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨ta, hta', hva'⟩ := tyOf_any hta
  obtain ⟨a', ha'⟩ : ∃ a', mop F.vm a = some a' := by
    cases a with
    | imm bits n => exact ⟨_, rfl⟩
    | var y =>
      obtain ⟨_, m, _, _, h3, _⟩ := hE y (hA.uses y (by rw [hargs]; simp))
      cases e : F.vm.find? y with
      | none => rw [e] at h3; cases h3
      | some o => exact ⟨o, e⟩
  obtain ⟨va, ma, hva, hfa, hma, hwa, hla⟩ := opnd_word hI hE hA (i := 0) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) hta' ha' hva'
  have hqa := hA.opnd (by rw [hargs]; simp) ha'
  have himm : ∀ b n, a = .imm b n → ma = n := fun b n e => by
    subst e; simp only [evalOp, Option.some.injEq] at hva; subst hva; exact hwa.symm
  have hmaE : mval E a' = some ma := by
    cases a' with
    | var q =>
      simp only [mval] at hma ⊢
      rw [hEag q (fun h => hqa q rfl (by rw [hds]; simp [h]))]; exact hma
    | imm => exact hma
  obtain ⟨pre2, E2, hrest1, hdsz, hcall2, hrun2, hval2, hag2⟩ := mallocSize_run cM hsz ha' hmaE himm
  have hpre' : pre = pre2 ++ [⟨[(nf, .int 256)], .bin .add base szo⟩,
      ⟨[], .evm .mstore [imm 64, .var nf]⟩] := by
    rw [hrest1, hms2, hms3] at hpre
    have e : (pre2 ++ [⟨[(nf, .int 256)], .bin .add base szo⟩,
        ⟨[], .evm .mstore [imm 64, .var nf]⟩]) ++ ms' = pre ++ ms' := by rw [← hpre]; simp
    exact (List.append_cancel_right e).symm
  subst hpre'
  have hBE2 : mval E2 base = some B := by
    cases base with
    | var q => simp only [mval] at hB ⊢; rw [hag2 q (hq q rfl).1]; exact hB
    | imm => exact hB
  set fp := fpWord w.memory with hfp
  by_cases hbud : hst.heapReq + align32 ma < heapBudget
  swap
  · exact Or.inl ⟨.exhausted, fun rest => ExecBody.exhausted hi hva (by rw [hwa]; omega),
      Or.inr (Or.inl rfl)⟩
  have hbud' : hst.heapReq + align32 ma < 2 ^ 255 := hbud
  have hlt : ma + 31 < W := by have := align32_ge ma; unfold W; omega
  have hval := hval2 hlt
  have hend : B + align32 ma < W := by unfold W; omega
  -- The machine's run.
  rw [runBodyO_plain O cM E _ (by
    intro st hst g' a''
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with hst | rfl | rfl
    · exact hcall2 st hst g' a''
    · simp
    · simp), runPlain_append, hrun2] at hres
  simp only [pure_bind] at hres
  rw [runPlain_bin cM hBE2 hval, eval_add, Nat.mod_mod, Nat.mod_eq_of_lt hend] at hres
  simp only [runPlain, Fe.M.exec_bind,
    run_mstore cM I w (by simp [mval, imm] : mval _ (imm 64) = some 64) (mval_insert_self _ _ _)
      (by unfold W; norm_num), Fe.Sonatina.bind] at hres
  simp at hres
  subst hres
  -- H's step and the invariant.
  obtain ⟨haddr, hI'⟩ := inv_heap hI hheap (base := B) (n := ma) hfpB hBF hbud hF0
  set kb := hst.blocks.size with hkb
  set g' := g.add kb B g.live True with hg'
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  have hfit : (H.Val.ptr kb 0).fits tx = true := by
    rw [fits_iff hwx'.1]; exact ⟨hwx'.2, by positivity⟩
  have hb : bindVals envH s.dsts [.ptr kb 0] = some (envH.insert x (.ptr kb 0)) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  have hlive_lt := hI.live_lt
  have hBW : B < W := by unfold W; omega
  have hsz' : ∀ b, b < kb → ({ hst.alloc .malloc ma B (freshAt w.memory B ma) with
      heapReq := hst.heapReq + align32 ma } : H.State).bsize b = hst.bsize b := fun b hb' => by
    show (hst.alloc .malloc ma B (freshAt w.memory B ma)).bsize b = _
    rw [bsize_alloc, if_neg (by omega)]
  have hrg : ∀ b, b < kb → g'.rg { hst.alloc .malloc ma B (freshAt w.memory B ma) with
      heapReq := hst.heapReq + align32 ma } b = g.rg hst b := fun b hb' => by
    simp only [Ghost.rg]
    rw [hg', Ghost.add_j_old (by omega : b ≠ kb), hsz' b hb']
  refine Or.inr ⟨_, _, rfl, envH.insert x (.ptr kb 0), _, g', hI', ?_, ?_,
    fun rest o hr => ExecBody.malloc hi hva (by rw [hwa]; exact hbud) (by rw [hwa]; exact haddr)
      (by rw [hwa]; exact freshAt_length w.memory B ma) hb (by rw [hwa]; exact hr)⟩
  · refine envRel_step' hE (fun y hy hn' => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn')) hb
      (fun r hr => ?_) (fun y hy hn' => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn'))
      ?_ ?_
    · have h1 : r ∉ D := fun e => hr (by rw [hds]; simp [e])
      have h2 : r ∉ dsz := fun e => hr (by rw [hds]; simp [e])
      have h3 : r ≠ nf := fun e => hr (by rw [hds]; simp [e])
      rw [insert_other (Ne.symm h3), hag2 r h2, hEag r h1]
    · intro y hy hny v m _ hv hok horig
      refine ⟨vrel_add hkb hv hok,
        hok.state (by show _ ≤ (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega), ?_⟩
      cases v with
      | int => trivial
      | ptr b o =>
        have hbk : b < kb := hok.1
        rcases horig with hh' | ⟨hl, hsite⟩
        · exact Or.inl (Ghost.add_heap_old (by omega) hh')
        · refine Or.inr ⟨Ghost.add_live_old (by omega) hl, ?_⟩
          rw [hrg b hbk]; exact hsite
    · intro y hy _
      simp only [hd, List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy
      refine ⟨.ptr kb 0, B, by simp, ⟨tx, hdt, hfit⟩, ?_, ?_, ?_, ?_⟩
      · rw [hx]
        simp only [Option.bind_some]
        cases base with
        | var q =>
          simp only [mval] at hBE2 ⊢
          rw [insert_other (Ne.symm (hq q rfl).2)]; exact hBE2
        | imm => exact hBE2
      · refine ⟨by simp [hg', Ghost.add, Nat.mod_eq_of_lt hBW], fun hz' => ?_⟩
        rw [hA.D]; exact hA.der hz' (by simp [stmtDerived, hi]) y (by simp [HStmt.defs, hd])
      · exact ⟨by show _ < (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega, by positivity⟩
      · exact Or.inl (Or.inl ⟨rfl, trivial⟩)
  · refine ⟨by show _ ≤ (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega,
      fun b hb' => Ghost.add_j_old (by omega), fun b hb' => hsz' b hb',
      fun b hb' => by show (hst.alloc _ _ _ _).addrOf b = _; rw [addrOf_alloc, if_neg (by omega)],
      fun b hb' => Ghost.add_heap_old (by have := hlive_lt b (hI.heap_live b hb'); omega) hb',
      fun b hb' _ => Ghost.add_live_old (by have := hlive_lt b hb'; omega) hb'⟩

theorem nodup_flatMap_of_mem {α β : Type} {f : α → List β} :
    ∀ {l : List α} {a : α}, (l.flatMap f).Nodup → a ∈ l → (f a).Nodup
  | [], _, _, h => by cases h
  | b :: l, a, hn, h => by
    rw [List.flatMap_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · exact (List.nodup_append.mp hn).1
    · exact nodup_flatMap_of_mem (List.nodup_append.mp hn).2.1 h

/-- A heap `evm_malloc` with the clamp: the diamond's base is `max(fp, minBase)`, and the
    statements after it end as H's step does (`heap_tail`). -/
theorem inst_clamp {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {L L' : List Nat} {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat}
    {ms ms' : List Stmt} {callee? : Option Nat} {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty}
    {minBase b0 : Nat} {rest1 : List Stmt} {base : Operand} {mb1 : Nat} {ms1 : List Stmt}
    {dc : List Nat} {szo : Operand} {ms2 ms3 : List Stmt} {dsz : List Nat} {nf : Nat}
    (hheap : S.hasHeap = true) (hF0 : S.F0 < 2 ^ 32) (hmin : minBase ≤ S.F0)
    (hA : At S F c Dr k s callee? L L' ds) (hmd : (mdefs c.mf).Nodup) (hnd : (defsOf ms).Nodup)
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hta : (c.tyOf a).any Ty.value = true)
    (hms : ms = ⟨[(b0, .int 256)], .evm .mload [imm 64]⟩ :: rest1)
    (hcl : ClampAt c mb minBase b0 rest1 base mb1 ms1 dc)
    (hsz : mallocSize F.vm a ms1 = some (szo, ms2, dsz))
    (hms2 : ms2 = ⟨[(nf, .int 256)], .bin .add base szo⟩ :: ms3)
    (hms3 : ms3 = ⟨[], .evm .mstore [imm 64, .var nf]⟩ :: ms')
    (hx : F.vm.find? x = some base) (hmb : mb' = mb1) (hds : ds = [b0] ++ dc ++ dsz ++ [nf]) :
    DiaOk P I cM S F c s mb ms mb' ms' L L' := by
  obtain ⟨hmb0, cnd, cur, lb, rb, mlb, mrb, jn, jb, φ, hcnd, hcur, hterm, hlr, hmlb, hmrb, hjl, hjr,
    hjb, hφ, hφt, hinc, rfl, hmb1, rfl, rfl⟩ := hcl
  subst mb1
  subst mb'
  have hr1 := take1_some hcnd
  obtain ⟨pre2, hpre2, hdsz⟩ := mallocSize_defs hsz
  have hjbody : jb.body = (pre2 ++ [⟨[(nf, .int 256)], .bin .add (.var φ.dst) szo⟩,
      ⟨[], .evm .mstore [imm 64, .var nf]⟩]) ++ ms' := by
    rw [hpre2, hms2, hms3]; simp
  have hj : ∀ ab, c.mf.block? jn = some ab → ab.phis ≠ [] := fun ab hab => by
    rw [hjb] at hab; cases hab; rw [hφ]; simp
  have harm : ∀ t mt, c.mf.block? t = some mt → jumpOnly mt jn = true →
      mt.phis = [] ∧ mt.body = [] ∧ mt.term = .jump jn ∧ t ≠ jn := fun t mt ht hj' => by
    simp only [jumpOnly, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hj'
    refine ⟨hj'.1.1, hj'.1.2, hj'.2, fun e => ?_⟩
    subst e; exact hj mt ht hj'.1.1
  obtain ⟨hlp, hlbd, hlt, hlj⟩ := harm lb mlb hmlb hjl
  obtain ⟨hrp, hrbd, hrt, hrj⟩ := harm rb mrb hmrb hjr
  refine ⟨cur, .var cnd, lb, rb, jb, _, hcur, hterm, hjb, hjbody, fun t ht _ => ?_, ?_⟩
  · rcases ht with rfl | rfl
    · exact ⟨mlb, hmlb, hlp, hlt⟩
    · exact ⟨mrb, hmrb, hrp, hrt⟩
  -- The join's phi is none of the statements' results after it.
  have hgjb : (jb.phis.map (·.dst) ++ jb.body.flatMap (·.dsts.map (·.1))).Nodup := by
    have hmem : jb ∈ c.mf.blocks := List.mem_of_find?_eq_some hjb
    unfold mdefs at hmd
    exact nodup_flatMap_of_mem (f := fun b : Block => b.phis.map (·.dst) ++
      b.body.flatMap (·.dsts.map (·.1))) (List.nodup_append.mp hmd).2.1 hmem
  have hqφ : φ.dst ∉ dsz ∧ φ.dst ≠ nf := by
    rw [hφ, hjbody] at hgjb
    simp only [List.map_cons, List.map_nil, List.singleton_append] at hgjb
    have hn := (List.nodup_cons.mp hgjb).1
    refine ⟨fun h => hn ?_, fun h => hn ?_⟩
    · rw [hdsz] at h
      simp only [defsOf, List.mem_map, List.mem_flatMap] at h
      obtain ⟨⟨d, t⟩, ⟨st, hst, hdt⟩, rfl⟩ := h
      exact List.mem_flatMap.mpr ⟨st, by simp [hst], List.mem_map.mpr ⟨_, hdt, rfl⟩⟩
    · exact List.mem_flatMap.mpr ⟨⟨[(nf, .int 256)], .bin .add (.var φ.dst) szo⟩, by simp, by simp [h]⟩
  have hb0c : b0 ≠ cnd := by
    rw [hms, hr1] at hnd
    simpa [defsOf] using hnd
  intro O g hst w envH envM hI hE res hres
  set fp := fpWord w.memory with hfp
  have hfpW : fp < W := toNat_lt' _
  have hfpdef : (Ethereum.uInt256OfByteArray (w.memory.readWithPadding 64 32)).toNat = fp := rfl
  set cv : Nat := if CmpOp.eval .gt 256 fp (minBase - 1) then 1 else 0 with hcv
  set E1 := (envM.insert b0 (.int 256 fp)).insert cnd (.int 256 cv) with hE1
  have h1 : (runPlain cM envM [⟨[(b0, .int 256)], .evm .mload [imm 64]⟩]).exec I w =
      some (.ok (envM.insert b0 (.int 256 fp), w)) := by
    simp only [runPlain, Fe.M.exec_bind,
      run_mload cM I w (by simp [mval, imm] : mval envM (imm 64) = some 64) (by unfold W; norm_num),
      bind_one, Fe.M.exec_pure]
    rw [hfpdef, Nat.mod_eq_of_lt hfpW]
  have hrun1 : (runBodyO O cM envM ms).exec I w = some (.ok (E1, w)) := by
    rw [runBodyO_plain O cM envM _ (by rw [hms, hr1]; simp), hms, hr1,
      show (⟨[(b0, .int 256)], .evm .mload [imm 64]⟩ :: [⟨[(cnd, .int 256)],
        .cmp .gt (.var b0) (imm (minBase - 1))⟩] : List Stmt) =
        [⟨[(b0, .int 256)], .evm .mload [imm 64]⟩] ++ [⟨[(cnd, .int 256)],
        .cmp .gt (.var b0) (imm (minBase - 1))⟩] from rfl, runPlain_append, exec_bind_ok h1,
      runPlain_cmp cM (mval_insert_self _ _ _) (by simp [mval, imm] :
        mval _ (imm (minBase - 1)) = some (minBase - 1))]
    rfl
  unfold diaRun at hres
  rw [exec_bind_ok hrun1, mval_evalInt (show mval E1 (.var cnd) = some cv by
    rw [hE1]; exact mval_insert_self _ _ _)] at hres
  have hmW : minBase < W := lt_of_lt_of_le (lt_of_le_of_lt hmin hF0) (by unfold W; norm_num)
  have hfpF := (hI.fp hheap).2.1
  -- The arm taken and the base.
  obtain ⟨B, hfpB, hBF, hres⟩ : ∃ B, fp ≤ B ∧ B ≤ S.F0 + hst.heapReq ∧
      (runBodyO O cM (E1.insert φ.dst (.int 256 B)) (pre2 ++
        [⟨[(nf, .int 256)], .bin .add (.var φ.dst) szo⟩, ⟨[], .evm .mstore [imm 64, .var nf]⟩])).exec
        I w = some res := by
    by_cases hge : minBase ≤ fp
    · have hc1 : cv = 1 := by
        simp only [hcv, CmpOp.eval, decide_eq_true_eq]; rw [if_pos (by omega)]
      refine ⟨fp, le_rfl, hfpF, ?_⟩
      rw [hc1] at hres
      simp only [bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true, ite_true, if_neg hlj, hmlb,
        hlbd, runBodyO, pure_bind] at hres
      simp [Fe.Sonatina.enter, hφ, hinc, evalOperand, Fe.Sonatina.bind, hφt, w256, Val.as,
        Ty.bits, hE1, Std.TreeMap.getElem?_insert, Ne.symm hb0c, compare_eq_iff_eq] at hres
      rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat)
        = W from rfl, Nat.mod_eq_of_lt hfpW] at hres
      exact hres
    · have hc0 : cv = 0 := by
        simp only [hcv, CmpOp.eval, decide_eq_true_eq]; rw [if_neg (by omega)]
      refine ⟨minBase, by omega, by omega, ?_⟩
      rw [hc0] at hres
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, if_neg hrj, hmrb, hrbd, runBodyO,
        pure_bind] at hres
      simp [Fe.Sonatina.enter, hφ, hinc, evalOperand, imm, Fe.Sonatina.bind, hφt, w256, Val.as,
        Ty.bits, beq_eq_false_iff_ne.mpr hlr] at hres
      rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat)
        = W from rfl, Nat.mod_eq_of_lt hmW] at hres
      exact hres
  exact heap_tail (D := [b0, cnd, φ.dst]) (ms3 := ms3) hheap hF0 hI hE hA hi hd hwx hta
    (mval_insert_self _ _ _) (fun q e => by cases e; exact hqφ) (by rw [← hfp]; exact hfpB) hBF
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [insert_other (Ne.symm hr.2.2), hE1, insert_other (Ne.symm hr.2.1),
        insert_other (Ne.symm hr.1)])
    hsz hms2 hms3 hx (by rw [hds]; simp) hjbody O res hres

end Fe.Sonatina.Stage3.Place
