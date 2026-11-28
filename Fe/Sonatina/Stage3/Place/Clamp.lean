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
