import Fe.Sonatina.Stage3.Place.InstMem

/-!
# Allocation: `alloca` and the heap's `evm_malloc`

`alloca T` has no machine statement: its result is the immediate of its record word's address
`A`.  H allocates a block of `T`'s size; the proof puts it at `A` (H's address word 1 if `A` is
0) holding the machine's bytes there (`inv_alloca`).  The live blocks whose ranges meet the new
one leave the ghost's live set; by rule A1 no value live after the `alloca` points into one, and
the function's footprint holds the new range, so the blocks a caller keeps are kept
(`GhostLe`).

A heap `evm_malloc n` (bumping the free pointer, without the clamp) is `b0 = mload 0x40;
size; nf = add b0 size; mstore 0x40 nf`.  H allocates `n` bytes within its budget, else ends
`exhausted`; the proof puts the block at the free pointer (`inv_heap`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The frame relation after a statement that changes the ghost: as `envRel_step`, each value
    live after it that it does not define is carried over by `htr`. -/
theorem envRel_step' {z : Bool} {F : Frame} {g g' : Ghost} {hst hst' : H.State}
    {envH envH' : HEnv} {envM envM' : Env} {L L' : List Nat} {dsts : List (Nat × Ty)}
    {vals : List H.Val} {ds : List Nat}
    (hE : EnvRel z F g hst envH envM L)
    (hL : ∀ y ∈ L', y ∉ dsts.map (·.1) → y ∈ L)
    (hb : bindVals envH dsts vals = some envH')
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?)
    (hcl : ∀ y ∈ L', y ∉ dsts.map (·.1) → ∀ m ∈ ds, F.vm.find? y ≠ some (.var m))
    (htr : ∀ y ∈ L', y ∉ dsts.map (·.1) → ∀ v m, envH[y]? = some v → VRel g z (F.D y) v m →
      ValOk hst v → OrigOk g hst F.R F.fpf (origOf F.O (.var y)) v →
      VRel g' z (F.D y) v m ∧ ValOk hst' v ∧ OrigOk g' hst' F.R F.fpf (origOf F.O (.var y)) v)
    (hnew : ∀ x ∈ dsts.map (·.1), x ∈ L' → ∃ v m, envH'[x]? = some v ∧
      (∃ t, F.decls.find? x = some t ∧ v.fits t = true) ∧ (F.vm.find? x).bind (mval envM') = some m ∧
      VRel g' z (F.D x) v m ∧ ValOk hst' v ∧ OrigOk g' hst' F.R F.fpf (origOf F.O (.var x)) v) :
    EnvRel z F g' hst' envH' envM' L' := by
  intro x hx
  by_cases hd : x ∈ dsts.map (·.1)
  · exact hnew x hd hx
  · obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := hE x (hL x hx hd)
    obtain ⟨h4', h5', h6'⟩ := htr x hx hd v m h1 h4 h5 h6
    refine ⟨v, m, ?_, h2, ?_, h4', h5', h6'⟩
    · rw [bindVals_other hb hd]; exact h1
    · rw [mval_keep hkeep (hcl x hx hd)]; exact h3

theorem Ghost.add_live_old {g : Ghost} {k A : Nat} {keep : Nat → Prop} {p : Prop} {b : Nat}
    (hb : b ≠ k) (h : keep b) : (g.add k A keep p).live b := Or.inr ⟨hb, h⟩

theorem Ghost.add_heap_old {g : Ghost} {k A : Nat} {keep : Nat → Prop} {p : Prop} {b : Nat}
    (hb : b ≠ k) (h : g.heap b) : (g.add k A keep p).heap b := Or.inr ⟨hb, h⟩

/-- An old value keeps its relation to the ghost with a block added: its block is an old one,
    whose machine base, size and address word stay, and it stays live when `keep` holds of it. -/
theorem vrel_add {g : Ghost} {z dx : Bool} {hst : H.State} {k A : Nat} {keep : Nat → Prop}
    {p : Prop} {v : H.Val} {m : Nat} (hk : k = hst.blocks.size) (hv : VRel g z dx v m)
    (hok : ValOk hst v) : VRel (g.add k A keep p) z dx v m := by
  cases v with
  | int => exact hv
  | ptr b o =>
    have hb : b ≠ k := by have := hok.1; omega
    exact ⟨by rw [Ghost.add_j_old hb]; exact hv.1, hv.2⟩

/-- An `alloca`: H's block where the record puts it; the value is the block's pointer, related to
    the machine's immediate; values live after it keep their blocks live (A1), and the blocks
    outside the function's footprint stay live (the range is in it). -/
theorem inst_alloca {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {t : Ty} {x : Nat} {tx : Ty}
    (hstr : c.src.structs = P.module.structs)
    (hRx : ∀ loc n, c.frec.allocas.lookup x = some loc → sizeOf c.src.structs sizeFuel t = some n →
      F.R.find? x = some (c.prec.wordAddr loc.word, c.prec.wordAddr loc.word + n))
    (hsec : ∀ r, F.R.find? x = some r → r.2 < 2 ^ 32 ∧ (r.1 = 0 → S.z = true) ∧
      (S.hasHeap = true → r.2 ≤ S.e ∧ Disj r (0x40, 0x60)) ∧ r ∈ F.fpf)
    (hA1 : ∀ r, F.R.find? x = some r → ∀ y ∈ L', y ≠ x → ∀ o ∈ origOf F.O (.var y), o ≠ 0 →
      ∀ r', F.R.find? (o - 1) = some r' → Disj r r')
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.alloca t)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, loc, hloc, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
  obtain ⟨⟨n, hn⟩, hwx⟩ := hc
  set A := c.prec.wordAddr loc.word with hAdef
  have hR := hRx loc n hloc hn
  obtain ⟨hlt, hz, hh, hfp⟩ := hsec _ hR
  simp only at hlt hz hh
  obtain ⟨haddr, hI'⟩ := inv_alloca hI (A := A) (n := n) hlt hz hh
  refine ⟨[], rfl, rfl, fun O res hres => ?_⟩
  simp only [runBodyO, Fe.M.exec_pure, Option.some.injEq] at hres
  subst hres
  set kb := hst.blocks.size with hkb
  set g' := g.add kb A (fun b => g.live b ∧ Disj (g.rg hst b) (A, A + n)) False with hg'
  set hst' := hst.alloc .alloca n (if A = 0 then 1 else A) (freshAt w.memory A n) with hhst'
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  have hfit : (H.Val.ptr kb 0).fits tx = true := by
    rw [fits_iff hwx'.1]; exact ⟨hwx'.2, by positivity⟩
  have hb : bindVals envH s.dsts [.ptr kb 0] = some (envH.insert x (.ptr kb 0)) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  have hAW : A < W := lt_of_lt_of_le (by omega) (by unfold W; norm_num : 2 ^ 32 ≤ W)
  have hlive_lt := hI.live_lt
  -- Ranges of old blocks are unchanged.
  have hrg : ∀ b, b < kb → g'.rg hst' b = g.rg hst b := fun b hb' => by
    simp only [Ghost.rg]
    rw [hg', Ghost.add_j_old (by omega : b ≠ kb), hhst', bsize_alloc, if_neg (by omega)]
  refine Or.inr ⟨envM, w, rfl, envH.insert x (.ptr kb 0), hst', g', hI', ?_, ?_,
    fun rest o hr => ExecBody.alloca hi (by rw [← hstr]; exact hn) haddr (freshAt_length _ _ _) hb hr⟩
  · refine envRel_step' hE (fun y hy hn' => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn')) hb
      (fun _ _ => rfl) (fun y hy hn' => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn'))
      ?_ ?_
    · intro y hy hny v m _ hv hok horig
      refine ⟨vrel_add hkb hv hok, hok.state (by rw [hhst', alloc_size]; omega), ?_⟩
      cases v with
      | int => trivial
      | ptr b o =>
        have hbk : b < kb := hok.1
        have hyx : y ≠ x := fun e => hny (by rw [hd, e]; simp)
        rcases horig with hh' | ⟨hl, hsite | ⟨h0, hdisj⟩⟩
        · exact Or.inl (Ghost.add_heap_old (by omega) hh')
        · obtain ⟨s', hs', hRs⟩ := hsite
          refine Or.inr ⟨Ghost.add_live_old (by omega) ⟨hl, ?_⟩, Or.inl ⟨s', hs', by rw [hrg b hbk]; exact hRs⟩⟩
          exact (hA1 _ hR y hy hyx (s' + 1) hs' (by omega) _
            (by simp only [Nat.add_sub_cancel]; exact hRs)).symm
        · refine Or.inr ⟨Ghost.add_live_old (by omega) ⟨hl, (hdisj _ hfp).symm⟩, Or.inr ⟨h0, ?_⟩⟩
          intro r' hr'; rw [hrg b hbk]; exact hdisj r' hr'
    · intro y hy _
      simp only [hd, List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy
      refine ⟨.ptr kb 0, A, by simp, ⟨tx, hdt, hfit⟩, by rw [hx]; simp [mval, imm], ?_, ?_, ?_⟩
      · refine ⟨by simp [hg', Ghost.add, Nat.mod_eq_of_lt hAW], fun hz' => ?_⟩
        rw [hA.D]; exact hA.der hz' (by simp [stmtDerived, hi]) y (by simp [HStmt.defs, hd])
      · exact ⟨by rw [hhst', alloc_size]; omega, by positivity⟩
      · refine Or.inr ⟨Or.inl rfl, Or.inl ⟨y, hA.orig y tx hd (y + 1) (by simp [stmtOrig, hi, hd]), ?_⟩⟩
        rw [hR]
        simp [Ghost.rg, hg', Ghost.add, hhst', bsize_alloc, hkb, hAdef]
  · refine ⟨by rw [hhst', alloc_size]; omega, fun b hb' => Ghost.add_j_old (by omega),
      fun b hb' => by rw [hhst', bsize_alloc, if_neg (by omega)],
      fun b hb' => by rw [hhst', addrOf_alloc, if_neg (by omega)],
      fun b hb' => Ghost.add_heap_old (by have := hlive_lt b (hI.heap_live b hb'); omega) hb',
      fun b hb' hd' => Ghost.add_live_old (by have := hlive_lt b hb'; omega) ⟨hb', (hd' _ hfp).symm⟩⟩

/-! ## The heap -/

theorem orElse_eq_some {α : Type} {x y : Option α} {a : α} (h : (x <|> y) = some a) :
    x = some a ∨ (x = none ∧ y = some a) := by
  cases x <;> simp_all

/-- The clamp diamond of a heap `evm_malloc` (`emit_word_max_with_compare`): `cnd = gt b0
    (minBase - 1)` ends block `mb`, which branches to two blocks that only jump to the join `jn`,
    whose one phi takes `b0` or `minBase`. -/
def ClampAt (c : FCtx) (mb minBase b0 : Nat) (rest1 : List Stmt) (base : Operand) (mb1 : Nat)
    (ms1 : List Stmt) (dc : List Nat) : Prop :=
  minBase ≠ 0 ∧ ∃ (cnd : Nat) (cur : Block) (lb rb : Nat) (mlb mrb : Block) (jn : Nat) (jb : Block)
    (φ : Phi), take1 (.cmp .gt (.var b0) (imm (minBase - 1))) rest1 = some (cnd, []) ∧
    c.mf.block? mb = some cur ∧ cur.term = .br (.var cnd) lb rb ∧ lb ≠ rb ∧
    c.mf.block? lb = some mlb ∧ c.mf.block? rb = some mrb ∧ jumpOnly mlb jn = true ∧
    jumpOnly mrb jn = true ∧ c.mf.block? jn = some jb ∧ jb.phis = [φ] ∧ φ.ty = w256 ∧
    φ.incoming = [(.var b0, lb), (imm minBase, rb)] ∧ base = .var φ.dst ∧ mb1 = jn ∧
    ms1 = jb.body ∧ dc = [cnd, φ.dst]

/-- A heap `evm_malloc`'s template: `b0 = mload 0x40`, the clamp diamond or none, the aligned
    size, `nf = add base size`, `mstore 0x40 nf`; the result is the base. -/
theorem stmt_heap {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty} {minBase : Nat}
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)])
    (hl : c.frec.mallocs.lookup x = some (.heap minBase none true))
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    isWord tx = true ∧ (c.tyOf a).any Ty.value = true ∧ vm' = vm ∧
    ∃ b0 rest1 base mb1 ms1 dc szo ms2 dsz nf ms3,
      ms = ⟨[(b0, .int 256)], .evm .mload [imm 64]⟩ :: rest1 ∧
      (ClampAt c mb minBase b0 rest1 base mb1 ms1 dc ∨
        (base = .var b0 ∧ mb1 = mb ∧ ms1 = rest1 ∧ dc = [])) ∧
      mallocSize vm a ms1 = some (szo, ms2, dsz) ∧
      ms2 = ⟨[(nf, .int 256)], .bin .add base szo⟩ :: ms3 ∧
      ms3 = ⟨[], .evm .mstore [imm 64, .var nf]⟩ :: ms' ∧
      vm.find? x = some base ∧ mb' = mb1 ∧ ds = [b0] ++ dc ++ dsz ++ [nf] := by
  simp only [stmt, hi, hd, hl, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.bind_none, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq,
    reduceCtorEq, false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, _, rfl, h⟩ := h
  simp only [Bool.and_eq_true] at hc
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨b0, rest1⟩, hb0, ⟨base, mb1, ms1, dc⟩, hcl, ⟨szo, ms2, dsz⟩, hsz, ⟨nf, ms3⟩, hnf, ms4,
    hst0, h⟩ := h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
    Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  refine ⟨hc.1, hc.2, rfl, b0, rest1, base, mb1, ms1, dc, szo, ms2, dsz, nf, ms3, take1_some hb0,
    ?_, hsz, take1_some hnf, take0_some hst0, hx, rfl, rfl⟩
  rcases orElse_eq_some hcl with hcl | ⟨-, hcl⟩
  · left
    split at hcl
    · next hne =>
      simp only [Option.bind_eq_some_iff] at hcl
      obtain ⟨⟨cnd, r1⟩, hcnd, hcl⟩ := hcl
      split at hcl
      · next hr1 =>
        simp only [Option.bind_eq_some_iff] at hcl
        obtain ⟨cur, hcur, hcl⟩ := hcl
        split at hcl
        · next cv lb rb hterm =>
          simp only [Option.bind_eq_some_iff] at hcl
          obtain ⟨mlb, hmlb, mrb, hmrb, hcl⟩ := hcl
          split at hcl
          · next jn hjt =>
            split at hcl
            · next hok =>
              simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
              obtain ⟨⟨⟨hcv, hlr⟩, hjl⟩, hjr⟩ := hok
              simp only [Option.bind_eq_some_iff] at hcl
              obtain ⟨jb, hjb, hcl⟩ := hcl
              split at hcl
              · next φ hph =>
                split at hcl
                · next hok2 =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hok2
                  simp only [Option.some.injEq, Prod.mk.injEq] at hcl
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcl
                  have hr1' : r1 = [] := List.isEmpty_iff.mp hr1
                  subst hr1'
                  exact ⟨by simpa using hne, cnd, cur, lb, rb, mlb, mrb, jn, jb, φ, hcnd, hcur,
                    by rw [hterm, hcv], hlr, hmlb, hmrb, hjl, hjr, hjb, hph, hok2.1, hok2.2, rfl, rfl,
                    rfl, rfl⟩
                · cases hcl
              · cases hcl
            · cases hcl
          · cases hcl
        · cases hcl
      · cases hcl
    · cases hcl
  · right
    simp only [Option.some.injEq, Prod.mk.injEq] at hcl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcl
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem align32_lt {n : Nat} (h : n + 31 < W) : align32 n < W := by
  unfold align32; omega

/-- The machine's run of a heap malloc's size statements: the size aligned to words. -/
theorem mallocSize_run (cM : Ctx) {vm : VM} {a szo : Operand} {ms ms2 : List Stmt}
    {dsz : List Nat} (h : mallocSize vm a ms = some (szo, ms2, dsz)) {E : Env} {ma : Nat}
    {a' : Operand} (ha' : mop vm a = some a') (hm : mval E a' = some ma)
    (himm : ∀ b n, a = .imm b n → ma = n) :
    ∃ pre E', ms = pre ++ ms2 ∧ dsz = defsOf pre ∧ (∀ st ∈ pre, ∀ g a, st.inst ≠ .call g a) ∧
      runPlain cM E pre = pure E' ∧ (ma + 31 < W → mval E' szo = some (align32 ma)) ∧
      ∀ r, r ∉ dsz → E'[r]? = E[r]? := by
  have dyn : mallocSize.dyn vm a ms = some (szo, ms2, dsz) → ∃ pre E', ms = pre ++ ms2 ∧
      dsz = defsOf pre ∧ (∀ st ∈ pre, ∀ g a, st.inst ≠ .call g a) ∧
      runPlain cM E pre = pure E' ∧ (ma + 31 < W → mval E' szo = some (align32 ma)) ∧
      ∀ r, r ∉ dsz → E'[r]? = E[r]? := by
    intro h
    simp only [mallocSize.dyn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨a'', ha'', ⟨t, r1⟩, ht, ⟨sz, r2⟩, hs, rfl, rfl, rfl⟩ := h
    rw [ha'] at ha''; cases ha''
    have hm1 := take1_some ht
    have hm2 := take1_some hs
    simp only at hm1 hm2
    have h31 : mval E (imm 31) = some 31 := by simp [mval, imm]
    have hk : mval (E.insert t (.int 256 (BinOp.eval .add 256 ma 31 % W)))
        (imm (2 ^ 256 - 32)) = some (2 ^ 256 - 32) := by simp [mval, imm]
    refine ⟨[⟨[(t, .int 256)], .bin .add a' (imm 31)⟩,
      ⟨[(sz, .int 256)], .bin .and (.var t) (imm (2 ^ 256 - 32))⟩],
      (E.insert t (.int 256 (BinOp.eval .add 256 ma 31 % W))).insert sz
        (.int 256 (BinOp.eval .and 256 (BinOp.eval .add 256 ma 31 % W) (2 ^ 256 - 32) % W)),
      by rw [hm1, hm2]; rfl, by simp [defsOf], by simp, ?_, ?_, ?_⟩
    · rw [runPlain_bin cM hm h31, runPlain_bin cM (mval_insert_self _ _ _) hk]; rfl
    · intro hlt
      rw [mval_insert_self]
      have he : BinOp.eval .add 256 ma 31 % W = BinOp.eval .add 256 ma 31 :=
        Nat.mod_eq_of_lt (eval_lt _ (by omega) (by unfold W; norm_num))
      rw [he, mallocSize_word hlt, Nat.mod_eq_of_lt (align32_lt hlt)]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [insert_other (Ne.symm hr.2), insert_other (Ne.symm hr.1)]
  cases a with
  | imm bits n =>
    simp only [mallocSize] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨[], E, rfl, rfl, by simp, rfl, fun _ => ?_, fun _ _ => rfl⟩
      rw [himm bits n rfl]; simp [mval, imm]
    · exact dyn h
  | var y => exact dyn h

/-- A heap `evm_malloc n` without the clamp: within H's budget, H's block at the free pointer
    the machine reads, which it bumps by the aligned size (`inv_heap`); past it, H ends
    `exhausted`. -/
theorem inst_heap {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {ms ms' : List Stmt} {callee? : Option Nat}
    {ds : List Nat} {a : Operand} {x : Nat} {tx : Ty} {b0 : Nat} {rest1 : List Stmt}
    {szo : Operand} {ms2 ms3 : List Stmt} {dsz : List Nat} {nf : Nat}
    (hheap : S.hasHeap = true) (hF0 : S.F0 < 2 ^ 32)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) (hnd : ds.Nodup)
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hta : (c.tyOf a).any Ty.value = true)
    (hms : ms = ⟨[(b0, .int 256)], .evm .mload [imm 64]⟩ :: rest1)
    (hsz : mallocSize F.vm a rest1 = some (szo, ms2, dsz))
    (hms2 : ms2 = ⟨[(nf, .int 256)], .bin .add (.var b0) szo⟩ :: ms3)
    (hms3 : ms3 = ⟨[], .evm .mstore [imm 64, .var nf]⟩ :: ms')
    (hx : F.vm.find? x = some (.var b0)) (hds : ds = [b0] ++ [] ++ dsz ++ [nf]) :
    ∃ pre, ms = pre ++ ms' ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  subst hds
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
  have hq := hA.opnd (by rw [hargs]; simp) ha'
  have himm : ∀ b n, a = .imm b n → ma = n := fun b n e => by
    subst e; simp only [evalOp, Option.some.injEq] at hva; subst hva; exact hwa.symm
  have hnd3 : (b0 :: (dsz ++ [nf])).Nodup := hnd
  obtain ⟨hb0m, hnd2⟩ := List.nodup_cons.mp hnd3
  have hb0d : b0 ∉ dsz := fun h => hb0m (List.mem_append_left _ h)
  have hb0nf : b0 ≠ nf := fun e => hb0m (by simp [e])
  have hnfd : nf ∉ dsz := fun h => (List.nodup_append.mp hnd2).2.2 nf h nf (by simp) rfl
  set fp := fpWord w.memory with hfp
  have hfpW : fp < W := toNat_lt' _
  set E1 := envM.insert b0 (.int 256 fp) with hE1
  have hma1 : mval E1 a' = some ma := by
    rw [hE1, mval_insert_other fun q hq' e => hq q hq' (by simp [e])]; exact hma
  obtain ⟨pre2, E2, hrest1, hdsz, hcall2, hrun2, hval2, hag2⟩ := mallocSize_run cM hsz ha' hma1 himm
  have hb0E2 : mval E2 (.var b0) = some fp := by
    simp only [mval]; rw [hag2 b0 hb0d, hE1, Std.TreeMap.getElem?_insert_self]; rfl
  have hfpdef : (Ethereum.uInt256OfByteArray (w.memory.readWithPadding 64 32)).toNat = fp := rfl
  refine ⟨⟨[(b0, .int 256)], .evm .mload [imm 64]⟩ :: pre2 ++
    [⟨[(nf, .int 256)], .bin .add (.var b0) szo⟩, ⟨[], .evm .mstore [imm 64, .var nf]⟩],
    by rw [hms, hrest1, hms2, hms3]; simp, fun O res hres => ?_⟩
  by_cases hbud : hst.heapReq + align32 ma < heapBudget
  swap
  · exact Or.inl ⟨.exhausted, fun rest => ExecBody.exhausted hi hva (by rw [hwa]; omega),
      Or.inr (Or.inl rfl)⟩
  have hbud' : hst.heapReq + align32 ma < 2 ^ 255 := hbud
  have hlt : ma + 31 < W := by have := align32_ge ma; unfold W; omega
  have hval := hval2 hlt
  have hfpF := (hI.fp hheap).2.1
  have hend : fp + align32 ma < W := by unfold W; omega
  -- The machine's run.
  rw [runBodyO_plain O cM envM _ (by
    intro st hst g' a''
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hst
    rcases hst with rfl | hst | rfl | rfl
    · simp
    · exact hcall2 st hst g' a''
    · simp
    · simp)] at hres
  simp only [List.cons_append, runPlain, Fe.M.exec_bind,
    run_mload cM I w (by simp [mval, imm] : mval envM (imm 64) = some 64) (by unfold W; norm_num),
    bind_one, Fe.M.exec_pure] at hres
  rw [hfpdef, Nat.mod_eq_of_lt hfpW, ← hE1, runPlain_append, hrun2] at hres
  simp only [pure_bind] at hres
  rw [runPlain_bin cM hb0E2 hval, eval_add, Nat.mod_mod, Nat.mod_eq_of_lt hend] at hres
  simp only [runPlain, Fe.M.exec_bind,
    run_mstore cM I w (by simp [mval, imm] : mval _ (imm 64) = some 64) (mval_insert_self _ _ _)
      (by unfold W; norm_num), Fe.Sonatina.bind] at hres
  simp at hres
  subst hres
  -- H's step and the invariant.
  obtain ⟨haddr, hI'⟩ := inv_heap hI hheap (base := fp) (n := ma) le_rfl hfpF hbud hF0
  set kb := hst.blocks.size with hkb
  set g' := g.add kb fp g.live True with hg'
  have hwx' : Ty.value tx = true ∧ tx.bits = 256 := by
    simp only [isWord, Bool.and_eq_true, beq_iff_eq] at hwx; exact hwx
  have hfit : (H.Val.ptr kb 0).fits tx = true := by
    rw [fits_iff hwx'.1]; exact ⟨hwx'.2, by positivity⟩
  have hb : bindVals envH s.dsts [.ptr kb 0] = some (envH.insert x (.ptr kb 0)) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  have hlive_lt := hI.live_lt
  have hsz' : ∀ b, b < kb → ({ hst.alloc .malloc ma fp (freshAt w.memory fp ma) with
      heapReq := hst.heapReq + align32 ma } : H.State).bsize b = hst.bsize b := fun b hb' => by
    show (hst.alloc .malloc ma fp (freshAt w.memory fp ma)).bsize b = _
    rw [bsize_alloc, if_neg (by omega)]
  have hrg : ∀ b, b < kb → g'.rg { hst.alloc .malloc ma fp (freshAt w.memory fp ma) with
      heapReq := hst.heapReq + align32 ma } b = g.rg hst b := fun b hb' => by
    simp only [Ghost.rg]
    rw [hg', Ghost.add_j_old (by omega : b ≠ kb), hsz' b hb']
  refine Or.inr ⟨_, _, rfl, envH.insert x (.ptr kb 0), _, g', hI', ?_, ?_,
    fun rest o hr => ExecBody.malloc hi hva (by rw [hwa]; exact hbud) (by rw [hwa]; exact haddr)
      (by rw [hwa]; exact freshAt_length w.memory fp ma) hb (by rw [hwa]; exact hr)⟩
  · refine envRel_step' hE (fun y hy hn' => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn')) hb
      (fun r hr => ?_) (fun y hy hn' => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn'))
      ?_ ?_
    · have h1 : r ≠ b0 := fun e => hr (by simp [e])
      have h2 : r ∉ dsz := fun e => hr (by simp [e])
      have h3 : r ≠ nf := fun e => hr (by simp [e])
      rw [insert_other (Ne.symm h3), hag2 r h2, hE1, insert_other (Ne.symm h1)]
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
      refine ⟨.ptr kb 0, fp, by simp, ⟨tx, hdt, hfit⟩, ?_, ?_, ?_, ?_⟩
      · rw [hx]; simp only [Option.bind_some, mval]
        rw [insert_other (Ne.symm hb0nf), hag2 b0 hb0d, hE1, Std.TreeMap.getElem?_insert_self]; rfl
      · refine ⟨by simp [hg', Ghost.add, Nat.mod_eq_of_lt hfpW], fun hz' => ?_⟩
        rw [hA.D]; exact hA.der hz' (by simp [stmtDerived, hi]) y (by simp [HStmt.defs, hd])
      · exact ⟨by show _ < (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega, by positivity⟩
      · exact Or.inl (Or.inl ⟨rfl, trivial⟩)
  · refine ⟨by show _ ≤ (hst.alloc _ _ _ _).blocks.size; rw [alloc_size]; omega,
      fun b hb' => Ghost.add_j_old (by omega), fun b hb' => hsz' b hb',
      fun b hb' => by show (hst.alloc _ _ _ _).addrOf b = _; rw [addrOf_alloc, if_neg (by omega)],
      fun b hb' => Ghost.add_heap_old (by have := hlive_lt b (hI.heap_live b hb'); omega) hb',
      fun b hb' _ => Ghost.add_live_old (by have := hlive_lt b hb'; omega) hb'⟩

end Fe.Sonatina.Stage3.Place
