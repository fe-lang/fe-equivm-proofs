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
    (hA1 : ∀ r, F.R.find? x = some r → ∀ y ∈ L', y ≠ x → ∀ o ∈ origOf F.O (.var y),
      o = 0 ∨ ∃ r', F.R.find? (o - 1) = some r' ∧ Disj r r')
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
          rcases hA1 _ hR y hy hyx (s' + 1) hs' with h0 | ⟨r', hr', hd'⟩
          · cases h0
          · simp only [Nat.add_sub_cancel] at hr'
            rw [hRs] at hr'; cases hr'
            exact hd'.symm
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

end Fe.Sonatina.Stage3.Place
