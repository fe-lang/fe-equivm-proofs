import Fe.Sonatina.Stage3.Place.InstGep

/-!
# Typed loads and stores, `memzero`

A typed `mload`/`mstore` of 32 bytes is the machine's `evm_mload`/`evm_mstore` at the address's
word; `memzero d n` is a copy from calldata at `calldatasize` (zeros, when calldata has fewer
than `2 ^ 256` bytes, `hcd`).  An access H resolves is into a block the origins rule (S3) keeps
live, so the machine's address is the block's machine base plus the offset, below `2 ^ 256`, and
the machine's bytes there are the cells' values (`Inv.bytes`).  An access H does not resolve is
`ub`.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Accesses -/

/-- An access of `len > 0` bytes H resolves is into a block, at an offset that leaves room. -/
theorem range_ptr {st : H.State} {v : H.Val} {len : Nat} {r : H.Range}
    (h : st.range v len = some r) (hl : len ≠ 0) :
    ∃ b o, v = .ptr b o ∧ r = .at b o ∧ o + len ≤ st.bsize b ∧ b < st.blocks.size := by
  unfold State.range at h
  rw [if_neg hl] at h
  cases v with
  | int => cases h
  | ptr b o =>
    dsimp only at h
    cases hb : st.blocks[b]? with
    | none => rw [hb] at h; cases h
    | some blk =>
      rw [hb] at h
      dsimp only at h
      split at h
      · next hle =>
        cases h
        refine ⟨b, o, rfl, rfl, by simp [State.bsize, hb, hle], ?_⟩
        exact (Array.getElem?_eq_some_iff.mp hb).1
      · cases h

/-- A pointer rule S3 allows is into a live block. -/
theorem live_of_orig {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {R : NatMap Range} {fpf : List Range} {os : List Nat} {b o : Nat}
    (h : OrigOk g hst R fpf os (.ptr b o)) : g.live b := by
  rcases h with h | ⟨h, _⟩
  · exact hI.heap_live b h
  · exact h

/-- The machine address of an access into a live block is its base plus the offset. -/
theorem addr_of_vrel {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {dx : Bool} {b o m len : Nat} (hv : VRel g S.z dx (.ptr b o) m) (hb : g.live b)
    (ho : o + len ≤ hst.bsize b) : m = g.j b + o := by
  rw [← hv.1]
  have := hI.bound b hb
  exact Nat.mod_eq_of_lt (by omega)

theorem OrigOk.state {g : Ghost} {hst hst' : H.State} {R : NatMap Range} {fpf : List Range}
    {os : List Nat} {v : H.Val} (h : OrigOk g hst R fpf os v)
    (hlt : ∀ b, g.live b → b < hst.blocks.size)
    (hbs : ∀ b, b < hst.blocks.size → hst'.bsize b = hst.bsize b) : OrigOk g hst' R fpf os v := by
  cases v with
  | int => trivial
  | ptr b o =>
    rcases h with h | ⟨hl, h⟩
    · exact Or.inl h
    · have hr : g.rg hst' b = g.rg hst b := by simp only [Ghost.rg, hbs b (hlt b hl)]
      show g.heap b ∨ (g.live b ∧ ((∃ s, s + 1 ∈ os ∧ R.find? s = some (g.rg hst' b)) ∨
        (0 ∈ os ∧ ∀ r ∈ fpf, Disj r (g.rg hst' b))))
      rw [hr]; exact Or.inr ⟨hl, h⟩

theorem ValOk.state {hst hst' : H.State} {v : H.Val} (h : ValOk hst v)
    (hsz : hst.blocks.size ≤ hst'.blocks.size) : ValOk hst' v := by
  cases v with
  | int => trivial
  | ptr b o => exact ⟨lt_of_lt_of_le h.1 hsz, h.2⟩

/-- A statement that gives no value and changes H's state to one whose blocks keep their sizes
    and address words, related by `Inv` to the machine's: the step goes on. -/
theorem stepOk_st0 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst hst' : H.State} {w w' : World} {envH : HEnv} {envM envM' : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) (hd : s.dsts = [])
    (hstep : stepInst P.ctx I envH hst s.inst = .ok [] hst') (hI' : Inv S hst' w' g)
    (hsz : hst'.blocks.size = hst.blocks.size)
    (hbs : ∀ b, b < hst.blocks.size → hst'.bsize b = hst.bsize b)
    (had : ∀ b, b < hst.blocks.size → hst'.addrOf b = hst.addrOf b)
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) :
    StepOk P I S F g hst envH s L' (.ok (envM', w')) := by
  have hb : bindVals envH s.dsts [] = some envH := by simp [bindVals, hd]
  have hdefs : s.defs = [] := by simp [HStmt.defs, hd]
  refine Or.inr ⟨envM', w', rfl, envH, hst', g, hI', ?_, ⟨le_of_eq hsz.symm, fun _ _ => rfl, hbs,
    had, fun _ h => h, fun _ h _ => h⟩, fun rest o hr => ExecBody.step hstep hb hr⟩
  refine envRel_step hE (fun y hy _ => hA.keep y hy (by rw [hdefs]; simp)) hb hkeep
    (fun y hy _ => hA.clob y (Or.inr hy) (by rw [hdefs]; simp))
    (fun v h => h.state (le_of_eq hsz.symm)) (fun _ _ h => h.state hI.live_lt hbs) ?_
  intro y hy; simp [hd] at hy

/-! ## The machine's memory operations -/

theorem toNat_ofNat_lt {m : Nat} (h : m < W) : (Ethereum.UInt256.ofNat m).toNat = m := by
  simp only [Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat]
  exact Nat.mod_eq_of_lt h

theorem run_mload (cM : Ctx) (I : Fe.EVM.Env) {env : Env} {a : Operand} {m : Nat} (w : World)
    (ha : mval env a = some m) (hm : m < W) :
    (runInst cM env (.evm .mload [a])).exec I w = some (.ok ([.int 256
      (Ethereum.uInt256OfByteArray (w.memory.readWithPadding m 32)).toNat], w)) := by
  simp [runInst, EvmOp.run, Fe.EVM.mload, mval_evalWord ha, toNat_ofNat_lt hm, word]

theorem run_mstore (cM : Ctx) (I : Fe.EVM.Env) {env : Env} {a v : Operand} {ma mv : Nat}
    (w : World) (ha : mval env a = some ma) (hv : mval env v = some mv) (hm : ma < W) :
    (runInst cM env (.evm .mstore [a, v])).exec I w = some (.ok ([],
      { w with memory := (Ethereum.UInt256.ofNat mv).toByteArray.write 0 w.memory ma 32 })) := by
  simp [runInst, EvmOp.run, Fe.EVM.mstore, mval_evalWord ha, mval_evalWord hv, toNat_ofNat_lt hm]

/-- The byte value of cell `k` of a stored value is byte `k` of its word. -/
theorem cells_byte (st : H.State) (v : H.Val) {k : Nat} (hk : k < 32) :
    ((v.cells[k]?).getD (.byte 0)).val st.addrOf = (wordBytes (st.word v)).data.getD k 0 := by
  have h1 := congrArg (·[k]?) (cells_val st v)
  have hl := cells_length v
  simp only [List.getElem?_map] at h1
  rw [List.getElem?_eq_getElem (by omega : k < v.cells.length)] at h1 ⊢
  simp only [Option.map_some, Option.getD_some] at h1 ⊢
  rw [Reasoning.Theory.byteArray_toList_eq, Array.getElem?_toList] at h1
  rw [Array.getD_eq_getD_getElem?, ← h1]
  rfl

theorem fits_int256_nonint {t : Ty} (ht : Ty.value t = true) (hn : ∀ n, t = .int n → False)
    {w : Nat} (hw : w < W) : (H.Val.int 256 w).fits t = true := by
  cases t with
  | ptr => simp only [H.Val.fits, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; exact hw
  | int n => exact absurd rfl (hn n)
  | _ => simp [Ty.value] at ht

theorem load_fits {st : H.State} {b o : Nat} {t : Ty} {v : H.Val} (h : st.load b o t = some v)
    (ht : Ty.value t = true) (hok : ∀ b' o', v = .ptr b' o' → o' < W) : v.fits t = true := by
  unfold State.load at h
  dsimp only at h
  revert h
  split
  · intro h; cases h; simp only [H.Val.fits, decide_eq_true_eq]; exact hok _ _ rfl
  · intro h; cases h
    simp only [H.Val.fits, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; exact hok _ _ rfl
  · split
    · intro h; cases h
      simp only [H.Val.fits, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; assumption
    · intro h; cases h
  · intro h; cases h
    exact fits_int256_nonint ht (by assumption) (toNat_lt' _)

/-- A memory change the invariant does not see: no byte changes. -/
theorem Inv.mem_congr {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {m' : ByteArray} (hm : ∀ i, mem m' i = mem w.memory i) : Inv S hst { w with memory := m' } g where
  world := hI.world
  live_lt := hI.live_lt
  heap_live := hI.heap_live
  heap_has := hI.heap_has
  bytes_size := hI.bytes_size
  exact := hI.exact
  zero := hI.zero
  bound := hI.bound
  disj := hI.disj
  bytes := fun b hb i hi => by rw [hm]; exact hI.bytes b hb i hi
  frags := hI.frags
  e96 := hI.e96
  heap_floor := hI.heap_floor
  fp := fun hh => by
    rw [show fpWord m' = fpWord w.memory from fpWord_congr fun k _ => hm (64 + k)]
    exact hI.fp hh
  frame := hI.frame

theorem tyOf_any {c : FCtx} {a : Operand} (h : (c.tyOf a).any Ty.value = true) :
    ∃ t, c.tyOf a = some t ∧ Ty.value t = true := by
  cases e : c.tyOf a with
  | none => rw [e] at h; cases h
  | some t => rw [e] at h; exact ⟨t, rfl, h⟩

/-- A typed load of 32 bytes (`evm_mload`): from a live block, the machine's word there is the
    word of H's value, which a loaded pointer's origin (a heap block) keeps related. -/
theorem inst_mload {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {t : Ty} {x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.mload a t)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, a', ha', ⟨r, rest⟩, ht, _, ⟨hx, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hvt, hsw⟩, hta⟩ := hc
  obtain ⟨ta, hta', -⟩ := tyOf_any hta
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) hta' ha'
  refine ⟨[_], take1_some ht, rfl, ?_⟩
  cases hr : hst.range va 32 with
  | none => exact templ_ub _ (by simp [stepInst, hi, hva, hvt, hr])
  | some rg =>
    obtain ⟨b, o, rfl, rfl, hob, hbl⟩ := range_ptr hr (by norm_num)
    cases hl : hst.load b o t with
    | none => exact templ_ub _ (by simp [stepInst, hi, hva, hvt, hr, hl])
    | some v =>
      have hlive := live_of_orig hI hga
      have hmaddr := addr_of_vrel hI hra hlive hob
      have hbd := hI.bound b hlive
      obtain ⟨hw, hrel, hok, hheap⟩ := inv_load hI hlive hob hl (F.D x)
      have hfit : v.fits t = true := load_fits hl hvt fun b' o' e => by subst e; exact hok.2
      have hlt : hst.word v < W := word_lt hst v hfit (value_bits hvt).2
      refine templ_one (bits := 256) (M := hst.word v) hI hE hA hd hx (by simp) ?_ hlt
        (by simp [stepInst, hi, hva, hvt, hr, hl]) (fits_sameW hsw hfit) hrel hok ?_
      · rw [run_mload cM I w hma (by omega), hmaddr, hw]
      · cases v with
        | int => trivial
        | ptr b' o' => exact Or.inl (hheap b' o' rfl)

/-- A typed store of 32 bytes (`evm_mstore`): into a live block, the machine writing the 32 bytes
    of the value's word where H writes its cells; a stored pointer is a heap block's (S3), and none
    is stored in address-0 mode (S8). -/
theorem inst_mstore {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a v : Operand} {t : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.mstore a v t)) (hd : s.dsts = [])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨tv, htv, hc, a', ha', v', hv', rest, ht0, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hvt, hsw⟩, hta⟩ := hc
  obtain ⟨ta, hta', -⟩ := tyOf_any hta
  have hargs : s.inst.args = [a, v] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) hta' ha'
  obtain ⟨vv, mv, hvv, hfv, hmv, hrv, hov, hgv⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) htv hv'
  have hnd : S.z = true → F.dOp v = false := fun hz => by
    rw [hA.dOp]
    cases e : Dr.op k v
    · rfl
    · exact absurd (hA.obs hz 1 v (by rw [hargs]; rfl) e) (by simp [nonObserving, hi])
  have hwv : hst.word vv = mv := vrel_exact hI hrv hov hnd
  have hfvt : vv.fits t = true := fits_sameW (sameW_symm hsw) hfv
  refine ⟨[_], take0_some ht0, rfl, ?_⟩
  cases hr : hst.range va 32 with
  | none => exact templ_ub _ (by simp [stepInst, hi, hva, hvv, hvt, hfvt, hr])
  | some rg =>
    obtain ⟨b, o, rfl, rfl, hob, hbl⟩ := range_ptr hr (by norm_num)
    have hlive := live_of_orig hI hga
    have hmaddr := addr_of_vrel hI hra hlive hob
    have hbd := hI.bound b hlive
    intro O res hres
    rw [runBodyO_plain O cM envM _ (by simp)] at hres
    simp only [runPlain, Fe.M.exec_bind, run_mstore cM I w hma hmv (by omega)] at hres
    simp [Fe.Sonatina.bind] at hres
    subst hres
    have hI' := inv_write hI hlive (cs := vv.cells) (o := o) (by rw [cells_length]; exact hob)
      (m' := (Ethereum.UInt256.ofNat mv).toByteArray.write 0 w.memory ma 32) (fun i => ?_)
      (fun cc hc b' o' k' he => ?_)
    · exact stepOk_st0 hI hE hA hd (by simp [stepInst, hi, hva, hvv, hvt, hfvt, hr]) hI'
        (write_blocks_size ..) (fun b' _ => bsize_write ..) (fun b' _ => by rw [addrOf_write])
        (fun _ _ => rfl)
    · rw [mem_write, cells_length, hmaddr]
      split
      · next hin =>
        rw [Nat.zero_add, ← hwv]
        exact (cells_byte hst vv (by omega)).symm
      · rfl
    · cases vv with
      | int => simp [H.Val.cells] at hc; obtain ⟨_, _, rfl⟩ := hc; cases he
      | ptr bp op' =>
        simp only [H.Val.cells, List.mem_map, List.mem_finRange, true_and] at hc
        obtain ⟨_, rfl⟩ := hc
        cases he
        have h3 := hA.s3 a v (Or.inl ⟨t, hi⟩)
        rw [h3] at hgv
        refine ⟨?_, hov.2, ?_⟩
        · rcases hgv with h | ⟨_, ⟨s', hs', _⟩ | ⟨h0, _⟩⟩
          · exact h
          · simp at hs'
          · simp at h0
        · cases hz : S.z
          · rfl
          · exact absurd (hrv.2 hz) (by rw [hnd hz]; simp)

theorem zeros_size (n : Nat) : (⟨Array.replicate n 0⟩ : ByteArray).size = n := by
  show (Array.replicate n (0 : UInt8)).size = n
  exact Array.size_replicate

theorem run_calldataSize (cM : Ctx) (I : Fe.EVM.Env) {env : Env} (w : World) :
    (runInst cM env (.evm .calldataSize [])).exec I w = some (.ok ([.int 256
      (Ethereum.UInt256.ofNat I.calldata.size).toNat], w)) := by
  simp [runInst, EvmOp.run, Fe.EVM.calldatasize, word]

theorem run_calldataCopy (cM : Ctx) (I : Fe.EVM.Env) {env : Env} {d o l : Operand} {md mo ml : Nat}
    (w : World) (hd : mval env d = some md) (ho : mval env o = some mo) (hl : mval env l = some ml)
    (hmd : md < W) (hmo : mo < W) (hml : ml < W) :
    (runInst cM env (.evm .calldataCopy [d, o, l])).exec I w = some (.ok ([],
      { w with memory := I.calldata.write mo w.memory md ml })) := by
  simp [runInst, EvmOp.run, Fe.EVM.calldatacopy, mval_evalWord hd, mval_evalWord ho,
    mval_evalWord hl, toNat_ofNat_lt hmd, toNat_ofNat_lt hmo, toNat_ofNat_lt hml]

/-- `memzero d n` (a copy from calldata at `calldatasize`, `hcd`): zero bytes into a live block,
    where H writes zero bytes. -/
theorem inst_memzero {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {d l : Operand}
    (hcd : I.calldata.size < W)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.memzero d l)) (hdd : s.dsts = [])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, hdd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, ⟨sz, rest1⟩, hts, d', hd', l', hl', rest, ht0, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨td, htd, hvd⟩ := tyOf_any hc.1
  obtain ⟨tl, htl, hvl⟩ := tyOf_any hc.2
  have hargs : s.inst.args = [d, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vd, md, hvd', hfd, hmd, hrd, hod, hgd⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) htd hd'
  obtain ⟨vl, ml, hvl', hfl, hml, hwl, hll⟩ := opnd_word hI hE hA (i := 1) (by rw [hargs]; rfl)
    (by simp [nonObserving, hi]) htl hl' hvl
  have hld := vrel_lt hrd hfd hvd
  have hms1 := take1_some hts
  have hms2 := take0_some ht0
  simp only at hms1 hms2
  refine ⟨[_, _], by rw [hms1, hms2]; rfl, rfl, fun O res hres => ?_⟩
  set E1 := envM.insert sz (.int 256 I.calldata.size) with hE1
  have hsz1 : mval E1 (.var sz) = some I.calldata.size := mval_insert_self _ _ _
  have hd1 : mval E1 d' = some md := by
    rw [hE1, mval_insert_other fun q hq e => hA.opnd (by rw [hargs]; simp) hd' q hq (by simp [e])]
    exact hmd
  have hl1 : mval E1 l' = some ml := by
    rw [hE1, mval_insert_other fun q hq e => hA.opnd (by rw [hargs]; simp) hl' q hq (by simp [e])]
    exact hml
  rw [runBodyO_plain O cM envM _ (by simp)] at hres
  simp only [runPlain, Fe.M.exec_bind, run_calldataSize, toNat_ofNat_lt hcd] at hres
  simp only [Fe.Sonatina.bind, List.length_cons, List.length_nil, beq_self_eq_true, if_true,
    Fe.M.exec_pure, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    Val.as, Ty.bits, Nat.mod_eq_of_lt hcd, pure_bind] at hres
  rw [← hE1, run_calldataCopy cM I w hd1 hsz1 hl1 hld hcd hll] at hres
  simp [Fe.Sonatina.bind] at hres
  subst hres
  have hkeep : ∀ r, r ∉ [sz] → E1[r]? = envM[r]? := fun r hr =>
    insert_other fun e => hr (by simp [e])
  -- The bytes the machine writes are zeros.
  have hz0 : ∀ i, I.calldata.data.getD (I.calldata.size + i) 0 = 0 := fun i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (show I.calldata.data.size ≤ I.calldata.size + i from Nat.le_add_right _ _)]
    rfl
  by_cases h0 : ml = 0
  · subst h0
    have hI' := hI.mem_congr (m' := I.calldata.write I.calldata.size w.memory md 0)
      (fun i => by rw [mem_write]; simp)
    have hr0 : hst.range vd 0 = some .empty := by simp [State.range]
    exact stepOk_st0 hI hE hA hdd (by simp only [stepInst, hi, hvd', hvl', hwl, hr0]; rfl) hI'
      rfl (fun _ _ => rfl) (fun _ _ => rfl) hkeep
  · cases hr : hst.range vd ml with
    | none => exact Or.inl ⟨.ub, fun _ => ExecBody.ub (by simp only [stepInst, hi, hvd', hvl', hwl,
        hr]), Or.inl rfl⟩
    | some rg =>
      obtain ⟨b, o, rfl, rfl, hob, hbl⟩ := range_ptr hr h0
      have hlive := live_of_orig hI hgd
      have hmaddr := addr_of_vrel hI hrd hlive hob
      have hI' := inv_write hI hlive (cs := ((⟨Array.replicate ml 0⟩ : ByteArray).toList.map .byte))
        (o := o) (by rw [List.length_map, toList_length, zeros_size]; exact hob)
        (m' := I.calldata.write I.calldata.size w.memory md ml) (fun i => ?_)
        (fun cc hc b' o' k' he => ?_)
      · exact stepOk_st0 hI hE hA hdd (by simp only [stepInst, hi, hvd', hvl', hwl, hr]; rfl)
          hI' (write_blocks_size ..) (fun b' _ => bsize_write ..) (fun b' _ => by rw [addrOf_write])
          hkeep
      · rw [mem_write, hmaddr]
        rw [List.length_map, toList_length, zeros_size]
        split
        · next hin =>
          rw [hz0, List.getElem?_map, Reasoning.Theory.byteArray_toList_eq]
          simp [Array.getElem?_replicate, show i - (g.j b + o) < ml by omega, MByte.val]
        · rfl
      · simp only [List.mem_map] at hc
        obtain ⟨_, _, rfl⟩ := hc
        cases he

end Fe.Sonatina.Stage3.Place
