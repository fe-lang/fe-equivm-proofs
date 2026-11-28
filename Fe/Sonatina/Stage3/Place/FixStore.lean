import Fe.Sonatina.Stage3.Place.FixStep

/-!
# After a terminal fixed buffer: stores through the buffer

Rule S6 allows `mstore`, `evm_mstore` and `evm_mstore8` after the site only at an address of
the must-origin set: a pointer into the buffer (`SR.must`).  H writes the cells into the buffer's
block, or is `ub` past its end; the machine writes the cells' byte values at the buffer's base
plus the offset (`SR.write`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

section rel

variable {S : SecFacts} {fn : Fn} {kt base n t : Nat} {b : HBlock} {j : Nat} {L : List Nat}
  {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}

theorem SR.blk (hR : SR S fn kt base n t b j L g hst w envH envM) :
    ∃ blk, hst.blocks[kt]? = some blk ∧ blk.size = n ∧ blk.bytes.size = n := by
  obtain ⟨blk, hblk⟩ : ∃ blk, hst.blocks[kt]? = some blk :=
    ⟨_, Array.getElem?_eq_getElem hR.hkt⟩
  have h1 := hR.ksz
  simp only [State.bsize, hblk, Option.map_some, Option.getD_some] at h1
  exact ⟨blk, hblk, h1, by rw [hR.bsz kt blk hblk, h1]⟩

/-- H's range of `len > 0` bytes at a pointer into the buffer. -/
theorem SR.range (hR : SR S fn kt base n t b j L g hst w envH envM) {o len : Nat} (hl : len ≠ 0) :
    hst.range (.ptr kt o) len = if o + len ≤ n then some (.at kt o) else none := by
  obtain ⟨blk, hblk, hsz, -⟩ := hR.blk
  simp [State.range, hl, hblk, hsz]

/-- A write into the buffer, the machine writing the cells' byte values at the base plus the
    offset, keeps `SR`. -/
theorem SR.write (hR : SR S fn kt base n t b j L g hst w envH envM) {o : Nat} {cs : List MByte}
    {m' : ByteArray} (hlen : o + cs.length ≤ n)
    (hm : ∀ k, mem m' k = if base + o ≤ k ∧ k < base + o + cs.length then
      ((cs[k - (base + o)]?).getD (.byte 0)).val hst.addrOf else mem w.memory k)
    {b' : HBlock} {j' : Nat} {L' : List Nat} (hq : FixInv fn b' j' envH) (hL : ∀ x ∈ L', x ∈ L) :
    SR S fn kt base n t b' j' L' g (hst.write (.at kt o) cs) { w with memory := m' } envH envM := by
  have hsz := write_blocks_size hst kt o cs
  have had := addrOf_write hst (.at kt o) cs
  obtain ⟨blk0, hblk0, hs0, hb0⟩ := hR.blk
  refine ⟨hR.world, fun bb blk hblk => ?_, fun bb hbb hj => ?_, fun bb hbb hj => ?_,
    fun x hx => ?_, by rw [hsz]; exact hR.hkt, by rw [bsize_write]; exact hR.ksz, hR.jt, hR.bn,
    fun k hk => ?_, hq, hR.must⟩
  · rw [write_blocks_get?] at hblk
    cases hb : hst.blocks[bb]? with
    | none => rw [hb] at hblk; cases hblk
    | some blk' =>
      rw [hb] at hblk
      simp only [Option.map_some, Option.some.injEq] at hblk
      subst hblk
      split
      · simp only [foldl_set_size]; exact hR.bsz bb blk' hb
      · exact hR.bsz bb blk' hb
  · rw [had]; exact hR.exact bb (by rwa [hsz] at hbb) hj
  · exact hR.zero bb (by rwa [hsz] at hbb) hj
  · obtain ⟨v, m, e1, e2, e3, e4, e5, e6⟩ := hR.vals x (hL x hx)
    refine ⟨v, m, e1, e2, e3, e4, ?_, e6⟩
    cases v with
    | int => trivial
    | ptr => exact ⟨by rw [hsz]; exact e5.1, e5.2⟩
  · have hk0 : hst.blocks[kt]'hR.hkt = blk0 := by
      rw [Array.getElem?_eq_getElem hR.hkt] at hblk0; exact Option.some.inj hblk0
    have hc := cell_write hst kt o cs kt k hR.hkt (by rw [hk0, hb0]; exact hlen)
    show mem m' (base + k) = ((hst.write (.at kt o) cs).cell kt k).val (hst.write (.at kt o) cs).addrOf
    rw [had, hc, hm (base + k)]
    by_cases h1 : o ≤ k
    · rw [if_pos (⟨rfl, h1⟩ : kt = kt ∧ o ≤ k)]
      by_cases h2 : k < o + cs.length
      · rw [if_pos (⟨by omega, by omega⟩ : base + o ≤ base + k ∧ base + k < base + o + cs.length),
          show base + k - (base + o) = k - o by omega, List.getElem?_eq_getElem (by omega)]
        rfl
      · rw [if_neg (by omega : ¬ (base + o ≤ base + k ∧ base + k < base + o + cs.length)),
          List.getElem?_eq_none (by omega), Option.getD_none]
        exact hR.buf k hk
    · rw [if_neg (by omega : ¬ (base + o ≤ base + k ∧ base + k < base + o + cs.length)),
        if_neg (by omega : ¬ (kt = kt ∧ o ≤ k))]
      exact hR.buf k hk

end rel

/-- One byte. -/
def byte1 (x : Nat) : ByteArray := ⟨#[UInt8.ofNat x]⟩

theorem run_mstore8 (cM : Ctx) (I : Fe.EVM.Env) {env : Env} {a v : Operand} {ma mv : Nat}
    (w : World) (ha : mval env a = some ma) (hv : mval env v = some mv) (hm : ma < W) :
    (runInst cM env (.evm .mstore8 [a, v])).exec I w = some (.ok ([],
      { w with memory := (byte1 (Ethereum.UInt256.ofNat mv).toNat).write 0 w.memory ma 1 })) := by
  simp [runInst, EvmOp.run, Fe.EVM.mstore8, byte1, mval_evalWord ha, mval_evalWord hv, toNat_ofNat_lt hm]

/-- What `stmt` accepts at an EVM store: the one machine statement, the same operation on the
    mapped operands. -/
theorem stmt_evmStore {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {op : EvmOp} {a v : Operand}
    (hop : op = .mstore ∨ op = .mstore8) (hi : s.inst = .base (.evm op [a, v]))
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ a' v', mop vm a = some a' ∧ mop vm v = some v' ∧ ms = ⟨[], .evm op [a', v']⟩ :: ms' ∧
      mb' = mb ∧ ds = [] ∧ s.dsts = [] ∧ (c.tyOf a).any Ty.value = true ∧
      (c.tyOf v).any Ty.value = true := by
  simp only [stmt, hi, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨⟨nA, nR⟩, har, hc, args', hargs', ⟨rs, rest⟩, htk, vm2, hfold, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨ds', hms, hlen, -, rfl⟩ := takeN_some htk
  have hnR : nR = 0 := by rcases hop with rfl | rfl <;> simp [EvmOp.arity] at har <;> omega
  subst hnR
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨_, -⟩, hnR⟩, -⟩, harg⟩ := hc
  have hds : ds' = [] := List.eq_nil_of_length_eq_zero hlen
  subst hds
  obtain _ | ⟨ha', _ | ⟨hv', h0⟩⟩ := mapM_some_forall₂ hargs'
  cases h0
  exact ⟨_, _, ha', hv', hms, rfl, rfl, List.eq_nil_of_length_eq_zero hnR,
    harg a (by simp), harg v (by simp)⟩

theorem stmt_mstore {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {a v : Operand} {t : Ty}
    (hi : s.inst = .base (.mstore a v t)) (hd : s.dsts = [])
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ a' v' tv, mop vm a = some a' ∧ mop vm v = some v' ∧ ms = ⟨[], .evm .mstore [a', v']⟩ :: ms' ∧
      mb' = mb ∧ ds = [] ∧ (c.tyOf a).any Ty.value = true ∧ c.tyOf v = some tv ∧
      Ty.value t = true ∧ sameW tv t = true := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨tv, htv, hc, a', ha', v', hv', rest, ht0, rfl, rfl, rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hvt, hsw⟩, hta⟩ := hc
  exact ⟨a', v', tv, ha', hv', take0_some ht0, rfl, rfl, hta, htv, hvt, hsw⟩

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- The end of a store's step: within the buffer H writes the cells and the machine their
    bytes; past its end H is `ub`. -/
theorem FnUnp.storeTail {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {i : Nat} {s : HStmt} (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs₀ : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs₀)) {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs₀).1 = some (vm', mb', ms', ds))
    (hd : s.dsts = []) {kt base n t : Nat} {g : Ghost} {hst : H.State} {w : World} {envH : HEnv}
    {envM : Env} (hR : SR (secS src r efp) fn kt base n t b i (fn.live b i) g hst w envH envM)
    {o len : Nat} {cs : List MByte} {m' : ByteArray} {pre : List Stmt} {cM : Ctx} {O : Oracle}
    (hlen : cs.length = len)
    (hout : ¬ o + len ≤ n → stepInst src.ctx I envH hst s.inst = .ub)
    (hin : o + len ≤ n → stepInst src.ctx I envH hst s.inst = .ok [] (hst.write (.at kt o) cs) ∧
      (∀ k, mem m' k = if base + o ≤ k ∧ k < base + o + cs.length then
        ((cs[k - (base + o)]?).getD (.byte 0)).val hst.addrOf else mem w.memory k) ∧
      ∀ res, (runBodyO O cM envM pre).exec I w = some res → res = .ok (envM, { w with memory := m' })) :
    ∀ res, (runBodyO O cM envM pre).exec I w = some res →
      (∃ o, (∀ rest, ExecBody src I envH (s :: rest) hst (.halt o)) ∧ Excuses o res) ∨
      ∃ envM' w', res = .ok (envM', w') ∧ ∃ envH' hst',
        SR (secS src r efp) fn kt base n t b (i + 1) (fn.live b (i + 1)) g hst' w' envH' envM' ∧
        ∀ rest o, ExecBody src I envH' rest hst' o → ExecBody src I envH (s :: rest) hst o := by
  intro res hres
  by_cases hw : o + len ≤ n
  · obtain ⟨hstep, hm, hrun⟩ := hin hw
    obtain rfl := hrun res hres
    have hbv : bindVals envH s.dsts [] = some envH := by simp [bindVals, hd]
    have hexec : ∀ rest o', ExecBody src I envH rest (hst.write (.at kt o) cs) o' →
        ExecBody src I envH (s :: rest) hst o' := fun rest o' hr => ExecBody.step hstep hbv hr
    have hA := U.at hS hb hs hp hstm
    refine Or.inr ⟨envM, _, rfl, envH, _, hR.write (by omega) hm
      (U.fixStep I b hb i s hs envH hst envH _ hR.q (hexec [] _ ExecBody.nil))
      (fun y hy => hA.keep y hy (by simp [HStmt.defs, hd])), hexec⟩
  · exact Or.inl ⟨.ub, fun rest => ExecBody.ub (hout hw), Or.inl rfl⟩

/-- A store through the buffer after a terminal fixed buffer keeps `SR`. -/
theorem FnUnp.sfxStoreStep {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {i : Nat} {s : HStmt} (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds))
    {a v : Operand} (hkind : (∃ t, s.inst = .base (.mstore a v t)) ∨
      s.inst = .base (.evm .mstore [a, v]) ∨ s.inst = .base (.evm .mstore8 [a, v]))
    {kt base n t : Nat} (hinM : fixInM (fixM fn.f t) a = true)
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b i (fn.live b i) g hst w envH envM) (O : Oracle) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ ∀ res, (runBodyO O cM envM pre).exec I w = some res →
      (∃ o, (∀ rest, ExecBody src I envH (s :: rest) hst (.halt o)) ∧ Excuses o res) ∨
      ∃ envM' w', res = .ok (envM', w') ∧ ∃ envH' hst',
        SR (secS src r efp) fn kt base n t b (i + 1) (fn.live b (i + 1)) g hst' w' envH' envM' ∧
        ∀ rest o, ExecBody src I envH' rest hst' o → ExecBody src I envH (s :: rest) hst o := by
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have hA := U.at hS hb hs hp hstm
  have hI := hR.inv
  have hEv := hR.envRel (l := fn.live b i) (fun x hx => hx)
  have hargs : s.inst.args = [a, v] := by
    rcases hkind with ⟨t, h⟩ | h | h <;> simp [h, HInst.args, HInst.skel, Inst.args]
  have hnobs : (secS src r efp).z = true → (vF fn.F (fn.live b i)).dOp v = false := by
    intro hz
    have h8 := U.rules.s8 hz
    show fn.F.dOp v = false
    rw [U.dOp]
    rcases hkind with ⟨t, h⟩ | h | h
    · exact notObserved_mstore h8 hb hsm h
    · exact notObserved_evm_mstore h8 hb hsm (Or.inl rfl) h
    · exact notObserved_evm_mstore h8 hb hsm (Or.inr rfl) h
  -- The machine statement and the operands.
  obtain ⟨op, len, a', v', ha', hv', hms, rfl, rfl, hd, hta, htv, hop⟩ : ∃ op len a' v',
      mop fn.F.vm a = some a' ∧ mop fn.F.vm v = some v' ∧ ms = ⟨[], .evm op [a', v']⟩ :: ms' ∧
      mb' = mb ∧ ds = [] ∧ s.dsts = [] ∧ (fn.c.tyOf a).any Ty.value = true ∧
      (fn.c.tyOf v).any Ty.value = true ∧
      ((op = .mstore ∧ len = 32 ∧ (s.inst = .base (.evm .mstore [a, v]) ∨ ∃ t tv,
          s.inst = .base (.mstore a v t) ∧ fn.c.tyOf v = some tv ∧ Ty.value t = true ∧
          sameW tv t = true)) ∨
        (op = .mstore8 ∧ len = 1 ∧ s.inst = .base (.evm .mstore8 [a, v]))) := by
    rcases hkind with ⟨t, hi⟩ | hi | hi
    · have hd : s.dsts = [] := by
        cases hds : s.dsts with
        | nil => rfl
        | cons _ _ => simp [stmt, hi, hds] at hstm
      obtain ⟨a', v', tv, ha', hv', hms, h1, h2, hta, htv, hvt, hsw⟩ := stmt_mstore hi hd hstm
      have hval : Ty.value tv = true := by simp only [sameW, Bool.and_eq_true] at hsw; exact hsw.1.1
      exact ⟨.mstore, 32, a', v', ha', hv', hms, h1, h2, hd, hta, by simp [htv, hval],
        Or.inl ⟨rfl, rfl, Or.inr ⟨t, tv, hi, htv, hvt, hsw⟩⟩⟩
    · obtain ⟨a', v', ha', hv', hms, h1, h2, hd, hta, htv⟩ := stmt_evmStore (Or.inl rfl) hi hstm
      exact ⟨.mstore, 32, a', v', ha', hv', hms, h1, h2, hd, hta, htv, Or.inl ⟨rfl, rfl, Or.inl hi⟩⟩
    · obtain ⟨a', v', ha', hv', hms, h1, h2, hd, hta, htv⟩ := stmt_evmStore (Or.inr rfl) hi hstm
      exact ⟨.mstore8, 1, a', v', ha', hv', hms, h1, h2, hd, hta, htv, Or.inr ⟨rfl, rfl, hi⟩⟩
  obtain ⟨ta, hta', -⟩ := tyOf_any hta
  obtain ⟨tv, htv', hvtv⟩ := tyOf_any htv
  obtain ⟨va, ma, hva, -, hma, hra, -, -⟩ := opnd_rel hEv hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, hy]; simp)) hta' ha'
  obtain ⟨vv, mv, hvv, hfv, hmv, hrv, hov, -⟩ := opnd_rel hEv hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, hy]; simp)) htv' hv'
  have hwv : hst.word vv = mv := by
    have := vrel_exact hI hrv hov hnobs; rwa [vSt_word] at this
  have hmvW : mv < W := vrel_lt hrv hfv hvtv
  obtain ⟨y, rfl⟩ : ∃ y, a = .var y := by
    cases a with
    | var y => exact ⟨y, rfl⟩
    | imm => simp [fixInM] at hinM
  obtain ⟨o, rfl⟩ := hR.must y (by simpa [fixInM] using hinM) va hva
  have hma' : (base + o) % W = ma := by have := hra.1; simp only [vG] at this; rwa [hR.jt] at this
  have hbn := hR.bn
  refine ⟨[⟨[], .evm op [a', v']⟩], hms, rfl, ?_⟩
  rcases hop with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hi⟩
  · refine U.storeTail hS I hb hs hp hstm hd hR (o := o) (len := 32) (cs := vv.cells)
      (m' := (Ethereum.UInt256.ofNat mv).toByteArray.write 0 w.memory (base + o) 32) (cells_length vv)
      (fun hw => ?_) (fun hw => ?_)
    · have hr : hst.range (.ptr kt o) 32 = none := by rw [hR.range (by norm_num), if_neg hw]
      rcases hk with hi | ⟨t, tv', hi, htv'', hvt, hsw⟩
      · simp [stepInst, hi, List.mapM_cons, hva, hvv, evmH, EvmOp.arity, EvmOp.memFree, hr]
      · have hfvt : vv.fits t = true := by
          rw [htv'] at htv''; cases htv''; exact fits_sameW (sameW_symm hsw) hfv
        simp [stepInst, hi, hva, hvv, hvt, hfvt, hr]
    · have hr : hst.range (.ptr kt o) 32 = some (.at kt o) := by rw [hR.range (by norm_num), if_pos hw]
      have hmaE : ma = base + o := by rw [← hma', Nat.mod_eq_of_lt (by omega)]
      subst hmaE
      refine ⟨?_, fun k => ?_, fun res hres => ?_⟩
      · rcases hk with hi | ⟨t, tv', hi, htv'', hvt, hsw⟩
        · simp [stepInst, hi, List.mapM_cons, hva, hvv, evmH, EvmOp.arity, EvmOp.memFree, hr]
        · have hfvt : vv.fits t = true := by
            rw [htv'] at htv''; cases htv''; exact fits_sameW (sameW_symm hsw) hfv
          simp [stepInst, hi, hva, hvv, hvt, hfvt, hr]
      · rw [mem_write, cells_length]
        split
        · next hin =>
          rw [Nat.zero_add, ← hwv]
          exact (cells_byte hst vv (by omega)).symm
        · rfl
      · rw [runBodyO_plain O cM envM _ (by simp)] at hres
        simp only [runPlain, Fe.M.exec_bind, run_mstore cM I w hma hmv (by omega)] at hres
        simp [Fe.Sonatina.bind] at hres
        exact hres.symm
  · refine U.storeTail hS I hb hs hp hstm hd hR (o := o) (len := 1)
      (cs := [.byte (UInt8.ofNat (hst.word vv))])
      (m' := (byte1 (Ethereum.UInt256.ofNat mv).toNat).write 0 w.memory (base + o) 1) rfl
      (fun hw => ?_) (fun hw => ?_)
    · have hr : hst.range (.ptr kt o) 1 = none := by rw [hR.range (by norm_num), if_neg hw]
      simp [stepInst, hi, List.mapM_cons, hva, hvv, evmH, EvmOp.arity, EvmOp.memFree, hr]
    · have hr : hst.range (.ptr kt o) 1 = some (.at kt o) := by rw [hR.range (by norm_num), if_pos hw]
      have hmaE : ma = base + o := by rw [← hma', Nat.mod_eq_of_lt (by omega)]
      subst hmaE
      refine ⟨?_, fun k => ?_, fun res hres => ?_⟩
      · simp [stepInst, hi, List.mapM_cons, hva, hvv, evmH, EvmOp.arity, EvmOp.memFree, hr,
          State.writeBytes, Reasoning.Theory.byteArray_toList_eq]
      · rw [mem_write, List.length_singleton]
        split
        · next hin =>
          have hk : k - (base + o) = 0 := by omega
          rw [hk]
          simp [byte1, MByte.val, toNat_ofNat_lt hmvW, hwv]
        · rfl
      · rw [runBodyO_plain O cM envM _ (by simp)] at hres
        simp only [runPlain, Fe.M.exec_bind, run_mstore8 cM I w hma hmv (by omega)] at hres
        simp [Fe.Sonatina.bind] at hres
        exact hres.symm

end unp

end Fe.Sonatina.Stage3.Place
