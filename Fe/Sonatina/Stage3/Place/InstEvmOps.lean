import Fe.Sonatina.Stage3.Place.InstEvmMem

/-!
# EVM operations that touch memory, one by one

Each lemma: the operation's template (one machine statement, the same operation on the operands'
machine values) ends as H's step does.  The ranges, writes and world parts are
`InstEvmMem.lean`'s.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

section ops

variable {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
  {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
  {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat}

/-- `evm_mstore8 p v`: H writes the byte of `v`'s word where the machine does. -/
theorem evm_mstore8 {p v : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .mstore8 [p, v]))
    (harg : ∀ a ∈ [p, v], (c.tyOf a).any Ty.value = true)
    (hm : [p, v].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .mstore8 args'⟩] := by
  obtain ⟨p', t1, hp, hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨v', t2, hv, hm2, rfl⟩ := mapM_cons' hm1
  cases mapM_nil' hm2
  have hargs : s.inst.args = [p, v] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vp, mp, hvp, hmp, hlp, hrp, -, hgp, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg p (by simp)) hp
  obtain ⟨vv, mv, hvv, hmv, hlv, -, -, -, hwv⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg v (by simp)) hv
  have hwv := hwv (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .mstore8 [vp, vv] :=
    step_evm hi (by simp [hvp, hvv])
  intro O res hres
  rw [run_evm0 O cM envM .mstore8 (.cons hmp (.cons hmv .nil))
    (Fe.EVM.mstore8 (.ofNat mp) (.ofNat mv)) rfl] at hres
  cases hr : hst.range vp 1 with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr])
  | some rg =>
    have hR := rangeAt_of hI hrp hgp hr
    simp only [Fe.EVM.mstore8, Fe.M.exec_bind, Fe.M.exec_modify, Fe.M.exec_pure,
      Option.some.injEq, toNat_ofNat_lt hlp, toNat_ofNat_lt hlv] at hres
    subst hres
    have hI' := inv_writeBytes_at hI hR (bs := ⟨#[UInt8.ofNat mv]⟩) rfl
      (m' := (⟨#[UInt8.ofNat mv]⟩ : ByteArray).write 0 w.memory mp 1) (fun i => by
        rw [mem_write]; simp only [Nat.zero_add])
    exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwv])
      hI' (write_size ..) (fun _ _ => bsize_write ..) (fun _ _ => by rw [State.writeBytes, addrOf_write])
      (fun _ _ => rfl)

/-- `evm_keccak256 p l`: the hash of H's bytes at the range, the machine's there. -/
theorem evm_keccak {p l : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .keccak256 [p, l]))
    (harg : ∀ a ∈ [p, l], (c.tyOf a).any Ty.value = true)
    (hm : [p, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .keccak256 args'⟩] := by
  obtain ⟨p', t1, hp, hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨l', t2, hl, hm2, rfl⟩ := mapM_cons' hm1
  cases mapM_nil' hm2
  have hargs : s.inst.args = [p, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vp, mp, hvp, hmp, hlp, hrp, -, hgp, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg p (by simp)) hp
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg l (by simp)) hl
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .keccak256 [vp, vl] :=
    step_evm hi (by simp [hvp, hvl])
  intro O res hres
  rw [run_evm1 O cM envM .keccak256 (.cons hmp (.cons hml .nil)) r
    (Fe.EVM.keccak256 (.ofNat mp) (.ofNat ml)) rfl] at hres
  cases hr : hst.range vp ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl])
  | some rg =>
    have hR := rangeAt_of hI hrp hgp hr
    simp only [Fe.EVM.keccak256, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_pure,
      Option.some.injEq, toNat_ofNat_lt hlp, toNat_ofNat_lt hll, hR.bytes hI, toNat_ofNat] at hres
    subst hres
    exact stepOk_pure1 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl, W])
      (fits_word hwx (Nat.mod_lt _ (by positivity))) insert_keep (mval_ins hvx) rfl trivial trivial

/-- `evm_mload a` (a typed load at `i256`): from a live block, the machine's word there is the
    word of H's value. -/
theorem evm_mload {a : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .mload [a]))
    (harg : ∀ b ∈ [a], (c.tyOf b).any Ty.value = true)
    (hm : [a].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .mload args'⟩] := by
  obtain ⟨a', t1, ha, hm1, rfl⟩ := mapM_cons' hm
  cases mapM_nil' hm1
  have hargs : s.inst.args = [a] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hma, hla, hra, -, hga, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg a (by simp)) ha
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .mload [va] :=
    step_evm hi (by simp [hva])
  intro O res hres
  rw [run_evm1 O cM envM .mload (.cons hma .nil) r (Fe.EVM.mload (.ofNat ma)) rfl] at hres
  cases hr : hst.range va 32 with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr])
  | some rg =>
    rcases rangeAt_of hI hra hga hr with ⟨-, h0⟩ | ⟨b, o, rfl, hb, hob, hmaddr⟩
    · cases h0
    cases hl : hst.load b o (.int 256) with
    | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hl])
    | some v =>
      obtain ⟨hw, hrel, hok, hheap⟩ := inv_load hI hb hob hl (F.D x)
      simp only [Fe.EVM.mload, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_pure, Option.some.injEq,
        toNat_ofNat_lt hla] at hres
      rw [hmaddr, hw] at hres
      subst hres
      have hfit : v.fits (.int 256) = true := load_fits hl (by decide) fun b' o' e => by
        subst e; exact hok.2
      refine stepOk_pure1 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hl])
        (fits_sameW (sameW_symm (isWord_sameW hwx)) hfit) insert_keep (mval_ins hvx) hrel hok ?_
      cases v with
      | int => trivial
      | ptr b' o' => exact Or.inl (hheap b' o' rfl)

/-- `evm_mstore a v`: H writes `v`'s cells where the machine writes its word's bytes; a stored
    pointer is a heap block's (S3), and none is stored in address-0 mode (S8). -/
theorem evm_mstore {a v : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .mstore [a, v]))
    (harg : ∀ b ∈ [a, v], (c.tyOf b).any Ty.value = true)
    (hm : [a, v].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .mstore args'⟩] := by
  obtain ⟨a', t1, ha, hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨v', t2, hv, hm2, rfl⟩ := mapM_cons' hm1
  cases mapM_nil' hm2
  have hargs : s.inst.args = [a, v] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hma, hla, hra, -, hga, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg a (by simp)) ha
  obtain ⟨vv, mv, hvv, hmv, hlv, hrv, hov, hgv, hwv⟩ := evm_arg hI hE hA (i := 1)
    (by rw [hargs]; rfl) (harg v (by simp)) hv
  have hwv := hwv (by simp [nonObserving, hi, EvmOp.addrPos])
  have hnd : S.z = true → F.dOp v = false := fun hz => by
    rw [hA.dOp]
    cases e : Dr.op k v
    · rfl
    · exact absurd (hA.obs hz 1 v (by rw [hargs]; rfl) e) (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .mstore [va, vv] :=
    step_evm hi (by simp [hva, hvv])
  intro O res hres
  rw [run_evm0 O cM envM .mstore (.cons hma (.cons hmv .nil))
    (Fe.EVM.mstore (.ofNat ma) (.ofNat mv)) rfl] at hres
  cases hr : hst.range va 32 with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr])
  | some rg =>
    have hR := rangeAt_of hI hra hga hr
    simp only [Fe.EVM.mstore, Fe.M.exec_bind, Fe.M.exec_modify, Fe.M.exec_pure,
      Option.some.injEq, toNat_ofNat_lt hla] at hres
    subst hres
    have hI' := inv_write_at hI hR (cs := vv.cells) (cells_length vv)
      (m' := (Ethereum.UInt256.ofNat mv).toByteArray.write 0 w.memory ma 32) (fun i => by
        rw [mem_write]
        split
        · next hin =>
          rw [Nat.zero_add, cells_byte hst vv (by omega), hwv]; rfl
        · rfl) (fun cc hc b' o' k' he => ?_)
    · exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr])
        hI' (write_size ..) (fun _ _ => bsize_write ..) (fun _ _ => by rw [addrOf_write])
        (fun _ _ => rfl)
    · cases vv with
      | int => simp [H.Val.cells] at hc; obtain ⟨_, _, rfl⟩ := hc; cases he
      | ptr bp op' =>
        simp only [H.Val.cells, List.mem_map, List.mem_finRange, true_and] at hc
        obtain ⟨_, rfl⟩ := hc
        cases he
        have h3 := hA.s3 a v (Or.inr hi)
        rw [h3] at hgv
        refine ⟨?_, hov.2, ?_⟩
        · rcases hgv with h | ⟨_, ⟨s', hs', _⟩ | ⟨h0, _⟩⟩
          · exact h
          · simp at hs'
          · simp at h0
        · cases hz : S.z
          · rfl
          · exact absurd (hrv.2 hz) (by rw [hnd hz]; simp)

/-- `evm_mcopy d s l`: H copies the cells of one range to the other, the machine their bytes. -/
theorem evm_mcopy {d sr l : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .mcopy [d, sr, l]))
    (harg : ∀ b ∈ [d, sr, l], (c.tyOf b).any Ty.value = true)
    (hm : [d, sr, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .mcopy args'⟩] := by
  obtain ⟨d', t1, hd', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨s', t2, hs', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [d, sr, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vd, md, hvd, hmd, hld, hrd, -, hgd, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg d (by simp)) hd'
  obtain ⟨vs, ms, hvs, hms, hls, hrs, -, hgs, -⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg sr (by simp)) hs'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .mcopy [vd, vs, vl] :=
    step_evm hi (by simp [hvd, hvs, hvl])
  intro O res hres
  rw [run_evm0 O cM envM .mcopy (.cons hmd (.cons hms (.cons hml .nil)))
    (mcopyIR (.ofNat md) (.ofNat ms) (.ofNat ml)) rfl] at hres
  cases hr : hst.range vd ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl])
  | some rd =>
  cases hr2 : hst.range vs ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hr2, hwl])
  | some rs =>
    have hRd := rangeAt_of hI hrd hgd hr
    have hRs := rangeAt_of hI hrs hgs hr2
    obtain ⟨hcl, hcv, hcf⟩ := cells_at hI hRs
    unfold mcopyIR at hres
    split_ifs at hres
    · simp [Fe.M.exec_bind, Fe.M.exec_diverge] at hres
    simp only [Fe.EVM.mcopy, Fe.M.exec_bind, Fe.M.exec_modify, Fe.M.exec_pure, Option.some.injEq,
      toNat_ofNat_lt hld, toNat_ofNat_lt hls, toNat_ofNat_lt hll] at hres
    subst hres
    have hI' := inv_write_at hI hRd (cs := hst.cells rs ml) hcl
      (m' := w.memory.write ms w.memory md ml) (fun i => by
        rw [mem_write]
        split
        · next hin => rw [hcv _ (by omega)]; rfl
        · rfl) hcf
    exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hr2, hwl])
      hI' (write_size ..) (fun _ _ => bsize_write ..) (fun _ _ => by rw [addrOf_write])
      (fun _ _ => rfl)

/-- `evm_calldata_copy d o l`: H writes the calldata's bytes where the machine copies them. -/
theorem evm_calldataCopy {d o l : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .calldataCopy [d, o, l]))
    (harg : ∀ b ∈ [d, o, l], (c.tyOf b).any Ty.value = true)
    (hm : [d, o, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .calldataCopy args'⟩] := by
  obtain ⟨d', t1, hd', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨o', t2, ho', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [d, o, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vd, md, hvd, hmd, hld, hrd, -, hgd, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg d (by simp)) hd'
  obtain ⟨vo, mo, hvo, hmo, hlo, -, -, -, hwo⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg o (by simp)) ho'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwo := hwo (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .calldataCopy [vd, vo, vl] :=
    step_evm hi (by simp [hvd, hvo, hvl])
  intro O res hres
  rw [run_evm0 O cM envM .calldataCopy (.cons hmd (.cons hmo (.cons hml .nil)))
    (Fe.EVM.calldatacopy (.ofNat md) (.ofNat mo) (.ofNat ml)) rfl] at hres
  cases hr : hst.range vd ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl])
  | some rg =>
    have hR := rangeAt_of hI hrd hgd hr
    simp only [Fe.EVM.calldatacopy, Fe.M.exec_bind, Fe.M.exec_read, Fe.M.exec_modify,
      Fe.M.exec_pure, Option.some.injEq, toNat_ofNat_lt hld, toNat_ofNat_lt hlo,
      toNat_ofNat_lt hll] at hres
    subst hres
    have hI' := inv_writeBytes_at hI hR (bs := I.calldata.readWithPadding mo ml)
      (Check.readWithPadding_size' _ _ _) (m' := I.calldata.write mo w.memory md ml)
      (mem_copy _ _ _ _ _)
    exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwo, hwl])
      hI' (write_size ..) (fun _ _ => bsize_write ..) (fun _ _ => by rw [State.writeBytes, addrOf_write])
      (fun _ _ => rfl)

/-- `evm_code_copy d o l`: H writes the code's bytes where the machine copies them. -/
theorem evm_codeCopy {d o l : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .codeCopy [d, o, l]))
    (harg : ∀ b ∈ [d, o, l], (c.tyOf b).any Ty.value = true)
    (hm : [d, o, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .codeCopy args'⟩] := by
  obtain ⟨d', t1, hd', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨o', t2, ho', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [d, o, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vd, md, hvd, hmd, hld, hrd, -, hgd, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg d (by simp)) hd'
  obtain ⟨vo, mo, hvo, hmo, hlo, -, -, -, hwo⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg o (by simp)) ho'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwo := hwo (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .codeCopy [vd, vo, vl] :=
    step_evm hi (by simp [hvd, hvo, hvl])
  intro O res hres
  rw [run_evm0 O cM envM .codeCopy (.cons hmd (.cons hmo (.cons hml .nil)))
    (Fe.EVM.codecopy (.ofNat md) (.ofNat mo) (.ofNat ml)) rfl] at hres
  cases hr : hst.range vd ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl])
  | some rg =>
    have hR := rangeAt_of hI hrd hgd hr
    simp only [Fe.EVM.codecopy, Fe.M.exec_bind, Fe.M.exec_read, Fe.M.exec_modify,
      Fe.M.exec_pure, Option.some.injEq, toNat_ofNat_lt hld, toNat_ofNat_lt hlo,
      toNat_ofNat_lt hll] at hres
    subst hres
    have hI' := inv_writeBytes_at hI hR (bs := I.code.readWithPadding mo ml)
      (Check.readWithPadding_size' _ _ _) (m' := I.code.write mo w.memory md ml)
      (mem_copy _ _ _ _ _)
    exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwo, hwl])
      hI' (write_size ..) (fun _ _ => bsize_write ..) (fun _ _ => by rw [State.writeBytes, addrOf_write])
      (fun _ _ => rfl)

/-- `evm_ext_code_copy a d o l`: H writes the account's code bytes where the machine copies them. -/
theorem evm_extCodeCopy {a d o l : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .extCodeCopy [a, d, o, l]))
    (harg : ∀ b ∈ [a, d, o, l], (c.tyOf b).any Ty.value = true)
    (hm : [a, d, o, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .extCodeCopy args'⟩] := by
  obtain ⟨a', t0, ha', hm0, rfl⟩ := mapM_cons' hm
  obtain ⟨d', t1, hd', hm1, rfl⟩ := mapM_cons' hm0
  obtain ⟨o', t2, ho', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [a, d, o, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hma, hla, -, -, -, hwa⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg a (by simp)) ha'
  obtain ⟨vd, md, hvd, hmd, hld, hrd, -, hgd, -⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg d (by simp)) hd'
  obtain ⟨vo, mo, hvo, hmo, hlo, -, -, -, hwo⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg o (by simp)) ho'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 3) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwa := hwa (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwo := hwo (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .extCodeCopy [va, vd, vo, vl] :=
    step_evm hi (by simp [hva, hvd, hvo, hvl])
  intro O res hres
  rw [run_evm0 O cM envM .extCodeCopy (.cons hma (.cons hmd (.cons hmo (.cons hml .nil))))
    (Fe.EVM.extcodecopy (.ofNat ma) (.ofNat md) (.ofNat mo) (.ofNat ml)) rfl] at hres
  cases hr : hst.range vd ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwl])
  | some rg =>
    have hR := rangeAt_of hI hrd hgd hr
    simp only [Fe.EVM.extcodecopy, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_set,
      Fe.M.exec_pure, Option.some.injEq, toNat_ofNat_lt hld, toNat_ofNat_lt hlo,
      toNat_ofNat_lt hll] at hres
    subst hres
    have hI' := inv_writeBytes_at hI hR
      (bs := (((w.accounts.get? (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))).option
        ByteArray.empty (·.code)).readWithPadding mo ml))
      (Check.readWithPadding_size' _ _ _) (mem_copy _ _ _ _ _)
    have hst1 : stepInst P.ctx I envH hst s.inst = .ok [] (hst.writeBytes rg
        (((w.accounts.get? (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))).option
          ByteArray.empty (·.code)).readWithPadding mo ml)) := by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, State.uword, hwa, hwo, hwl,
        ← world_accounts hI]
    exact stepOk_st0 hI hE hA hd hst1 hI' (write_size ..) (fun _ _ => bsize_write ..)
      (fun _ _ => by rw [State.writeBytes, addrOf_write]) (fun _ _ => rfl)

/-- `evm_return_data_copy d o l`: past the return data both exit `oob`; else H writes the return
    data's bytes where the machine copies them. -/
theorem evm_returnDataCopy {d o l : Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm .returnDataCopy [d, o, l]))
    (harg : ∀ b ∈ [d, o, l], (c.tyOf b).any Ty.value = true)
    (hm : [d, o, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm .returnDataCopy args'⟩] := by
  obtain ⟨d', t1, hd', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨o', t2, ho', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [d, o, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vd, md, hvd, hmd, hld, hrd, -, hgd, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg d (by simp)) hd'
  obtain ⟨vo, mo, hvo, hmo, hlo, -, -, -, hwo⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg o (by simp)) ho'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwo := hwo (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .returnDataCopy [vd, vo, vl] :=
    step_evm hi (by simp [hvd, hvo, hvl])
  have hrdw := world_returnData hI
  intro O res hres
  rw [run_evm0 O cM envM .returnDataCopy (.cons hmd (.cons hmo (.cons hml .nil)))
    (Fe.EVM.returndatacopy (.ofNat md) (.ofNat mo) (.ofNat ml)) rfl] at hres
  by_cases hob : mo + ml > w.returnData.size
  · simp only [Fe.EVM.returndatacopy, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_fail,
      toNat_ofNat_lt hlo, toNat_ofNat_lt hll, hob, if_true, Option.some.injEq] at hres
    subst hres
    exact stepOk_exit (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hwo, hwl, ← hrdw, hob])
  cases hr : hst.range vd ml with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwo, hwl, ← hrdw, hob])
  | some rg =>
    have hR := rangeAt_of hI hrd hgd hr
    simp only [Fe.EVM.returndatacopy, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_set,
      Fe.M.exec_pure, Option.some.injEq, toNat_ofNat_lt hld, toNat_ofNat_lt hlo,
      toNat_ofNat_lt hll, hob, if_false] at hres
    subst hres
    have hI' := inv_writeBytes_at hI hR (bs := w.returnData.readWithPadding mo ml)
      (Check.readWithPadding_size' _ _ _) (mem_copy _ _ _ _ _)
    have hst1 : stepInst P.ctx I envH hst s.inst =
        .ok [] (hst.writeBytes rg (w.returnData.readWithPadding mo ml)) := by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hr, hwo, hwl, ← hrdw, hob]
    exact stepOk_st0 hI hE hA hd hst1 hI' (write_size ..) (fun _ _ => bsize_write ..)
      (fun _ _ => by rw [State.writeBytes, addrOf_write]) (fun _ _ => rfl)

/-- `evm_log k p l topics…`: under a static call both exit `static`; else H emits its bytes at
    the range, the machine's there. -/
theorem evm_log {kk : Nat} {p l : Operand} {ts : List Operand} {args' : List Operand}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = [])
    (hi : s.inst = .base (.evm (.log kk) (p :: l :: ts))) (hk : kk ≤ 4) (hlen : ts.length = kk)
    (harg : ∀ b ∈ p :: l :: ts, (c.tyOf b).any Ty.value = true)
    (hm : (p :: l :: ts).mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[], .evm (.log kk) args'⟩] := by
  obtain ⟨p', t1, hp', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨l', ts', hl', hts, rfl⟩ := mapM_cons' hm1
  have hargs : s.inst.args = p :: l :: ts := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vp, mp, hvp, hmp, hlp, hrp, -, hgp, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg p (by simp)) hp'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  obtain ⟨tvs, tms, htvs, htms, hmap, hlt⟩ := args_rel (st := hst) (envH := envH) (envM := envM) hts
    (fun a ha a' ha' => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
      obtain ⟨v, m, hv, hm, -, -, -, -, hw⟩ := evm_arg hI hE hA (i := j + 2)
        (by rw [hargs]; simpa using hj) (harg a (by simp [ha])) ha'
      exact ⟨v, m, hv, hm, hw (by simp [nonObserving, hi, EvmOp.addrPos])⟩)
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst (.log kk) (vp :: vl :: tvs) :=
    step_evm hi (by simp [hvp, hvl, htvs])
  rw [hlen] at hlt
  intro O res hres
  rw [run_evm0 O cM envM (.log kk) (.cons hmp (.cons hml htms))
    (Fe.EVM.logData (.ofNat mp) (.ofNat ml) (tms.map Ethereum.UInt256.ofNat).toArray) rfl] at hres
  rw [show Fe.EVM.logData (.ofNat mp) (.ofNat ml) (tms.map Ethereum.UInt256.ofNat).toArray =
    (get >>= fun m => Fe.EVM.emit (tms.map Ethereum.UInt256.ofNat).toArray
      (m.memory.readWithPadding (Ethereum.UInt256.ofNat mp).toNat (Ethereum.UInt256.ofNat ml).toNat))
    from rfl, exec_get_bind, toNat_ofNat_lt hlp, toNat_ofNat_lt hll] at hres
  by_cases hperm : I.perm = false
  · simp only [Fe.EVM.emit, Fe.M.exec_bind, Fe.M.exec_read, hperm, Bool.false_eq_true, if_false,
      Fe.M.exec_fail, Option.some.injEq] at hres
    subst hres
    exact stepOk_exit (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hk, hlt, hperm])
  cases hr : hst.range vp ml with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hk, hlt, hperm, hwl, hr])
  | some rg =>
    have hR := rangeAt_of hI hrp hgp hr
    rw [hR.bytes hI] at hres
    refine stepOk_lift0 hI hE hA hd (ignoresMemory_emit _ _) ?_ hres
    rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hk, hlt, hperm, hwl, hr, hmap]

/-- `evm_create v p l`: H creates from its bytes at the range, the machine's there, by the
    memory-free core of the creation. -/
theorem evm_create {v p l : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .create [v, p, l]))
    (harg : ∀ b ∈ [v, p, l], (c.tyOf b).any Ty.value = true)
    (hm : [v, p, l].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .create args'⟩] := by
  obtain ⟨v', t1, hv', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨p', t2, hp', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  cases mapM_nil' hm3
  have hargs : s.inst.args = [v, p, l] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vv, mv, hvv, hmv, hlv, -, -, -, hwv⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg v (by simp)) hv'
  obtain ⟨vp, mp, hvp, hmp, hlp, hrp, -, hgp, -⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg p (by simp)) hp'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  have hwv := hwv (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .create [vv, vp, vl] :=
    step_evm hi (by simp [hvv, hvp, hvl])
  intro O res hres
  rw [run_evm1 O cM envM .create (.cons hmv (.cons hmp (.cons hml .nil))) r
    (Fe.EVM.create (.ofNat mv) (.ofNat mp) (.ofNat ml)) rfl, Fe.EVM.create,
    exec_bind_congr (H.createWith_eq_core _ _ _ _ I w), toNat_ofNat_lt hlp,
    toNat_ofNat_lt hll] at hres
  by_cases hperm : I.perm = false
  · simp only [H.createCore, Fe.M.exec_bind, Fe.M.exec_read, hperm, if_true, Fe.M.exec_fail,
      Option.some.injEq] at hres
    subst hres
    exact stepOk_exit (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm])
  by_cases hbig : ml > 49152
  · simp [H.createCore, Fe.M.exec_bind, Fe.M.exec_read, hperm, H.readWithPadding_size, hbig,
      Fe.M.exec_diverge] at hres
  cases hr : hst.range vp ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm, hbig,
      hwl, hr])
  | some rg =>
    have hR := rangeAt_of hI hrp hgp hr
    rw [hR.bytes hI] at hres
    refine stepOk_lift1 hI hE hA hd hwx hvx (ignoresMemory_createCore _ _ _) ?_ hres
    rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm, hbig, hwl, hr, State.uword, hwv]

/-- `evm_create2 v p l salt`: as `evm_create`, with the salt's word. -/
theorem evm_create2 {v p l sa : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .create2 [v, p, l, sa]))
    (harg : ∀ b ∈ [v, p, l, sa], (c.tyOf b).any Ty.value = true)
    (hm : [v, p, l, sa].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .create2 args'⟩] := by
  obtain ⟨v', t1, hv', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨p', t2, hp', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨l', t3, hl', hm3, rfl⟩ := mapM_cons' hm2
  obtain ⟨sa', t4, hs', hm4, rfl⟩ := mapM_cons' hm3
  cases mapM_nil' hm4
  have hargs : s.inst.args = [v, p, l, sa] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨vv, mv, hvv, hmv, hlv, -, -, -, hwv⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg v (by simp)) hv'
  obtain ⟨vp, mp, hvp, hmp, hlp, hrp, -, hgp, -⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg p (by simp)) hp'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg l (by simp)) hl'
  obtain ⟨vs, ms, hvs, hms, hls, -, -, -, hws⟩ := evm_arg hI hE hA (i := 3) (by rw [hargs]; rfl)
    (harg sa (by simp)) hs'
  have hwv := hwv (by simp [nonObserving, hi, EvmOp.addrPos])
  have hwl := hwl (by simp [nonObserving, hi, EvmOp.addrPos])
  have hws := hws (by simp [nonObserving, hi, EvmOp.addrPos])
  have hstep : stepInst P.ctx I envH hst s.inst = evmH I hst .create2 [vv, vp, vl, vs] :=
    step_evm hi (by simp [hvv, hvp, hvl, hvs])
  intro O res hres
  rw [run_evm1 O cM envM .create2 (.cons hmv (.cons hmp (.cons hml (.cons hms .nil)))) r
    (Fe.EVM.create2 (.ofNat mv) (.ofNat mp) (.ofNat ml) (.ofNat ms)) rfl, Fe.EVM.create2,
    exec_bind_congr (H.createWith_eq_core _ _ _ _ I w), toNat_ofNat_lt hlp,
    toNat_ofNat_lt hll] at hres
  by_cases hperm : I.perm = false
  · simp only [H.createCore, Fe.M.exec_bind, Fe.M.exec_read, hperm, if_true, Fe.M.exec_fail,
      Option.some.injEq] at hres
    subst hres
    exact stepOk_exit (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm])
  by_cases hbig : ml > 49152
  · simp [H.createCore, Fe.M.exec_bind, Fe.M.exec_read, hperm, H.readWithPadding_size, hbig,
      Fe.M.exec_diverge] at hres
  cases hr : hst.range vp ml with
  | none => exact stepOk_ub (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm, hbig,
      hwl, hr])
  | some rg =>
    have hR := rangeAt_of hI hrp hgp hr
    rw [hR.bytes hI] at hres
    refine stepOk_lift1 hI hE hA hd hwx hvx (ignoresMemory_createCore _ _ _) ?_ hres
    rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, hperm, hbig, hwl, hr, State.uword, hwv, hws]

/-- `evm_call g a v ap al rp rl`: under a static call moving value both exit `static`; else H
    calls with its bytes at the input range, the machine's there, by the memory-free core of the
    message call, and writes the output where the machine does. -/
theorem evm_call {ag aa av aap aal arp arl : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .call [ag, aa, av, aap, aal, arp, arl]))
    (harg : ∀ b ∈ [ag, aa, av, aap, aal, arp, arl], (c.tyOf b).any Ty.value = true)
    (hm : [ag, aa, av, aap, aal, arp, arl].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .call args'⟩] := by
  obtain ⟨g', t1, hg', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨a', t2, ha', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨v', t3, hv', hm3, rfl⟩ := mapM_cons' hm2
  obtain ⟨ap', t4, hap', hm4, rfl⟩ := mapM_cons' hm3
  obtain ⟨al', t5, hal', hm5, rfl⟩ := mapM_cons' hm4
  obtain ⟨rp', t6, hrp', hm6, rfl⟩ := mapM_cons' hm5
  obtain ⟨rl', t7, hrl', hm7, rfl⟩ := mapM_cons' hm6
  cases mapM_nil' hm7
  have hargs : s.inst.args = [ag, aa, av, aap, aal, arp, arl] := by
    simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : nonObserving Dr k s ⊆ [3, 5] := by
    intro i hi'; simp only [nonObserving, hi, EvmOp.addrPos] at hi'
    simp only [List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hi'
    obtain ⟨⟨a, b⟩, ⟨h1, -⟩, rfl⟩ := hi'
    rcases h1 with h1 | h1 <;> simp [Prod.ext_iff] at h1 <;> simp [h1]
  obtain ⟨vg, mg, hvg, hmg, hlg, -, -, -, hwg⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg ag (by simp)) hg'
  obtain ⟨va, ma, hva, hma, hla, -, -, -, hwa⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg aa (by simp)) ha'
  obtain ⟨vv, mv, hvv, hmv, hlv, -, -, -, hwv⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg av (by simp)) hv'
  obtain ⟨vap, map, hvap, hmap, hlap, hrap, -, hgap, -⟩ := evm_arg hI hE hA (i := 3)
    (by rw [hargs]; rfl) (harg aap (by simp)) hap'
  obtain ⟨val, mal, hval, hmal, hlal, -, -, -, hwal⟩ := evm_arg hI hE hA (i := 4)
    (by rw [hargs]; rfl) (harg aal (by simp)) hal'
  obtain ⟨vrp, mrp, hvrp, hmrp, hlrp, hrrp, -, hgrp, -⟩ := evm_arg hI hE hA (i := 5)
    (by rw [hargs]; rfl) (harg arp (by simp)) hrp'
  obtain ⟨vrl, mrl, hvrl, hmrl, hlrl, -, -, -, hwrl⟩ := evm_arg hI hE hA (i := 6)
    (by rw [hargs]; rfl) (harg arl (by simp)) hrl'
  have hwg := hwg fun h => by simpa using hno h
  have hwa := hwa fun h => by simpa using hno h
  have hwv := hwv fun h => by simpa using hno h
  have hwal := hwal fun h => by simpa using hno h
  have hwrl := hwrl fun h => by simpa using hno h
  have hstep : stepInst P.ctx I envH hst s.inst =
      evmH I hst .call [vg, va, vv, vap, val, vrp, vrl] :=
    step_evm hi (by simp [hvg, hva, hvv, hvap, hval, hvrp, hvrl])
  intro O res hres
  rw [run_evm1 O cM envM .call (.cons hmg (.cons hma (.cons hmv (.cons hmap (.cons hmal
    (.cons hmrp (.cons hmrl .nil))))))) r
    (Fe.EVM.call (.ofNat mg) (.ofNat ma) (.ofNat mv) (.ofNat map) (.ofNat mal) (.ofNat mrp)
      (.ofNat mrl)) rfl] at hres
  by_cases hst' : I.perm = false ∧ Ethereum.UInt256.ofNat mv ≠ ⟨0⟩
  · simp only [Fe.EVM.call, Fe.M.exec_bind, Fe.M.exec_read, hst', if_true, Fe.M.exec_fail,
      Option.some.injEq, ne_eq, not_false_eq_true, and_self] at hres
    subst hres
    exact stepOk_exit (by rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwv, hst'])
  cases hr1 : hst.range vap mal with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwv, hst', hwal, hr1])
  | some ar =>
  cases hr2 : hst.range vrp mrl with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwv, hst', hwal, hr1, hwrl, hr2])
  | some rr =>
    have hR1 := rangeAt_of hI hrap hgap hr1
    have hR2 := rangeAt_of hI hrrp hgrp hr2
    refine stepOk_call hI hE hA hd hwx hvx (rl := .ofNat mrl)
      (fe := fun input => read >>= fun I' => H.messageCore (.ofNat mg) I'.codeOwner
        (Ethereum.AccountAddress.ofUInt256 (.ofNat ma)) (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))
        (.ofNat mv) (.ofNat mv) input I'.perm)
      (fun _ => ignoresMemory_readCore _ fun _ => ignoresMemory_messageCore _ _ _ _ _ _ _ _) hR1
      (by rw [toNat_ofNat_lt hlrl]; exact hR2) ?_ ?_
    · rw [hstep]
      simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwv, hst', hwal, hr1, hwrl, hr2, hwg, hwa]
    · rw [← hres]
      simp only [Fe.EVM.call, bind_assoc, Fe.M.exec_bind, Fe.M.exec_read, hst', if_false,
        H.message_eq_core, Fe.M.exec_get, Fe.M.exec_modify, Fe.M.exec_pure, toNat_ofNat_lt hlap,
        toNat_ofNat_lt hlal, toNat_ofNat_lt hlrp]
      split <;> rfl

/-- `evm_call_code g a v ap al rp rl`: as `evm_call`, the code at `a` run as this contract, with
    no failure under a static call. -/
theorem evm_callCode {ag aa av aap aal arp arl : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .callCode [ag, aa, av, aap, aal, arp, arl]))
    (harg : ∀ b ∈ [ag, aa, av, aap, aal, arp, arl], (c.tyOf b).any Ty.value = true)
    (hm : [ag, aa, av, aap, aal, arp, arl].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .callCode args'⟩] := by
  obtain ⟨g', t1, hg', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨a', t2, ha', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨v', t3, hv', hm3, rfl⟩ := mapM_cons' hm2
  obtain ⟨ap', t4, hap', hm4, rfl⟩ := mapM_cons' hm3
  obtain ⟨al', t5, hal', hm5, rfl⟩ := mapM_cons' hm4
  obtain ⟨rp', t6, hrp', hm6, rfl⟩ := mapM_cons' hm5
  obtain ⟨rl', t7, hrl', hm7, rfl⟩ := mapM_cons' hm6
  cases mapM_nil' hm7
  have hargs : s.inst.args = [ag, aa, av, aap, aal, arp, arl] := by
    simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : nonObserving Dr k s ⊆ [3, 5] := by
    intro i hi'; simp only [nonObserving, hi, EvmOp.addrPos] at hi'
    simp only [List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hi'
    obtain ⟨⟨a, b⟩, ⟨h1, -⟩, rfl⟩ := hi'
    rcases h1 with h1 | h1 <;> simp [Prod.ext_iff] at h1 <;> simp [h1]
  obtain ⟨vg, mg, hvg, hmg, hlg, -, -, -, hwg⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg ag (by simp)) hg'
  obtain ⟨va, ma, hva, hma, hla, -, -, -, hwa⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg aa (by simp)) ha'
  obtain ⟨vv, mv, hvv, hmv, hlv, -, -, -, hwv⟩ := evm_arg hI hE hA (i := 2) (by rw [hargs]; rfl)
    (harg av (by simp)) hv'
  obtain ⟨vap, map, hvap, hmap, hlap, hrap, -, hgap, -⟩ := evm_arg hI hE hA (i := 3)
    (by rw [hargs]; rfl) (harg aap (by simp)) hap'
  obtain ⟨val, mal, hval, hmal, hlal, -, -, -, hwal⟩ := evm_arg hI hE hA (i := 4)
    (by rw [hargs]; rfl) (harg aal (by simp)) hal'
  obtain ⟨vrp, mrp, hvrp, hmrp, hlrp, hrrp, -, hgrp, -⟩ := evm_arg hI hE hA (i := 5)
    (by rw [hargs]; rfl) (harg arp (by simp)) hrp'
  obtain ⟨vrl, mrl, hvrl, hmrl, hlrl, -, -, -, hwrl⟩ := evm_arg hI hE hA (i := 6)
    (by rw [hargs]; rfl) (harg arl (by simp)) hrl'
  have hwg := hwg fun h => by simpa using hno h
  have hwa := hwa fun h => by simpa using hno h
  have hwv := hwv fun h => by simpa using hno h
  have hwal := hwal fun h => by simpa using hno h
  have hwrl := hwrl fun h => by simpa using hno h
  have hstep : stepInst P.ctx I envH hst s.inst =
      evmH I hst .callCode [vg, va, vv, vap, val, vrp, vrl] :=
    step_evm hi (by simp [hvg, hva, hvv, hvap, hval, hvrp, hvrl])
  intro O res hres
  rw [run_evm1 O cM envM .callCode (.cons hmg (.cons hma (.cons hmv (.cons hmap (.cons hmal
    (.cons hmrp (.cons hmrl .nil))))))) r
    (callcode (.ofNat mg) (.ofNat ma) (.ofNat mv) (.ofNat map) (.ofNat mal) (.ofNat mrp)
      (.ofNat mrl)) rfl] at hres
  cases hr1 : hst.range vap mal with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1])
  | some ar =>
  cases hr2 : hst.range vrp mrl with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2])
  | some rr =>
    have hR1 := rangeAt_of hI hrap hgap hr1
    have hR2 := rangeAt_of hI hrrp hgrp hr2
    refine stepOk_call hI hE hA hd hwx hvx (rl := .ofNat mrl)
      (fe := fun input => read >>= fun I' => H.messageCore (.ofNat mg) I'.codeOwner
        I'.codeOwner (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))
        (.ofNat mv) (.ofNat mv) input I'.perm)
      (fun _ => ignoresMemory_readCore _ fun _ => ignoresMemory_messageCore _ _ _ _ _ _ _ _) hR1
      (by rw [toNat_ofNat_lt hlrl]; exact hR2) ?_ ?_
    · rw [hstep]
      simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2, hwg, hwa, hwv]
    · rw [← hres]
      simp only [callcode, bind_assoc, Fe.M.exec_bind, Fe.M.exec_read, 
        H.message_eq_core, Fe.M.exec_get, Fe.M.exec_modify, Fe.M.exec_pure, toNat_ofNat_lt hlap,
        toNat_ofNat_lt hlal, toNat_ofNat_lt hlrp]
      split <;> rfl

/-- `evm_static_call g a ap al rp rl`: as `evm_call`, with no value, the callee changing
    nothing. -/
theorem evm_staticCall {ag aa aap aal arp arl : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .staticCall [ag, aa, aap, aal, arp, arl]))
    (harg : ∀ b ∈ [ag, aa, aap, aal, arp, arl], (c.tyOf b).any Ty.value = true)
    (hm : [ag, aa, aap, aal, arp, arl].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .staticCall args'⟩] := by
  obtain ⟨g', t1, hg', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨a', t2, ha', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨ap', t4, hap', hm4, rfl⟩ := mapM_cons' hm2
  obtain ⟨al', t5, hal', hm5, rfl⟩ := mapM_cons' hm4
  obtain ⟨rp', t6, hrp', hm6, rfl⟩ := mapM_cons' hm5
  obtain ⟨rl', t7, hrl', hm7, rfl⟩ := mapM_cons' hm6
  cases mapM_nil' hm7
  have hargs : s.inst.args = [ag, aa, aap, aal, arp, arl] := by
    simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : nonObserving Dr k s ⊆ [2, 4] := by
    intro i hi'; simp only [nonObserving, hi, EvmOp.addrPos] at hi'
    simp only [List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hi'
    obtain ⟨⟨a, b⟩, ⟨h1, -⟩, rfl⟩ := hi'
    rcases h1 with h1 | h1 <;> simp [Prod.ext_iff] at h1 <;> simp [h1]
  obtain ⟨vg, mg, hvg, hmg, hlg, -, -, -, hwg⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg ag (by simp)) hg'
  obtain ⟨va, ma, hva, hma, hla, -, -, -, hwa⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg aa (by simp)) ha'
  obtain ⟨vap, map, hvap, hmap, hlap, hrap, -, hgap, -⟩ := evm_arg hI hE hA (i := 2)
    (by rw [hargs]; rfl) (harg aap (by simp)) hap'
  obtain ⟨val, mal, hval, hmal, hlal, -, -, -, hwal⟩ := evm_arg hI hE hA (i := 3)
    (by rw [hargs]; rfl) (harg aal (by simp)) hal'
  obtain ⟨vrp, mrp, hvrp, hmrp, hlrp, hrrp, -, hgrp, -⟩ := evm_arg hI hE hA (i := 4)
    (by rw [hargs]; rfl) (harg arp (by simp)) hrp'
  obtain ⟨vrl, mrl, hvrl, hmrl, hlrl, -, -, -, hwrl⟩ := evm_arg hI hE hA (i := 5)
    (by rw [hargs]; rfl) (harg arl (by simp)) hrl'
  have hwg := hwg fun h => by simpa using hno h
  have hwa := hwa fun h => by simpa using hno h
  have hwal := hwal fun h => by simpa using hno h
  have hwrl := hwrl fun h => by simpa using hno h
  have hstep : stepInst P.ctx I envH hst s.inst =
      evmH I hst .staticCall [vg, va, vap, val, vrp, vrl] :=
    step_evm hi (by simp [hvg, hva, hvap, hval, hvrp, hvrl])
  intro O res hres
  rw [run_evm1 O cM envM .staticCall (.cons hmg (.cons hma (.cons hmap (.cons hmal
    (.cons hmrp (.cons hmrl .nil)))))) r
    (Fe.EVM.staticcall (.ofNat mg) (.ofNat ma) (.ofNat map) (.ofNat mal) (.ofNat mrp)
      (.ofNat mrl)) rfl] at hres
  cases hr1 : hst.range vap mal with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1])
  | some ar =>
  cases hr2 : hst.range vrp mrl with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2])
  | some rr =>
    have hR1 := rangeAt_of hI hrap hgap hr1
    have hR2 := rangeAt_of hI hrrp hgrp hr2
    refine stepOk_call hI hE hA hd hwx hvx (rl := .ofNat mrl)
      (fe := fun input => read >>= fun I' => H.messageCore (.ofNat mg) I'.codeOwner
        (Ethereum.AccountAddress.ofUInt256 (.ofNat ma)) (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))
        ⟨0⟩ ⟨0⟩ input false)
      (fun _ => ignoresMemory_readCore _ fun _ => ignoresMemory_messageCore _ _ _ _ _ _ _ _) hR1
      (by rw [toNat_ofNat_lt hlrl]; exact hR2) ?_ ?_
    · rw [hstep]
      simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2, hwg, hwa]
    · rw [← hres]
      simp only [Fe.EVM.staticcall, bind_assoc, Fe.M.exec_bind, Fe.M.exec_read, 
        H.message_eq_core, Fe.M.exec_get, Fe.M.exec_modify, Fe.M.exec_pure, toNat_ofNat_lt hlap,
        toNat_ofNat_lt hlal, toNat_ofNat_lt hlrp]
      split <;> rfl

/-- `evm_delegate_call g a ap al rp rl`: as `evm_call`, the code at `a` run as this contract
    for this call's caller and value. -/
theorem evm_delegateCall {ag aa aap aal arp arl : Operand} {args' : List Operand} {r x : Nat} {tx : Ty}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) (hd : s.dsts = [(x, tx)]) (hwx : isWord tx = true)
    (hvx : F.vm.find? x = some (.var r))
    (hi : s.inst = .base (.evm .delegateCall [ag, aa, aap, aal, arp, arl]))
    (harg : ∀ b ∈ [ag, aa, aap, aal, arp, arl], (c.tyOf b).any Ty.value = true)
    (hm : [ag, aa, aap, aal, arp, arl].mapM (mop F.vm) = some args') :
    TemplOk P I cM S F g hst w envH envM s L' [⟨[(r, .int 256)], .evm .delegateCall args'⟩] := by
  obtain ⟨g', t1, hg', hm1, rfl⟩ := mapM_cons' hm
  obtain ⟨a', t2, ha', hm2, rfl⟩ := mapM_cons' hm1
  obtain ⟨ap', t4, hap', hm4, rfl⟩ := mapM_cons' hm2
  obtain ⟨al', t5, hal', hm5, rfl⟩ := mapM_cons' hm4
  obtain ⟨rp', t6, hrp', hm6, rfl⟩ := mapM_cons' hm5
  obtain ⟨rl', t7, hrl', hm7, rfl⟩ := mapM_cons' hm6
  cases mapM_nil' hm7
  have hargs : s.inst.args = [ag, aa, aap, aal, arp, arl] := by
    simp [hi, HInst.args, HInst.skel, Inst.args]
  have hno : nonObserving Dr k s ⊆ [2, 4] := by
    intro i hi'; simp only [nonObserving, hi, EvmOp.addrPos] at hi'
    simp only [List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hi'
    obtain ⟨⟨a, b⟩, ⟨h1, -⟩, rfl⟩ := hi'
    rcases h1 with h1 | h1 <;> simp [Prod.ext_iff] at h1 <;> simp [h1]
  obtain ⟨vg, mg, hvg, hmg, hlg, -, -, -, hwg⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl)
    (harg ag (by simp)) hg'
  obtain ⟨va, ma, hva, hma, hla, -, -, -, hwa⟩ := evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl)
    (harg aa (by simp)) ha'
  obtain ⟨vap, map, hvap, hmap, hlap, hrap, -, hgap, -⟩ := evm_arg hI hE hA (i := 2)
    (by rw [hargs]; rfl) (harg aap (by simp)) hap'
  obtain ⟨val, mal, hval, hmal, hlal, -, -, -, hwal⟩ := evm_arg hI hE hA (i := 3)
    (by rw [hargs]; rfl) (harg aal (by simp)) hal'
  obtain ⟨vrp, mrp, hvrp, hmrp, hlrp, hrrp, -, hgrp, -⟩ := evm_arg hI hE hA (i := 4)
    (by rw [hargs]; rfl) (harg arp (by simp)) hrp'
  obtain ⟨vrl, mrl, hvrl, hmrl, hlrl, -, -, -, hwrl⟩ := evm_arg hI hE hA (i := 5)
    (by rw [hargs]; rfl) (harg arl (by simp)) hrl'
  have hwg := hwg fun h => by simpa using hno h
  have hwa := hwa fun h => by simpa using hno h
  have hwal := hwal fun h => by simpa using hno h
  have hwrl := hwrl fun h => by simpa using hno h
  have hstep : stepInst P.ctx I envH hst s.inst =
      evmH I hst .delegateCall [vg, va, vap, val, vrp, vrl] :=
    step_evm hi (by simp [hvg, hva, hvap, hval, hvrp, hvrl])
  intro O res hres
  rw [run_evm1 O cM envM .delegateCall (.cons hmg (.cons hma (.cons hmap (.cons hmal
    (.cons hmrp (.cons hmrl .nil)))))) r
    (Fe.EVM.delegatecall (.ofNat mg) (.ofNat ma) (.ofNat map) (.ofNat mal) (.ofNat mrp)
      (.ofNat mrl)) rfl] at hres
  cases hr1 : hst.range vap mal with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1])
  | some ar =>
  cases hr2 : hst.range vrp mrl with
  | none => exact stepOk_ub (by
      rw [hstep]; simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2])
  | some rr =>
    have hR1 := rangeAt_of hI hrap hgap hr1
    have hR2 := rangeAt_of hI hrrp hgrp hr2
    refine stepOk_call hI hE hA hd hwx hvx (rl := .ofNat mrl)
      (fe := fun input => read >>= fun I' => H.messageCore (.ofNat mg) I'.source
        I'.codeOwner (Ethereum.AccountAddress.ofUInt256 (.ofNat ma))
        ⟨0⟩ I'.weiValue input I'.perm)
      (fun _ => ignoresMemory_readCore _ fun _ => ignoresMemory_messageCore _ _ _ _ _ _ _ _) hR1
      (by rw [toNat_ofNat_lt hlrl]; exact hR2) ?_ ?_
    · rw [hstep]
      simp [evmH, EvmOp.arity, EvmOp.memFree, State.uword, hwal, hr1, hwrl, hr2, hwg, hwa]
    · rw [← hres]
      simp only [Fe.EVM.delegatecall, bind_assoc, Fe.M.exec_bind, Fe.M.exec_read, 
        H.message_eq_core, Fe.M.exec_get, Fe.M.exec_modify, Fe.M.exec_pure, toNat_ofNat_lt hlap,
        toNat_ofNat_lt hlal, toNat_ofNat_lt hlrp]
      split <;> rfl

end ops

end Fe.Sonatina.Stage3.Place
