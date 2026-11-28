import Fe.Sonatina.Stage3.Place.InstEvmOps

/-!
# EVM message calls, and the pattern of the EVM operations that touch memory

The message calls (`evm_call`, `evm_call_code`, `evm_static_call`, `evm_delegate_call`) run their
memory-free core (`H.messageCore`) on the input range's bytes and write the output where the
machine does (`stepOk_call`).  `inst_evmMem` is the pattern lemma of every EVM operation that
touches memory: `stmt`'s `evm` arm, by cases on the operation.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

section ops

variable {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
  {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
  {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat}

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

/-- An EVM operation that touches memory (`lower_structural`): the same operation on the
    operands' machine values ends as H's step does. -/
theorem inst_evmMem {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : EvmOp} {args : List Operand}
    (hmem : op.memFree = false)
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.evm op args))
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  simp only [stmt, hi, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_none,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq, reduceCtorEq,
    false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨⟨nA, nR⟩, har, hc, args', hargs', ⟨rs, rest⟩, htk, vm2, hfold, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨ds', hms, hlen, hty, rfl⟩ := takeN_some htk
  obtain ⟨-, hvmx⟩ := foldlM_bindV hfold
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨-, hnA⟩, hnR⟩, hdw⟩, harg⟩ := hc
  refine ⟨[_], hms, rfl, ?_⟩
  have hR0 : nR = 0 → s.dsts = [] ∧ ds' = [] := fun h0 =>
    ⟨List.eq_nil_of_length_eq_zero (hnR.trans h0), List.eq_nil_of_length_eq_zero (hlen.trans h0)⟩
  have hR1 : nR = 1 → ∃ x tx r, s.dsts = [(x, tx)] ∧ ds' = [(r, .int 256)] ∧ isWord tx = true ∧
      F.vm.find? x = some (.var r) := by
    intro h1
    obtain ⟨⟨x, tx⟩, hd⟩ := len1 (hnR.trans h1)
    obtain ⟨⟨r, tr⟩, hd'⟩ := len1 (hlen.trans h1)
    subst hd'
    have htr : tr = .int 256 := hty (r, tr) (by simp)
    subst htr
    exact ⟨x, tx, r, hd, rfl, hdw (x, tx) (by simp [hd]), hvmx ((x, tx), r) (by simp [hd])⟩
  cases op <;> simp only [EvmOp.memFree, reduceCtorEq] at hmem <;>
    simp only [EvmOp.arity, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at har
  case log kk =>
    split at har
    · next hk =>
      obtain ⟨rfl, rfl⟩ := har
      obtain ⟨hd, rfl⟩ := hR0 rfl
      rcases args with _ | ⟨p, _ | ⟨l, ts⟩⟩
      · simp at hnA
      · simp at hnA
      · exact evm_log hI hE hA hd hi hk (by simpa using hnA) harg hargs'
    · cases har
  all_goals obtain ⟨rfl, rfl⟩ := har
  case mload =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hnA
    exact evm_mload hI hE hA hd hwx hvx hi harg hargs'
  case mstore =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨v, _ | ⟨_, _⟩⟩⟩ <;> simp at hnA
    exact evm_mstore hI hE hA hd hi harg hargs'
  case mstore8 =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨v, _ | ⟨_, _⟩⟩⟩ <;> simp at hnA
    exact evm_mstore8 hI hE hA hd hi harg hargs'
  case keccak256 =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a, _ | ⟨l, _ | ⟨_, _⟩⟩⟩ <;> simp at hnA
    exact evm_keccak hI hE hA hd hwx hvx hi harg hargs'
  case mcopy =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hnA
    exact evm_mcopy hI hE hA hd hi harg hargs'
  case calldataCopy =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hnA
    exact evm_calldataCopy hI hE hA hd hi harg hargs'
  case codeCopy =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hnA
    exact evm_codeCopy hI hE hA hd hi harg hargs'
  case extCodeCopy =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨o, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hnA
    exact evm_extCodeCopy hI hE hA hd hi harg hargs'
  case returnDataCopy =>
    obtain ⟨hd, rfl⟩ := hR0 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hnA
    exact evm_returnDataCopy hI hE hA hd hi harg hargs'
  case create =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hnA
    exact evm_create hI hE hA hd hwx hvx hi harg hargs'
  case create2 =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨l, _ | ⟨t, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hnA
    exact evm_create2 hI hE hA hd hwx hvx hi harg hargs'
  case call =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hnA
    exact evm_call hI hE hA hd hwx hvx hi harg hargs'
  case callCode =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hnA
    exact evm_callCode hI hE hA hd hwx hvx hi harg hargs'
  case staticCall =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hnA
    exact evm_staticCall hI hE hA hd hwx hvx hi harg hargs'
  case delegateCall =>
    obtain ⟨x, tx, r, hd, rfl, hwx, hvx⟩ := hR1 rfl
    rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hnA
    exact evm_delegateCall hI hE hA hd hwx hvx hi harg hargs'

end Fe.Sonatina.Stage3.Place
