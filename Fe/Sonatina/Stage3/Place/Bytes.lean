import Fe.Sonatina.Stage3.Place.Dia
import Fe.Sonatina.Stage3.Place.InstEvmCalls

/-!
# `evm_mload_bytes`
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Words read from bytes -/

theorem rwp_toList (m : ByteArray) (a n : Nat) :
    (m.readWithPadding a n).toList = (List.range n).map fun i => mem m (a + i) := by
  rw [readWithPadding_of_mem (l := (List.range n).map fun i => mem m (a + i)) (by simp)
    (fun i hi => by simp), Reasoning.Theory.byteArray_toList_eq]

theorem fromBE_lt (l : List UInt8) (hl : l.length = 32) : Ethereum.fromBytesBigEndian l < W := by
  unfold Ethereum.fromBytesBigEndian Function.comp
  have h := Ethereum.fromBytes'_le (bs := l.reverse)
  rw [List.length_reverse, hl] at h
  simpa [W] using h

/-- The machine's word at `a`, the 32 bytes there big-endian. -/
theorem mload_word (m : ByteArray) (a : Nat) :
    (Ethereum.uInt256OfByteArray (m.readWithPadding a 32)).toNat =
      Ethereum.fromByteArrayBigEndian (m.readWithPadding a 32) := by
  rw [Reasoning.Theory.uInt256OfByteArray_eq, toNat_ofNat, Nat.mod_eq_of_lt]
  exact fromBE_lt _ (by rw [rwp_toList]; simp)

/-- The first `n` bytes of the word at `a`: the word shifted right by the other bytes. -/
theorem mload_shift (m : ByteArray) (a : Nat) {n : Nat} (hn : n ≤ 32) :
    Ethereum.fromByteArrayBigEndian (m.readWithPadding a 32) >>> (8 * (32 - n)) =
      Ethereum.fromByteArrayBigEndian (m.readWithPadding a n) := by
  unfold Ethereum.fromByteArrayBigEndian
  rw [shift_bytes _ (by rw [rwp_toList]; simp), rwp_toList, rwp_toList, ← List.map_take,
    List.take_range, min_eq_left hn]

/-- `evm_mload_bytes a n` at a constant `n` (`lower_mload_bytes`): `0` for no byte; past 32
    bytes H is undefined; the word at `a` for 32; the word shifted right for fewer. -/
theorem inst_bytesImm {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {bits n : Nat} {x : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .mloadBytes a (.imm bits n)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  have hargs : s.inst.args = [a, .imm bits n] := by rw [hi]; rfl
  cases n with
  | zero =>
    simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.bind_none, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq,
      reduceCtorEq, false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
    obtain ⟨hc, a', ha', h⟩ := h
    obtain ⟨vm1, ⟨hx, -⟩, rfl, rfl, rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hwx, hta⟩, -⟩ := hc
    obtain ⟨va, ma, hva, -, -, -, -, -, -⟩ := evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl) hta ha'
    have hA' : At S F c Dr k s callee? L L' [] := hA
    refine ⟨[], rfl, rfl, templ_alias hI hE hA' hd hx (by simp [mval, imm]) (v := .int 256 0)
      (by simp only [stepInst, hi, hva]; simp [evalOp, H.State.word, H.Val.word]) (fits_word hwx (by unfold W; norm_num))
      rfl trivial trivial⟩
  | succ n =>
    simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.bind_none, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq,
      reduceCtorEq, false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
    obtain ⟨hc, a', ha', h⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hwx, hta⟩, -⟩ := hc
    obtain ⟨va, ma, hva, hma, hla, hra, -, hga, -⟩ :=
      evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl) hta ha'
    have hwn : ∀ st : H.State, st.word (.int bits (n + 1)) = n + 1 := fun _ => rfl
    by_cases h32 : 32 < n + 1
    · -- H is undefined; the machine's statement is the word load.
      rw [if_pos (by omega)] at h
      obtain ⟨⟨r, ms1⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vm1, hvm1, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hx : F.vm.find? x = some (.var r) := by
        split at hvm1
        · assumption
        · cases hvm1
      exact ⟨[_], take1_some hr, rfl, templ_ub _ (by
        simp only [stepInst, hi, hva]; simp [evalOp, hwn, h32])⟩
    have hstep : ∀ rg, hst.range va (n + 1) = some rg → stepInst P.ctx I envH hst s.inst =
        .ok [.int 256 (Ethereum.fromByteArrayBigEndian (hst.bytes rg (n + 1)))] hst := by
      intro rg hrg
      simp only [stepInst, hi, hva]; simp [evalOp, hwn, h32, hrg]
    have hstepN : hst.range va (n + 1) = none → stepInst P.ctx I envH hst s.inst = .ub := by
      intro hrg
      simp only [stepInst, hi, hva]; simp [evalOp, hwn, h32, hrg]
    by_cases h32' : 32 ≤ n + 1
    · have hn32 : n + 1 = 32 := by omega
      rw [if_pos h32'] at h
      obtain ⟨⟨r, ms1⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vm1, hvm1, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hx : F.vm.find? x = some (.var r) := by
        split at hvm1
        · assumption
        · cases hvm1
      refine ⟨[_], take1_some hr, rfl, fun O res hres => ?_⟩
      rw [run_evm1 O cM envM .mload (.cons hma .nil) r (Fe.EVM.mload (.ofNat ma)) rfl] at hres
      cases hrg : hst.range va (n + 1) with
      | none => exact stepOk_ub (hstepN hrg)
      | some rg =>
        have hR := rangeAt_of hI hra hga hrg
        simp only [Fe.EVM.mload, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_pure, Option.some.injEq,
          toNat_ofNat_lt hla] at hres
        subst hres
        have hvalM : (Ethereum.uInt256OfByteArray (w.memory.readWithPadding ma 32)).toNat =
            Ethereum.fromByteArrayBigEndian (hst.bytes rg (n + 1)) := by
          rw [mload_word, ← hR.bytes hI, hn32]
        have hlt : Ethereum.fromByteArrayBigEndian (hst.bytes rg (n + 1)) < W := by
          rw [← hvalM]; exact toNat_lt' _
        refine stepOk_pure1 hI hE hA hd (hstep rg hrg) (fits_word hwx hlt) insert_keep ?_ rfl
          trivial trivial
        rw [hx]; simp [mval, hvalM]
    · rw [if_neg h32'] at h
      obtain ⟨⟨w0, ms1⟩, hw0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨r, ms2⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vm1, hvm1, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hx : F.vm.find? x = some (.var r) := by
        split at hvm1
        · assumption
        · cases hvm1
      have hm1 := take1_some hw0
      have hm2 := take1_some hr
      simp only at hm1 hm2
      refine ⟨[⟨[(w0, .int 256)], .evm .mload [a']⟩,
        ⟨[(r, .int 256)], .bin .shr (imm ((32 - (n + 1)) * 8)) (.var w0)⟩],
        by rw [hm1, hm2]; rfl, rfl, fun O res hres => ?_⟩
      rw [show [⟨[(w0, .int 256)], .evm .mload [a']⟩,
        ⟨[(r, .int 256)], .bin .shr (imm ((32 - (n + 1)) * 8)) (.var w0)⟩] =
        [⟨[(w0, .int 256)], .evm .mload [a']⟩] ++
        [(⟨[(r, .int 256)], .bin .shr (imm ((32 - (n + 1)) * 8)) (.var w0)⟩ : Stmt)] from rfl,
        runBodyO_append, run_evm1 O cM envM .mload (.cons hma .nil) w0 (Fe.EVM.mload (.ofNat ma)) rfl,
        bind_assoc] at hres
      simp only [Fe.EVM.mload, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_pure, toNat_ofNat_lt hla,
        pure_bind] at hres
      rw [runBodyO_plain O cM _ _ (by simp), runPlain_bin cM (x := (32 - (n + 1)) * 8) (by simp [mval, imm])
        (mval_insert_self _ _ _)] at hres
      simp only [runPlain, Fe.M.exec_pure, Option.some.injEq] at hres
      subst hres
      cases hrg : hst.range va (n + 1) with
      | none => exact stepOk_ub (hstepN hrg)
      | some rg =>
        have hR := rangeAt_of hI hra hga hrg
        have hsh : BinOp.eval .shr 256 ((32 - (n + 1)) * 8)
            ((Ethereum.uInt256OfByteArray (w.memory.readWithPadding ma 32)).toNat) % W =
            Ethereum.fromByteArrayBigEndian (hst.bytes rg (n + 1)) := by
          simp only [BinOp.eval]
          rw [if_neg (by omega), mload_word, Nat.mul_comm, mload_shift _ _ (by omega), hR.bytes hI,
            Nat.mod_eq_of_lt]
          rw [← hR.bytes hI, ← mload_shift _ _ (by omega : n + 1 ≤ 32), ← mload_word]
          exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (toNat_lt' _)
        have hlt : Ethereum.fromByteArrayBigEndian (hst.bytes rg (n + 1)) < W := by
          rw [← hsh]; exact Nat.mod_lt _ (by unfold W; positivity)
        refine stepOk_pure1 hI hE hA hd (hstep rg hrg) (fits_word hwx hlt) (fun r' hr' => ?_) ?_ rfl
          trivial trivial
        · have h1 : r' ≠ w0 := fun e => hr' (by simp [e])
          have h2 : r' ≠ r := fun e => hr' (by simp [e])
          rw [insert_other (Ne.symm h2), insert_other (Ne.symm h1)]
        · rw [hx, ← hsh]; simp [mval]

/-- The dynamic `evm_mload_bytes a l`'s template (`lower_mload_bytes`): block `mb` ends in
    `br l' ld jn`; `ld` loads the word and shifts it by `256 - 8 l` and jumps to `jn`, whose one
    phi takes 0 from `mb` and the shifted word from `ld`. -/
theorem stmt_bytesDyn {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {a : Operand} {y x : Nat} {tx : Ty}
    (hi : s.inst = .mloadBytes a (.var y)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    isWord tx = true ∧ (c.tyOf a).any Ty.value = true ∧ (c.tyOf (.var y)).any Ty.value = true ∧
    ∃ a' l' cur ld jn lb w t1 t2 sh jb φ, mop vm a = some a' ∧ mop vm (.var y) = some l' ∧
      ms = [] ∧ c.mf.block? mb = some cur ∧ cur.term = .br l' ld jn ∧ c.mf.block? ld = some lb ∧
      lb.body = [⟨[(w, .int 256)], .evm .mload [a']⟩, ⟨[(t1, .int 256)], .bin .shl (imm 3) l'⟩,
        ⟨[(t2, .int 256)], .bin .sub (imm 256) (.var t1)⟩,
        ⟨[(sh, .int 256)], .bin .shr (.var t2) (.var w)⟩] ∧
      lb.phis = [] ∧ lb.term = .jump jn ∧ c.mf.block? jn = some jb ∧ jb.phis = [φ] ∧
      φ.ty = w256 ∧ φ.incoming = [(imm 0, mb), (.var sh, ld)] ∧ vm.find? x = some (.var φ.dst) ∧
      vm' = vm ∧ mb' = jn ∧ ms' = jb.body ∧ ds = [w, t1, t2, sh, φ.dst] := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.bind_none, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, beq_iff_eq,
      reduceCtorEq, false_and, exists_false, and_false, ite_true, ite_false, ↓reduceIte] at h
  obtain ⟨hc, a', ha', hms, l', hl', cur, hcur, h⟩ := h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hwx, hta⟩, htl⟩ := hc
  split at h
  · next cnd ld jn hterm =>
    split at h
    · next hcnd =>
      rw [hcnd] at hterm
      obtain ⟨lb, hlb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨w, r1⟩, hw, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨t1, r2⟩, ht1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨t2, r3⟩, ht2, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨sh, r4⟩, hsh, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · next hok =>
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hok
        obtain ⟨⟨hr4, hph⟩, hlt⟩ := hok
        obtain ⟨jb, hjb, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · next φ hφ =>
          split at h
          · next hok2 =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hok2
            obtain ⟨vm1, hvm1, h⟩ := Option.bind_eq_some_iff.mp h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            split at hvm1
            · next hx =>
              simp only [Option.some.injEq] at hvm1
              subst hvm1
              have e1 := take1_some hw
              have e2 := take1_some ht1
              have e3 := take1_some ht2
              have e4 := take1_some hsh
              simp only at e1 e2 e3 e4
              subst hr4
              refine ⟨hwx, hta, htl, a', l', cur, ld, jn, lb, w, t1, t2, sh, jb, φ, ha', hl',
                List.isEmpty_iff.mp hms, hcur, hterm, hlb, ?_, hph, hlt, hjb, hφ,
                hok2.1, hok2.2, hx, rfl, rfl, rfl, rfl⟩
              rw [e1, e2, e3, e4]
            · cases hvm1
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem dyn_shift {ml : Nat} (h1 : 1 ≤ ml) (h32 : ml ≤ 32) (W1 : Nat) :
    BinOp.eval .shr 256 (BinOp.eval .sub 256 256 (BinOp.eval .shl 256 3 ml % W) % W) W1 % W =
      (W1 >>> (8 * (32 - ml))) % W := by
  have e1 : BinOp.eval .shl 256 3 ml % W = 8 * ml := by
    simp only [BinOp.eval, if_neg (by omega : ¬ (3 ≥ 256)), Nat.shiftLeft_eq]
    rw [show ((ml * 2 ^ 3 : Nat) : Int) = ((ml * 2 ^ 3 : Nat) : Int) from rfl]
    rw [wrap_nat, Nat.mod_mod, Nat.mod_eq_of_lt
      (lt_of_le_of_lt (by omega : ml * 2 ^ 3 ≤ 256) (by norm_num))]
    ring
  have e2 : BinOp.eval .sub 256 256 (8 * ml) % W = 256 - 8 * ml := by
    simp only [BinOp.eval]
    rw [show ((256 : Nat) : Int) - ((8 * ml : Nat) : Int) = ((256 - 8 * ml : Nat) : Int) by omega,
      wrap_nat, Nat.mod_mod, Nat.mod_eq_of_lt
        (lt_of_le_of_lt (by omega : 256 - 8 * ml ≤ 256) (by norm_num))]
  rw [e1, e2]
  simp only [BinOp.eval, if_neg (by omega : ¬ (256 - 8 * ml ≥ 256))]
  rw [show 256 - 8 * ml = 8 * (32 - ml) by omega]

/-- The dynamic `evm_mload_bytes a l`: when `l` is 0, H's value and the machine's join are 0;
    otherwise H is undefined past 32 bytes or outside a block, and the shifted word is the first
    `l` bytes at `a` big-endian. -/
theorem inst_bytesDyn {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {L L' : List Nat} {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat}
    {ms ms' : List Stmt} {callee? : Option Nat} {vm' : VM} {ds : List Nat} {a : Operand} {y : Nat}
    {x : Nat} {tx : Ty} (hA : At S F c Dr k s callee? L L' ds) (hmd : (mdefs c.mf).Nodup)
    (hi : s.inst = .mloadBytes a (.var y)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    DiaOk P I cM S F c s mb ms mb' ms' L L' := by
  obtain ⟨hwx, hta, htl, a', l', cur, ld, jn, lb, w0, t1, t2, sh, jb, φ, ha', hl', rfl, hcur, hterm,
    hlb, hbody, hph, hlt, hjb, hφ, hφt, hinc, hx, -, hmb, rfl, rfl⟩ := stmt_bytesDyn hi hd h
  subst mb'
  have hne : ld ≠ jn := fun e => by
    subst e; rw [hlb] at hjb; cases hjb; rw [hph] at hφ; cases hφ
  refine ⟨cur, l', ld, jn, jb, [], hcur, hterm, hjb, rfl, fun b hb hbj => ?_, ?_⟩
  · rcases hb with rfl | rfl
    · exact ⟨lb, hlb, hph, hlt⟩
    · exact absurd rfl hbj
  intro O g hst w envH envM hI hE res hres
  have hargs : s.inst.args = [a, .var y] := by rw [hi]; rfl
  obtain ⟨va, ma, hva, hma, hla, hra, -, hga, -⟩ :=
    evm_arg hI hE hA (i := 0) (by rw [hargs]; rfl) hta ha'
  obtain ⟨vl, ml, hvl, hml, hll, -, -, -, hwl⟩ :=
    evm_arg hI hE hA (i := 1) (by rw [hargs]; rfl) htl hl'
  have hwl := hwl (by simp [nonObserving, hi, isZeroImm])
  have hφd : jb.phis.map (fun p => (p.dst, p.ty)) = [(φ.dst, .int 256)] := by
    rw [hφ]; simp [hφt, w256]
  -- H's step, by the length's word.
  have hstepH : stepInst P.ctx I envH hst s.inst = (if ml > 32 then .ub else if ml = 0 then
      .ok [.int 256 0] hst else match hst.range va ml with
        | some r => .ok [.int 256 (Ethereum.fromByteArrayBigEndian (hst.bytes r ml))] hst
        | none => .ub) := by
    simp only [stepInst, hi, hva, hvl, hwl]; rfl
  unfold diaRun at hres
  simp only [runBodyO, pure_bind, mval_evalInt hml] at hres
  by_cases h0 : ml = 0
  · -- The machine takes the join from `mb`; its phi is 0.
    have hif : (if (ml != 0) = true then ld else jn) = jn := by simp [h0]
    rw [hif, if_pos rfl, pure_bind] at hres
    simp [Fe.Sonatina.enter, hφ, hinc, evalOperand, imm, Fe.Sonatina.bind, hφt, w256, Val.as,
      Ty.bits] at hres
    subst hres
    exact stepOk_pure1 hI hE hA hd (by rw [hstepH, if_neg (by omega), if_pos h0])
      (fits_word hwx (by unfold W; norm_num)) (fun r' hr' => insert_other fun e => hr' (by simp [e]))
      (by rw [hx]; simp [mval]) rfl trivial trivial
  · have hif : (if (ml != 0) = true then ld else jn) = ld := by simp [h0]
    rw [hif, if_neg hne, hlb] at hres
    simp only [bind_assoc] at hres
    by_cases h32 : 32 < ml
    · exact stepOk_ub (by rw [hstepH, if_pos h32])
    cases hrg : hst.range va ml with
    | none => exact stepOk_ub (by rw [hstepH, if_neg h32, if_neg h0, hrg])
    | some rg =>
      have hR := rangeAt_of hI hra hga hrg
      have hnd4 : [w0, t1, t2, sh].Nodup := by
        refine hmd.sublist ?_
        have hmem : lb ∈ c.mf.blocks := List.mem_of_find?_eq_some hlb
        unfold mdefs
        refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
        refine List.Sublist.trans ?_ (sublist_flatMap (f := fun b : Block =>
          b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) hmem)
        refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
        rw [hbody]; simp
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true] at hnd4
      have hml1 : 1 ≤ ml := by omega
      have hml32 : ml ≤ 32 := by omega
      have hcl : ∀ q ∈ ([w0, t1, t2, sh, φ.dst] : List Nat), l' ≠ .var q := by
        intro q hq e
        have hyL : y ∈ L := hA.uses y (by rw [hargs]; simp)
        have hyd : y ∉ s.defs := hA.self y (by rw [hargs]; simp)
        exact hA.clob y (Or.inl hyL) hyd q hq (by rw [← e]; exact hl')
      have hml' : ∀ (E : Env) (q : Nat) (v : Val), q ∈ ([w0, t1, t2, sh, φ.dst] : List Nat) →
          mval E l' = some ml → mval (E.insert q v) l' = some ml := by
        intro E q v hq hE
        rw [mval_insert_other fun q' e hq' => hcl q hq (by rw [e, hq'])]; exact hE
      rw [hbody, show [(⟨[(w0, .int 256)], .evm .mload [a']⟩ : Stmt),
        ⟨[(t1, .int 256)], .bin .shl (imm 3) l'⟩, ⟨[(t2, .int 256)], .bin .sub (imm 256) (.var t1)⟩,
        ⟨[(sh, .int 256)], .bin .shr (.var t2) (.var w0)⟩] =
        [(⟨[(w0, .int 256)], .evm .mload [a']⟩ : Stmt)] ++
        [⟨[(t1, .int 256)], .bin .shl (imm 3) l'⟩, ⟨[(t2, .int 256)], .bin .sub (imm 256) (.var t1)⟩,
        ⟨[(sh, .int 256)], .bin .shr (.var t2) (.var w0)⟩] from rfl, runBodyO_append,
        run_evm1 O cM envM .mload (.cons hma .nil) w0 (Fe.EVM.mload (.ofNat ma)) rfl] at hres
      simp only [bind_assoc, Fe.EVM.mload, Fe.M.exec_bind, Fe.M.exec_get, Fe.M.exec_pure,
        toNat_ofNat_lt hla, pure_bind] at hres
      set W1 := (Ethereum.uInt256OfByteArray (w.memory.readWithPadding ma 32)).toNat with hW1
      set E1 := envM.insert w0 (.int 256 W1) with hE1
      rw [runBodyO_plain O cM _ _ (by simp),
        runPlain_bin cM (x := 3) (by simp [mval, imm]) (hml' envM w0 _ (by simp) hml),
        runPlain_bin cM (x := 256) (by simp [mval, imm]) (mval_insert_self _ _ _),
        runPlain_bin cM (mval_insert_self _ _ _)
          (by rw [mval_insert_other (fun q e => ?_), mval_insert_other (fun q e => ?_)]
              · exact mval_insert_self _ _ _
              · cases e; first | exact hnd4.1.1 | exact hnd4.1.2.1
              · cases e; first | exact hnd4.1.1 | exact hnd4.1.2.1)] at hres
      have hmbld : mb ≠ ld := fun e => by
        subst e; rw [hcur] at hlb; cases hlb; rw [hterm] at hlt; cases hlt
      simp [runPlain, Fe.Sonatina.enter, hφ, hinc, evalOperand, imm, Fe.Sonatina.bind, hφt, w256,
        Val.as, Ty.bits, beq_eq_false_iff_ne.mpr hmbld, runBodyO] at hres
      subst hres
      have hval : BinOp.eval .shr 256 (BinOp.eval .sub 256 256 (BinOp.eval .shl 256 3 ml % W) % W)
          W1 % W = Ethereum.fromByteArrayBigEndian (hst.bytes rg ml) := by
        rw [dyn_shift hml1 hml32, hW1, mload_word, mload_shift _ _ hml32, hR.bytes hI,
          Nat.mod_eq_of_lt]
        rw [← hR.bytes hI, ← mload_shift _ _ hml32, ← mload_word]
        exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (toNat_lt' _)
      have hlt' : Ethereum.fromByteArrayBigEndian (hst.bytes rg ml) < W := by
        rw [← hval]; exact Nat.mod_lt _ (by unfold W; positivity)
      refine stepOk_pure1 hI hE hA hd (by rw [hstepH, if_neg h32, if_neg h0, hrg])
        (fits_word hwx hlt') (fun r' hr' => ?_) ?_ rfl trivial trivial
      · simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil] at hr'
        obtain ⟨h1, h2, h3, h4, h5, -⟩ := hr'
        rw [insert_other (Ne.symm h5), insert_other (Ne.symm h4), insert_other (Ne.symm h3),
          insert_other (Ne.symm h2), insert_other (Ne.symm h1)]
      · rw [hx]
        simp only [Option.bind_some, mval, Std.TreeMap.getElem?_insert_self]
        rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat)
          = W from rfl, Nat.mod_mod, hval]

end Fe.Sonatina.Stage3.Place
