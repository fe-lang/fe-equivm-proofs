import Fe.Sonatina.Stage3.Place.InstEvm
import Fe.Sonatina.Stage3.Place.Sim

/-!
# EVM operations that touch memory

`evm_*` of the operations that read or write memory (`EvmOp.memFree = false`), lowered as the
same operation on the operands' words (`lower_structural`).  H resolves each memory range in a
block (`State.range`, `ub` otherwise, §3.4); a range of `len > 0` bytes is into a block the
origins rule (S3) keeps live, so the machine's address is the block's machine base plus the
offset (`RangeAt`), where the machine's bytes are the cells' values (`RangeAt.bytes`), and a
write there keeps the invariant (`inv_write_at`, `inv_writeBytes_at`).  A range of no bytes
touches nothing on either side.  Address operands are the only ones S8 lets be derived in
address-0 mode (`EvmOp.addrPos`); every other operand's word in H is its machine word.

The world part of logs, creations and calls ignores memory (`emit`, `H.createCore`,
`H.messageCore`), so H runs it on its world as the machine does (`IgnoresMemory.onH`): both
exit alike, or both go on with the same result and worlds equal but for memory
(`stepOk_lift0`, `stepOk_lift1`, `stepOk_call`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Ranges -/

/-- Range `r` of `len` bytes, H's resolution of an access at machine address `ma`: no bytes, or
    a window of a live block at its machine base plus the offset. -/
def RangeAt (g : Ghost) (st : H.State) (r : H.Range) (ma len : Nat) : Prop :=
  (r = .empty ∧ len = 0) ∨ ∃ b o, r = .at b o ∧ g.live b ∧ o + len ≤ st.bsize b ∧ ma = g.j b + o

theorem rangeAt_of {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {dx : Bool} {v : H.Val} {ma len : Nat} {R : NatMap Range} {fpf : List Range} {os : List Nat}
    {r : H.Range} (hv : VRel g S.z dx v ma) (ho : OrigOk g hst R fpf os v)
    (hr : hst.range v len = some r) : RangeAt g hst r ma len := by
  by_cases hl : len = 0
  · subst hl
    simp only [State.range, if_true, Option.some.injEq] at hr
    exact Or.inl ⟨hr.symm, rfl⟩
  · obtain ⟨b, o, rfl, rfl, hob, -⟩ := range_ptr hr hl
    have hlive := live_of_orig hI ho
    exact Or.inr ⟨b, o, rfl, hlive, hob, addr_of_vrel hI hv hlive hob⟩

theorem RangeAt.mono {g : Ghost} {st : H.State} {r : H.Range} {ma len len' : Nat}
    (h : RangeAt g st r ma len) (hl : len' ≤ len) : RangeAt g st r ma len' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨b, o, rfl, h1, h2, h3⟩
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨b, o, rfl, h1, by omega, h3⟩

theorem RangeAt.state {g : Ghost} {st st' : H.State} {r : H.Range} {ma len : Nat}
    (h : RangeAt g st r ma len) (hbs : ∀ b, st'.bsize b = st.bsize b) : RangeAt g st' r ma len := by
  rcases h with h | ⟨b, o, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, o, h1, h2, by rw [hbs]; exact h3, h4⟩

/-- The machine's bytes at a range H resolves are H's bytes there. -/
theorem RangeAt.bytes {S : SecFacts} {st : H.State} {w : World} {g : Ghost} (hI : Inv S st w g)
    {r : H.Range} {ma len : Nat} (h : RangeAt g st r ma len) :
    w.memory.readWithPadding ma len = st.bytes r len := by
  rcases h with ⟨rfl, rfl⟩ | ⟨b, o, rfl, hb, ho, rfl⟩
  · rw [readWithPadding_of_mem (l := []) (n := 0) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))]
    simp [State.bytes, State.cells]
  · exact inv_bytes hI hb ho

theorem write_size (st : H.State) (r : H.Range) (cs : List MByte) :
    (st.write r cs).blocks.size = st.blocks.size := by
  cases r with
  | empty => rfl
  | «at» b o => exact write_blocks_size st b o cs

/-- A write of cells at a range H resolves, the machine writing their byte values at the
    machine address and nothing else, keeps the invariant if every fragment written is one of a
    heap pointer, outside address-0 mode. -/
theorem inv_write_at {S : SecFacts} {st : H.State} {w : World} {g : Ghost} (hI : Inv S st w g)
    {r : H.Range} {ma len : Nat} (h : RangeAt g st r ma len) {cs : List MByte}
    (hcs : cs.length = len) {m' : ByteArray}
    (hm : ∀ i, mem m' i = if ma ≤ i ∧ i < ma + len then
        ((cs[i - ma]?).getD (.byte 0)).val st.addrOf else mem w.memory i)
    (hfr : ∀ c ∈ cs, ∀ b' o' k, c = .frag b' o' k → g.heap b' ∧ o' < W ∧ S.z = false) :
    Inv S (st.write r cs) { w with memory := m' } g := by
  rcases h with ⟨rfl, rfl⟩ | ⟨b, o, rfl, hb, ho, rfl⟩
  · exact hI.mem_congr fun i => by rw [hm, if_neg (by omega)]
  · exact inv_write hI hb (by omega) (by rw [hcs]; exact hm) hfr

/-- A write of plain bytes at a range H resolves keeps the invariant. -/
theorem inv_writeBytes_at {S : SecFacts} {st : H.State} {w : World} {g : Ghost} (hI : Inv S st w g)
    {r : H.Range} {ma len : Nat} (h : RangeAt g st r ma len) {bs : ByteArray}
    (hbs : bs.size = len) {m' : ByteArray}
    (hm : ∀ i, mem m' i = if ma ≤ i ∧ i < ma + len then bs.data.getD (i - ma) 0 else mem w.memory i) :
    Inv S (st.writeBytes r bs) { w with memory := m' } g := by
  refine inv_write_at hI h (by rw [List.length_map, toList_length, hbs]) (fun i => ?_) ?_
  · rw [hm]
    split
    · next hi =>
      rw [List.getElem?_map, Reasoning.Theory.byteArray_toList_eq, Array.getElem?_toList,
        Array.getD_eq_getD_getElem?]
      cases bs.data[i - ma]? <;> rfl
    · rfl
  · intro c hc b' o' k he
    simp only [List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    cases he

/-- The machine's copy of `len` bytes of `src` from `sa` to `da`, against H's write of
    `src.readWithPadding sa len`. -/
theorem mem_copy (src : ByteArray) (sa : Nat) (m : ByteArray) (da len i : Nat) :
    mem (src.write sa m da len) i =
      if da ≤ i ∧ i < da + len then (src.readWithPadding sa len).data.getD (i - da) 0
      else mem m i := by
  rw [mem_write]
  split
  · next hi => rw [Check.readWithPadding_getD _ _ _ _ (by omega)]
  · rfl

/-! ## Steps -/

/-- H exits as the machine does. -/
theorem stepOk_exit {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {envH : HEnv} {s : HStmt} {L' : List Nat} {e : Exit World}
    (hstep : stepInst P.ctx I envH hst s.inst = .exit e) :
    StepOk P I S F g hst envH s L' (.error e) :=
  Or.inl ⟨_, fun _ => ExecBody.exit hstep, Or.inr (Or.inr ⟨e, rfl, Or.inr (Or.inr
    ⟨.error e, rfl, EndsAs.exit e⟩)⟩)⟩

/-- H is undefined, whatever the machine does. -/
theorem stepOk_ub {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {envH : HEnv} {s : HStmt} {L' : List Nat} {r : Except (Exit World) (Env × World)}
    (hstep : stepInst P.ctx I envH hst s.inst = .ub) : StepOk P I S F g hst envH s L' r :=
  Or.inl ⟨.ub, fun _ => ExecBody.ub hstep, Or.inl rfl⟩

/-- `stepOk_st1` for a change of H's state that keeps the blocks' number, sizes and address
    words. -/
theorem stepOk_st1' {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst hst' : H.State} {w w' : World} {envH : HEnv} {envM envM' : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)])
    {v : H.Val} (hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst')
    (hI' : Inv S hst' w' g) (hsz : hst'.blocks.size = hst.blocks.size)
    (hbs : ∀ b, hst'.bsize b = hst.bsize b) (had : ∀ b, hst'.addrOf b = hst.addrOf b)
    (hfit : v.fits tx = true)
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {m : Nat}
    (hm : (F.vm.find? x).bind (mval envM') = some m) (hv : VRel g S.z (F.D x) v m)
    (hok : ValOk hst' v) (horig : OrigOk g hst' F.R F.fpf (origOf F.O (.var x)) v) :
    StepOk P I S F g hst envH s L' (.ok (envM', w')) := by
  have hb : bindVals envH s.dsts [v] = some (envH.insert x v) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  refine Or.inr ⟨envM', w', rfl, envH.insert x v, hst', g, hI', ?_,
    ⟨le_of_eq hsz.symm, fun _ _ => rfl, fun b _ => hbs b, fun b _ => had b, fun _ h => h,
      fun _ h _ => h⟩, fun rest o hr => ExecBody.step hstep hb hr⟩
  refine envRel_step hE (fun y hy hn => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn)) hb hkeep
    (fun y hy hn => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn))
    (fun v h => h.state (le_of_eq hsz.symm)) (fun _ _ h => h.state hI.live_lt fun b _ => hbs b) ?_
  intro y hy _
  simp only [hd, List.map_cons, List.map_nil, List.mem_singleton] at hy
  subst hy
  exact ⟨v, m, by simp, ⟨tx, hdt, hfit⟩, hm, hv, hok, horig⟩

/-- A word result binds a word: the machine's value of `x` is `u`. -/
theorem mval_one {envM : Env} {r : Nat} {u : Ethereum.UInt256} {F : Frame} {x : Nat}
    (hx : F.vm.find? x = some (.var r)) :
    (F.vm.find? x).bind (mval (envM.insert r (.int 256 u.toNat))) = some u.toNat := by
  rw [hx]; simp [mval]

theorem mval_ins {envM : Env} {r n : Nat} {F : Frame} {x : Nat}
    (hx : F.vm.find? x = some (.var r)) :
    (F.vm.find? x).bind (mval (envM.insert r (.int 256 n))) = some n := by
  rw [hx]; simp [mval]

theorem insert_keep {envM : Env} {r : Nat} {v : Val} :
    ∀ r', r' ∉ [r] → (envM.insert r v)[r']? = envM[r']? := fun _ hr' =>
  insert_other fun e => hr' (by simp [e])

/-- An operation with no result whose world part `x` ignores memory: H runs `x` on its world,
    as the machine does on its own. -/
theorem stepOk_lift0 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' []) (hd : s.dsts = []) {α : Type} {x : FeM α}
    (hx : IgnoresMemory x) (hstep : stepInst P.ctx I envH hst s.inst = liftFe I hst x fun _ st => .ok [] st)
    {res : Except (Exit World) (Env × World)} (hres : (x >>= fun _ => pure envM).exec I w = some res) :
    StepOk P I S F g hst envH s L' res := by
  have hon := IgnoresMemory.onH hx hI I
  rcases exec_bind_some hres with ⟨e, h1, rfl⟩ | ⟨a, w', h1, h2⟩
  · exact stepOk_exit (by rw [hstep]; simp [liftFe, hon, h1])
  · simp only [Fe.M.exec_pure, Option.some.injEq] at h2
    subst h2
    have hI' := inv_world hI (IgnoresMemory.keeps hx h1)
    exact stepOk_st0 hI hE hA hd (by rw [hstep]; simp [liftFe, hon, h1]) hI' rfl (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)

/-- An operation with one word result whose world part `x` ignores memory. -/
theorem stepOk_lift1 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {r : Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)])
    (hwx : isWord tx = true) (hvx : F.vm.find? x = some (.var r)) {m : FeM Ethereum.UInt256}
    (hx : IgnoresMemory m)
    (hstep : stepInst P.ctx I envH hst s.inst = liftFe I hst m fun a st => .ok [.int 256 a.toNat] st)
    {res : Except (Exit World) (Env × World)}
    (hres : (m >>= fun u => pure (envM.insert r (.int 256 u.toNat))).exec I w = some res) :
    StepOk P I S F g hst envH s L' res := by
  have hon := IgnoresMemory.onH hx hI I
  rcases exec_bind_some hres with ⟨e, h1, rfl⟩ | ⟨u, w', h1, h2⟩
  · exact stepOk_exit (by rw [hstep]; simp [liftFe, hon, h1])
  · simp only [Fe.M.exec_pure, Option.some.injEq] at h2
    subst h2
    have hI' := inv_world hI (IgnoresMemory.keeps hx h1)
    have hu : u.toNat < W := toNat_lt' u
    exact stepOk_st1' hI hE hA hd (by rw [hstep]; simp [liftFe, hon, h1]) hI' rfl (fun _ => rfl)
      (fun _ => rfl) (fits_word hwx hu) insert_keep (mval_one hvx) rfl trivial trivial

/-- The bytes of the return data a call writes: as many as `retCount` says, of the data. -/
theorem retCount_le (rl : Ethereum.UInt256) (o : ByteArray) :
    retCount rl o ≤ rl.toNat ∧ retCount rl o ≤ o.size := by
  unfold retCount
  have h1 : (Ethereum.UInt256.ofNat o.size).toNat ≤ o.size := by
    simp only [Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat]; exact Nat.mod_le _ _
  by_cases h : rl ≤ Ethereum.UInt256.ofNat o.size
  · have e : min rl (Ethereum.UInt256.ofNat o.size) = rl := if_pos h
    have h' : rl.toNat ≤ (Ethereum.UInt256.ofNat o.size).toNat := h
    rw [e]; exact ⟨le_refl _, by omega⟩
  · have e : min rl (Ethereum.UInt256.ofNat o.size) = Ethereum.UInt256.ofNat o.size := if_neg h
    have h' : ¬ rl.toNat ≤ (Ethereum.UInt256.ofNat o.size).toNat := h
    rw [e]; exact ⟨by omega, h1⟩

theorem extract_size {o : ByteArray} {n : Nat} (h : n ≤ o.size) : (o.extract 0 n).size = n := by
  rw [ByteArray.size_extract]; omega

theorem extract_getD {o : ByteArray} {n i : Nat} (hi : i < n) :
    (o.extract 0 n).data.getD i 0 = o.data.getD i 0 := by
  simp only [ByteArray.data_extract, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : i < o.data.size
  · rw [if_pos (by omega)]; simp
  · rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]

/-- A message call: its memory-free core `fe` on H's bytes of the input range, H then writing the
    output at the output range as the machine writes it. -/
theorem stepOk_call {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {r : Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' [r]) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)])
    (hwx : isWord tx = true) (hvx : F.vm.find? x = some (.var r))
    {fe : ByteArray → FeM (Ethereum.UInt256 × ByteArray)} (hfe : ∀ i, IgnoresMemory (fe i))
    {ar rr : H.Range} {mia mil mra : Nat} {rl : Ethereum.UInt256}
    (har : RangeAt g hst ar mia mil) (hrr : RangeAt g hst rr mra rl.toNat)
    (hstep : stepInst P.ctx I envH hst s.inst = callH I hst ar mil rr rl fe)
    {res : Except (Exit World) (Env × World)}
    (hres : (fe (w.memory.readWithPadding mia mil) >>= fun p =>
      modify (fun w : World => { w with memory := p.2.write 0 w.memory mra (retCount rl p.2) }) >>=
        fun _ => pure (envM.insert r (.int 256 p.1.toNat))).exec I w = some res) :
    StepOk P I S F g hst envH s L' res := by
  rw [har.bytes hI] at hres
  have hon := IgnoresMemory.onH (hfe (hst.bytes ar mil)) hI I
  rcases exec_bind_some hres with ⟨e, h1, rfl⟩ | ⟨⟨z, o⟩, w', h1, h2⟩
  · exact stepOk_exit (by rw [hstep]; simp [callH, liftFe, hon, h1])
  · simp only [Fe.M.exec_bind, Fe.M.exec_modify, Fe.M.exec_pure, Option.some.injEq] at h2
    subst h2
    have hkm := IgnoresMemory.keeps (hfe _) h1
    have hI1 := inv_world hI hkm
    obtain ⟨hc1, hc2⟩ := retCount_le rl o
    have hI2 := inv_writeBytes_at hI1 ((hrr.state fun _ => rfl).mono hc1)
      (bs := o.extract 0 (retCount rl o)) (extract_size hc2)
      (m' := o.write 0 w'.memory mra (retCount rl o)) (fun i => by
        rw [mem_write, hkm]
        split
        · next hi => rw [Nat.zero_add, extract_getD (by omega)]
        · rfl)
    have hu : z.toNat < W := toNat_lt' z
    have hbs : ∀ b, ({ hst with world := { w' with memory := hst.world.memory } }.writeBytes rr
        (o.extract 0 (retCount rl o))).bsize b = hst.bsize b := fun b => by
      simp only [State.writeBytes]; rw [bsize_write]; rfl
    have had : ∀ b, ({ hst with world := { w' with memory := hst.world.memory } }.writeBytes rr
        (o.extract 0 (retCount rl o))).addrOf b = hst.addrOf b := fun b => by
      simp only [State.writeBytes]; rw [addrOf_write]; rfl
    exact stepOk_st1' hI hE hA hd (by rw [hstep]; simp [callH, liftFe, hon, h1]) hI2
      (by simp only [State.writeBytes]; rw [write_size]) hbs had (fits_word hwx hu) insert_keep
      (mval_one hvx) rfl trivial trivial

/-! ## Operands and the machine's run -/

/-- An operand of an EVM operation: its H value and machine word, related; outside the address
    positions S8 leaves unobserved, H's word is the machine's. -/
theorem evm_arg {S : SecFacts} {F : Frame} {g : Ghost} {hst : H.State} {w : World}
    {envH : HEnv} {envM : Env} {L L' : List Nat} {c : FCtx} {Dr : Derived} {k : Nat}
    {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {i : Nat} {a a' : Operand}
    (hai : s.inst.args[i]? = some a) (ht : (c.tyOf a).any Ty.value = true)
    (hm : mop F.vm a = some a') :
    ∃ v m, evalOp envH a = some v ∧ mval envM a' = some m ∧ m < W ∧ VRel g S.z (F.dOp a) v m ∧
      ValOk hst v ∧ OrigOk g hst F.R F.fpf (origOf F.O a) v ∧
      (i ∉ nonObserving Dr k s → hst.word v = m) := by
  obtain ⟨ta, hta, hv⟩ := tyOf_any ht
  obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [← hy]; exact List.mem_of_getElem? hai)) hta hm
  refine ⟨v, m, h1, h3, vrel_lt h4 h2 hv, h4, h5, h6, fun hni => vrel_exact hI h4 h5 fun hz => ?_⟩
  rw [hA.dOp]
  cases hd : Dr.op k a
  · rfl
  · exact absurd (hA.obs hz i a hai hd) hni

theorem mapM_cons' {α β : Type} {f : α → Option β} {a : α} {as : List α} {bs : List β}
    (h : (a :: as).mapM f = some bs) : ∃ b bs', f a = some b ∧ as.mapM f = some bs' ∧ bs = b :: bs' := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨b, hb, bs', hbs, rfl⟩ := h
  exact ⟨b, bs', hb, hbs, rfl⟩

theorem mapM_nil' {α β : Type} {f : α → Option β} {bs : List β}
    (h : ([] : List α).mapM f = some bs) : bs = [] := by
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm

theorem toNat_ofNat (m : Nat) : (Ethereum.UInt256.ofNat m).toNat = m % W := by
  simp only [Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat]; rfl

theorem isWord_sameW {t : Ty} (h : isWord t = true) : sameW (.int 256) t = true := by
  simp only [isWord, Bool.and_eq_true, beq_iff_eq] at h
  simp only [sameW, h.1, h.2, Bool.and_true, beq_self_eq_true]
  decide

/-- The machine's run of an EVM operation with no result. -/
theorem run_evm0 (O : Oracle) (cM : Ctx) (envM : Env) (op : EvmOp) {args' : List Operand}
    {mws : List Nat} (hmws : List.Forall₂ (fun a' m => mval envM a' = some m) args' mws)
    (m : FeM Unit) (hop : op.run (mws.map Ethereum.UInt256.ofNat) = (m >>= fun _ => pure [])) :
    runBodyO O cM envM [⟨[], .evm op args'⟩] = (m >>= fun _ => pure envM) := by
  rw [runBodyO_plain O cM envM _ (by simp)]
  simp only [runPlain, runInst, mapM_evalWord hmws, pure_bind, hop, bind_assoc]
  simp [Fe.Sonatina.bind]

/-- The machine's run of an EVM operation with one word result. -/
theorem run_evm1 (O : Oracle) (cM : Ctx) (envM : Env) (op : EvmOp) {args' : List Operand}
    {mws : List Nat} (hmws : List.Forall₂ (fun a' m => mval envM a' = some m) args' mws) (r : Nat)
    (m : FeM Ethereum.UInt256)
    (hop : op.run (mws.map Ethereum.UInt256.ofNat) = (m >>= fun u => pure [word u])) :
    runBodyO O cM envM [⟨[(r, .int 256)], .evm op args'⟩] =
      (m >>= fun u => pure (envM.insert r (.int 256 u.toNat))) := by
  rw [runBodyO_plain O cM envM _ (by simp)]
  simp only [runPlain, runInst, mapM_evalWord hmws, pure_bind, hop, bind_assoc]
  congr 1
  funext u
  have hu : u.toNat % 2 ^ 256 = u.toNat := Nat.mod_eq_of_lt (toNat_lt' u)
  simp only [Fe.Sonatina.bind, word, Val.as, Ty.bits, List.length_cons, List.length_nil,
    beq_self_eq_true, if_true, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, hu, pure_bind, runPlain]

theorem step_evm {P : HSection} {I : Fe.EVM.Env} {envH : HEnv} {hst : H.State} {s : HStmt}
    {op : EvmOp} {args : List Operand} {vs : List H.Val} (hi : s.inst = .base (.evm op args))
    (hvs : args.mapM (evalOp envH) = some vs) :
    stepInst P.ctx I envH hst s.inst = evmH I hst op vs := by
  simp only [stepInst, hi, hvs]

/-- The cells of a range H resolves: their values are the machine's bytes there, and each
    fragment among them is a heap pointer's, outside address-0 mode. -/
theorem cells_at {S : SecFacts} {st : H.State} {w : World} {g : Ghost} (hI : Inv S st w g)
    {r : H.Range} {ma len : Nat} (h : RangeAt g st r ma len) :
    (st.cells r len).length = len ∧
    (∀ i, i < len → (((st.cells r len)[i]?).getD (.byte 0)).val st.addrOf = mem w.memory (ma + i)) ∧
    ∀ c ∈ st.cells r len, ∀ b' o' k, c = .frag b' o' k → g.heap b' ∧ o' < W ∧ S.z = false := by
  rcases h with ⟨rfl, rfl⟩ | ⟨b, o, rfl, hb, hob, rfl⟩
  · exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun c hc => by cases hc⟩
  · have hc : st.cells (.at b o) len = (List.range len).map fun i => st.cell b (o + i) :=
      cellsAt_eq (hI.live_lt b hb) o len
    rw [hc]
    refine ⟨by simp, fun i hi => ?_, fun c hcm b' o' k he => ?_⟩
    · rw [List.getElem?_map, List.getElem?_range hi]
      simp only [Option.map_some, Option.getD_some]
      rw [show g.j b + o + i = g.j b + (o + i) by omega]
      exact (hI.bytes b hb (o + i) (by omega)).symm
    · simp only [List.mem_map, List.mem_range] at hcm
      obtain ⟨i, hi, rfl⟩ := hcm
      exact hI.frags b hb (o + i) (by omega) b' o' k he

end Fe.Sonatina.Stage3.Place
