import Fe.Sonatina.Stage3.Place.FixQ
import Fe.Sonatina.Stage3.Place.Term

/-!
# After a terminal fixed buffer: the relation and the pure statements

From a terminal fixed buffer's site on (rule S6), `Inv` is not kept: the buffer's block may
overlap live and heap blocks, and stores through the buffer overwrite their machine bytes.  The
relation after the site (`SR`) keeps only what the rest of the run reads: the worlds but for
memory, the address words, the live values (without `OrigOk`), the buffer's cells against the
machine's bytes at its base, the must-origin values pointing into it, and `FixInv`.

A pure statement after the site (`sfxPure`) runs as its pattern lemma says, against a virtual
state that satisfies `Inv` (`vSt`, `vG`, `vS`, `vF`): every block shrunk to nothing but the
buffer, whose cells are the machine's bytes; no heap; every value's origins those of a parameter
with an empty footprint.  H's pure step depends on the state only through its address words
(`step_congr`), which the virtual state keeps.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Pure statements -/

/-- The statements after a site that neither store nor allocate nor call. -/
def sfxPure : HInst → Bool
  | .base (.bin ..) | .base (.not _) | .base (.neg _) | .base (.clz _) | .base (.ctz _)
  | .base (.ovf ..) | .base (.sat ..) | .base (.cast ..) | .base (.blackBox _)
  | .base (.symAddr _) | .base (.symSize _) | .gep .. | .truncNuw .. | .base (.cmp ..)
  | .base (.isZero _) => true
  | _ => false

/-- The result with its state replaced. -/
def setSt (st : H.State) : IRes → IRes
  | .ok vals _ => .ok vals st
  | r => r

theorem binVal_congr {st st' : H.State} (hw : st.word = st'.word) (op : BinOp) (x y : H.Val) :
    binVal st op x y = binVal st' op x y := by
  simp only [binVal, hw]

theorem castVal_congr {st st' : H.State} (hw : st.word = st'.word) (op : CastOp) (x : H.Val)
    (t : Ty) : castVal st op x t = castVal st' op x t := by
  simp only [castVal, hw]

/-- H's pure step depends on the state only through its words. -/
theorem step_congr {c : H.Ctx} {I : Fe.EVM.Env} {env : HEnv} {st st' : H.State} {i : HInst}
    (hp : sfxPure i = true) (hw : st.word = st'.word) :
    stepInst c I env st' i = setSt st' (stepInst c I env st i) := by
  cases i with
  | base i =>
    cases i <;> simp only [sfxPure, reduceCtorEq] at hp
    all_goals simp only [stepInst, binVal_congr hw, castVal_congr hw, hw]
    all_goals (repeat' split) <;> simp_all [setSt]
  | gep bt b is =>
    simp only [stepInst, hw]
    all_goals (repeat' split) <;> simp_all [setSt]
  | truncNuw a t =>
    simp only [stepInst, hw]
    all_goals (repeat' split) <;> simp_all [setSt]
  | mloadBytes => simp [sfxPure] at hp

theorem step_keep {c : H.Ctx} {I : Fe.EVM.Env} {env : HEnv} {st st₁ : H.State} {i : HInst}
    {vals : List H.Val} (hp : sfxPure i = true) (h : stepInst c I env st i = .ok vals st₁) :
    st₁ = st := by
  have := step_congr (c := c) (I := I) (env := env) (st := st) (st' := st) hp rfl
  rw [h] at this
  simp only [setSt, IRes.ok.injEq] at this
  exact this.2

theorem word_eq {st st' : H.State} (h : ∀ b, st.addrOf b = st'.addrOf b) : st.word = st'.word := by
  funext v
  simp only [State.word, funext h]

/-! ## The relation after the site -/

/-- The relation from a terminal fixed buffer's site on, at the point before statement `j` of
    block `b`, whose live values are `L`: the buffer is block `kt` of `n` bytes at machine base
    `base`, the site defines `t`. -/
structure SR (S : SecFacts) (fn : Fn) (kt base n t : Nat) (b : HBlock) (j : Nat) (L : List Nat)
    (g : Ghost) (hst : H.State) (w : World) (envH : HEnv) (envM : Env) : Prop where
  world : { w with memory := hst.world.memory } = hst.world
  bsz : ∀ (b : Nat) (blk : MemBlock), hst.blocks[b]? = some blk → blk.bytes.size = blk.size
  exact : ∀ b, b < hst.blocks.size → g.j b ≠ 0 → hst.addrOf b = g.j b
  zero : ∀ b, b < hst.blocks.size → g.j b = 0 → S.z = true
  vals : ∀ x ∈ L, ∃ v m, envH[x]? = some v ∧ (∃ ty, fn.F.decls.find? x = some ty ∧ v.fits ty = true) ∧
    (fn.F.vm.find? x).bind (mval envM) = some m ∧ VRel g S.z (fn.F.D x) v m ∧ ValOk hst v ∧
    ∀ b o, v = .ptr b o → g.j b < W
  hkt : kt < hst.blocks.size
  ksz : hst.bsize kt = n
  jt : g.j kt = base
  bn : base + n < W
  buf : ∀ k, k < n → mem w.memory (base + k) = (hst.cell kt k).val hst.addrOf
  q : FixInv fn b j envH
  must : ∀ y ∈ fixM fn.f t, ∀ v, envH[y]? = some v → ∃ o, v = .ptr kt o

/-! ## The virtual state -/

def vBlk (m : ByteArray) (kt n base : Nat) (b : Nat) (blk : MemBlock) : MemBlock :=
  if b = kt then ⟨n, ((List.range n).map fun k => MByte.byte (mem m (base + k))).toArray, blk.addr,
    blk.kind⟩
  else ⟨0, #[], blk.addr, blk.kind⟩

def vSt (hst : H.State) (w : World) (kt n base : Nat) : H.State :=
  { world := w, blocks := hst.blocks.mapIdx (vBlk w.memory kt n base), heapReq := hst.heapReq }

def vG (g : Ghost) (hst : H.State) : Ghost :=
  ⟨g.j, fun b => b < hst.blocks.size ∧ g.j b < W, fun _ => False⟩

def vS (S : SecFacts) : SecFacts := { S with hasHeap := false }

def vO (l : List Nat) : Orig := NatMap.ofList (l.map fun y => (y, [0]))

def vF (F : Frame) (l : List Nat) : Frame := { F with O := vO l, fpf := [] }

section virt

variable {hst : H.State} {w : World} {kt n base : Nat}

theorem vSt_size : (vSt hst w kt n base).blocks.size = hst.blocks.size := by simp [vSt]

theorem vSt_get (b : Nat) :
    (vSt hst w kt n base).blocks[b]? = hst.blocks[b]?.map (vBlk w.memory kt n base b) := by
  simp only [vSt]; exact Array.getElem?_mapIdx

theorem vSt_addr (b : Nat) : (vSt hst w kt n base).addrOf b = hst.addrOf b := by
  simp only [State.addrOf, vSt_get, Option.map_map]
  cases hst.blocks[b]? with
  | none => rfl
  | some blk => simp only [Option.map_some, Function.comp_apply, Option.getD_some, vBlk]; split <;> rfl

theorem vSt_word : (vSt hst w kt n base).word = hst.word := word_eq vSt_addr

theorem vSt_bsize (b : Nat) :
    (vSt hst w kt n base).bsize b = if b = kt ∧ b < hst.blocks.size then n else 0 := by
  simp only [State.bsize, vSt_get, Option.map_map]
  by_cases hb : b < hst.blocks.size
  · rw [Array.getElem?_eq_getElem hb]
    simp only [Option.map_some, Function.comp_apply, Option.getD_some, vBlk]
    split
    · next h => subst h; simp [hb]
    · next h => simp [h]
  · rw [Array.getElem?_eq_none (by omega)]
    simp [hb]

theorem vSt_cell {k : Nat} (hkt : kt < hst.blocks.size) (hk : k < n) :
    (vSt hst w kt n base).cell kt k = .byte (mem w.memory (base + k)) := by
  simp only [State.cell, vSt_get, Option.map_map, Array.getElem?_eq_getElem hkt, Option.map_some,
    Function.comp_apply, Option.getD_some, vBlk, if_true, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hk]

theorem vSt_bsz : ∀ (b : Nat) (blk : MemBlock), (vSt hst w kt n base).blocks[b]? = some blk →
    blk.bytes.size = blk.size := by
  intro b blk h
  rw [vSt_get] at h
  cases hb : hst.blocks[b]? with
  | none => rw [hb] at h; cases h
  | some blk' =>
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq, vBlk] at h
    subst h
    split <;> simp

end virt

theorem lookup_vO {y : Nat} : ∀ {l : List Nat}, (l.map fun y => (y, [0])).lookup y = some [0] ∨
    ((l.map fun y => (y, [0])).lookup y = none ∧ y ∉ l)
  | [] => Or.inr ⟨rfl, by simp⟩
  | x :: l => by
    simp only [List.map_cons, List.lookup]
    by_cases h : y = x
    · subst h; simp
    · have : (y == x) = false := by simpa using h
      simp only [this]
      rcases lookup_vO (l := l) with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, by simp [h, h2]⟩

theorem origOf_vO {l : List Nat} (a : Operand) : ∀ o ∈ origOf (vO l) a, o = 0 := by
  intro o ho
  cases a with
  | imm => simp [origOf] at ho
  | var y =>
    simp only [origOf, vO, NatMap.find?_ofList] at ho
    rcases lookup_vO (y := y) (l := l) with h | ⟨h, -⟩ <;> rw [h] at ho <;> simp_all

theorem origOf_vO_mem {l : List Nat} {y : Nat} (hy : y ∈ l) : 0 ∈ origOf (vO l) (.var y) := by
  simp only [origOf, vO, NatMap.find?_ofList]
  rcases lookup_vO (y := y) (l := l) with h | ⟨-, h⟩
  · rw [h]; simp
  · exact absurd hy h

/-- The origins a statement that does not allocate gives, from operands whose origins are all
    `0`, are `0`. -/
theorem stmtOrig_zero {fr : FuncRec} {O : Orig} (hO : ∀ a, ∀ o ∈ origOf O a, o = 0) {s : HStmt}
    (ha : ∀ t, s.inst ≠ .base (.alloca t)) (hm : ∀ a, s.inst ≠ .base (.malloc a)) :
    ∀ o ∈ stmtOrig fr O s, o = 0 := by
  intro o ho
  unfold stmtOrig at ho
  split at ho
  · next t hi => exact absurd hi (ha t)
  · next a hi => exact absurd hi (hm a)
  · exact hO _ o ho
  · split at ho
    all_goals first
      | (simp only [mem_nset, List.mem_append] at ho; rcases ho with ho | ho <;> exact hO _ o ho)
      | exact hO _ o ho
      | cases ho
  · split at ho
    all_goals first | exact hO _ o ho | cases ho
  · exact hO _ o ho
  · simp only [mem_nset, List.mem_append] at ho; rcases ho with ho | ho <;> exact hO _ o ho
  · cases ho

section rel

variable {S : SecFacts} {fn : Fn} {kt base n t : Nat} {b : HBlock} {j : Nat} {L : List Nat}
  {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}

theorem SR.inv (hR : SR S fn kt base n t b j L g hst w envH envM) :
    Inv (vS S) (vSt hst w kt n base) w (vG g hst) where
  world := rfl
  live_lt b hb := by rw [vSt_size]; exact hb.1
  heap_live _ h := h.elim
  heap_has _ h := h.elim
  bytes_size := vSt_bsz
  exact b hb hj := by rw [vSt_addr]; exact hR.exact b (by rwa [vSt_size] at hb) hj
  zero b hb hj := hR.zero b (by rwa [vSt_size] at hb) hj
  bound b hb := by
    rw [vSt_bsize]
    show g.j b + _ < W
    split
    · next h => obtain ⟨rfl, -⟩ := h; rw [hR.jt]; exact hR.bn
    · simpa using hb.2
  disj b b' _ _ hne := by
    simp only [Ghost.rg, vG, vSt_bsize]
    by_cases h1 : b = kt
    · have : ¬ (b' = kt ∧ b' < hst.blocks.size) := fun h => hne (h1.trans h.1.symm)
      exact Or.inr (Or.inl (by simp [this]))
    · have : ¬ (b = kt ∧ b < hst.blocks.size) := fun h => h1 h.1
      exact Or.inl (by simp [this])
  bytes b hb i hi := by
    rw [vSt_bsize] at hi
    split at hi
    · next h =>
      obtain ⟨rfl, hk⟩ := h
      show mem w.memory (g.j b + i) = _
      rw [vSt_cell hk hi, hR.jt]; rfl
    · cases hi
  frags b hb i hi b' o k hc := by
    rw [vSt_bsize] at hi
    split at hi
    · next h =>
      obtain ⟨rfl, hk⟩ := h
      rw [vSt_cell hk hi] at hc; cases hc
    · cases hi
  e96 h := by cases h
  heap_floor _ h := h.elim
  fp h := by cases h
  frame h := by cases h

theorem SR.envRel (hR : SR S fn kt base n t b j L g hst w envH envM) {l : List Nat}
    (hl : ∀ x ∈ L, x ∈ l) :
    EnvRel (vS S).z (vF fn.F l) (vG g hst) (vSt hst w kt n base) envH envM L := by
  intro x hx
  obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := hR.vals x hx
  refine ⟨v, m, h1, h2, h3, h4, ?_, ?_⟩
  · cases v with
    | int => trivial
    | ptr bb o => exact ⟨by rw [vSt_size]; exact h5.1, h5.2⟩
  · cases v with
    | int => trivial
    | ptr bb o =>
      exact Or.inr ⟨⟨h5.1, h6 bb o rfl⟩, Or.inr ⟨origOf_vO_mem (hl x hx), fun _ h => by cases h⟩⟩

end rel

theorem At.virt {S : SecFacts} {F : Frame} {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt}
    {callee? : Option Nat} {L L' ds : List Nat} (hA : At S F c Dr k s callee? L L' ds)
    {l : List Nat} (hl : ∀ x ∈ s.defs, x ∈ l) (hp : sfxPure s.inst = true) :
    At (vS S) (vF F l) c Dr k s callee? L L' ds where
  decls := hA.decls
  dsts := hA.dsts
  uses := hA.uses
  keep := hA.keep
  clob := hA.clob
  nodup := hA.nodup
  self := hA.self
  s3 a v h := by
    rcases h with ⟨t, ht⟩ | ht <;> rw [ht] at hp <;> simp [sfxPure] at hp
  orig x t hd o ho := by
    have h0 := stmtOrig_zero (fr := c.frec) (origOf_vO (l := l)) (s := s)
      (fun t ht => by rw [ht] at hp; simp [sfxPure] at hp)
      (fun a ht => by rw [ht] at hp; simp [sfxPure] at hp) o ho
    subst h0
    exact origOf_vO_mem (hl x (by simp [HStmt.defs, hd]))
  D := hA.D
  obs := hA.obs
  der := hA.der

/-! ## Must-origin steps -/

/-- A statement of the must-origin closure that H steps gives pointers into the buffer when its
    must-origin operands do and its integer operands are integers. -/
theorem mustStep_ptr {c : H.Ctx} {I : Fe.EVM.Env} {env : HEnv} {st st' : H.State}
    {Iv M : List Nat} {s : HStmt} {vals : List H.Val} {kt : Nat} (hm : mustStep Iv M s = true)
    (hM : ∀ y ∈ M, ∀ v, env[y]? = some v → ∃ o, v = .ptr kt o)
    (hI : ∀ y ∈ Iv, ∀ v, env[y]? = some v → IsInt v)
    (h : stepInst c I env st s.inst = .ok vals st') : ∀ v ∈ vals, ∃ o, v = .ptr kt o := by
  have km : ∀ a : Operand, (match a with | .var y => M.contains y | .imm .. => false) = true →
      ∀ v, evalOp env a = some v → ∃ o, v = .ptr kt o := by
    intro a ha v hv
    cases a with
    | imm => simp at ha
    | var y => exact hM y (by simpa using ha) v hv
  have ki : ∀ a : Operand, (match a with | .var y => Iv.contains y | .imm .. => true) = true →
      ∀ v, evalOp env a = some v → IsInt v := by
    intro a ha v hv
    cases a with
    | imm => simp only [evalOp, Option.some.injEq] at hv; subst hv; intro b o h; cases h
    | var y => exact hI y (by simpa using ha) v hv
  unfold mustStep at hm
  split at hm
  · next bt b' idxs hi =>
    rw [hi] at h
    simp only [stepInst] at h
    split at h
    · next x is hx _ =>
      obtain ⟨o, rfl⟩ := km b' hm x hx
      split at h
      · simp only [IRes.ok.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro v hv; simp at hv; subst hv; exact ⟨_, rfl⟩
      · cases h
    · cases h
  · next a b' hi =>
    rw [hi] at h
    simp only [stepInst] at h
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some x =>
      cases eb : evalOp env b' with
      | none => simp [ea, eb] at h
      | some y =>
        simp only [ea, eb] at h
        split at h
        · next v hv =>
          simp only [IRes.ok.injEq] at h
          obtain ⟨rfl, -⟩ := h
          intro v' hv'; simp at hv'; subst hv'
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hm
          rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · obtain ⟨o, rfl⟩ := km a h1 x ea
            have hy := ki b' h2 y eb
            cases y with
            | ptr => exact absurd rfl (hy _ _)
            | int bits k =>
              unfold binVal at hv
              split at hv
              · cases hv
              · simp only [ptrBin, Option.getD_some, Option.some.injEq] at hv
                exact ⟨_, hv.symm⟩
          · obtain ⟨o, rfl⟩ := km b' h1 y eb
            have hx := ki a h2 x ea
            cases x with
            | ptr => exact absurd rfl (hx _ _)
            | int bits k =>
              unfold binVal at hv
              split at hv
              · cases hv
              · simp only [ptrBin, Option.getD_some, Option.some.injEq] at hv
                exact ⟨_, hv.symm⟩
        · cases h
  · next a b' hi =>
    rw [hi] at h
    simp only [stepInst] at h
    simp only [Bool.and_eq_true] at hm
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some x =>
      cases eb : evalOp env b' with
      | none => simp [ea, eb] at h
      | some y =>
        simp only [ea, eb] at h
        split at h
        · next v hv =>
          simp only [IRes.ok.injEq] at h
          obtain ⟨rfl, -⟩ := h
          intro v' hv'; simp at hv'; subst hv'
          obtain ⟨o, rfl⟩ := km a hm.1 x ea
          have hy := ki b' hm.2 y eb
          cases y with
          | ptr => exact absurd rfl (hy _ _)
          | int bits k =>
            unfold binVal at hv
            split at hv
            · cases hv
            · simp only [ptrBin, ite_true, Option.getD_some, Option.some.injEq] at hv
              exact ⟨_, hv.symm⟩
        · cases h
  · next op a t hi =>
    rw [hi] at h
    simp only [stepInst] at h
    simp only [Bool.and_eq_true] at hm
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some x =>
      simp only [ea] at h
      split at h
      · next v hv =>
        simp only [IRes.ok.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro v' hv'; simp at hv'; subst hv'
        obtain ⟨o, rfl⟩ := km a hm.2 x ea
        unfold castVal at hv
        revert hv hm
        cases op <;> cases t <;> simp [keepsPtr, Ty.value] <;> (try split) <;> simp_all <;>
          (try (intros; subst_vars; exact ⟨_, rfl⟩))
      · cases h
  · next a hi =>
    rw [hi] at h
    simp only [stepInst] at h
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some x =>
      simp only [ea, IRes.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro v hv; simp at hv; subst hv
      exact km a hm _ ea
  · cases hm

/-! ## One statement of H that halts -/

theorem execBody_halt_one {P : HSection} {I : Fe.EVM.Env} {envH : HEnv} {s : HStmt}
    {hst : H.State} {o : Outcome} (h : ExecBody P I envH [s] hst (.halt o)) :
    (∃ e, stepInst P.ctx I envH hst s.inst = .exit e ∧ o = .ends (.error e)) ∨
    (stepInst P.ctx I envH hst s.inst = .ub ∧ o = .ub) ∨ (∃ a, s.inst = .base (.malloc a)) ∨
    ∃ g args, s.inst = .base (.call g args) := by
  cases h with
  | step _ _ hr => cases hr
  | exit hi => exact Or.inl ⟨_, hi, rfl⟩
  | ub hi => exact Or.inr (Or.inl ⟨hi, rfl⟩)
  | alloca _ _ _ _ _ hr => cases hr
  | malloc _ _ _ _ _ _ hr => cases hr
  | exhausted hs _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, hs⟩))
  | call _ _ _ _ hr => cases hr
  | callHalt hs _ _ => exact Or.inr (Or.inr (Or.inr ⟨_, _, hs⟩))

end Fe.Sonatina.Stage3.Place
