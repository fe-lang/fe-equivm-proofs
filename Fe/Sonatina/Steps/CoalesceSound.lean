import Fe.Sonatina.Steps.BranchCanonSound
import Fe.Sonatina.CheckArith

/-!
# `coalesce_copies` is sound (stage 1 of ruling R-11.4)

The output has the input's blocks, phis and terminators; the simulation relates the output and
the input at the same block entered from the same block, as `branch_canonicalize`'s does (`BR`,
`BMid`).  A statement both sides keep steps on both; a window of word loads and stores steps on
the input while the output runs the window's kept `add`/`sub` statements alongside, in order,
and then its `evm_mcopy` (`win_walk`, `win_fol`).

The window's memory (`CopyMem`): after `q` of its stores the input's memory is the window's
start memory `m₀` with the first `q` words of `m₀`'s `[S, S + 32 n)` written at `D`, so after
all `n` it is `mcopy D S (32 n)` of `m₀` (`ByteArray.write`, which reads its source before it
writes).  A load reads `m₀`: before the first store (`loadsFirst`), or from a range disjoint from
the destination's.  Each load's word goes to its store unchanged (`toByteArray_uInt256`), and
the addresses are the constants `addrNorm` computes, by L2 on the input (`addrNorm_sound`).  The
stage-1 bounds (`S + 32 n ≤ 2 ^ 256`, `D + 32 n ≤ 2 ^ 256`) make every address a word.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Fe.Sonatina.Check

/-! ## Words -/

theorem size_eq_W256 : UInt256.size = W256 := by norm_num [UInt256.size, W256]

theorem toNat_ofNat_mod (x : Nat) : (UInt256.ofNat x).toNat = x % W256 := by
  rw [← size_eq_W256]; rfl

theorem toNat_lt_W256 (v : UInt256) : v.toNat < W256 := size_eq_W256 ▸ v.val.isLt

theorem ofNat_toNat' (v : UInt256) : UInt256.ofNat v.toNat = v := by
  apply eq_of_toNat
  rw [toNat_ofNat_mod, Nat.mod_eq_of_lt (toNat_lt_W256 v)]

/-- The word round trip: the bytes of the word of 32 bytes are those bytes. -/
theorem toByteArray_uInt256 {b : ByteArray} (h : b.size = 32) :
    (uInt256OfByteArray b).toByteArray = b := by
  rw [Reasoning.Theory.uInt256OfByteArray_eq]
  exact Reasoning.Theory.toByteArray_ofNat_fromByteArrayBigEndian_of_size h

theorem word_as (v : UInt256) : (word v).as (.int 256) = word v :=
  as_word rfl (toNat_lt_W256 v)

theorem wrap_add_mod (x c : Nat) :
    wrap 256 ((x : Int) + (c : Int)) % W256 = (x % W256 + c) % W256 := by
  have hW : (UInt256.size : Int) = 2 ^ 256 := by norm_num [UInt256.size]
  have h := wrap_int ((x : Int) + c)
  rw [hW] at h
  zify
  rw [h]
  omega

theorem wrap_sub_mod (x c : Nat) (hc : c < W256) :
    wrap 256 ((x : Int) - (c : Int)) = (x % W256 + W256 - c % W256) % W256 := by
  unfold W256 at hc ⊢
  have hW : (UInt256.size : Int) = 2 ^ 256 := by norm_num [UInt256.size]
  have h := wrap_int ((x : Int) - c)
  rw [hW] at h
  rw [Nat.mod_eq_of_lt hc]
  have h1 : x % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by positivity)
  zify [show c ≤ x % 2 ^ 256 + 2 ^ 256 by omega]
  rw [h]
  omega

/-! ## The window's memory -/

/-- `m` is `m₀` with the first `q` words of `m₀`'s bytes from `S` written at `D`. -/
def CopyMem (m₀ : ByteArray) (S D q : Nat) (m : ByteArray) : Prop :=
  ∀ x, m.data.getD x 0 =
    if D ≤ x ∧ x < D + 32 * q then m₀.data.getD (S + (x - D)) 0 else m₀.data.getD x 0

theorem copyMem_zero (m₀ : ByteArray) (S D : Nat) : CopyMem m₀ S D 0 m₀ := fun x => by
  rw [ite_eq_right (by omega)]

/-- The store of word `q`: the word loaded from `m₀` at `S + 32 q`, written at `D + 32 q`. -/
theorem copyMem_store {m₀ m : ByteArray} {S D q : Nat} (h : CopyMem m₀ S D q m) :
    CopyMem m₀ S D (q + 1) ((uInt256OfByteArray (m₀.readWithPadding (S + 32 * q) 32)).toByteArray.write
      0 m (D + 32 * q) 32) := by
  intro x
  rw [write_getD, toByteArray_uInt256 (readWithPadding_size' _ _ _), h x]
  by_cases h1 : D + 32 * q ≤ x ∧ x < D + 32 * q + 32
  · rw [ite_eq_left h1, ite_eq_left (by omega), readWithPadding_getD _ _ _ _ (by omega)]
    congr 1; omega
  · rw [ite_eq_right h1]
    by_cases h2 : D ≤ x ∧ x < D + 32 * q
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- A word of `m₀` the stores have not reached reads as in `m₀`. -/
theorem copyMem_read {m₀ m : ByteArray} {S D q : Nat} (h : CopyMem m₀ S D q m) {a : Nat}
    (ha : q = 0 ∨ a + 32 ≤ D ∨ D + 32 * q ≤ a) :
    m.readWithPadding a 32 = m₀.readWithPadding a 32 :=
  readWithPadding_congr fun i hi => by rw [h (a + i), ite_eq_right (by omega)]

/-- All `n` words stored: the memory `mcopy` leaves. -/
theorem copyMem_end {m₀ m : ByteArray} {S D n : Nat} (h : CopyMem m₀ S D n m) :
    MemEq m (m₀.write S m₀ D (32 * n)) :=
  memEq_iff_getD.mpr fun x => by rw [h x, write_getD]

/-- A copy of all of memory onto itself is the identity: the length `2 ^ 256` the instruction
    reads as `0`. -/
theorem memEq_write_mod (m : ByteArray) {S D L : Nat} (hS : S + L ≤ W256) (hD : D + L ≤ W256) :
    MemEq (m.write S m D (L % W256)) (m.write S m D L) := by
  by_cases hL : L < W256
  · rw [Nat.mod_eq_of_lt hL]; exact MemEq.refl _
  · have hS0 : S = 0 := by omega
    have hD0 : D = 0 := by omega
    subst hS0 hD0
    refine memEq_iff_getD.mpr fun x => ?_
    rw [write_getD, write_getD]
    split_ifs <;> first | rfl | (congr 1; omega)

/-! ## Address normalization -/

section norm

variable {sig : Sigs} {syms : List String} {f f' : Func}

theorem stmtOf_spec {u : Nat} {i : Inst}
    (h : stmtOf (KCtx.of f f').B (KCtx.of f f').D (KCtx.of f f').T u = some i) :
    ∃ d j blk s ty, (u, Def.stmt d j) ∈ defList f ∧ ((domTree f).reach.find? d).isSome = true ∧
      f.block? d = some blk ∧ blk.body[j]? = some s ∧ s.inst = i ∧ s.dsts = [(u, ty)] := by
  unfold stmtOf at h
  split at h
  · next d j hD =>
    split at h
    · next hr =>
      split at h
      · next blk hblk =>
        split at h
        · next s hs =>
          split at h
          · next u' ty hd =>
            split at h
            · next hu =>
              subst hu
              simp only [Option.some.injEq] at h
              refine ⟨d, j, blk, s, ty, defsOf_mem hD, hr, ?_, hs, h, hd⟩
              simpa [KCtx.of, NatMap.find?_ofListBy, Func.block?] using hblk
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- An operand of a statement of a reachable block: its definitions come before the statement. -/
theorem useAt_stmt (hwf : f.wf sig syms = true) {T : DomTree} (hs : ssa f T = true) {d j : Nat}
    {blk : Block} (hdb : f.block? d = some blk) (hdr : (T.reach.find? d).isSome = true) {s : Stmt}
    (hsj : blk.body[j]? = some s) {o : Operand} (ho : o ∈ s.inst.args) : UseAt f T d j o := by
  cases o with
  | imm => trivial
  | var w =>
    intro d₁ j₁ hdef₁
    have hU := UniqueDefs.of_ssa hs
    have hdmem := List.mem_of_find?_eq_some hdb
    have hdid : blk.id = d := by simpa using List.find?_some hdb
    rcases stmt_operand hwf hs hdb hdr hsj ho with hp | ⟨blk', hb', hph | ⟨j', hj', s', hs', hv'⟩⟩ |
      ⟨d', hne', ha', hdefd⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      cases hU.fn (param_def hq) hdef₁
    · rw [hdb] at hb'; cases hb'
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
      cases hU.fn (hdid ▸ phi_def hdmem hφ) hdef₁
    · rw [hdb] at hb'; cases hb'
      obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
      have := hU.fn (hdid ▸ stmt_def hdmem hs' hdd) hdef₁
      simp only [Def.stmt.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact Or.inr ⟨rfl, hj'⟩
    · rcases definedIn_def hdefd with h' | ⟨j'', h'⟩
      · cases hU.fn h' hdef₁
      · have := (Def.stmt.inj (hU.fn h' hdef₁)).1
        subst this
        exact Or.inl ⟨hne', ha'⟩

theorem UseAt.mono {T : DomTree} {b k k' : Nat} {o : Operand} (h : UseAt f T b k o) (hk : k ≤ k') :
    UseAt f T b k' o := by
  cases o with
  | imm => trivial
  | var w =>
    intro d j hdef
    rcases h d j hdef with h | ⟨rfl, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩

/-- An operand of a statement before the point is used at the point. -/
theorem UseAt.trans {T : DomTree} {e d j b k : Nat} (hroot : T.idom.find? e = none)
    (hbroot : T.Anc e b) {o : Operand} (h : UseAt f T d j o) (hbef : Before T d j b k) :
    UseAt f T b k o := by
  cases o with
  | imm => trivial
  | var w =>
    intro d₁ j₁ hdef
    refine before_trans hroot hbroot ?_ hbef
    rcases h d₁ j₁ hdef with ⟨hne, ha⟩ | ⟨rfl, hj⟩
    · exact Or.inr ⟨hne, ha⟩
    · exact Or.inl ⟨rfl, hj⟩

theorem pairOpt_imm {env : Env} {a : Operand} {bits c : Nat} {p : Nat × Nat × Nat}
    (h : pairOpt env a (.imm bits c) = some p) :
    ∃ x, intVal env a = some (bits, x) ∧ p = (bits, x, c) := by
  unfold pairOpt at h
  rcases hx : intVal env a with _ | ⟨ba, x⟩ <;> rw [hx] at h
  · cases h
  · simp only [intVal, opVal, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · next hb =>
      simp only [beq_iff_eq] at hb
      subst hb
      simp only [Option.some.injEq] at h
      exact ⟨x, rfl, h.symm⟩
    · cases h

theorem pairOpt_imm_left {env : Env} {a : Operand} {bits c : Nat} {p : Nat × Nat × Nat}
    (h : pairOpt env (.imm bits c) a = some p) :
    ∃ x, intVal env a = some (bits, x) ∧ p = (bits, c, x) := by
  unfold pairOpt at h
  rw [show intVal env (.imm bits c) = some (bits, c) from rfl] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  rcases hx : intVal env a with _ | ⟨ba, x⟩ <;> rw [hx] at h
  · cases h
  · simp only [Option.bind_some] at h
    split at h
    · next hb =>
      simp only [beq_iff_eq] at hb
      subst hb
      simp only [Option.some.injEq] at h
      exact ⟨x, rfl, h.symm⟩
    · cases h

/-- `addrNorm`'s offset of an address with no base is its value modulo `2 ^ 256`: L2 at the
    point unfolds each `add` and `sub` it follows. -/
theorem addrNorm_sound (hwf : f.wf sig syms = true) (hv : (domTree f).valid f = true)
    (hs : ssa f (domTree f) = true) {X : Nat} {blk : Block} (hb : f.block? X = some blk)
    (hr : ((domTree f).reach.find? X).isSome = true) {kX : Nat} {env : Env}
    (hpu : PureInv f (domTree f) X kX env) :
    ∀ n o, (addrNorm (KCtx.of f f').B (KCtx.of f f').D (KCtx.of f f').T n o).1 = none →
      UseAt f (domTree f) X kX o → ∀ v, intVal env o = some v →
        v.2 % W256 = (addrNorm (KCtx.of f f').B (KCtx.of f f').D (KCtx.of f f').T n o).2
  | n, .imm _ c, _, _, v, hv' => by
    simp only [intVal, opVal, Option.some.injEq] at hv'
    subst hv'
    cases n <;> rfl
  | 0, .var u, h, _, _, _ => by simp [addrNorm] at h
  | n + 1, .var u, h, huse, v, hv' => by
    have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = X := by simpa using List.find?_some hb
    obtain ⟨e, he⟩ : ∃ e, f.blocks.head? = some e := by
      cases h : f.blocks.head? with
      | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
      | some e => exact ⟨e, rfl⟩
    have hroot := (DomTree.valid_entry hv he).2
    have hbroot := hid ▸ DomTree.valid_root hv he hmem (hid ▸ hr)
    -- the definition of `u` and the value L2 gives it
    have unfold_def : ∀ i, stmtOf (KCtx.of f f').B (KCtx.of f f').D (KCtx.of f f').T u = some i →
        i.pure = true → ∃ vals ty dblk d j s, pureVals env i = some vals ∧ [(u, ty)].length = vals.length ∧
          env[u]? = some ((vals.headD (.int 0 0)).as ty) ∧ ty = .int 256 ∧
          f.block? d = some dblk ∧ dblk.body[j]? = some s ∧ s.inst = i ∧
          ((domTree f).reach.find? d).isSome = true ∧ Before (domTree f) d j X kX := by
      intro i hi hpure
      obtain ⟨d, j, dblk, s, ty, hdef, hdr, hdb, hsj, hinst, hdsts⟩ := stmtOf_spec hi
      have hbef : Before (domTree f) d j X kX := huse d j hdef
      obtain ⟨vals, hpv, hl, hbound⟩ := hpu d j dblk s hdb hsj (by rw [hinst]; exact hpure) hdr hbef
      have hdmem := List.mem_of_find?_eq_some hdb
      have hty : ty = .int 256 := ((Func.wf_words hwf).2 dblk hdmem).2 s (List.mem_of_getElem? hsj)
        (u, ty) (by rw [hdsts]; exact List.mem_singleton_self _)
      rw [hdsts] at hl hbound
      rw [hinst] at hpv
      obtain ⟨v₀, rfl⟩ : ∃ v₀, vals = [v₀] := by
        match vals, hl with
        | [v₀], _ => exact ⟨v₀, rfl⟩
      exact ⟨[v₀], ty, dblk, d, j, s, hpv, hl, hbound ((u, ty), v₀) (List.mem_singleton_self _), hty,
        hdb, hsj, hinst, hdr, hbef⟩
    -- an operand of `u`'s definition is used at the point
    have harg : ∀ d j dblk s, f.block? d = some dblk → dblk.body[j]? = some s →
        ((domTree f).reach.find? d).isSome = true → Before (domTree f) d j X kX →
        ∀ o ∈ s.inst.args, UseAt f (domTree f) X kX o := fun d j dblk s hdb hsj hdr hbef o ho =>
      UseAt.trans hroot hbroot (useAt_stmt hwf hs hdb hdr hsj ho) hbef
    -- the immediate operand is a word
    have himm : ∀ (d j : Nat) (dblk : Block) (s : Stmt), f.block? d = some dblk → dblk.body[j]? = some s →
        ∀ bits c, Operand.imm bits c ∈ s.inst.args → bits = 256 ∧ c < W256 := by
      intro d j dblk s hdb hsj bits c hc
      have := (Func.wf_operands hwf (List.mem_of_find?_eq_some hdb)).2.1 s (List.mem_of_getElem? hsj) _ hc
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      exact this
    simp only [addrNorm] at h ⊢
    split at h
    · next _ a bits c hst =>
      dsimp only at h ⊢
      obtain ⟨vals, ty, dblk, d, j, s, hpv, _, hu, rfl, hdb, hsj, hinst, hdr, hbef⟩ :=
        unfold_def _ hst rfl
      obtain ⟨rfl, hc⟩ := himm d j dblk s hdb hsj bits c (by rw [hinst]; simp [Inst.args])
      simp only [pureVals, Option.map_eq_some_iff] at hpv
      obtain ⟨p, hp, rfl⟩ := hpv
      obtain ⟨xa, hxa, rfl⟩ := pairOpt_imm hp
      have ih := addrNorm_sound hwf hv hs hb hr hpu n a h
        (harg d j dblk s hdb hsj hdr hbef a (by rw [hinst]; simp [Inst.args])) _ hxa
      simp only [intVal, opVal, hu, List.headD, BinOp.eval, Val.as, Ty.bits,
        Option.some.injEq] at hv'
      subst hv'
      simp only [Nat.mod_mod]
      rw [wrap_add_mod, ih]
    · next _ bits c a _ hst =>
      dsimp only at h ⊢
      obtain ⟨vals, ty, dblk, d, j, s, hpv, _, hu, rfl, hdb, hsj, hinst, hdr, hbef⟩ :=
        unfold_def _ hst rfl
      obtain ⟨rfl, hc⟩ := himm d j dblk s hdb hsj bits c (by rw [hinst]; simp [Inst.args])
      simp only [pureVals, Option.map_eq_some_iff] at hpv
      obtain ⟨p, hp, rfl⟩ := hpv
      obtain ⟨xa, hxa, rfl⟩ := pairOpt_imm_left hp
      have ih := addrNorm_sound hwf hv hs hb hr hpu n a h
        (harg d j dblk s hdb hsj hdr hbef a (by rw [hinst]; simp [Inst.args])) _ hxa
      simp only [intVal, opVal, hu, List.headD, BinOp.eval, Val.as, Ty.bits,
        Option.some.injEq] at hv'
      subst hv'
      simp only [Nat.mod_mod]
      rw [Int.add_comm, wrap_add_mod, ih]
    · next _ a bits c hst =>
      dsimp only at h ⊢
      obtain ⟨vals, ty, dblk, d, j, s, hpv, _, hu, rfl, hdb, hsj, hinst, hdr, hbef⟩ :=
        unfold_def _ hst rfl
      obtain ⟨rfl, hc⟩ := himm d j dblk s hdb hsj bits c (by rw [hinst]; simp [Inst.args])
      simp only [pureVals, Option.map_eq_some_iff] at hpv
      obtain ⟨p, hp, rfl⟩ := hpv
      obtain ⟨xa, hxa, rfl⟩ := pairOpt_imm hp
      have ih := addrNorm_sound hwf hv hs hb hr hpu n a h
        (harg d j dblk s hdb hsj hdr hbef a (by rw [hinst]; simp [Inst.args])) _ hxa
      simp only [intVal, opVal, hu, List.headD, BinOp.eval, Val.as, Ty.bits,
        Option.some.injEq] at hv'
      subst hv'
      rw [wrap_sub_mod _ _ hc, Nat.mod_mod, ih]
      exact Nat.mod_mod _ _
    · simp at h

end norm

/-! ## The window's statements -/

theorem asLoad_spec {s : Stmt} {a : Operand} {r : Nat} (h : asLoad s = some (a, r)) :
    s.inst = .evm .mload [a] ∧ ∃ ty, s.dsts = [(r, ty)] := by
  unfold asLoad at h
  split at h
  · rename_i a' r' ty hi hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, ty, hd⟩
  · cases h

theorem asStore_spec {s : Stmt} {a v : Operand} (h : asStore s = some (a, v)) :
    s.inst = .evm .mstore [a, v] ∧ s.dsts = [] := by
  unfold asStore at h
  split at h
  · rename_i a' v' hi hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, hd⟩
  · cases h

theorem isArith_spec {s : Stmt} (h : isArith s = true) :
    ∃ op a b x ty, s.inst = .bin op a b ∧ s.dsts = [(x, ty)] := by
  unfold isArith at h
  split at h
  · rename_i a b x hi hd
    exact ⟨_, a, b, x.1, x.2, hi, hd⟩
  · rename_i a b x hi hd
    exact ⟨_, a, b, x.1, x.2, hi, hd⟩
  · cases h

theorem asLoad_none_of_store {s : Stmt} {a v : Operand} (h : asStore s = some (a, v)) :
    asLoad s = none := by
  unfold asLoad; rw [(asStore_spec h).1]

theorem asStore_none_of_load {s : Stmt} {a : Operand} {r : Nat} (h : asLoad s = some (a, r)) :
    asStore s = none := by
  unfold asStore; rw [(asLoad_spec h).1]

theorem asLoad_none_of_arith {s : Stmt} (h : isArith s = true) : asLoad s = none := by
  obtain ⟨_, _, _, _, _, hi, _⟩ := isArith_spec h
  unfold asLoad; rw [hi]

theorem asStore_none_of_arith {s : Stmt} (h : isArith s = true) : asStore s = none := by
  obtain ⟨_, _, _, _, _, hi, _⟩ := isArith_spec h
  unfold asStore; rw [hi]

/-- Snapshot: a load has no store before it. -/
theorem loadsFirst_pre : ∀ {pre : List Stmt} {st : Stmt} {ws : List Stmt},
    loadsFirst (pre ++ st :: ws) = true → (asLoad st).isSome = true → pre.filterMap asStore = []
  | [], _, _, _, _ => rfl
  | x :: pre, st, ws, h, hl => by
    simp only [List.cons_append, loadsFirst] at h
    split at h
    · next hx =>
      have := List.all_eq_true.mp h st (List.mem_append_right _ (List.mem_cons_self ..))
      simp only [Option.isNone_iff_eq_none] at this
      rw [this] at hl; cases hl
    · next hx =>
      simp only [Option.isSome_iff_ne_none, ne_eq, not_not] at hx
      rw [List.filterMap_cons, hx]
      exact loadsFirst_pre h hl

/-! ## Runs of the window's instructions -/

theorem run_mload (p : UInt256) : EvmOp.run .mload [p] = (do return [word (← Fe.EVM.mload p)]) := rfl

theorem run_mstore (p v : UInt256) :
    EvmOp.run .mstore [p, v] = (do Fe.EVM.mstore p v; return []) := rfl

theorem run_mcopy (d s l : UInt256) :
    EvmOp.run .mcopy [d, s, l] = (do Fe.EVM.mcopy d s l; return []) := rfl

theorem evalWord_of {env : Env} {o : Operand} {bits x : Nat} (h : intVal env o = some (bits, x)) :
    evalWord env o = pure (UInt256.ofNat x) := by
  unfold evalWord; rw [evalInt_eq, h]; rfl

theorem evalWord_none {env : Env} {o : Operand} (h : intVal env o = none) :
    evalWord env o = Fe.Sonatina.stuck := by
  unfold evalWord; rw [evalInt_eq, h]; rfl

theorem runStmtO_inst {o : Oracle} {c : Ctx} {env : Env} {s : Stmt}
    (h : ∀ g args, s.inst ≠ .call g args) : runStmtO o c env s = runInst c env s.inst := by
  unfold runStmtO
  split
  · next g args heq => exact absurd heq (h g args)
  · rfl

theorem runStmtO_pure {o : Oracle} {c : Ctx} {env : Env} {s : Stmt} (h : s.inst.pure = true) :
    runStmtO o c env s = lift (pureVals env s.inst) := by
  rw [runStmtO_inst fun g args heq => by rw [heq] at h; simp [Inst.pure] at h, runInst_pure c env _ h]

theorem bind_ok {env : Env} {dsts : List (Nat × Ty)} {vals : List Val} (h : dsts.length = vals.length) :
    Fe.Sonatina.bind env dsts vals = pure ((dsts.zip vals).foldl bindStep env) := by
  unfold Fe.Sonatina.bind
  rw [ite_eq_left (by simpa using h), foldl_bindStep (fun _ x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl)]

theorem exec_load (c : Ctx) {env : Env} {a : Operand} {bits x : Nat} (h : intVal env a = some (bits, x))
    {β : Type} (g : List Val → FeM β) (I : ExecutionEnv) (w : World) :
    (runInst c env (.evm .mload [a]) >>= g).exec I w =
      (g [word (uInt256OfByteArray (w.memory.readWithPadding (x % W256) 32))]).exec I w := by
  simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_of h, pure_bind, run_mload,
    Fe.EVM.mload, bind_assoc, Fe.M.exec_bind, Fe.M.exec_get, toNat_ofNat_mod]

theorem exec_store (c : Ctx) {env : Env} {a v : Operand} {ba xa bv xv : Nat}
    (ha : intVal env a = some (ba, xa)) (hv : intVal env v = some (bv, xv))
    {β : Type} (g : List Val → FeM β) (I : ExecutionEnv) (w : World) :
    (runInst c env (.evm .mstore [a, v]) >>= g).exec I w =
      (g []).exec I { w with memory := (UInt256.ofNat xv).toByteArray.write 0 w.memory (xa % W256) 32 } := by
  simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_of ha, evalWord_of hv, pure_bind,
    run_mstore, Fe.EVM.mstore, bind_assoc, Fe.M.exec_bind, Fe.M.exec_modify, toNat_ofNat_mod]

theorem exec_mcopy (c : Ctx) {env : Env} {d s : Operand} {L bd xd bs xs : Nat}
    (hd : intVal env d = some (bd, xd)) (hs : intVal env s = some (bs, xs))
    {β : Type} (g : List Val → FeM β) (I : ExecutionEnv) (w : World) :
    (runInst c env (.evm .mcopy [d, s, .imm 256 L]) >>= g).exec I w =
      (g []).exec I { w with memory := w.memory.write (xs % W256) w.memory (xd % W256) (L % W256) } := by
  simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_of hd, evalWord_of hs,
    evalWord_of (show intVal env (.imm 256 L) = some (256, L) from rfl), pure_bind,
    run_mcopy, Fe.EVM.mcopy, bind_assoc, Fe.M.exec_bind, Fe.M.exec_modify, toNat_ofNat_mod]

theorem exec_mcopy_stuck (c : Ctx) {env : Env} {d s : Operand} {L : Nat}
    (h : intVal env d = none ∨ intVal env s = none)
    {β : Type} (g : List Val → FeM β) (I : ExecutionEnv) (w : World) :
    (runInst c env (.evm .mcopy [d, s, .imm 256 L]) >>= g).exec I w = none := by
  rcases h with h | h
  · simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_none h, Fe.Sonatina.stuck,
      bind_assoc, Fe.M.exec_bind, Fe.M.exec_diverge]
  · rcases hd : intVal env d with _ | ⟨bd, xd⟩
    · simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_none hd, Fe.Sonatina.stuck,
        bind_assoc, Fe.M.exec_bind, Fe.M.exec_diverge]
    · simp only [runInst, List.mapM_cons, List.mapM_nil, evalWord_of hd, evalWord_none h,
        pure_bind, Fe.Sonatina.stuck, bind_assoc, Fe.M.exec_bind, Fe.M.exec_diverge]

theorem pureVals_sub {env' env : Env} (h : EnvSub env' env) {op : BinOp} {a b : Operand}
    {vals : List Val} (hv : pureVals env' (.bin op a b) = some vals) :
    pureVals env (.bin op a b) = some vals := by
  simp only [pureVals, Option.map_eq_some_iff] at hv ⊢
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨p, ?_, rfl⟩
  unfold pairOpt at hp ⊢
  rcases ha : intVal env' a with _ | ⟨ba, xa⟩ <;> rw [ha] at hp
  · cases hp
  rcases hb : intVal env' b with _ | ⟨bb, xb⟩ <;> rw [hb] at hp
  · simp at hp
  rw [h.intVal ha, h.intVal hb]
  exact hp

/-! ## What the check gives -/

/-- What a `coalesce_copies` check accepting `f` to `f'` gives. -/
structure KFacts (f f' : Func) : Prop where
  params : f'.params = f.params
  machine' : f'.machine = true
  valid : (domTree f).valid f = true
  ssa : ssa f (domTree f) = true
  len : f'.blocks.length = f.blocks.length
  blocks : ∀ p ∈ f'.blocks.zip f.blocks, (KCtx.of f f').blockOk p.1 p.2 = true

theorem checkCoalesce_facts {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    (h : checkCoalesce f ids s = true) : KFacts f s.func := by
  unfold checkCoalesce at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hp⟩, _⟩, hm⟩, hv⟩, hs⟩, hl⟩, hb⟩, _⟩ := h
  exact ⟨hp, hm, hv, hs, hl, hb⟩

theorem KCtx.blockOk_spec {X : KCtx} {b' b : Block} (h : X.blockOk b' b = true) :
    b'.id = b.id ∧ b'.phis = b.phis ∧ b'.term = b.term ∧
      X.cbodyOk (b.body.length + 1) b'.body b.body = true := by
  unfold KCtx.blockOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem kc_block {f f' : Func} (F : KFacts f f') {id : Nat} {b' : Block}
    (h : f'.block? id = some b') : ∃ b, f.block? id = some b ∧
      b'.id = b.id ∧ b'.phis = b.phis ∧ b'.term = b.term ∧
        (KCtx.of f f').cbodyOk (b.body.length + 1) b'.body b.body = true :=
  find_zip (P := fun b' b => b'.id = b.id ∧ b'.phis = b.phis ∧ b'.term = b.term ∧
      (KCtx.of f f').cbodyOk (b.body.length + 1) b'.body b.body = true)
    F.len (fun p hp => let h := KCtx.blockOk_spec (F.blocks p hp); ⟨h.1, h⟩) h

theorem kc_head {f f' : Func} (F : KFacts f f') {e' : Block} (he' : f'.blocks.head? = some e') :
    ∃ e, f.blocks.head? = some e ∧ e'.id = e.id := by
  cases hf : f'.blocks with
  | nil => rw [hf] at he'; cases he'
  | cons x' l' =>
    rw [hf] at he'
    cases hg : f.blocks with
    | nil => have := F.len; rw [hf, hg] at this; simp at this
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at he'
      have := (KCtx.blockOk_spec (F.blocks (x', x) (by rw [hf, hg]; exact List.mem_cons_self ..))).1
      exact ⟨x, rfl, he' ▸ this⟩

/-- What `runOk` gives with base-relative runs off (stage 1): the window holds loads, stores and
    arithmetic; load `i` reads at `S + 32 i` and store `i` writes load `i`'s result at `D + 32 i`,
    for `n` of each; both ranges end at or below `2 ^ 256`; all loads come first or the ranges are
    disjoint; the copy reads the first load's and the first store's address operands. -/
structure WinFacts (X : KCtx) (win : List Stmt) (mc : Stmt) (S D : Nat) : Prop where
  shape : ∀ st ∈ win, (asLoad st).isSome = true ∨ (asStore st).isSome = true ∨ isArith st = true
  nst : (win.filterMap asStore).length = (win.filterMap asLoad).length
  loads : ∀ i ld, (win.filterMap asLoad)[i]? = some ld → X.norm ld.1 = (none, S + 32 * i)
  stores : ∀ i st, (win.filterMap asStore)[i]? = some st →
    X.norm st.1 = (none, D + 32 * i) ∧ ∃ ld, (win.filterMap asLoad)[i]? = some ld ∧ st.2 = .var ld.2
  boundS : S + 32 * (win.filterMap asLoad).length ≤ W256
  boundD : D + 32 * (win.filterMap asLoad).length ≤ W256
  snap : loadsFirst win = true ∨ S + 32 * (win.filterMap asLoad).length ≤ D ∨
    D + 32 * (win.filterMap asLoad).length ≤ S
  copy : ∃ sa da, (∃ st ∈ win, (asLoad st).map (·.1) = some sa) ∧
    (∃ st ∈ win, (asStore st).map (·.1) = some da) ∧ X.norm sa = (none, S) ∧ X.norm da = (none, D) ∧
    mc = ⟨[], .evm .mcopy [da, sa, .imm 256 (32 * (win.filterMap asLoad).length)]⟩

theorem atOff_spec {X : KCtx} {base : Option Nat × Nat} {i : Nat} {o : Operand}
    (h : X.atOff base i o = true) (hb : base.1 = none) (hlt : base.2 + 32 * i < W256) :
    X.norm o = (none, base.2 + 32 * i) := by
  unfold KCtx.atOff at h
  rcases hn : X.norm o with ⟨bo, off⟩
  rw [hn] at h
  simp only [Bool.and_eq_true, beq_iff_eq, hb] at h
  rw [h.1, h.2, Nat.mod_eq_of_lt hlt]

theorem runOk_spec {X : KCtx} {win : List Stmt} {mc : Stmt} (h : X.runOk win mc = true) :
    ∃ S D, WinFacts X win mc S D := by
  unfold KCtx.runOk at h
  dsimp only at h
  split at h
  · rename_i s r0 d v0 last hl hs _
    simp only [allowBase, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
      decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none, ge_iff_le] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, _⟩, hn2⟩, hnst⟩, hmc⟩, hlds⟩, hsts⟩, ⟨⟨hsb, hdb⟩, hbS⟩, hbD⟩, hsnap⟩ := h
    have hmemL : (s, r0) ∈ win.filterMap asLoad := List.mem_of_mem_head? hl
    have hmemS : (d, v0) ∈ win.filterMap asStore := List.mem_of_mem_head? hs
    obtain ⟨stl, hstl, hl'⟩ := List.mem_filterMap.mp hmemL
    obtain ⟨sts, hsts', hs'⟩ := List.mem_filterMap.mp hmemS
    refine ⟨(X.norm s).2, (X.norm d).2, fun st hst => ?_, hnst, fun i ld hi => ?_, fun i st hi => ?_,
      hbS, hbD, hsnap.imp_right fun h => h.2,
      ⟨s, d, ⟨stl, hstl, by rw [hl']; rfl⟩, ⟨sts, hsts', by rw [hs']; rfl⟩, Prod.ext hsb rfl,
        Prod.ext hdb rfl, hmc⟩⟩
    · rcases hshape st hst with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have hlt := (List.getElem?_eq_some_iff.mp hi).1
      exact atOff_spec (hlds (ld, i) (List.mem_zipIdx_iff_getElem?.mpr hi)).1 hsb (by omega)
    · have hlt := (List.getElem?_eq_some_iff.mp hi).1
      have hlt' : i < (win.filterMap asLoad).length := by omega
      refine ⟨?_, (win.filterMap asLoad)[i], List.getElem?_eq_getElem hlt', ?_⟩
      · have hz : ((win.filterMap asStore).zip (win.filterMap asLoad))[i]? =
            some (st, (win.filterMap asLoad)[i]) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨hi, List.getElem?_eq_getElem hlt'⟩
        exact atOff_spec (hsts ((st, _), i) (List.mem_zipIdx_iff_getElem?.mpr hz)).1 hdb (by omega)
      · have hz : ((win.filterMap asStore).zip (win.filterMap asLoad))[i]? =
            some (st, (win.filterMap asLoad)[i]) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨hi, List.getElem?_eq_getElem hlt'⟩
        exact (hsts ((st, _), i) (List.mem_zipIdx_iff_getElem?.mpr hz)).2
  · cases h

/-! ## The window -/

/-- The walk's invariant after the window's statements `pre`: the memory holds the stores of
    `pre` (`CopyMem`), and each load of `pre` is bound to the word of `m₀` at its address. -/
def WInv (X : KCtx) (m₀ : ByteArray) (S D : Nat) (pre : List Stmt) (e : Env) (m : ByteArray) :
    Prop :=
  CopyMem m₀ S D (pre.filterMap asStore).length m ∧ ∀ ld ∈ pre.filterMap asLoad,
    e[ld.2]? = some (word (uInt256OfByteArray (m₀.readWithPadding (X.norm ld.1).2 32)))

section window

variable {sig : Sigs} {syms : List String} {f f' : Func}

theorem win_get {blk : Block} {k : Nat} {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest)
    {p : Nat} {st : Stmt} (h : win[p]? = some st) : blk.body[k + p]? = some st := by
  have hp := (List.getElem?_eq_some_iff.mp h).1
  rw [← List.getElem?_drop, hd, List.getElem?_append_left hp, h]

theorem pre_get {pre ws win : List Stmt} (hw : win = pre ++ ws) {st : Stmt} (h : st ∈ pre) :
    ∃ p, p < pre.length ∧ win[p]? = some st := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
  exact ⟨p, hp, by rw [hw, List.getElem?_append_left hp, List.getElem?_eq_getElem hp]⟩

theorem win_here {pre ws win : List Stmt} {st : Stmt} (hw : win = pre ++ st :: ws) :
    win[pre.length]? = some st := by
  rw [hw, List.getElem?_append_right (Nat.le_refl _)]; simp

theorem stmt_def' {b : Nat} {blk : Block} (hb : f.block? b = some blk) {j : Nat} {s : Stmt}
    (hs : blk.body[j]? = some s) {x : Nat × Ty} (hx : x ∈ s.dsts) : (x.1, Def.stmt b j) ∈ defList f := by
  have hid : blk.id = b := by simpa using List.find?_some hb
  exact hid ▸ stmt_def (List.mem_of_find?_eq_some hb) hs hx

/-- A statement's results are not the results of the window's loads before it. -/
theorem keep_loads (hU : UniqueDefs f) {b : Nat} {blk : Block} (hb : f.block? b = some blk) {k : Nat}
    {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest) {pre ws : List Stmt} {st : Stmt}
    (hw : win = pre ++ st :: ws) {ld : Operand × Nat} (hld : ld ∈ pre.filterMap asLoad)
    (vals : List Val) (e : Env) : ((st.dsts.zip vals).foldl bindStep e)[ld.2]? = e[ld.2]? := by
  refine fold_get_not _ _ _ fun hm => ?_
  obtain ⟨y, hy, hy1⟩ := List.mem_map.mp hm
  have hyd := (List.of_mem_zip hy).1
  obtain ⟨stl, hstl, hl⟩ := List.mem_filterMap.mp hld
  obtain ⟨p, hp, hwp⟩ := pre_get hw hstl
  rcases ld with ⟨la, lr⟩
  obtain ⟨_, ty, hdl⟩ := asLoad_spec hl
  have h1 : (lr, Def.stmt b (k + p)) ∈ defList f :=
    stmt_def' hb (win_get hd hwp) (x := (lr, ty)) (by rw [hdl]; exact List.mem_singleton_self _)
  have h2 : (y.1.1, Def.stmt b (k + pre.length)) ∈ defList f := stmt_def' hb (win_get hd (win_here hw)) hyd
  simp only at hy1
  rw [hy1] at h2
  have := Def.stmt.inj (hU.fn h1 h2)
  omega

/-- A store's value is the result of a load before it. -/
theorem store_load_before (hwf : f.wf sig syms = true) (F : KFacts f f') {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true) {k : Nat}
    {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest) {pre ws : List Stmt} {st : Stmt}
    (hw : win = pre ++ st :: ws) {a : Operand} {r : Nat} (hst : asStore st = some (a, .var r))
    {ld : Operand × Nat} (hld : ld ∈ win.filterMap asLoad) (hr2 : ld.2 = r) :
    ld ∈ pre.filterMap asLoad := by
  have hU := UniqueDefs.of_ssa F.ssa
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hsk := win_get hd (win_here hw)
  have hop : Operand.var r ∈ st.inst.args := by
    rw [(asStore_spec hst).1]; simp [Inst.args]
  have hdom := stmt_operand hwf F.ssa hb hr hsk hop
  obtain ⟨stl, hstl, hl⟩ := List.mem_filterMap.mp hld
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hstl
  have hpos := win_get hd hp
  rcases ld with ⟨la, lr⟩
  simp only at hr2
  subst hr2
  obtain ⟨_, ty, hdl⟩ := asLoad_spec hl
  have hdefl : (lr, Def.stmt b (k + p)) ∈ defList f :=
    stmt_def' hb hpos (x := (lr, ty)) (by rw [hdl]; exact List.mem_singleton_self _)
  rcases hdom with hpar | ⟨blk', hb', hph | ⟨j', hj', s', hs', hv'⟩⟩ | ⟨d', hne', _, hdefd⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpar
    cases hU.fn (param_def hq) hdefl
  · rw [hb] at hb'; cases hb'
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
    cases hU.fn (hid ▸ phi_def hmem hφ) hdefl
  · rw [hb] at hb'; cases hb'
    obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
    have := Def.stmt.inj (hU.fn (stmt_def' hb hs' hdd) hdefl)
    have hplt : p < pre.length := by omega
    have : pre[p]? = some stl := by
      rw [hw, List.getElem?_append_left hplt] at hp; exact hp
    exact List.mem_filterMap.mpr ⟨stl, List.mem_of_getElem? this, hl⟩
  · rcases definedIn_def hdefd with h' | ⟨j'', h'⟩
    · cases hU.fn h' hdefl
    · exact absurd (Def.stmt.inj (hU.fn h' hdefl)).1 hne'

/-- One statement of the window on the input: its values, the memory it leaves, and the
    invariant after it. -/
theorem in_step (hwf : f.wf sig syms = true) (F : KFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true)
    {k : Nat} {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest) {mc : Stmt} {S D : Nat}
    (W : WinFacts (KCtx.of f f') win mc S D) {m₀ : ByteArray} {pre ws : List Stmt} {st : Stmt}
    (hw : win = pre ++ st :: ws) {e : Env} {m : ByteArray}
    (hpi : PointInv f (domTree f) b (k + pre.length) e)
    (hpu : PureInv f (domTree f) b (k + pre.length) e)
    (hinv : WInv (KCtx.of f f') m₀ S D pre e m) (I : ExecutionEnv) (w₀ : World)
    (K : Env → FeM (List Val)) :
    ∃ vals m₂, IntVals vals ∧ (st.inst.pure = true → pureVals e st.inst = some vals) ∧
      st.dsts.length = vals.length ∧
      (runStmtO o c e st >>= fun vals => Fe.Sonatina.bind e st.dsts vals >>= K).exec I
          { w₀ with memory := m } =
        (K ((st.dsts.zip vals).foldl bindStep e)).exec I { w₀ with memory := m₂ } ∧
      WInv (KCtx.of f f') m₀ S D (pre ++ [st]) ((st.dsts.zip vals).foldl bindStep e) m₂ := by
  have hU := UniqueDefs.of_ssa F.ssa
  have hmem := List.mem_of_find?_eq_some hb
  have hsk := win_get hd (win_here hw)
  have hk : k + pre.length ≤ blk.body.length := (List.getElem?_eq_some_iff.mp hsk).1.le
  have hdef : ∀ o' ∈ st.inst.args, ∃ n, intVal e o' = some (256, n) := fun o' ho' =>
    uses_defined hwf F.ssa hb hr hk hpi o' (by unfold usesAt; rw [hsk]; exact ho')
  have hnorm : ∀ o' ∈ st.inst.args, ∀ N, (KCtx.of f f').norm o' = (none, N) → ∀ bits x,
      intVal e o' = some (bits, x) → x % W256 = N := fun o' ho' N hN bits x hx => by
    have := addrNorm_sound hwf F.valid F.ssa hb hr hpu (KCtx.of f f').fuel o'
      (by change ((KCtx.of f f').norm o').1 = none; rw [hN]) (useAt_stmt hwf F.ssa hb hr hsk ho') _ hx
    change _ = ((KCtx.of f f').norm o').2 at this
    rw [hN] at this
    exact this
  have hstin : st ∈ win := by rw [hw]; simp
  have hnst := W.nst
  have hqn : (pre.filterMap asStore).length ≤ (win.filterMap asStore).length := by
    rw [hw, List.filterMap_append, List.length_append]; omega
  rcases W.shape st hstin with hl | hs | ha
  · -- a load: it reads the word of `m₀`
    obtain ⟨⟨a, r⟩, hl'⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨hinst, ty, hdsts⟩ := asLoad_spec hl'
    have hty : ty = .int 256 := ((Func.wf_words hwf).2 blk hmem).2 st (List.mem_of_getElem? hsk)
      (r, ty) (by rw [hdsts]; exact List.mem_singleton_self _)
    subst hty
    have ha : a ∈ st.inst.args := by rw [hinst]; simp [Inst.args]
    obtain ⟨xa, hxa⟩ := hdef a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_filterMap.mpr ⟨st, hstin, hl'⟩)
    have hilt := (List.getElem?_eq_some_iff.mp hi).1
    have hN := W.loads i (a, r) hi
    have hxa' : xa % W256 = S + 32 * i := hnorm a ha _ hN _ _ hxa
    have hread : m.readWithPadding (S + 32 * i) 32 = m₀.readWithPadding (S + 32 * i) 32 := by
      refine copyMem_read hinv.1 ?_
      rcases W.snap with h | h | h
      · left
        rw [loadsFirst_pre (hw ▸ h) (by rw [hl']; rfl)]; rfl
      · right; left; omega
      · right; right; omega
    let v := uInt256OfByteArray (m₀.readWithPadding (S + 32 * i) 32)
    refine ⟨[word v], m, by simp [IntVals, word, Val.isInt], fun hp => by
      rw [hinst] at hp; simp [Inst.pure, EvmOp.isMod] at hp, by rw [hdsts]; rfl, ?_, ?_⟩
    · rw [runStmtO_inst (by rw [hinst]; intro g args h; cases h), hinst, exec_load c hxa]
      dsimp only
      rw [hxa', hread, bind_ok (by rw [hdsts]; rfl), pure_bind]
    · refine ⟨?_, fun ld hld => ?_⟩
      · rw [List.filterMap_append, List.filterMap_cons, asStore_none_of_load hl']
        simpa using hinv.1
      · rw [List.filterMap_append, List.mem_append] at hld
        rcases hld with hld | hld
        · rw [keep_loads hU hb hd hw hld]; exact hinv.2 ld hld
        · simp only [List.filterMap_cons, hl', List.filterMap_nil, List.mem_singleton] at hld
          subst hld
          rw [hdsts, hN]
          simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, bindStep,
            env_insert_get, ite_true, word_as]
          rfl
  · -- a store: the word of load `q` at `D + 32 q`
    obtain ⟨⟨a, v⟩, hs'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hinst, hdsts⟩ := asStore_spec hs'
    have hSq : (win.filterMap asStore)[(pre.filterMap asStore).length]? = some (a, v) := by
      rw [hw, List.filterMap_append, List.filterMap_cons, hs', List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hqlt := (List.getElem?_eq_some_iff.mp hSq).1
    obtain ⟨hNa, ld, hld, hv⟩ := W.stores _ (a, v) hSq
    simp only at hv
    subst hv
    have hNl := W.loads _ ld hld
    have hldpre := store_load_before hwf F hb hr hd hw hs' (List.mem_of_getElem? hld) rfl
    have hval := hinv.2 ld hldpre
    rw [hNl] at hval
    have ha : a ∈ st.inst.args := by rw [hinst]; simp [Inst.args]
    obtain ⟨xa, hxa⟩ := hdef a ha
    have hxa' := hnorm a ha _ hNa _ _ hxa
    let val := uInt256OfByteArray (m₀.readWithPadding (S + 32 * (pre.filterMap asStore).length) 32)
    have hxv : intVal e (.var ld.2) = some (256, val.toNat) := by
      simp only [intVal, opVal, hval, word]
      rfl
    refine ⟨[], val.toByteArray.write 0 m (D + 32 * (pre.filterMap asStore).length) 32,
      by simp [IntVals], fun hp => by rw [hinst] at hp; simp [Inst.pure, EvmOp.isMod] at hp,
      by rw [hdsts]; rfl, ?_, ?_⟩
    · rw [runStmtO_inst (by rw [hinst]; intro g args h; cases h), hinst, exec_store c hxa hxv]
      dsimp only
      rw [hxa', ofNat_toNat', bind_ok (by rw [hdsts]; rfl), pure_bind]
    · refine ⟨?_, fun ld' hld' => ?_⟩
      · rw [List.filterMap_append, List.filterMap_cons, hs']
        simpa using copyMem_store hinv.1
      · rw [List.filterMap_append, List.filterMap_cons, asLoad_none_of_store hs'] at hld'
        simp only [List.filterMap_nil, List.append_nil] at hld'
        rw [hdsts]
        exact hinv.2 ld' hld'
  · -- arithmetic: pure, on the operands' words
    obtain ⟨op, a, b', x, ty, hinst, hdsts⟩ := isArith_spec ha
    obtain ⟨xa, hxa⟩ := hdef a (by rw [hinst]; simp [Inst.args])
    obtain ⟨xb, hxb⟩ := hdef b' (by rw [hinst]; simp [Inst.args])
    have hpv : pureVals e st.inst = some [.int 256 (op.eval 256 xa xb)] := by
      rw [hinst]; simp [pureVals, pairOpt, hxa, hxb]
    refine ⟨[.int 256 (op.eval 256 xa xb)], m, by simp [IntVals, Val.isInt], fun _ => hpv,
      by rw [hdsts]; rfl, ?_, ?_⟩
    · rw [runStmtO_pure (by rw [hinst]; rfl), hpv]
      simp only [lift, pure_bind]
      rw [bind_ok (by rw [hdsts]; rfl), pure_bind]
    · refine ⟨?_, fun ld hld => ?_⟩
      · rw [List.filterMap_append, List.filterMap_cons, asStore_none_of_arith ha]
        simpa using hinv.1
      · rw [List.filterMap_append, List.filterMap_cons, asLoad_none_of_arith ha] at hld
        simp only [List.filterMap_nil, List.append_nil] at hld
        rw [keep_loads hU hb hd hw hld]
        exact hinv.2 ld hld

/-- The window on both sides: the input runs the window's statements, the output its kept
    arithmetic alongside, binding what the input binds; the output's memory is untouched. -/
theorem win_walk (hwf : f.wf sig syms = true) (F : KFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) {ob : Block} (hob : ob ∈ f'.blocks) {k : Nat}
    {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest) {mc : Stmt} {S D : Nat}
    (W : WinFacts (KCtx.of f f') win mc S D) {m₀ : ByteArray} (I : ExecutionEnv) (w₀ w' : World)
    (K : Env → FeM (List Val)) :
    ∀ (ws ks pre : List Stmt) (e' e : Env) (m : ByteArray), win = pre ++ ws →
      (KCtx.of f f').keptOk ks ws = true → (∀ s ∈ ks, s ∈ ob.body) →
      BMid f f' e' e b (k + pre.length) → WInv (KCtx.of f f') m₀ S D pre e m →
      (runBodyO o c e' ks).exec I w' = none ∨
      ∃ e₁' e₂ m₂, (runBodyO o c e' ks).exec I w' = some (.ok (e₁', w')) ∧
        (runBodyO o c e ws >>= K).exec I { w₀ with memory := m } =
          (K e₂).exec I { w₀ with memory := m₂ } ∧
        BMid f f' e₁' e₂ b (k + win.length) ∧ WInv (KCtx.of f f') m₀ S D win e₂ m₂
  | [], ks, pre, e', e, m, hw, hk, _, hm, hinv => by
    cases ks with
    | cons _ _ => simp [KCtx.keptOk] at hk
    | nil =>
      right
      simp only [List.append_nil] at hw
      subst hw
      exact ⟨e', e, m, by simp [runBodyO], by simp [runBodyO], hm, hinv⟩
  | st :: ws, ks, pre, e', e, m, hw, hk, hin, hm, hinv => by
    obtain ⟨hes, hds, hpi, hpu, hr⟩ := hm
    have hw' : win = (pre ++ [st]) ++ ws := by rw [hw]; simp
    have hsk := win_get hd (win_here hw)
    have hlen : k + (pre ++ [st]).length = k + pre.length + 1 := by simp; omega
    obtain ⟨vals, m₂, hiv, hpv, hl, hexec, hinv'⟩ :=
      in_step hwf F o c hb hr hd W hw hpi hpu hinv I w₀ (fun e₁ => runBodyO o c e₁ ws >>= K)
    have hpi' := point_succ' hwf hb hsk hpi hiv hl
    have hpu' := pureInv_stmt hwf F.valid F.ssa hb hr hsk hpu hpv hl
    have hin_exec : (runBodyO o c e (st :: ws) >>= K).exec I { w₀ with memory := m } =
        (runBodyO o c ((st.dsts.zip vals).foldl bindStep e) ws >>= K).exec I { w₀ with memory := m₂ } := by
      simp only [runBodyO, bind_assoc]; exact hexec
    -- the input alone through a statement whose results the output does not define
    have alone : fresh (KCtx.of f f').OD st = true → ∀ ks', (KCtx.of f f').keptOk ks' ws = true →
        (∀ s ∈ ks', s ∈ ob.body) →
        (runBodyO o c e' ks').exec I w' = none ∨
        ∃ e₁' e₂ m₂, (runBodyO o c e' ks').exec I w' = some (.ok (e₁', w')) ∧
          (runBodyO o c e (st :: ws) >>= K).exec I { w₀ with memory := m } =
            (K e₂).exec I { w₀ with memory := m₂ } ∧
          BMid f f' e₁' e₂ b (k + win.length) ∧ WInv (KCtx.of f f') m₀ S D win e₂ m₂ := by
      intro hf ks' hk' hin'
      have hes' : EnvSub e' ((st.dsts.zip vals).foldl bindStep e) := fun x v hx => by
        rw [fold_get_not _ _ _ ?_]
        · exact hes x v hx
        intro hxm
        obtain ⟨y, hy, hy1⟩ := List.mem_map.mp hxm
        have hfy := List.all_eq_true.mp hf y.1 (List.of_mem_zip hy).1
        have hdd := hds x (by rw [hx]; rfl)
        simp only [KCtx.of, Option.isNone_iff_eq_none] at hfy
        rw [hy1] at hfy
        rw [hfy] at hdd; cases hdd
      rcases win_walk hwf F o c hb hob hd W I w₀ w' K ws ks' (pre ++ [st]) e' _ m₂ hw' hk' hin'
          ⟨hes', hds, by rw [hlen]; exact hpi', by rw [hlen]; exact hpu', hr⟩ hinv' with
        h | ⟨e₁', e₂, m₃, h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨e₁', e₂, m₃, h1, hin_exec.trans h2, h3, h4⟩
    cases ks with
    | nil =>
      simp only [KCtx.keptOk, List.all_cons, Bool.and_eq_true] at hk
      exact alone hk.1 [] (by simpa [KCtx.keptOk] using hk.2) hin
    | cons k1 ks' =>
      simp only [KCtx.keptOk] at hk
      split at hk
      · next hmatch =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
        obtain ⟨hks, harith⟩ := hmatch
        subst hks
        -- both sides run the statement
        obtain ⟨op, a, b', x, ty, hinst, hdsts⟩ := isArith_spec harith
        have hpure : k1.inst.pure = true := by rw [hinst]; rfl
        have hout : runBodyO o c e' (k1 :: ks') = (lift (pureVals e' k1.inst) >>= fun vals =>
            Fe.Sonatina.bind e' k1.dsts vals >>= fun e₁ => runBodyO o c e₁ ks') := by
          simp only [runBodyO, runStmtO_pure hpure]
        rcases hpv' : pureVals e' k1.inst with _ | vals'
        · left; rw [hout, hpv']; rfl
        · have hvv : vals' = vals := by
            have h1 := pureVals_sub hes (hinst ▸ hpv')
            have h2 := hpv hpure
            rw [hinst, h1] at h2
            cases h2; rfl
          subst hvv
          have hes' := EnvSub.fold hes (k1.dsts.zip vals')
          have hds' : DomSub f' ((k1.dsts.zip vals').foldl bindStep e') := fun k' hk' => by
            obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hk'
            rcases fold_get_cases _ _ _ _ hv' with ⟨y, hy, rfl, _⟩ | ⟨he, _⟩
            · exact out_stmt_def hob (hin k1 (List.mem_cons_self ..)) (List.of_mem_zip hy).1
            · exact hds k' (by rw [he]; rfl)
          have hout' : (runBodyO o c e' (k1 :: ks')).exec I w' =
              (runBodyO o c ((k1.dsts.zip vals').foldl bindStep e') ks').exec I w' := by
            rw [hout, hpv']; simp only [lift, pure_bind]; rw [bind_ok hl, pure_bind]
          rcases win_walk hwf F o c hb hob hd W I w₀ w' K ws ks' (pre ++ [k1]) _ _ m₂ hw' hk
              (fun s hs => hin s (List.mem_cons_of_mem _ hs))
              ⟨hes', hds', by rw [hlen]; exact hpi', by rw [hlen]; exact hpu', hr⟩ hinv' with
            h | ⟨e₁', e₂, m₃, h1, h2, h3, h4⟩
          · exact Or.inl (hout'.trans h)
          · exact Or.inr ⟨e₁', e₂, m₃, hout'.trans h1, hin_exec.trans h2, h3, h4⟩
      · simp only [Bool.and_eq_true] at hk
        exact alone hk.1 (k1 :: ks') hk.2 hin

/-- A window against its kept arithmetic and its copy: the input's memory after the window is
    the copy's. -/
theorem win_fol (hwf : f.wf sig syms = true) (F : KFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) {ob : Block} (hob : ob ∈ f'.blocks) {k : Nat}
    {win rest : List Stmt} (hd : blk.body.drop k = win ++ rest) {mc : Stmt} {S D : Nat}
    (W : WinFacts (KCtx.of f f') win mc S D) {e' e : Env} (hm : BMid f f' e' e b k)
    {kept : List Stmt} (hkept : (KCtx.of f f').keptOk kept win = true)
    (hin : ∀ s ∈ kept, s ∈ ob.body) (K : Env → FeM (List Val)) :
    Fol (fun e₂' y => ∃ e₂, y = (runBodyO o c e₂ rest >>= K) ∧ BMid f f' e₂' e₂ b (k + win.length))
      (runBodyO o c e' kept >>= fun e₁' => runBodyO o c e₁' [mc])
      (runBodyO o c e win >>= fun e₂ => runBodyO o c e₂ rest >>= K) := by
  intro I w' w hw
  obtain ⟨sa, da, ⟨sts, hsts, hsa⟩, ⟨std, hstd, hda⟩, hNs, hNd, hmc⟩ := W.copy
  rcases win_walk hwf F o c hb hob hd W (m₀ := w.memory) I w w' (fun e₂ => runBodyO o c e₂ rest >>= K)
      win kept [] e' e w.memory (by simp) hkept hin (by simpa using hm)
      ⟨copyMem_zero _ _ _, fun _ h => by simp at h⟩ with
    hst | ⟨e₁', e₂, m₂, hout, hinp, hm₂, hinv⟩
  · rw [Fe.M.exec_bind, hst]; trivial
  rw [Fe.M.exec_bind, hout]
  dsimp only
  obtain ⟨hes, hds, hpi₂, hpu₂, hr⟩ := hm₂
  -- the copy's operands: the window's first load's and first store's addresses
  have hval : ∀ st ∈ win, ∀ o' ∈ st.inst.args, ∀ N, (KCtx.of f f').norm o' = (none, N) → ∀ bits x,
      intVal e₁' o' = some (bits, x) → x % W256 = N := fun st hst o' ho' N hN bits x hx => by
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hst
    have hplt := (List.getElem?_eq_some_iff.mp hp).1
    have huse := UseAt.mono (useAt_stmt hwf F.ssa hb hr (win_get hd hp) ho')
      (show k + p ≤ k + win.length by omega)
    have := addrNorm_sound hwf F.valid F.ssa hb hr hpu₂ (KCtx.of f f').fuel o'
      (by change ((KCtx.of f f').norm o').1 = none; rw [hN]) huse _ (hes.intVal hx)
    change _ = ((KCtx.of f f').norm o').2 at this
    rw [hN] at this
    exact this
  have hsa' : sa ∈ sts.inst.args := by
    rcases hl : asLoad sts with _ | ⟨a, r⟩ <;> rw [hl] at hsa
    · cases hsa
    · simp only [Option.map_some, Option.some.injEq] at hsa
      subst hsa
      rw [(asLoad_spec hl).1]; simp [Inst.args]
  have hda' : da ∈ std.inst.args := by
    rcases hl : asStore std with _ | ⟨a, v⟩ <;> rw [hl] at hda
    · cases hda
    · simp only [Option.map_some, Option.some.injEq] at hda
      subst hda
      rw [(asStore_spec hl).1]; simp [Inst.args]
  have hrun : runBodyO o c e₁' [mc] = (runInst c e₁' (.evm .mcopy [da, sa,
      .imm 256 (32 * (win.filterMap asLoad).length)]) >>= fun vals =>
        Fe.Sonatina.bind e₁' [] vals >>= fun e => runBodyO o c e []) := by
    subst hmc
    simp only [runBodyO]
    rw [runStmtO_inst (by intro g args h; cases h)]
  rcases hxd : intVal e₁' da with _ | ⟨bd, xd⟩
  · rw [hrun, exec_mcopy_stuck c (Or.inl hxd)]; trivial
  rcases hxs : intVal e₁' sa with _ | ⟨bs, xs⟩
  · rw [hrun, exec_mcopy_stuck c (Or.inr hxs)]; trivial
  rw [hrun, exec_mcopy c hxd hxs, bind_ok rfl, pure_bind]
  simp only [runBodyO, List.zip_nil_left, List.foldl_nil, Fe.M.exec_pure]
  refine ⟨runBodyO o c e₂ rest >>= K, { w with memory := m₂ }, hinp, ⟨e₂, rfl, hes, hds, hpi₂, hpu₂, hr⟩,
    ⟨hw.accounts, hw.logs, ?_, hw.returnData, hw.feed, hw.calls⟩⟩
  dsimp only
  rw [hval std hstd da hda' D hNd _ _ hxd, hval sts hsts sa hsa' S hNs _ _ hxs]
  have hend := copyMem_end hinv.1
  rw [W.nst] at hend
  exact (MemEq.write hw.memory hw.memory S D _).trans
    ((memEq_write_mod w.memory W.boundS W.boundD).trans hend.symm)

end window

/-! ## The simulation -/

section sim

variable {sig : Sigs} {syms : List String} {f f' : Func}

/-- An output block's statements against the input block's, from point `k`. -/
theorem kc_stmts (hwf : f.wf sig syms = true) (F : KFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block} (hb : f.block? b = some blk) {ob : Block}
    (hob : ob ∈ f'.blocks) (K : Env → FeM (List Val)) :
    ∀ (n : Nat) (is os : List Stmt) (k : Nat) (e' e : Env), blk.body.drop k = is →
      k ≤ blk.body.length → (KCtx.of f f').cbodyOk n os is = true → (∀ s ∈ os, s ∈ ob.body) →
      BMid f f' e' e b k →
      Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ BMid f f' e₂' e₂ b blk.body.length)
        (runBodyO o c e' os) (runBodyO o c e is >>= K)
  | _, [], os, k, e', e, hd, hk, hok, _, hm => by
    have hkl : k = blk.body.length := by
      have := List.drop_eq_nil_iff.mp hd; omega
    subst hkl
    cases os with
    | nil => simp only [runBodyO, pure_bind]; exact Fol.pure ⟨e, rfl, hm⟩
    | cons _ _ => simp [KCtx.cbodyOk] at hok
  | 0, _ :: _, _, _, _, _, _, _, hok, _, _ => by simp [KCtx.cbodyOk] at hok
  | n + 1, i :: is, os, k, e', e, hd, hk, hok, hin, hm => by
    have hlt : k < blk.body.length := by
      rcases Nat.lt_or_ge k blk.body.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; cases hd
    unfold KCtx.cbodyOk at hok
    simp only [Bool.or_eq_true] at hok
    rcases hok with hsame | hwin
    · -- the same statement on both sides
      cases os with
      | nil => simp at hsame
      | cons s' os =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsame
      obtain ⟨hsi, hok⟩ := hsame
      subst hsi
      have hsk : blk.body[k]? = some s' := by
        rw [List.drop_eq_getElem_cons hlt] at hd
        simp only [List.cons.injEq] at hd
        rw [List.getElem?_eq_getElem hlt, hd.1]
      have hdk : blk.body.drop (k + 1) = is := by
        rw [List.drop_eq_getElem_cons hlt] at hd
        simp only [List.cons.injEq] at hd
        exact hd.2
      obtain ⟨hes, hds, hpi, hpu, hr⟩ := hm
      have hmach : s'.inst.machine = true :=
        Func.machine_block (Func.wf_machine hwf) hb s' (List.mem_of_getElem? hsk)
      have hsob : s' ∈ ob.body := hin s' (List.mem_cons_self ..)
      simp only [runBodyO, bind_assoc]
      refine Fol.bind (Fol.approx (Approx.strengthen (Approx.runStmtO_sub ho hes hpi.1.int s' hmach)
          (returns_runStmtO_pure hoi c hpi.1.int hmach))
        (Q := fun vals y => IntVals vals ∧ (s'.inst.pure = true → pureVals e s'.inst = some vals) ∧
          y = (Fe.Sonatina.bind e s'.dsts vals >>= fun e₁ => runBodyO o c e₁ is >>= K))
        fun a' a ⟨h1, h2, h3⟩ => ⟨h1 ▸ h2, h1 ▸ h3, h1 ▸ rfl⟩) ?_
      rintro vals y ⟨hiv, hpv, rfl⟩
      refine Fol.bind (Fol.approx (bind_rel e' e s'.dsts vals)
        (Q := fun e₁' y₂ => ∃ e₁, y₂ = (runBodyO o c e₁ is >>= K) ∧ BMid f f' e₁' e₁ b (k + 1))
        fun a' a ⟨hl, h1, h2⟩ => ⟨a, rfl, ?_⟩) ?_
      · subst h1 h2
        refine ⟨EnvSub.fold hes _, fun k' hk' => ?_, point_succ' hwf hb hsk hpi hiv hl,
          pureInv_stmt hwf F.valid F.ssa hb hr hsk hpu hpv hl, hr⟩
        obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hk'
        rcases fold_get_cases _ _ _ _ hv' with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
        · exact out_stmt_def hob hsob (List.of_mem_zip hx).1
        · exact hds k' (by rw [he]; rfl)
      · rintro e₁' y₂ ⟨e₁, rfl, hm₁⟩
        exact kc_stmts hwf F ho hoi c hb hob K n is os (k + 1) e₁' e₁ hdk (by omega) hok
          (fun s hs => hin s (List.mem_cons_of_mem _ hs)) hm₁
    · -- a window, its kept arithmetic and its copy
      obtain ⟨w, hwr, hwin⟩ := List.any_eq_true.mp hwin
      have hwlt : w < is.length := List.mem_range.mp hwr
      split at hwin
      · next mc hmc =>
        simp only [Bool.and_eq_true] at hwin
        obtain ⟨⟨hrun, hkept⟩, hrest⟩ := hwin
        obtain ⟨kk, hmc, hkept, hrest⟩ : ∃ kk, os[kk]? = some mc ∧
            (KCtx.of f f').keptOk (os.take kk) ((i :: is).take (w + 2)) = true ∧
            (KCtx.of f f').cbodyOk n (os.drop (kk + 1)) ((i :: is).drop (w + 2)) = true :=
          ⟨_, hmc, hkept, hrest⟩
        obtain ⟨S, D, W⟩ := runOk_spec hrun
        have hd' : blk.body.drop k = (i :: is).take (w + 2) ++ (i :: is).drop (w + 2) := by
          rw [hd, List.take_append_drop]
        have hwl : ((i :: is).take (w + 2)).length = w + 2 := by simp; omega
        have hd2 : blk.body.drop (k + ((i :: is).take (w + 2)).length) = (i :: is).drop (w + 2) := by
          rw [hwl, ← List.drop_drop, hd]
        have hk2 : k + ((i :: is).take (w + 2)).length ≤ blk.body.length := by
          have := congrArg List.length hd
          simp only [List.length_drop, List.length_cons] at this
          omega
        -- the output: its kept statements, the copy, the rest
        have hlt' := (List.getElem?_eq_some_iff.mp hmc).1
        have hdrop : os.drop kk = mc :: os.drop (kk + 1) := by
          rw [List.drop_eq_getElem_cons hlt', (List.getElem?_eq_some_iff.mp hmc).2]
        have hout : runBodyO o c e' os =
            (runBodyO o c e' (os.take kk) >>= fun e₁' => runBodyO o c e₁' [mc]) >>= fun e₂' =>
              runBodyO o c e₂' (os.drop (kk + 1)) := by
          conv_lhs => rw [← List.take_append_drop kk os, hdrop]
          rw [runBodyO_append, bind_assoc]
          congr 1
          funext e₁'
          exact runBodyO_append o c [mc] _ e₁'
        have hinp : runBodyO o c e (i :: is) >>= K =
            runBodyO o c e ((i :: is).take (w + 2)) >>= fun e₂ =>
              runBodyO o c e₂ ((i :: is).drop (w + 2)) >>= K := by
          conv_lhs => rw [← List.take_append_drop (w + 2) (i :: is)]
          rw [runBodyO_append, bind_assoc]
        rw [hout, hinp]
        refine Fol.bind (win_fol hwf F o c hb hob hd' W hm hkept
          (fun s hs => hin s (List.mem_of_mem_take hs)) K) fun e₂' y ⟨e₂, hy, hm₂⟩ => ?_
        subst hy
        exact kc_stmts hwf F ho hoi c hb hob K n _ _ _ e₂' e₂ hd2 hk2 hrest
          (fun s hs => hin s (List.mem_of_mem_drop hs)) hm₂
      · cases hwin

theorem termRel_refl (t : Term) : termRel (· == ·) t t = true := by
  cases t with
  | brTable s d cs =>
    have hd : optRel (· == ·) d d = true := by cases d <;> simp [optRel]
    simp only [termRel, decide_true, Bool.true_and, hd, beq_self_eq_true, Bool.and_true,
      List.all_eq_true]
    intro x hx
    obtain ⟨⟨a, b⟩, ha, rfl⟩ : ∃ a ∈ cs, x = (a, a) := by
      induction cs with
      | nil => simp at hx
      | cons y cs ih =>
        simp only [List.zip_cons_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨y, List.mem_cons_self .., rfl⟩
        · obtain ⟨a, ha, rfl⟩ := ih hx
          exact ⟨a, List.mem_cons_of_mem _ ha, rfl⟩
    simp
  | _ => simp [termRel]

/-- The terminator, the input's. -/
theorem kc_term (hwf : f.wf sig syms = true) (F : KFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) {e' e : Env} (hm : BMid f f' e' e b blk.body.length) :
    Fol (BQ o c f f' b) (runTerm e' blk.term) (runTerm e blk.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) := by
  obtain ⟨hes, hds, hpi, hpu, hr⟩ := hm
  have hdef : ∀ op ∈ blk.term.args, ∃ v, intVal e op = some v := fun op hop => by
    obtain ⟨n, hn⟩ := term_defined hwf F.ssa hb hr hpi op hop
    exact ⟨_, hn⟩
  have hgoto : ∀ d, d ∈ blk.term.succs → BR f f' (e', some b, d) (e, some b, d) := fun d hd =>
    ⟨rfl, hes, hds, blockInv_of_point F.valid hb hr hpi hd, fun pblk hp => by
      rw [hb] at hp; cases hp; exact hpu⟩
  have happ : Approx (NextTgt (fun a b => a = e' ∧ b = e) fun d' d => d' = d) (runTerm e' blk.term)
      (runTerm e blk.term) :=
    Approx.mono (approx_runTerm _ hes blk.term blk.term (termRel_refl _) hdef) fun n' n h => by
      cases n' <;> cases n <;> simp only [NextTgt] at h ⊢
      · exact ⟨h.1, by simpa using h.2⟩
      · exact h
  refine Fol.approx (Approx.strengthen happ (returns_runTerm hpi.1.int blk.term))
    fun n' n ⟨hn, hok⟩ => ?_
  rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
  · obtain ⟨⟨hea, heb⟩, rfl⟩ := hn
    subst ea eb
    obtain ⟨_, hd⟩ := hok
    exact ⟨(e, some b, d'), fun _ _ => rfl, hgoto d' hd⟩
  · subst hn; rfl

/-- One output block against the input's run from a related state. -/
theorem kc_block_fol (hwf : f.wf sig syms = true) (F : KFacts f f') {o : Oracle}
    (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {s' s : BState} (hR : BR f f' s' s) :
    Fol (BQ o c f f' s'.2.2) (stepBlock o c f' s'.1 s'.2.1 s'.2.2) (runFrom o c f s) := by
  obtain ⟨env', prev', b⟩ := s'
  obtain ⟨env, prev, b₀⟩ := s
  obtain ⟨hbb, hes, hds, hbi, hbp⟩ := hR
  simp only [Prod.mk.injEq] at hbb
  obtain ⟨rfl, rfl⟩ := hbb
  simp only at hes hds hbi hbp ⊢
  unfold stepBlock
  cases hob : f'.block? b with
  | none => exact Fol.stuck
  | some ob =>
  dsimp only
  have hobm := List.mem_of_find?_eq_some hob
  obtain ⟨ib, hib, _, hph, hterm, hbody⟩ := kc_block F hob
  rw [runFrom_enter o c hib]
  refine Fol.bind (Fol.approx (S := fun e₁' e₁ => BMid f f' e₁' e₁ b 0)
    (Q := fun e₁' y => ∃ e₁, y = inRun o c f b ib e₁ ∧ BMid f f' e₁' e₁ b 0) ?_
    fun a' a h => ⟨a, rfl, h⟩) ?_
  · rw [enter_eq, enter_eq]
    refine Approx.lift fun e₁' he₁' => ?_
    have he₁'' : enterOpt env' prev' ib = some e₁' := by
      unfold enterOpt at he₁' ⊢; rw [← hph]; exact he₁'
    obtain ⟨e₁, he₁, hes₁, hk⟩ := enterOpt_sub hes he₁''
    refine ⟨e₁, he₁, hes₁, fun k hk' => ?_,
      returns_lift_some (P := PointInv f (domTree f) b 0)
        (by rw [← he₁, ← enter_eq]; exact point_zero hwf F.valid hbi hib),
      returns_lift_some (P := PureInv f (domTree f) b 0)
        (by rw [← he₁, ← enter_eq]; exact pureInv_enter hwf F.valid F.ssa hbi hbp hib),
      hbi.2.2.1⟩
    rcases hk k hk' with h | h
    · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp h
      rw [← hph] at hφ
      exact defsOf_isSome (phi_def hobm hφ)
    · exact hds k h
  · rintro e₁' _ ⟨e₁, rfl, hm⟩
    unfold inRun
    have := kc_stmts hwf F ho hoi c hib hobm (fun e => runTerm e ib.term >>= fun
        | .goto e d => runFrom o c f (e, some b, d)
        | .done v => pure v) _ ib.body ob.body 0 e₁' e₁ rfl (Nat.zero_le _) hbody (fun _ h => h) hm
    refine Fol.bind this fun e₂' y ⟨e₂, hy, hm₂⟩ => ?_
    subst hy
    rw [hterm]
    exact kc_term hwf F o c hib hm₂

theorem kc_sim (hwf : f.wf sig syms = true) (F : KFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) : Sim o c f' f (BR f f') := by
  intro s' s hR I w' w hw
  have h := kc_block_fol hwf F ho hoi c hR I w' w hw
  revert h
  rcases (stepBlock o c f' s'.1 s'.2.1 s'.2.2).exec I w' with _ | (e' | ⟨n, w₁'⟩)
  · intro _; trivial
  · exact id
  · rintro ⟨y₁, w₁, hy, hq, hw₁⟩
    cases n with
    | goto env d =>
      obtain ⟨t, ht, hR'⟩ := hq
      exact ⟨t, w₁, hy.trans (ht I w₁), hR', hw₁⟩
    | done v =>
      simp only [BQ] at hq
      subst hq
      exact ⟨w₁, by rw [hy, Fe.M.exec_pure], hw₁⟩

/-- A `coalesce_copies` step is sound (stage 1): the output function, its calls run by an oracle
    that approximates itself and returns integers on integers, approximates the well-formed input
    function on integers. -/
theorem coalesce_sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx)
    {ids : Option (List (List Nat))} {s : FuncSnap} (hwf : f.wf sig syms = true)
    (h : checkCoalesce f ids s = true) : FuncRef o c (some s.func) (some f) := by
  have F := checkCoalesce_facts h
  have sim := kc_sim hwf F ho hoi c
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he' : s.func.blocks.head? with
  | none => exact Approx.stuck _
  | some e' =>
  obtain ⟨e, he, hid⟩ := kc_head F he'
  rw [he]
  dsimp only
  rw [F.params, hid]
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _)
    (Returns.and (entry_inv hwf F.valid he hargs) (returns_bind {} f.params args)))
    fun env env₀ ⟨e₁, hi, _, hfold⟩ => ?_
  cases e₁
  refine Sim.approx sim (env, none, e.id) (env, none, e.id)
    ⟨rfl, EnvSub.refl _, fun k hk => ?_, hi, trivial⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  rw [hfold] at hv
  rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
  · exact defsOf_isSome (param_def (F.params ▸ (List.of_mem_zip hx).1))
  · simp at he₀

end sim

theorem coalesceCopies_stepSound : StepSound .coalesceCopies :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    coalesce_sound ho hoi c hw (by simp only [checkFunc, Bool.and_eq_true] at h; exact h.2)

end Fe.Sonatina.Steps
