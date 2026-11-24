import Fe.Sonatina.Steps.L2
import Fe.Sonatina.Steps.Validate

/-!
# `branch_canonicalize` and `branch_conditions` are sound

The output has the input's blocks; the simulation (`BR`) relates the output and the input at
the same block entered from the same block, the output's environment binding less (`EnvSub`)
and only output values (`DomSub`), the input carrying the definedness invariant and L2
(`BlockInv`, `BlockPure`).  In a block, an output statement steps with the same input statement,
and the input steps alone through a deleted `is_zero` (total on the words the definedness
invariant gives; its result is no output value).  A peeled branch reads, in the input, the value
of `is_zero^k c'`, which L2 unfolds at the branch to `c'`'s value (`peel_sound`).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## What the check gives -/

/-- What a `branch_canonicalize` check accepting `f` to `f'` gives. -/
structure BCFacts (f f' : Func) : Prop where
  params : f'.params = f.params
  machine' : f'.machine = true
  valid : (domTree f).valid f = true
  ssa : ssa f (domTree f) = true
  len : f'.blocks.length = f.blocks.length
  blocks : ∀ p ∈ f'.blocks.zip f.blocks, (BCtx.of f f').blockOk p.1 p.2 = true

theorem checkBranchCanon_facts {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    (h : checkBranchCanon f ids s = true) : BCFacts f s.func := by
  unfold checkBranchCanon at h
  rcases ids with _ | ids
  · simp at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hp⟩, hm⟩, hv⟩, hs⟩, hl⟩, hb⟩, _⟩, _⟩ := h
  exact ⟨hp, hm, hv, hs, hl, hb⟩

theorem BCtx.blockOk_spec {X : BCtx} {b' b : Block} (h : X.blockOk b' b = true) :
    b'.id = b.id ∧ b'.phis = b.phis ∧ bodyOk X.OD b'.body b.body = true ∧
      X.termOk b'.term b.term = true := by
  unfold BCtx.blockOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Blocks paired in order with equal ids: a block of the first list by its id has its pair. -/
theorem find_zip {P : Block → Block → Prop} :
    ∀ {l' l : List Block}, l'.length = l.length → (∀ p ∈ l'.zip l, p.1.id = p.2.id ∧ P p.1 p.2) →
      ∀ {id : Nat} {b' : Block}, l'.find? (·.id == id) = some b' →
        ∃ b, l.find? (·.id == id) = some b ∧ P b' b
  | [], _, _, _, _, _, h => by cases h
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | x' :: l', x :: l, hl, h, id, b', hf => by
    have hx := h (x', x) (List.mem_cons_self ..)
    rw [List.find?_cons] at hf ⊢
    rw [← hx.1]
    split at hf
    · next he =>
      simp only [he, Option.some.injEq] at hf ⊢
      subst hf
      exact ⟨x, rfl, hx.2⟩
    · next he =>
      simp only [he]
      exact find_zip (by simpa using hl) (fun p hp => h p (List.mem_cons_of_mem _ hp)) hf

theorem bc_block {f f' : Func} (F : BCFacts f f') {id : Nat} {b' : Block}
    (h : f'.block? id = some b') : ∃ b, f.block? id = some b ∧
      b'.id = b.id ∧ b'.phis = b.phis ∧ bodyOk (BCtx.of f f').OD b'.body b.body = true ∧
        (BCtx.of f f').termOk b'.term b.term = true :=
  find_zip (P := fun b' b => b'.id = b.id ∧ b'.phis = b.phis ∧
      bodyOk (BCtx.of f f').OD b'.body b.body = true ∧ (BCtx.of f f').termOk b'.term b.term = true)
    F.len (fun p hp => let h := BCtx.blockOk_spec (F.blocks p hp); ⟨h.1, h⟩) h

theorem bc_head {f f' : Func} (F : BCFacts f f') {e' : Block} (he' : f'.blocks.head? = some e') :
    ∃ e, f.blocks.head? = some e ∧ e'.id = e.id := by
  cases hf : f'.blocks with
  | nil => rw [hf] at he'; cases he'
  | cons x' l' =>
    rw [hf] at he'
    cases hg : f.blocks with
    | nil => have := F.len; rw [hf, hg] at this; simp at this
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at he'
      have := (BCtx.blockOk_spec (F.blocks (x', x) (by rw [hf, hg]; exact List.mem_cons_self ..))).1
      exact ⟨x, rfl, he' ▸ this⟩

/-! ## Peeling -/

section peel

variable {sig : Sigs} {syms : List String} {f f' : Func}

/-- A value read at point `(b, k)`: each statement definition of it comes before the point. -/
def UseAt (f : Func) (T : DomTree) (b k : Nat) : Operand → Prop
  | .var u => ∀ d j, (u, Def.stmt d j) ∈ defList f → Before T d j b k
  | _ => True

theorem isZeroArg_spec {f f' : Func} {c c₁ : Operand}
    (h : isZeroArg (BCtx.of f f').B (BCtx.of f f').D (BCtx.of f f').T c = some c₁) :
    ∃ u d j blk s ty, c = .var u ∧ (u, Def.stmt d j) ∈ defList f ∧
      ((domTree f).reach.find? d).isSome = true ∧ f.block? d = some blk ∧ blk.body[j]? = some s ∧
      s.inst = .isZero c₁ ∧ s.dsts = [(u, ty)] := by
  unfold isZeroArg at h
  split at h
  · next u =>
    split at h
    · next d j hD =>
      split at h
      · next hr =>
        split at h
        · next blk hblk =>
          split at h
          · next s hs =>
            split at h
            · next a u' ty hi hd =>
              split at h
              · next hu =>
                subst hu
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨u', d, j, blk, s, ty, rfl, defsOf_mem hD, hr, ?_, hs, hi, hd⟩
                simpa [BCtx.of, NatMap.find?_ofListBy, Func.block?] using hblk
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Before is transitive through a statement's dominance: an operand's definition before a
    statement before the point is before the point. -/
theorem before_trans {T : DomTree} {e d j d₁ j₁ b k : Nat} (hroot : T.idom.find? e = none)
    (hbroot : T.Anc e b) (h₁ : (d₁ = d ∧ j₁ < j) ∨ (d₁ ≠ d ∧ T.Anc d₁ d))
    (h : Before T d j b k) : Before T d₁ j₁ b k := by
  rcases h₁ with ⟨rfl, hj⟩ | ⟨hne, ha⟩
  · rcases h with h | ⟨rfl, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
  · rcases h with ⟨hne', ha'⟩ | ⟨rfl, _⟩
    · refine Or.inl ⟨fun he => ?_, ha.trans ha'⟩
      subst he
      exact hne' (DomTree.anc_antisymm hroot hbroot ha' ha)
    · exact Or.inl ⟨hne, ha⟩

/-- A peeled branch goes where the input's goes: `peelOk` and L2 at the branch. -/
theorem peel_sound (hwf : f.wf sig syms = true) (F : BCFacts f f') {X : Nat} {blk : Block}
    (hb : f.block? X = some blk) (hr : ((domTree f).reach.find? X).isSome = true) {kX : Nat}
    {env : Env} (hpu : PureInv f (domTree f) X kX env) {c' : Operand} {a' b' : Nat} :
    ∀ n c a b, peelOk (BCtx.of f f').B (BCtx.of f f').D (BCtx.of f f').T c' a' b' n c a b = true →
      UseAt f (domTree f) X kX c → ∀ v, intVal env c = some v →
        ∃ v', intVal env c' = some v' ∧
          (if v.2 != 0 then a else b) = (if v'.2 != 0 then a' else b')
  | 0, _, _, _, h, _, _, _ => by simp [peelOk] at h
  | n + 1, c, a, b, h, huse, v, hv => by
    have hU := UniqueDefs.of_ssa F.ssa
    have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = X := by simpa using List.find?_some hb
    obtain ⟨e, he⟩ : ∃ e, f.blocks.head? = some e := by
      cases h : f.blocks.head? with
      | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
      | some e => exact ⟨e, rfl⟩
    have hroot := (DomTree.valid_entry F.valid he).2
    have hbroot := hid ▸ DomTree.valid_root F.valid he hmem (hid ▸ hr)
    unfold peelOk at h
    split at h
    swap
    · cases h
    next c₁ hz =>
    obtain ⟨u, d, j, dblk, s, ty, rfl, hdef, hdr, hdb, hsj, hinst, hdsts⟩ := isZeroArg_spec hz
    have hdmem := List.mem_of_find?_eq_some hdb
    have hbef : Before (domTree f) d j X kX := huse d j hdef
    obtain ⟨vals, hpv, hl, hbound⟩ :=
      hpu d j dblk s hdb hsj (by rw [hinst]; rfl) hdr hbef
    rw [hinst] at hpv
    simp only [pureVals, Option.map_eq_some_iff] at hpv
    obtain ⟨⟨bits, x⟩, hx, rfl⟩ := hpv
    have hu := hbound ((u, ty), bool (x == 0)) (by rw [hdsts]; exact List.mem_singleton_self _)
    have hty : ty = .int 256 := ((Func.wf_words hwf).2 dblk hdmem).2 s (List.mem_of_getElem? hsj)
      (u, ty) (by rw [hdsts]; exact List.mem_singleton_self _)
    subst hty
    -- the input's condition is `is_zero c₁`
    have hvx : v = (256, if x = 0 then 1 else 0) := by
      have : intVal env (.var u) = some (256, (if x = 0 then 1 else 0) % 2 ^ 256) := by
        simp only [intVal, opVal]
        rw [hu]
        by_cases h0 : x = 0 <;> simp [bool, Val.as, Ty.bits, h0]
      rw [hv] at this
      cases x <;> simpa using this
    subst hvx
    have htgt : (if (if x = 0 then 1 else 0) != 0 then a else b) = (if x != 0 then b else a) := by
      by_cases h0 : x = 0 <;> simp [h0]
    rw [htgt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | h
    · exact ⟨(bits, x), hx, rfl⟩
    · -- the next `is_zero`: its definition is before the branch
      have huse₁ : UseAt f (domTree f) X kX c₁ := by
        cases c₁ with
        | var w =>
          intro d₁ j₁ hdef₁
          refine before_trans hroot hbroot ?_ hbef
          have hop : Operand.var w ∈ s.inst.args := by rw [hinst]; exact List.mem_singleton_self _
          rcases stmt_operand hwf F.ssa hdb hdr hsj hop with hp | ⟨blk', hb', hph | ⟨j', hj', s', hs', hv'⟩⟩ |
            ⟨d', hne', ha', hdefd⟩
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            cases hU.fn (param_def hq) hdef₁
          · rw [hdb] at hb'; cases hb'
            obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
            have hdid : dblk.id = d := by simpa using List.find?_some hdb
            cases hU.fn (hdid ▸ phi_def hdmem hφ) hdef₁
          · rw [hdb] at hb'; cases hb'
            obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
            have hdid : dblk.id = d := by simpa using List.find?_some hdb
            have := hU.fn (hdid ▸ stmt_def hdmem hs' hdd) hdef₁
            simp only [Def.stmt.injEq] at this
            obtain ⟨rfl, rfl⟩ := this
            exact Or.inl ⟨rfl, hj'⟩
          · rcases definedIn_def hdefd with h' | ⟨j'', h'⟩
            · cases hU.fn h' hdef₁
            · have := (Def.stmt.inj (hU.fn h' hdef₁)).1
              subst this
              exact Or.inr ⟨hne', ha'⟩
        | imm => trivial
        | undef => trivial
      obtain ⟨v', hv', htg⟩ := peel_sound hwf F hb hr hpu n c₁ b a h huse₁ (bits, x) hx
      exact ⟨v', hv', htg⟩

end peel

/-! ## The simulation -/

section sim

variable {sig : Sigs} {syms : List String} {f f' : Func}

/-- The relation before statement `k` of block `b`. -/
def BMid (f f' : Func) (e' e : Env) (b k : Nat) : Prop :=
  EnvSub e' e ∧ DomSub f' e' ∧ PointInv f (domTree f) b k e ∧ PureInv f (domTree f) b k e ∧
    ((domTree f).reach.find? b).isSome = true

/-- The simulation: the same block entered from the same block. -/
def BR (f f' : Func) (s' s : BState) : Prop :=
  s'.2 = s.2 ∧ EnvSub s'.1 s.1 ∧ DomSub f' s'.1 ∧ BlockInv f (domTree f) s ∧
    BlockPure f (domTree f) s

/-- Where the input's run stands once an output block ends. -/
def BQ (o : Oracle) (c : Ctx) (f f' : Func) (b : Nat) : Next → FeM (List Val) → Prop
  | .goto e d, y => ∃ t, (∀ I w, y.exec I w = (runFrom o c f t).exec I w) ∧ BR f f' (e, some b, d) t
  | .done v, y => y = pure v

theorem mapM_option_sub {α β : Type} {g' g : α → Option β} (hg : ∀ a v, g' a = some v → g a = some v) :
    ∀ {l : List α} {vs : List β}, l.mapM g' = some vs → l.mapM g = some vs
  | [], _, h => h
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h ⊢
    rcases ha : g' a with _ | b
    · rw [ha] at h; simp at h
    rcases hl : l.mapM g' with _ | bs
    · rw [ha, hl] at h; simp at h
    rw [ha, hl] at h
    rw [hg a b ha, mapM_option_sub hg hl]
    exact h

/-- Entering the same block in an environment that binds less. -/
theorem enterOpt_sub {env' env : Env} (h : EnvSub env' env) {prev : Option Nat} {blk : Block}
    {e₁' : Env} (he : enterOpt env' prev blk = some e₁') :
    ∃ e₁, enterOpt env prev blk = some e₁ ∧ EnvSub e₁' e₁ ∧
      ∀ k, (e₁'[k]?).isSome = true → k ∈ blk.phis.map (·.dst) ∨ (env'[k]?).isSome = true := by
  unfold enterOpt at he ⊢
  rcases hv : blk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env') with _ | vals
  · rw [hv] at he; cases he
  rw [hv] at he
  rw [mapM_option_sub (g' := fun phi => prev >>= inc phi >>= opVal env') (fun phi v hpv => by
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hpv ⊢
    obtain ⟨o, ho, hov⟩ := hpv
    exact ⟨o, ho, h.opVal hov⟩) hv]
  simp only [Option.bind_eq_bind, Option.bind_some] at he ⊢
  split at he
  · next hl =>
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, by rw [if_pos hl], EnvSub.fold h _, fun k hk => ?_⟩
    obtain ⟨v, hk'⟩ := Option.isSome_iff_exists.mp hk
    rcases fold_get_cases _ _ _ _ hk' with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
    · left
      rw [← enter_keys (by simpa using hl)]
      exact List.mem_map_of_mem hx
    · right; rw [he]; rfl
  · cases he

theorem out_stmt_def {ob : Block} (hob : ob ∈ f'.blocks) {s : Stmt} (hs : s ∈ ob.body) {x : Nat × Ty}
    (hx : x ∈ s.dsts) : ((defsOf f').find? x.1).isSome = true := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
  exact defsOf_isSome (stmt_def hob hj hx)

/-- An output block's statements against the input block's, from point `k`. -/
theorem bc_stmts (hwf : f.wf sig syms = true) (F : BCFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block} (hb : f.block? b = some blk) {ob : Block}
    (hob : ob ∈ f'.blocks) (K : Env → FeM (List Val)) :
    ∀ (is os : List Stmt) (k : Nat) (e' e : Env), blk.body.drop k = is → k ≤ blk.body.length →
      bodyOk (BCtx.of f f').OD os is = true → (∀ s ∈ os, s ∈ ob.body) → BMid f f' e' e b k →
      Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ BMid f f' e₂' e₂ b blk.body.length)
        (runBodyO o c e' os) (runBodyO o c e is >>= K)
  | [], os, k, e', e, hd, hk, hok, _, hm => by
    have hkl : k = blk.body.length := by
      have := List.drop_eq_nil_iff.mp hd; omega
    subst hkl
    cases os with
    | nil => simp only [runBodyO, pure_bind]; exact Fol.pure ⟨e, rfl, hm⟩
    | cons _ _ => simp [bodyOk] at hok
  | s :: is, os, k, e', e, hd, hk, hok, hin, hm => by
    have hlt : k < blk.body.length := by
      rcases Nat.lt_or_ge k blk.body.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; cases hd
    have hsk : blk.body[k]? = some s := by
      rw [List.drop_eq_getElem_cons hlt] at hd
      simp only [List.cons.injEq] at hd
      rw [List.getElem?_eq_getElem hlt, hd.1]
    have hdk : blk.body.drop (k + 1) = is := by
      rw [List.drop_eq_getElem_cons hlt] at hd
      simp only [List.cons.injEq] at hd
      exact hd.2
    obtain ⟨hes, hds, hpi, hpu, hr⟩ := hm
    have hmach : s.inst.machine = true :=
      (Func.machine_block (Func.wf_machine hwf) hb).2.1 s (List.mem_of_getElem? hsk)
    have hv := F.valid
    have hs := F.ssa
    -- the input's statement with its results
    have step_in : ∀ vals, IntVals vals → (s.inst.pure = true → pureVals e s.inst = some vals) →
        s.dsts.length = vals.length →
        PointInv f (domTree f) b (k + 1) ((s.dsts.zip vals).foldl bindStep e) ∧
          PureInv f (domTree f) b (k + 1) ((s.dsts.zip vals).foldl bindStep e) :=
      fun vals hiv hpv hl => ⟨point_succ' hwf hb hsk hpi hiv hl, pureInv_stmt hwf hv hs hb hr hsk hpu hpv hl⟩
    -- the input alone through a deleted statement
    have deleted : deletable (BCtx.of f f').OD s = true →
        ∀ os', bodyOk (BCtx.of f f').OD os' is = true → (∀ s ∈ os', s ∈ ob.body) →
        Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ BMid f f' e₂' e₂ b blk.body.length)
          (runBodyO o c e' os') (runBodyO o c e (s :: is) >>= K) := by
      intro hdel os' hok' hin'
      unfold deletable at hdel
      split at hdel
      · next a u ty hi hd =>
        simp only [Option.isNone_iff_eq_none] at hdel
        -- the operand is a word
        obtain ⟨n, hn⟩ : ∃ n, intVal e a = some (256, n) := by
          have := uses_defined hwf hs hb hr (Nat.le_of_lt hlt) hpi a (by
            unfold usesAt; rw [hsk]; simp only [hi, Inst.args]; exact List.mem_singleton_self _)
          exact this
        have hpv : pureVals e s.inst = some [bool (n == 0)] := by
          rw [hi]; simp only [pureVals, hn, Option.map_some]
        have hrun : runStmtO o c e s = pure [bool (n == 0)] := by
          unfold runStmtO
          split
          · next heq => rw [heq] at hi; cases hi
          · rw [runInst_pure c e _ (by rw [hi]; rfl), hpv]; rfl
        have hbind : Fe.Sonatina.bind e s.dsts [bool (n == 0)] =
            pure ((s.dsts.zip [bool (n == 0)]).foldl bindStep e) := by
          unfold Fe.Sonatina.bind
          rw [hd]
          simp only [List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte]
          rfl
        simp only [runBodyO, hrun, pure_bind, hbind, bind_assoc]
        have hsd := step_in [bool (n == 0)] (by simp [IntVals, bool, Val.isInt])
          (fun _ => hpv) (by rw [hd]; rfl)
        refine bc_stmts hwf F ho hoi c hb hob K is os' (k + 1) e' _ hdk (by omega) hok' hin'
          ⟨fun x v hx => ?_, hds, hsd.1, hsd.2, hr⟩
        rw [fold_get_not _ _ _ ?_]
        · exact hes x v hx
        intro hxm
        rw [hd] at hxm
        simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.mem_singleton] at hxm
        subst hxm
        have := hds _ (by rw [hx]; rfl)
        have hdel' : (defsOf f').find? x = none := hdel
        rw [hdel'] at this; cases this
      · cases hdel
    cases os with
    | nil =>
      simp only [bodyOk, Bool.and_eq_true] at hok
      exact deleted hok.1 [] hok.2 (fun _ h => nomatch h)
    | cons s' os =>
      simp only [bodyOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨rfl, hok⟩ | ⟨hdel, hok⟩
      · -- the same statement on both sides
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
          have hsd := step_in vals hiv hpv hl
          refine ⟨EnvSub.fold hes _, fun k' hk' => ?_, hsd.1, hsd.2, hr⟩
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hk'
          rcases fold_get_cases _ _ _ _ hv' with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
          · exact out_stmt_def hob hsob (List.of_mem_zip hx).1
          · exact hds k' (by rw [he]; rfl)
        · rintro e₁' y₂ ⟨e₁, rfl, hm₁⟩
          exact bc_stmts hwf F ho hoi c hb hob K is os (k + 1) e₁' e₁ hdk (by omega) hok
            (fun s hs => hin s (List.mem_cons_of_mem _ hs)) hm₁
      · exact deleted hdel (s' :: os) hok hin

/-- A terminator the check accepts against the input's. -/
theorem bc_term (hwf : f.wf sig syms = true) (F : BCFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) {t' : Term} (ht : (BCtx.of f f').termOk t' blk.term = true)
    {e' e : Env} (hm : BMid f f' e' e b blk.body.length) :
    Fol (BQ o c f f' b) (runTerm e' t') (runTerm e blk.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) := by
  obtain ⟨hes, hds, hpi, hpu, hr⟩ := hm
  have hdef : ∀ op ∈ blk.term.args, ∃ v, intVal e op = some v := fun op hop => by
    obtain ⟨n, hn⟩ := term_defined hwf F.ssa hb hr hpi op hop
    exact ⟨_, hn⟩
  -- where the input goes is related to where the output goes
  have hgoto : ∀ d, d ∈ blk.term.succs → BR f f' (e', some b, d) (e, some b, d) := fun d hd =>
    ⟨rfl, hes, hds, blockInv_of_point F.valid hb hr hpi hd, fun pblk hp => by
      rw [hb] at hp; cases hp; exact hpu⟩
  have happ : Approx (NextTgt (fun a b => a = e' ∧ b = e) fun d' d => d' = d) (runTerm e' t')
      (runTerm e blk.term) := by
    unfold BCtx.termOk at ht
    simp only [Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · exact Approx.mono (approx_runTerm _ hes t' blk.term ht hdef) fun n' n h => by
        cases n' <;> cases n <;> simp only [NextTgt] at h ⊢
        · exact ⟨h.1, by simpa using h.2⟩
        · exact h
    · split at ht
      · next c' a' b' cnd ta tb ht' =>
        have hmem := List.mem_of_find?_eq_some hb
        have hid : blk.id = b := by simpa using List.find?_some hb
        obtain ⟨vc, hvc⟩ := hdef cnd (by rw [ht']; exact List.mem_singleton_self _)
        have huse : UseAt f (domTree f) b blk.body.length cnd := by
          cases cnd with
          | var u =>
            intro d j hdef'
            have := (ssa_block F.ssa hmem (hid ▸ hr)).2.2 _ (by rw [ht']; exact List.mem_singleton_self _)
            rw [hid] at this
            have hU := UniqueDefs.of_ssa F.ssa
            rcases useOk_sound (Func.wf_ids hwf) this with hp | ⟨blk', hb', hph | ⟨j', hj', s', hs', hv'⟩⟩ |
              ⟨d', hne', ha', hdefd⟩
            · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
              cases hU.fn (param_def hq) hdef'
            · rw [hb] at hb'; cases hb'
              obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
              cases hU.fn (hid ▸ phi_def hmem hφ) hdef'
            · rw [hb] at hb'; cases hb'
              obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
              have := hU.fn (hid ▸ stmt_def hmem hs' hdd) hdef'
              simp only [Def.stmt.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              exact Or.inr ⟨rfl, hj'⟩
            · rcases definedIn_def hdefd with h' | ⟨j'', h'⟩
              · cases hU.fn h' hdef'
              · have := (Def.stmt.inj (hU.fn h' hdef')).1
                subst this
                exact Or.inl ⟨hne', ha'⟩
          | imm => trivial
          | undef => trivial
        obtain ⟨v', hv', htg⟩ := peel_sound hwf F hb hr hpu _ cnd ta tb ht huse vc hvc
        rw [ht']
        unfold runTerm
        dsimp only
        rw [evalInt_eq, evalInt_eq, lift_bind, lift_bind, hvc]
        rcases hc' : intVal e' c' with _ | v''
        · exact Approx.stuck _
        · have := hes.intVal hc'
          rw [hv'] at this
          cases this
          rcases v' with ⟨_, x'⟩
          rcases vc with ⟨_, xc⟩
          exact Approx.pure ⟨⟨rfl, rfl⟩, htg.symm⟩
      · cases ht
  refine Fol.approx (Approx.strengthen happ (returns_runTerm hpi.1.int blk.term
    (Func.machine_block (Func.wf_machine hwf) hb).2.2)) fun n' n ⟨hn, hok⟩ => ?_
  rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
  · obtain ⟨⟨hea, heb⟩, rfl⟩ := hn
    subst ea eb
    obtain ⟨_, hd⟩ := hok
    exact ⟨(e, some b, d'), fun _ _ => rfl, hgoto d' hd⟩
  · subst hn; rfl

/-- One output block against the input's run from a related state. -/
theorem bc_block_fol (hwf : f.wf sig syms = true) (F : BCFacts f f') {o : Oracle}
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
  obtain ⟨ib, hib, _, hph, hbody, hterm⟩ := bc_block F hob
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
    have := bc_stmts hwf F ho hoi c hib hobm (fun e => runTerm e ib.term >>= fun
        | .goto e d => runFrom o c f (e, some b, d)
        | .done v => pure v) ib.body ob.body 0 e₁' e₁ rfl (Nat.zero_le _) hbody (fun _ h => h) hm
    refine Fol.bind this fun e₂' y ⟨e₂, hy, hm₂⟩ => ?_
    subst hy
    exact bc_term hwf F o c hib hterm hm₂

theorem bc_sim (hwf : f.wf sig syms = true) (F : BCFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) : Sim o c f' f (BR f f') := by
  intro s' s hR I w' w hw
  have h := bc_block_fol hwf F ho hoi c hR I w' w hw
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

/-- A `branch_canonicalize` or `branch_conditions` step is sound: the output function, its calls
    run by an oracle that approximates itself and returns integers on integers, approximates the
    well-formed input function on integers. -/
theorem branchCanon_sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx)
    {ids : Option (List (List Nat))} {s : FuncSnap} (hwf : f.wf sig syms = true)
    (h : checkBranchCanon f ids s = true) : FuncRef o c (some s.func) (some f) := by
  have F := checkBranchCanon_facts h
  have sim := bc_sim hwf F ho hoi c
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he' : s.func.blocks.head? with
  | none => exact Approx.stuck _
  | some e' =>
  obtain ⟨e, he, hid⟩ := bc_head F he'
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

theorem branchCanon_stepSound : StepSound .branchCanonicalize :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ hw h => branchCanon_sound ho hoi c hw h

theorem branchConditions_stepSound : StepSound .branchConditions :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ hw h => branchCanon_sound ho hoi c hw h

end Fe.Sonatina.Steps
