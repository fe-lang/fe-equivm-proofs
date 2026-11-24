import Fe.Sonatina.Steps.Validate

/-!
# `cfg_cleanup` is sound

The simulation (`CCtx.R`): the output at block `b` entered from output block `p'` against the
input at `b` entered from the last block `q` of the input's path (the end of `p'`'s chain or a
tunnel block), with

- the output's environment binding less than the input's (`EnvSub`), and only values of the
  output (`DomSub`);
- the input's definedness invariant (`BlockInv`, `Defined.lean`);
- the trivial-phi invariant on the input's state (`PointTPI`): for each entry `v ↦ x` of `σ`,
  `v` a phi of block `B`, wherever `B` is a tree ancestor-or-self of the point, `v` holds the
  value of `x`; entering a block from a surviving, uncut predecessor keeps it (`tpi_enter`,
  by `σ`'s check, `ssa`'s phi uses, D1's edge condition and the tree's antisymmetry), and so does
  a statement (`tpi_stmt`, by unique definitions);
- each phi the output block keeps taking, from `p'`, the value the input's phi of the same value
  takes from `q`.

One output block runs its chain's statements against the input's blocks of the chain, the input
stepping alone through each link's terminator, tunnel blocks and the next block's phis, all
total (`Fol`, a simulation of one output computation against the input's remaining run).  A
statement whose operands `σ` rewrites reads, in the input, values equal to them by the invariant.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## What the check gives -/

theorem CCtx.find_B (O : Option (List Summary)) (f f' : Func) (id : Nat) :
    (CCtx.of O f f').B.find? id = f.block? id := by
  simp only [CCtx.of, NatMap.find?_ofListBy, Func.block?]

theorem CCtx.find_B' (O : Option (List Summary)) (f f' : Func) (id : Nat) :
    (CCtx.of O f f').B'.find? id = f'.block? id := by
  simp only [CCtx.of, NatMap.find?_ofListBy, Func.block?]

/-- What a `cfg_cleanup` check accepting `f` to `f'` gives. -/
structure CCFacts (O : Option (List Summary)) (f f' : Func) : Prop where
  params : f'.params = f.params
  head : ∃ e e', f.blocks.head? = some e ∧ f'.blocks.head? = some e' ∧ e'.id = e.id
  machine' : f'.machine = true
  valid : (domTree f).valid f = true
  ssa : ssa f (domTree f) = true
  phisDef : (CCtx.of O f f').phisDefOk f = true
  sigma : (CCtx.of O f f').sigmaOk = true
  blocks : ∀ ob ∈ f'.blocks, (CCtx.of O f f').blockOk ob = true

theorem checkCfgCleanup_facts {O : Option (List Summary)} {f : Func}
    {ids : Option (List (List Nat))} {s : FuncSnap} (h : checkCfgCleanup O f ids s = true) :
    CCFacts O f s.func := by
  unfold checkCfgCleanup at h
  rcases ids with _ | ids
  · simp at h
  cases he : f.blocks.head? with
  | none => simp [he] at h
  | some e =>
  cases he' : s.func.blocks.head? with
  | none => simp [he, he'] at h
  | some e' =>
  simp only [he, he', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hp⟩, hid⟩, hm⟩, hv⟩, hs⟩, hpd⟩, hsig⟩, hbl⟩, _⟩ := h
  exact ⟨hp, ⟨e, e', he, he', hid⟩, hm, hv, hs, hpd, hsig, hbl⟩

section spec

variable {O : Option (List Summary)} {f f' : Func}

theorem cands_mem {L : NatMap Unit} {OD : NatMap Def} {b : Block} {φ : Phi}
    (h : (b, φ) ∈ candsOf L OD f) : b ∈ f.blocks ∧ φ ∈ b.phis ∧ (L.find? b.id).isSome = true := by
  simp only [candsOf, List.mem_flatMap] at h
  obtain ⟨b', hb', hm⟩ := h
  split at hm
  · next hl =>
    obtain ⟨φ', hφ', e⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hb', (List.mem_filter.mp hφ').1, hl⟩
  · cases hm

/-- An entry of `σ` comes from a candidate whose check holds. -/
theorem sigma_spec (F : CCFacts O f f') {v : Nat} {x : Operand}
    (h : (CCtx.of O f f').σ.find? v = some x) :
    ∃ b φ, b ∈ f.blocks ∧ φ ∈ b.phis ∧ φ.dst = v ∧ (CCtx.of O f f').sigOk b φ x = true := by
  have h' := h
  simp only [CCtx.of, sigmaOf, NatMap.find?_ofList] at h'
  obtain ⟨⟨b, φ⟩, hbφ, hmap⟩ := List.mem_filterMap.mp (mem_of_lookup h')
  have hd : φ.dst = v := by
    revert hmap
    dsimp only
    split
    · split
      · intro h; cases h
      · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1
    · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1
  obtain ⟨hb, hφ, _⟩ := cands_mem hbφ
  refine ⟨b, φ, hb, hφ, hd, ?_⟩
  have hs := F.sigma
  unfold CCtx.sigmaOk at hs
  have := List.all_eq_true.mp hs (b, φ) hbφ
  dsimp only at this
  rw [hd, h] at this
  exact this

theorem sigOk_spec {X : CCtx} {b : Block} {φ : Phi} {x : Operand} (h : X.sigOk b φ x = true) :
    x.wf = true ∧ (∀ u, x = .var u → X.σ.find? u = none ∧ X.strictDom b.id u = true) ∧
      ∀ o q, (o, q) ∈ φ.incoming → X.live q = true → X.cutAt q = false →
        o = .var φ.dst ∨ X.hat o = x := by
  unfold CCtx.sigOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw, hm⟩, hall⟩, _⟩ := h
  refine ⟨hw, fun u hu => ?_, fun o q hoq hl hc => hall o ?_⟩
  · subst hu
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    exact hm
  · simp only [liveOpsOf, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(o, q), ⟨hoq, hl, hc⟩, rfl⟩

theorem strictDom_spec {X : CCtx} {b u : Nat} (h : X.strictDom b u = true) :
    X.D.find? u = some .param ∨
      ∃ d, d ≠ b ∧ X.T.Anc d b ∧ (X.D.find? u = some (.phi d) ∨ ∃ j, X.D.find? u = some (.stmt d j)) := by
  unfold CCtx.strictDom at h
  split at h
  · next he => exact Or.inl he
  · next d he =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact Or.inr ⟨d, h.1, DomTree.anc_sound h.2, Or.inl he⟩
  · next d j he =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact Or.inr ⟨d, h.1, DomTree.anc_sound h.2, Or.inr ⟨j, he⟩⟩
  · cases h

/-- A phi of a surviving block is no value of the output, unless the output block of its id keeps
    it. -/
theorem phisDef_spec (F : CCFacts O f f') {b : Block} (hb : b ∈ f.blocks)
    (hl : (CCtx.of O f f').live b.id = true) {φ : Phi} (hφ : φ ∈ b.phis) :
    (defsOf f').find? φ.dst = none ∨ ∃ ob, f'.block? b.id = some ob ∧ φ.dst ∈ ob.phis.map (·.dst) := by
  have h := F.phisDef
  unfold CCtx.phisDefOk at h
  have := List.all_eq_true.mp h b hb
  simp only [hl, Bool.not_true, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
    Option.isNone_iff_eq_none] at this
  rcases this φ hφ with h | h
  · exact Or.inl h
  · right
    rw [CCtx.find_B'] at h
    split at h
    · next ob hob =>
      simp only [List.any_eq_true, beq_iff_eq] at h
      obtain ⟨φ', hφ', e⟩ := h
      exact ⟨ob, hob, List.mem_map.mpr ⟨φ', hφ', e⟩⟩
    · cases h

theorem chainFrom_cons (X : CCtx) : ∀ n c, ∃ rest, X.chainFrom n c = c :: rest
  | 0, c => ⟨[], rfl⟩
  | n + 1, c => by
    unfold CCtx.chainFrom
    split
    · split
      · dsimp only
        split
        · exact ⟨_, rfl⟩
        · exact ⟨[], rfl⟩
      · exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩

/-- An output block's check: the chain from its id, the phis it keeps, its statements, and its
    terminator. -/
theorem blockOk_spec {X : CCtx} {ob : Block} (h : X.blockOk ob = true) :
    ∃ c0 rest cm, X.B.find? ob.id = some c0 ∧ X.linksOk (ob.id :: rest) = true ∧
      ((ob.id :: rest).getLast? >>= X.B.find?) = some cm ∧
      (∀ φ' ∈ ob.phis, ∃ φ ∈ c0.phis, φ.dst = φ'.dst ∧ φ.ty = φ'.ty) ∧
      ob.body = (X.chainBody (ob.id :: rest)).map (Stmt.mapOps X.hat) ∧ X.termOk ob cm = true := by
  unfold CCtx.blockOk at h
  obtain ⟨rest, hr⟩ := chainFrom_cons X X.fuel ob.id
  simp only [hr] at h
  split at h
  · next c0 cm hc0 hcm =>
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨hl, hph⟩, hbody⟩, ht⟩ := h
    exact ⟨c0, rest, cm, hc0, hl, hcm, hph, hbody, ht⟩
  · cases h

end spec

/-! ## The trivial-phi invariant -/

section tpi

variable {O : Option (List Summary)} {f f' : Func}

/-- The trivial-phi invariant at block `b`: each entry `v ↦ x` of `σ` whose phi block is a tree
    ancestor-or-self of `b` holds. -/
def PointTPI (X : CCtx) (f : Func) (env : Env) (b : Nat) : Prop :=
  ∀ v x, X.σ.find? v = some x → ∀ B, (v, Def.phi B) ∈ defList f → X.T.Anc B b →
    opVal env (.var v) = opVal env x

/-- An entry of `σ`: its phi's block, its value's definition strictly above it. -/
theorem sigma_entry (F : CCFacts O f f') {v : Nat} {x : Operand}
    (h : (CCtx.of O f f').σ.find? v = some x) :
    ∃ b φ, b ∈ f.blocks ∧ φ ∈ b.phis ∧ φ.dst = v ∧ (v, Def.phi b.id) ∈ defList f ∧
      x.wf = true ∧
      (∀ u, x = .var u → (CCtx.of O f f').σ.find? u = none ∧ ((u, Def.param) ∈ defList f ∨
        ∃ d, d ≠ b.id ∧ (domTree f).Anc d b.id ∧
          ((u, Def.phi d) ∈ defList f ∨ ∃ j, (u, Def.stmt d j) ∈ defList f))) ∧
      ∀ o q, (o, q) ∈ φ.incoming → (CCtx.of O f f').live q = true →
        (CCtx.of O f f').cutAt q = false → o = .var v ∨ (CCtx.of O f f').hat o = x := by
  obtain ⟨b, φ, hb, hφ, hd, hok⟩ := sigma_spec F h
  obtain ⟨hw, hx, hops⟩ := sigOk_spec hok
  refine ⟨b, φ, hb, hφ, hd, hd ▸ phi_def hb hφ, hw, fun u hu => ?_, fun o q hoq hl hc => hd ▸ hops o q hoq hl hc⟩
  obtain ⟨hn, hs⟩ := hx u hu
  refine ⟨hn, ?_⟩
  rcases strictDom_spec hs with hp | ⟨d, hne, ha, hdd⟩
  · exact Or.inl (defsOf_mem hp)
  · refine Or.inr ⟨d, hne, ha, ?_⟩
    rcases hdd with hdd | ⟨j, hdd⟩
    · exact Or.inl (defsOf_mem hdd)
    · exact Or.inr ⟨j, defsOf_mem hdd⟩

/-- A use the check of strict SSA accepts at a point of a block where the invariant holds reads,
    through `σ`, the same value. -/
theorem hat_congr {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {env : Env} {b k : Nat} (ht : PointTPI (CCtx.of O f f') f env b)
    {o : Operand} (hu : useOk (defsOf f) (domTree f) b k o = true) :
    opVal env ((CCtx.of O f f').hat o) = opVal env o := by
  have hU := UniqueDefs.of_ssa F.ssa
  cases o with
  | var u =>
    simp only [CCtx.hat]
    cases hσ : (CCtx.of O f f').σ.find? u with
    | none => rfl
    | some x =>
      simp only [Option.getD_some]
      obtain ⟨cb, cφ, _, _, _, hdef, _⟩ := sigma_entry F hσ
      refine (ht u x hσ cb.id hdef ?_).symm
      rcases useOk_sound (Func.wf_ids hwf) hu with hp | ⟨blk, hb, hph | ⟨j, _, s, hs, hv⟩⟩ |
        ⟨d, _, ha, hd⟩
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
        cases hU.fn (param_def hp') hdef
      · have := phi_of_definedIn hU ⟨blk, hb, Or.inl hph⟩ hdef
        subst this; exact .refl
      · have hmem := List.mem_of_find?_eq_some hb
        obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv
        cases hU.fn (stmt_def hmem hs hdd) hdef
      · exact phi_of_definedIn hU hd hdef ▸ ha
  | imm => rfl
  | undef => rfl

end tpi

/-- Entering a block from a surviving, uncut predecessor keeps the trivial-phi invariant. -/
theorem tpi_enter {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {env : Env} {q b : Nat} (hi : BlockInv f (domTree f) (env, some q, b))
    (ht : PointTPI (CCtx.of O f f') f env q) (hq : (CCtx.of O f f').live q = true)
    (hqc : (CCtx.of O f f').cutAt q = false) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) : PointTPI (CCtx.of O f f') f e₁ b := by
  have hU := UniqueDefs.of_ssa F.ssa
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨hw, _, hr, hqr, hedge, _⟩ := hi
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  obtain ⟨e, _, he, _, _⟩ := F.head
  have hroot := (DomTree.valid_entry F.valid he).2
  have hbroot : (domTree f).Anc e.id b := hid ▸ DomTree.valid_root F.valid he hmem (hid ▸ hr)
  intro v x hσ B hB hanc
  obtain ⟨cb, cφ, hcb, hcφ, hcd, hcdef, hxw, hxdom, hops⟩ := sigma_entry F hσ
  have hcbB : cb.id = B := Def.phi.inj (hU.fn hcdef hB)
  -- `x` is no phi of `blk`, unless `B` is `b`'s strict descendant, which it is not
  have hxe : ∀ u, x = .var u → (B = b → False) ∨ True → u ∉ blk.phis.map (·.dst) → True := fun _ _ _ _ => trivial
  clear hxe
  have hxkeep : B = b ∨ (domTree f).Anc B b → opVal (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip
      vals).foldl bindStep env) x = opVal env x := by
    intro _
    cases x with
    | var u =>
      show (List.foldl bindStep env _)[u]? = env[u]?
      refine fold_get_not _ _ _ ?_
      rw [hkeys]
      intro hu
      obtain ⟨φu, hφu, rfl⟩ := List.mem_map.mp hu
      have hdu := phi_def hmem hφu
      rcases (hxdom _ rfl).2 with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
      · cases hU.fn hp hdu
      · have hdb : d = blk.id := Def.phi.inj (hU.fn hd hdu)
        rw [hcbB] at hne ha
        rw [hdb, hid] at hne ha
        exact hne (DomTree.anc_antisymm hroot hbroot hanc ha).symm
      · cases hU.fn hd hdu
    | imm => rfl
    | undef => rfl
  by_cases hBb : B = b
  · subst hBb
    have hcb' : cb = blk := by
      have := block?_of_mem (Func.wf_ids hwf) hcb
      rw [hcbB, hb] at this
      exact (Option.some.inj this).symm
    subst hcb'
    obtain ⟨o, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hcφ
    have hom : (o, q) ∈ cφ.incoming := inc_mem hinc
    have hox : opVal env o = opVal env x := by
      rcases hops o q hom hq hqc with rfl | hh
      · exact ht _ x hσ _ hB (phiUse_anc hwf F.ssa hb hr hqr hcφ hom hB)
      · cases o with
        | var u =>
          simp only [CCtx.hat] at hh
          cases hσu : (CCtx.of O f f').σ.find? u with
          | none => rw [hσu] at hh; simp only [Option.getD_none] at hh; rw [hh]
          | some x' =>
            rw [hσu, Option.getD_some] at hh
            subst hh
            obtain ⟨cb', cφ', _, _, _, hcdef', _⟩ := sigma_entry F hσu
            exact ht u x' hσu _ hcdef' (phiUse_anc hwf F.ssa hb hr hqr hcφ hom hcdef')
        | imm => simp only [CCtx.hat] at hh; rw [hh]
        | undef => simp only [CCtx.hat] at hh; rw [hh]
    have hxv : opVal env x = some val := hox ▸ hov
    have hnorm : val.as cφ.ty = val := by
      rw [((Func.wf_words hwf).2 cb hmem).1 cφ hcφ]
      by_cases hxvar : ∃ u, x = .var u
      · obtain ⟨u, rfl⟩ := hxvar
        obtain ⟨n, hn, e⟩ := hw u val hxv
        exact as_word e hn
      · obtain ⟨n, hn, e⟩ := wf_imm_word hxw hxv fun u h => hxvar ⟨u, h⟩
        exact as_word e hn
    rw [hxkeep (Or.inl rfl), hxv]
    show (List.foldl bindStep env _)[v]? = some val
    rw [← hcd, hget, hnorm]
  · have hBq := (DomTree.anc_of_edge F.valid hqr hedge hanc).resolve_left hBb
    rw [hxkeep (Or.inr hanc), ← ht v x hσ B hB hBq]
    show (List.foldl bindStep env _)[v]? = env[v]?
    refine fold_get_not _ _ _ ?_
    rw [hkeys]
    intro hv
    obtain ⟨φv, hφv, e⟩ := List.mem_map.mp hv
    have := Def.phi.inj (hU.fn (e ▸ phi_def hmem hφv) hB)
    exact hBb (this ▸ hid ▸ rfl)

/-- A statement keeps the trivial-phi invariant: it binds neither a phi nor a value defined above
    a phi's block. -/
theorem tpi_stmt {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {env : Env} {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (hr : ((domTree f).reach.find? b).isSome = true) {k : Nat} {s : Stmt}
    (hs : blk.body[k]? = some s) (ht : PointTPI (CCtx.of O f f') f env b)
    (l : List ((Nat × Ty) × Val)) (hl : ∀ y ∈ l, y.1 ∈ s.dsts) :
    PointTPI (CCtx.of O f f') f (l.foldl bindStep env) b := by
  have hU := UniqueDefs.of_ssa F.ssa
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e, _, he, _, _⟩ := F.head
  have hroot := (DomTree.valid_entry F.valid he).2
  have hbroot : (domTree f).Anc e.id b := hid ▸ DomTree.valid_root F.valid he hmem (hid ▸ hr)
  have hnot : ∀ u d, (u, d) ∈ defList f → (∀ j, d ≠ Def.stmt b j) → u ∉ l.map (·.1.1) := by
    intro u d hd hne hu
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
    have := hU.fn hd (hid ▸ stmt_def hmem hs (hl y hy))
    exact hne k this
  intro v x hσ B hB hanc
  obtain ⟨cb, cφ, hcb, hcφ, hcd, hcdef, hxw, hxdom, hops⟩ := sigma_entry F hσ
  have hcbB : cb.id = B := Def.phi.inj (hU.fn hcdef hB)
  have hx : opVal (l.foldl bindStep env) x = opVal env x := by
    cases x with
    | var u =>
      show (l.foldl bindStep env)[u]? = env[u]?
      refine fold_get_not _ _ _ ?_
      rcases (hxdom _ rfl).2 with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
      · exact hnot u _ hp fun _ h => by cases h
      · exact hnot u _ hd fun _ h => by cases h
      · refine hnot u _ hd fun j' h => ?_
        cases h
        rw [hcbB] at hne ha
        exact hne (DomTree.anc_antisymm hroot hbroot hanc ha).symm
    | imm => rfl
    | undef => rfl
  rw [hx, ← ht v x hσ B hB hanc]
  show (l.foldl bindStep env)[v]? = env[v]?
  exact fold_get_not _ _ _ (hnot v _ hB fun _ h => by cases h)

/-! ## The input's steps -/

section run

variable {O : Option (List Summary)} {f f' : Func}

theorem tunnel_spec {t t₂ : Nat} {tb : Block} (h : (CCtx.of O f f').tunnel t = some (tb, t₂)) :
    f.block? t = some tb ∧ tb.body = [] ∧ f'.block? t = none ∧ (CCtx.of O f f').live t = true ∧
      tb.term = .jump t₂ := by
  unfold CCtx.tunnel at h
  rw [CCtx.find_B, CCtx.find_B'] at h
  split at h
  · next tb' htb =>
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hc
      split at h
      · next t₂' hj => simp only [Option.some.injEq, Prod.mk.injEq] at h
                       obtain ⟨rfl, rfl⟩ := h
                       exact ⟨htb, hc.1.1, hc.1.2, hc.2, hj⟩
      · cases h
    · cases h
  · cases h

/-- Entering, in the input alone, a surviving block that is no output block keeps the output's
    environment below the input's. -/
theorem envSub_enter_gone (F : CCFacts O f f') {e' env e₂ : Env} (hes : EnvSub e' env)
    (hds : DomSub f' e') {t : Nat} {tb : Block} (htb : f.block? t = some tb)
    (hlt : (CCtx.of O f f').live t = true) (hno : f'.block? t = none) {prev : Option Nat}
    (he : enterOpt env prev tb = some e₂) : EnvSub e' e₂ := by
  obtain ⟨vals, _, hlen, rfl⟩ := enterOpt_spec he
  have hmem := List.mem_of_find?_eq_some htb
  have hid : tb.id = t := by simpa using List.find?_some htb
  intro k v hk
  rw [fold_get_not _ _ _ ?_]
  · exact hes k v hk
  rw [enter_keys hlen]
  intro hkm
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hkm
  rcases phisDef_spec F hmem (hid ▸ hlt) hφ with h | ⟨ob, hob, _⟩
  · have := hds _ (by rw [hk]; rfl)
    rw [h] at this; cases this
  · rw [hid, hno] at hob; cases hob

/-- From a slot target, the input runs through the tunnel blocks the check walked, to the state
    entering the output's target, keeping the invariants; the operands there read as `θ'` says at
    the slot's block's end. -/
theorem walk_run {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') (o : Oracle) (c : Ctx) {d' : Nat} {e' e₀ : Env} (hds : DomSub f' e') :
    ∀ (n : Nat) (θ : Operand → Operand) (r t : Nat) (env : Env) (q : Nat)
      (θ' : Operand → Operand), (CCtx.of O f f').walk d' n θ r t = some (q, θ') →
      BlockInv f (domTree f) (env, some r, t) → PointTPI (CCtx.of O f f') f env r →
      (CCtx.of O f f').live r = true → (CCtx.of O f f').cutAt r = false → EnvSub e' env →
      (∀ a, opVal env a = opVal e₀ (θ a)) →
      ∃ env₁, (∀ I w, (runFrom o c f (env, some r, t)).exec I w =
          (runFrom o c f (env₁, some q, d')).exec I w) ∧
        BlockInv f (domTree f) (env₁, some q, d') ∧ PointTPI (CCtx.of O f f') f env₁ q ∧
        (CCtx.of O f f').live q = true ∧ (CCtx.of O f f').cutAt q = false ∧ EnvSub e' env₁ ∧
        ∀ a, opVal env₁ a = opVal e₀ (θ' a)
  | 0, _, _, _, _, _, _, hw, _, _, _, _, _, _ => by simp [CCtx.walk] at hw
  | n + 1, θ, r, t, env, q, θ', hw, hi, ht, hl, hc, hes, hθ => by
    unfold CCtx.walk at hw
    split at hw
    · next htd =>
      simp only [beq_iff_eq] at htd
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      subst htd
      exact ⟨env, fun _ _ => rfl, hi, ht, hl, hc, hes, hθ⟩
    · cases htn : (CCtx.of O f f').tunnel t with
      | none => rw [htn] at hw; cases hw
      | some p =>
      rcases p with ⟨tb, t₂⟩
      rw [htn] at hw
      obtain ⟨htb, hbody, hno, hlt, hterm⟩ := tunnel_spec htn
      have hmem := List.mem_of_find?_eq_some htb
      obtain ⟨e₂, he₂⟩ := enter_total hwf F.ssa hi htb
      have hpz : PointInv f (domTree f) t 0 e₂ := returns_lift_some
        (by rw [← he₂, ← enter_eq]; exact point_zero hwf F.valid hi htb)
      have hbi : BlockInv f (domTree f) (e₂, some t, t₂) :=
        blockInv_of_point F.valid htb hi.2.2.1 (by rw [hbody]; exact hpz)
          (by rw [hterm]; exact List.mem_singleton_self _)
      have htp := tpi_enter hwf F hi ht hl hc htb he₂
      have hct : (CCtx.of O f f').cutAt t = false := by
        simp only [CCtx.cutAt, CCtx.find_B, htb, Option.any_some, cut, trimIdx, hbody,
          List.findIdx?_nil, Option.isSome_none]
      have hes₂ := envSub_enter_gone F hes hds htb hlt hno he₂
      have hθ₂ : ∀ a, opVal e₂ a = opVal e₀ (CCtx.through θ tb r a) := by
        obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he₂
        have hU := UniqueDefs.of_ssa F.ssa
        intro a
        cases a with
        | var w =>
          simp only [CCtx.through]
          cases hfd : tb.phis.find? (·.dst == w) with
          | none =>
            show (List.foldl bindStep env _)[w]? = _
            rw [fold_get_not _ _ _ (by
              rw [enter_keys hlen]
              intro hm
              obtain ⟨φ, hφ, e⟩ := List.mem_map.mp hm
              have := List.find?_eq_none.mp hfd φ hφ
              simp [e] at this)]
            exact hθ (.var w)
          | some φ =>
            have hφ := List.mem_of_find?_eq_some hfd
            have hφd : φ.dst = w := by simpa using List.find?_some hfd
            obtain ⟨ao, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hφ
            simp only [hinc]
            show (List.foldl bindStep env _)[w]? = _
            rw [← hφd, hget, ← hθ ao, hov,
              ((Func.wf_words hwf).2 tb hmem).1 φ hφ, phi_val_word hwf hmem hφ (inc_mem hinc)
                hi.1 hov]
        | imm bits v => exact hθ (.imm bits v)
        | undef ty => exact hθ (.undef ty)
      obtain ⟨env₁, hex, hrest⟩ :=
        walk_run hwf F o c hds n _ t t₂ e₂ q θ' hw hbi htp hlt hct hes₂ hθ₂
      exact ⟨env₁, fun I w => (jump_step o c htb hbody hterm he₂ I w).trans (hex I w), hrest⟩

end run

/-! ## One output block against the input -/

section sim

variable {O : Option (List Summary)} {f f' : Func}

/-- The relation before statement `k` of input block `b`, inside an output block. -/
def Mid (O : Option (List Summary)) (f f' : Func) (e' e : Env) (b k : Nat) : Prop :=
  EnvSub e' e ∧ DomSub f' e' ∧ PointInv f (domTree f) b k e ∧
    PointTPI (CCtx.of O f f') f e b ∧ ((domTree f).reach.find? b).isSome = true

/-- Each phi the output block `b` keeps takes, from `p'`, the value the input's phi of the same
    value takes from `q`. -/
def PhiRel (f f' : Func) (env' env : Env) (p' q b : Nat) : Prop :=
  ∀ ob, f'.block? b = some ob → ∀ φ' ∈ ob.phis, ∀ val, (inc φ' p').bind (opVal env') = some val →
    ∃ blk φ, f.block? b = some blk ∧ φ ∈ blk.phis ∧ φ.dst = φ'.dst ∧ φ.ty = φ'.ty ∧
      (inc φ q).bind (opVal env) = some val

/-- The simulation: the output at `b` against the input at `b`. -/
def CR (O : Option (List Summary)) (f f' : Func) (s' s : BState) : Prop :=
  s'.2.2 = s.2.2 ∧ EnvSub s'.1 s.1 ∧ DomSub f' s'.1 ∧ BlockInv f (domTree f) s ∧
    ((s'.2.1 = none ∧ s.2.1 = none) ∨
      ∃ p' q, s'.2.1 = some p' ∧ s.2.1 = some q ∧ (CCtx.of O f f').live q = true ∧
        (CCtx.of O f f').cutAt q = false ∧ PointTPI (CCtx.of O f f') f s.1 q ∧
        PhiRel f f' s'.1 s.1 p' q s.2.2)

/-- Where the input's remaining run `y` stands once output block `b` ends with `n`. -/
def Qs (o : Oracle) (c : Ctx) (O : Option (List Summary)) (f f' : Func) (b : Nat) :
    Next → FeM (List Val) → Prop
  | .goto e d, y => ∃ t, (∀ I w, y.exec I w = (runFrom o c f t).exec I w) ∧ CR O f f' (e, some b, d) t
  | .done v, y => y = pure v

/-- Statements of an input block against the same statements through `σ` in the output. -/
theorem stmts_fol {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) {ob : Block} (hob : ob ∈ f'.blocks)
    (K : Env → FeM (List Val)) :
    ∀ n k e' e, k + n ≤ blk.body.length →
      (∀ s ∈ (blk.body.drop k).take n, s.mapOps (CCtx.of O f f').hat ∈ ob.body) →
      Mid O f f' e' e b k →
      Fol (fun e₂' y₁ => ∃ e₂, y₁ = K e₂ ∧ Mid O f f' e₂' e₂ b (k + n))
        (runBodyO o c e' (((blk.body.drop k).take n).map (Stmt.mapOps (CCtx.of O f f').hat)))
        (runBodyO o c e ((blk.body.drop k).take n) >>= K)
  | 0, k, e', e, _, _, hm => by
    simp only [List.take_zero, List.map_nil, runBodyO, pure_bind, Nat.add_zero]
    exact Fol.pure ⟨e, rfl, hm⟩
  | n + 1, k, e', e, hk, hin, hm => by
    have hmem := List.mem_of_find?_eq_some hb
    have hid : blk.id = b := by simpa using List.find?_some hb
    have hlt : k < blk.body.length := by omega
    have hs : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    have hdt : (blk.body.drop k).take (n + 1) = blk.body[k] :: (blk.body.drop (k + 1)).take n := by
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    rw [hdt] at hin ⊢
    generalize blk.body[k] = s at hs hin
    obtain ⟨hes, hds, hpi, htp, hr⟩ := hm
    have hsob : s.mapOps (CCtx.of O f f').hat ∈ ob.body := hin s (List.mem_cons_self ..)
    have hmach : (s.mapOps (CCtx.of O f f').hat).inst.machine = true :=
      (Func.machine_of_mem F.machine' hob).2.1 _ hsob
    have hsm : s.inst.machine = true :=
      (Func.machine_block (Func.wf_machine hwf) hb).2.1 s (List.mem_of_getElem? hs)
    have hcong : ∀ a ∈ s.inst.args, opVal e ((CCtx.of O f f').hat a) = opVal e a := fun a ha =>
      hat_congr hwf F htp (hid ▸ (ssa_block F.ssa hmem (hid ▸ hr)).2.1 k s hs a ha)
    have happ : Approx Eq (runStmtO o c e' (s.mapOps (CCtx.of O f f').hat)) (runStmtO o c e s) := by
      rw [← runStmtO_mapOps o c s hcong]
      exact Approx.runStmtO_sub ho hes hpi.1.int _ hmach
    simp only [List.map_cons, runBodyO, bind_assoc]
    refine Fol.bind (Fol.approx (Approx.strengthen happ (returns_runStmtO hoi c hpi.1.int hsm))
      (Q := fun vals y₁ => IntVals vals ∧ y₁ = (Fe.Sonatina.bind e s.dsts vals >>= fun e₁ =>
        runBodyO o c e₁ ((blk.body.drop (k + 1)).take n) >>= K))
      fun a' a ⟨h1, h2⟩ => ⟨h1 ▸ h2, h1 ▸ rfl⟩) ?_
    rintro vals y₁ ⟨hiv, rfl⟩
    refine Fol.bind (Fol.approx (bind_rel e' e s.dsts vals)
      (Q := fun e₁' y₂ => ∃ e₁, y₂ = (runBodyO o c e₁ ((blk.body.drop (k + 1)).take n) >>= K) ∧
        Mid O f f' e₁' e₁ b (k + 1)) fun a' a ⟨hl, h1, h2⟩ => ⟨a, rfl, ?_⟩) ?_
    · subst h1 h2
      refine ⟨EnvSub.fold hes _, fun k' hk' => ?_, point_succ' hwf hb hs hpi hiv hl,
        tpi_stmt hwf F hb hr hs htp _ fun y hy => (List.of_mem_zip hy).1, hr⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk'
      rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem hsob
        exact defsOf_isSome (stmt_def hob hj (List.of_mem_zip hx).1)
      · exact hds k' (by rw [he]; rfl)
    · rintro e₁' y₂ ⟨e₁, rfl, hm₁⟩
      have := stmts_fol hwf F ho hoi c hb hob K n (k + 1) e₁' e₁ (by omega)
        (fun s' hs' => hin s' (List.mem_cons_of_mem _ hs')) hm₁
      refine Fol.mono this fun a y h => ?_
      rw [show k + (n + 1) = k + 1 + n by omega]
      exact h

theorem arrive_spec {X : CCtx} {b cm k d' : Nat} {θ : Operand → Operand} {q : Nat}
    (h : X.arrive b cm k d' θ q = true) :
    X.live q = true ∧ X.cutAt q = false ∧ ∀ ob, X.B'.find? d' = some ob → ∃ ib, X.B.find? d' = some ib ∧
      ∀ φ' ∈ ob.phis, ∀ o', inc φ' b = some o' → ∃ φ ∈ ib.phis, φ.dst = φ'.dst ∧ φ.ty = φ'.ty ∧
        ∃ a, inc φ q = some a ∧ o' = X.hat (θ a) ∧ useOk X.D X.T cm k (θ a) = true := by
  unfold CCtx.arrive at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hl, hc⟩, hm⟩ := h
  refine ⟨hl, hc, fun ob hob => ?_⟩
  rw [hob] at hm
  dsimp only at hm
  split at hm
  · cases hm
  · next ib hib =>
    refine ⟨ib, hib, fun φ' hφ' o' ho' => ?_⟩
    have := List.all_eq_true.mp hm φ' hφ'
    rw [ho'] at this
    dsimp only at this
    split at this
    · cases this
    · next φ hφ =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨hty, hrest⟩ := this
      split at hrest
      · cases hrest
      · next a ha =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
        exact ⟨φ, List.mem_of_find?_eq_some hφ, by simpa using List.find?_some hφ, hty, a, ha,
          hrest.1, hrest.2⟩

/-- The last block's terminator against the output's: each slot through its tunnel blocks to
    a state related to the output's target. -/
theorem term_fol {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') (o : Oracle) (c : Ctx) {ob : Block} {cm : Nat} {cmb : Block}
    (hcm : f.block? cm = some cmb) (hlive : (CCtx.of O f f').live cm = true)
    (htrim : trimIdx O cmb = none)
    (ht : termRel (fun d' d => (CCtx.of O f f').slotOk ob.id cmb.id cmb.body.length d' d) ob.term
      (cmb.term.mapOps (CCtx.of O f f').hat) = true)
    {e' e : Env} (hm : Mid O f f' e' e cm cmb.body.length) :
    Fol (Qs o c O f f' ob.id) (runTerm e' ob.term) (runTerm e cmb.term >>= fun
      | .goto e d => runFrom o c f (e, some cm, d)
      | .done v => pure v) := by
  obtain ⟨hes, hds, hpi, htp, hr⟩ := hm
  have hmem := List.mem_of_find?_eq_some hcm
  have hid : cmb.id = cm := by simpa using List.find?_some hcm
  have hcong : ∀ a ∈ cmb.term.args, opVal e ((CCtx.of O f f').hat a) = opVal e a := fun a ha =>
    hat_congr hwf F htp (hid ▸ (ssa_block F.ssa hmem (hid ▸ hr)).2.2 a ha)
  have hdef : ∀ op ∈ (cmb.term.mapOps (CCtx.of O f f').hat).args, ∃ v, intVal e op = some v := by
    rw [Term.args_mapOps]
    intro op hop
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hop
    obtain ⟨n, hn⟩ := term_defined hwf F.ssa hcm hr hpi a ha
    exact ⟨_, by unfold intVal at hn ⊢; rw [hcong a ha]; exact hn⟩
  have happ := approx_runTerm _ hes ob.term _ ht hdef
  rw [runTerm_mapOps _ hcong] at happ
  have happ2 := Approx.strengthen happ (returns_runTerm hpi.1.int cmb.term
    (Func.machine_block (Func.wf_machine hwf) hcm).2.2)
  refine Fol.approx happ2 fun n' n ⟨hn, hok⟩ => ?_
  rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
  · obtain ⟨⟨hea, heb⟩, hslot⟩ := hn
    subst ea eb
    obtain ⟨_, hd⟩ := hok
    unfold CCtx.slotOk at hslot
    rcases hw : (CCtx.of O f f').walk d' (CCtx.of O f f').fuel id cmb.id d with _ | ⟨q, θ⟩
    · rw [hw] at hslot; cases hslot
    rw [hw] at hslot
    dsimp only at hslot
    rw [hid] at hw
    have hbi := blockInv_of_point F.valid hcm hr hpi hd
    have hcc : (CCtx.of O f f').cutAt cm = false := by
      simp only [CCtx.cutAt, CCtx.find_B, hcm, Option.any_some, cut]
      show (trimIdx O cmb).isSome = false
      rw [htrim]; rfl
    obtain ⟨env₁, hex, hbi₁, htp₁, hl₁, hc₁, hes₁, hθ⟩ :=
      walk_run hwf F o c hds _ id cm d e q θ hw hbi htp hlive hcc hes fun _ => rfl
    obtain ⟨_, _, hall⟩ := arrive_spec hslot
    refine ⟨(env₁, some q, d'), hex, rfl, hes₁, hds, hbi₁,
      Or.inr ⟨ob.id, q, rfl, rfl, hl₁, hc₁, htp₁, ?_⟩⟩
    intro ob₂ hob₂ φ' hφ' val hval
    obtain ⟨ib, hib, hph⟩ := hall ob₂ (by rw [CCtx.find_B']; exact hob₂)
    obtain ⟨o', ho', hov'⟩ := Option.bind_eq_some_iff.mp hval
    obtain ⟨φ, hφ, hdst, hty, a, ha, rfl, huse⟩ := hph φ' hφ' o' ho'
    refine ⟨ib, φ, by rw [← CCtx.find_B O f f']; exact hib, hφ, hdst, hty, ?_⟩
    rw [ha, Option.bind_some, hθ a, ← hat_congr hwf F htp (hid ▸ huse)]
    exact hes.opVal hov'
  · subst hn
    rfl

theorem linkOk_spec {X : CCtx} {c n : Nat} (h : X.linkOk c n = true) :
    X.live c = true ∧ (∃ cb, X.B.find? c = some cb ∧ cut X.O cb = false ∧
      termRel (X.linkTo c) (.jump n) cb.term = true) ∧ X.B'.find? n = none := by
  unfold CCtx.linkOk at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hl, hm⟩, hn⟩ := h
  refine ⟨hl, ?_, hn⟩
  split at hm
  · next cb hcb =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
    exact ⟨cb, hcb, hm.1.1, hm.1.2⟩
  · cases hm

theorem linksOk_live {X : CCtx} {c : Nat} {rest : List Nat} (h : X.linksOk (c :: rest) = true) :
    X.live c = true := by
  cases rest with
  | nil => exact h
  | cons n rest =>
    simp only [CCtx.linksOk, Bool.and_eq_true] at h
    exact (linkOk_spec h.1).1

theorem linksOk_block {X : CCtx} {c n : Nat} {rest : List Nat}
    (h : X.linksOk (c :: n :: rest) = true) {cmb : Block}
    (hl : ((c :: n :: rest).getLast? >>= X.B.find?) = some cmb) : ∃ nb, X.B.find? n = some nb := by
  cases rest with
  | nil => exact ⟨cmb, by simpa using hl⟩
  | cons m rest =>
    simp only [CCtx.linksOk, Bool.and_eq_true] at h
    obtain ⟨nb, hnb, _⟩ := (linkOk_spec h.2.1).2.1
    exact ⟨nb, hnb⟩

/-- An output block's chain against the input's run from its first block. -/
theorem chain_fol {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {ob : Block}
    (hob : ob ∈ f'.blocks) :
    ∀ (ch : List Nat) (cid : Nat) (cb : Block), f.block? cid = some cb →
      (CCtx.of O f f').linksOk (cid :: ch) = true → ∀ cmb : Block,
      ((cid :: ch).getLast? >>= (CCtx.of O f f').B.find?) = some cmb →
      (CCtx.of O f f').termOk ob cmb = true →
      (∀ s ∈ (CCtx.of O f f').chainBody (cid :: ch), s.mapOps (CCtx.of O f f').hat ∈ ob.body) →
      ∀ e' e, Mid O f f' e' e cid 0 →
      Fol (Qs o c O f f' ob.id)
        (runBodyO o c e' (((CCtx.of O f f').chainBody (cid :: ch)).map
          (Stmt.mapOps (CCtx.of O f f').hat)) >>= fun e₂' => runTerm e₂' ob.term)
        (inRun o c f cid cb e) := by
  intro ch
  induction ch with
  | nil =>
    intro cid cb hcb hlinks cmb hlast hterm hin e' e hm
    simp only [List.getLast?_singleton, Option.bind_eq_bind, Option.bind_some, CCtx.find_B, hcb,
      Option.some.injEq] at hlast
    subst hlast
    have hcbody : (CCtx.of O f f').chainBody [cid] = (CCtx.of O f f').lastBody cb := by
      simp only [CCtx.chainBody, CCtx.find_B, hcb, Option.map_some, Option.getD_some]
    rw [hcbody] at hin ⊢
    unfold inRun
    unfold CCtx.lastBody at hin ⊢
    unfold CCtx.termOk at hterm
    cases htr : trimIdx (CCtx.of O f f').O cb with
    | some k =>
      simp only [htr] at hin hterm ⊢
      simp only [decide_eq_true_eq] at hterm
      have hk : k < cb.body.length := by
        obtain ⟨h, _⟩ := List.findIdx?_eq_some_iff_getElem.mp htr
        exact h
      have hsplit : runBodyO o c e cb.body = runBodyO o c e (cb.body.take (k + 1)) >>= fun e =>
          runBodyO o c e (cb.body.drop (k + 1)) := by
        rw [← runBodyO_append, List.take_append_drop]
      rw [hsplit, bind_assoc]
      have := stmts_fol hwf F ho hoi c hcb hob (fun e => runBodyO o c e (cb.body.drop (k + 1)) >>=
          fun e => runTerm e cb.term >>= fun
            | .goto e d => runFrom o c f (e, some cid, d)
            | .done v => pure v) (k + 1) 0 e' e (by omega) (by simpa using hin) hm
      simp only [List.drop_zero] at this
      refine Fol.bind this fun e₂' y₁ _ => ?_
      rw [hterm]
      exact Fol.stuck
    | none =>
      simp only [htr] at hin hterm ⊢
      have := stmts_fol hwf F ho hoi c hcb hob (fun e => runTerm e cb.term >>= fun
            | .goto e d => runFrom o c f (e, some cid, d)
            | .done v => pure v) cb.body.length 0 e' e (by omega) (by simpa using hin) hm
      simp only [List.drop_zero, List.take_length] at this
      refine Fol.bind this fun e₂' y₁ ⟨e₂, hy, hm₂⟩ => ?_
      subst hy
      simp only [Nat.zero_add] at hm₂
      exact term_fol hwf F o c hcb (linksOk_live hlinks) (htr : trimIdx O cb = none) hterm hm₂
  | cons n ch ih =>
    intro cid cb hcb hlinks cmb hlast hterm hin e' e hm
    have hlinks' := hlinks
    simp only [CCtx.linksOk, Bool.and_eq_true] at hlinks'
    obtain ⟨hlink, hrest⟩ := hlinks'
    obtain ⟨hlc, ⟨cb', hcb', hcut, hrel⟩, hno⟩ := linkOk_spec hlink
    rw [CCtx.find_B, hcb] at hcb'
    cases hcb'
    rw [CCtx.find_B'] at hno
    obtain ⟨nb, hnb⟩ := linksOk_block hlinks hlast
    rw [CCtx.find_B] at hnb
    have hcbody : (CCtx.of O f f').chainBody (cid :: n :: ch) =
        cb.body ++ (CCtx.of O f f').chainBody (n :: ch) := by
      simp only [CCtx.chainBody, CCtx.find_B, hcb, Option.map_some, Option.getD_some]
    rw [hcbody] at hin
    rw [hcbody, List.map_append, runBodyO_append, bind_assoc]
    unfold inRun
    have := stmts_fol hwf F ho hoi c hcb hob (fun e => runTerm e cb.term >>= fun
          | .goto e d => runFrom o c f (e, some cid, d)
          | .done v => pure v) cb.body.length 0 e' e (by omega)
      (by simpa using fun s hs => hin s (List.mem_append_left _ hs)) hm
    simp only [List.drop_zero, List.take_length] at this
    refine Fol.bind this fun e₁' y₁ ⟨e₁, hy, hm₁⟩ => ?_
    subst hy
    simp only [Nat.zero_add] at hm₁
    obtain ⟨hes₁, hds₁, hpi₁, htp₁, hr₁⟩ := hm₁
    have hmem := List.mem_of_find?_eq_some hcb
    have hdef : ∀ op ∈ cb.term.args, ∃ v, intVal e₁ op = some v := fun op hop => by
      obtain ⟨k, hk⟩ := term_defined hwf F.ssa hcb hr₁ hpi₁ op hop
      exact ⟨_, hk⟩
    have happ := Approx.strengthen (Approx.pure_left
      (approx_runTerm _ (EnvSub.refl e₁) (.jump n) cb.term hrel hdef))
      (returns_runTerm hpi₁.1.int cb.term (Func.machine_block (Func.wf_machine hwf) hcb).2.2)
    rw [show (runBodyO o c e₁' ((CCtx.of O f f').chainBody (n :: ch) |>.map
        (Stmt.mapOps (CCtx.of O f f').hat)) >>= fun e₂' => runTerm e₂' ob.term) =
        (runTerm e₁ (.jump n) >>= fun _ => runBodyO o c e₁' ((CCtx.of O f f').chainBody (n :: ch)
          |>.map (Stmt.mapOps (CCtx.of O f f').hat)) >>= fun e₂' => runTerm e₂' ob.term) by
      simp only [runTerm, pure_bind]]
    refine Fol.bind (Fol.approx happ (Q := fun _ y₂ => ∃ d, y₂ = runFrom o c f (e₁, some cid, d) ∧
        d ∈ cb.term.succs ∧ (CCtx.of O f f').linkTo cid n d = true) fun n' n0 ⟨hn, hok⟩ => ?_) ?_
    · obtain ⟨hn, hn'⟩ := hn
      subst hn'
      rcases n0 with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
      obtain ⟨⟨_, heb⟩, hld⟩ := hn
      subst eb
      obtain ⟨_, hd⟩ := hok
      exact ⟨d, rfl, hd, hld⟩
    rintro _ y₂ ⟨d, rfl, hd, hld⟩
    unfold CCtx.linkTo at hld
    rcases hw : (CCtx.of O f f').walk n (CCtx.of O f f').fuel id cid d with _ | ⟨q, θ⟩
    · rw [hw] at hld; cases hld
    rw [hw] at hld
    simp only [Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at hld
    have hbi := blockInv_of_point F.valid hcb hr₁ hpi₁ hd
    have hcc : (CCtx.of O f f').cutAt cid = false := by
      simp only [CCtx.cutAt, CCtx.find_B, hcb, Option.any_some]; exact hcut
    obtain ⟨env₂, hex, hbi₂, htp₂, hl₂, hc₂, hes₂, _⟩ :=
      walk_run hwf F o c hds₁ _ id cid d e₁ q θ hw hbi htp₁ hlc hcc hes₁ fun _ => rfl
    obtain ⟨e₃, he₃⟩ := enter_total hwf F.ssa hbi₂ hnb
    refine Fol.congr (fun I w => (hex I w).trans (by rw [runFrom_enter o c hnb])) ?_
    rw [enter_eq, he₃]
    refine Fol.total (P := fun x => x = e₃) (Total.lift rfl rfl) fun x hx => ?_
    rw [hx]
    have hpz : PointInv f (domTree f) n 0 e₃ := returns_lift_some
      (by rw [← he₃, ← enter_eq]; exact point_zero hwf F.valid hbi₂ hnb)
    refine ih n nb hnb hrest cmb (by simpa using hlast) hterm
      (fun s hs => hin s (List.mem_append_right _ hs)) e₁' e₃
      ⟨envSub_enter_gone F hes₂ hds₁ hnb (linksOk_live hrest) hno he₃, hds₁, hpz,
        tpi_enter hwf F hbi₂ htp₂ hl₂ hc₂ hnb he₃, hbi₂.2.2.1⟩

end sim

/-! ## The simulation and soundness -/

section sound

variable {O : Option (List Summary)} {f f' : Func}

/-- Entering the output block against entering its chain's first block: the phis the output
    keeps take the input's values. -/
theorem enter_rel {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {env' env : Env} {prev' prev : Option Nat} {b : Nat} {ob c0 : Block}
    (hob : f'.block? b = some ob) (hc0 : f.block? b = some c0)
    (hlive : (CCtx.of O f f').live b = true) (hes : EnvSub env' env) (hds : DomSub f' env')
    (hbi : BlockInv f (domTree f) (env, prev, b))
    (hprev : (prev' = none ∧ prev = none) ∨ ∃ p' q, prev' = some p' ∧ prev = some q ∧
      (CCtx.of O f f').live q = true ∧ (CCtx.of O f f').cutAt q = false ∧
      PointTPI (CCtx.of O f f') f env q ∧ PhiRel f f' env' env p' q b) :
    Approx (fun e₁' e₁ => Mid O f f' e₁' e₁ b 0) (enter env' prev' ob) (enter env prev c0) := by
  have hU := UniqueDefs.of_ssa F.ssa
  have hmem := List.mem_of_find?_eq_some hc0
  have hid : c0.id = b := by simpa using List.find?_some hc0
  have hobm := List.mem_of_find?_eq_some hob
  rw [enter_eq, enter_eq]
  refine Approx.lift fun e₁' he₁' => ?_
  rcases hprev with ⟨rfl, rfl⟩ | ⟨p', q, rfl, rfl, hlq, hcq, htq, hphi⟩
  · obtain ⟨vals', hF', _, rfl⟩ := enterOpt_spec he₁'
    have hob0 : ob.phis = [] := by
      cases hp : ob.phis with
      | nil => rfl
      | cons φ _ =>
        rw [hp] at hF'
        cases hF' with
        | cons h _ => simp at h
    obtain ⟨e, _, he, _, _⟩ := F.head
    have hbe : b = e.id := by
      have ha := hid ▸ DomTree.valid_root F.valid he hmem (hid ▸ hbi.2.2.1)
      rcases ha.inv with h | ⟨i, hi, _⟩
      · exact h.symm
      · have : (domTree f).idom.find? b = none := hbi.2.2.2
        rw [this] at hi; cases hi
    have hce : c0 = e := by
      have := block?_of_mem (Func.wf_ids hwf) (List.mem_of_mem_head? he)
      rw [← hbe, hc0] at this; exact Option.some.inj this
    have he0 := entry_phis hwf he
    have hin : enterOpt env none c0 = some env := by unfold enterOpt; rw [hce, he0]; rfl
    refine ⟨env, hin, ?_⟩
    simp only [hob0, List.map_nil, List.zip_nil_left, List.foldl_nil]
    refine ⟨hes, hds, returns_lift_some (P := PointInv f (domTree f) b 0)
      (by rw [← hin, ← enter_eq]; exact point_zero hwf F.valid hbi hc0), ?_, hbi.2.2.1⟩
    intro v x _ B hB hanc
    exfalso
    rcases hanc.inv with rfl | ⟨i, hi, _⟩
    · rcases mem_defList hB with ⟨h, _⟩ | ⟨bb, hbb, φ, hφ, hd, _⟩ | ⟨_, _, _, _, _, h, _⟩
      · cases h
      · have hbbid : bb.id = B := (Def.phi.inj hd).symm
        have : bb = c0 := by
          have := block?_of_mem (Func.wf_ids hwf) hbb
          rw [hbbid, hc0] at this; exact (Option.some.inj this).symm
        rw [this, hce, he0] at hφ; cases hφ
      · cases h
    · have : (domTree f).idom.find? b = none := hbi.2.2.2
      change (domTree f).idom.find? b = some i at hi
      rw [this] at hi; cases hi
  · obtain ⟨e₁, he₁⟩ := enter_total hwf F.ssa hbi hc0
    refine ⟨e₁, he₁, ?_, ?_, returns_lift_some (P := PointInv f (domTree f) b 0)
      (by rw [← he₁, ← enter_eq]; exact point_zero hwf F.valid hbi hc0),
      tpi_enter hwf F hbi htq hlq hcq hc0 he₁, hbi.2.2.1⟩
    · obtain ⟨vals', hF', hlen', rfl⟩ := enterOpt_spec he₁'
      obtain ⟨vals, hF, hlen, rfl⟩ := enterOpt_spec he₁
      intro k v hk
      rcases fold_get_cases _ _ _ _ hk with ⟨x, hx, rfl, rfl⟩ | ⟨hk', hnk⟩
      · rw [List.zip_map_left] at hx
        obtain ⟨⟨φ', v'⟩, hz, rfl⟩ := List.mem_map.mp hx
        have hR := (List.forall₂_iff_zip.mp hF').2 hz
        simp only [Option.bind_eq_bind, Option.bind_some] at hR
        obtain ⟨blk, φ, hblk, hφ, hdst, hty, hval⟩ :=
          hphi ob hob φ' (List.of_mem_zip hz).1 v' hR
        rw [hc0] at hblk; cases hblk
        obtain ⟨o, w, hinc, how, hget⟩ := enter_val hF hlen (hU.phis hmem) hφ
        rw [hinc, Option.bind_some, how] at hval
        cases hval
        simp only [Prod.map, id]
        rw [← hdst, hget, hty]
      · rw [fold_get_not _ _ _ ?_]
        · exact hes k v hk'
        rw [enter_keys hlen]
        intro hkm
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hkm
        rcases phisDef_spec F hmem (hid ▸ hlive) hφ with h | ⟨ob₂, hob₂, hin⟩
        · have := hds _ (by rw [hk']; rfl)
          rw [h] at this; cases this
        · rw [hid, hob] at hob₂; cases hob₂
          exact hnk (by rw [enter_keys hlen']; exact hin)
    · obtain ⟨vals', _, hlen', rfl⟩ := enterOpt_spec he₁'
      intro k hk
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
      rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
      · rw [List.zip_map_left] at hx
        obtain ⟨⟨φ', v'⟩, hz, rfl⟩ := List.mem_map.mp hx
        exact defsOf_isSome (phi_def hobm (List.of_mem_zip hz).1)
      · exact hds k (by rw [he]; rfl)

/-- One output block against the input's run from a related state. -/
theorem block_fol {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx)
    {s' s : BState} (hR : CR O f f' s' s) :
    Fol (Qs o c O f f' s'.2.2) (stepBlock o c f' s'.1 s'.2.1 s'.2.2) (runFrom o c f s) := by
  obtain ⟨env', prev', b⟩ := s'
  obtain ⟨env, prev, b'⟩ := s
  obtain ⟨hbb, hes, hds, hbi, hprev⟩ := hR
  simp only at hbb hes hds hbi hprev ⊢
  subst hbb
  unfold stepBlock
  cases hob : f'.block? b with
  | none => exact Fol.stuck
  | some ob =>
  dsimp only
  have hobm := List.mem_of_find?_eq_some hob
  have hobid : ob.id = b := by simpa using List.find?_some hob
  obtain ⟨c0, rest, cmb, hc0, hlinks, hlast, _, hbody, hterm⟩ := blockOk_spec (F.blocks ob hobm)
  rw [CCtx.find_B, hobid] at hc0
  rw [hobid] at hlinks hlast hbody
  rw [runFrom_enter o c hc0]
  refine Fol.bind (Fol.approx (enter_rel hwf F hob hc0 (linksOk_live hlinks) hes hds hbi hprev)
    (Q := fun e₁' y => ∃ e₁, y = inRun o c f b c0 e₁ ∧ Mid O f f' e₁' e₁ b 0)
    fun a' a h => ⟨a, rfl, h⟩) ?_
  rintro e₁' _ ⟨e₁, rfl, hm⟩
  rw [hbody]
  have := chain_fol hwf F ho hoi c hobm rest b c0 hc0 hlinks cmb hlast hterm
    (fun s hs => by rw [hbody]; exact List.mem_map_of_mem hs) e₁' e₁ hm
  rwa [hobid] at this

theorem cfg_sim {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true)
    (F : CCFacts O f f') {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    Sim o c f' f (CR O f f') := by
  intro s' s hR I w' w hw
  have h := block_fol hwf F ho hoi c hR I w' w hw
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
      simp only [Qs] at hq
      subst hq
      exact ⟨w₁, by rw [hy, Fe.M.exec_pure], hw₁⟩

/-- A `cfg_cleanup` step is sound: the output function, its calls run by an oracle that
    approximates itself and returns integers on integers, approximates the well-formed input
    function on integers. -/
theorem cfgCleanup_sound {sig : Sigs} {syms : List String} {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {ids : Option (List (List Nat))} {s : FuncSnap}
    (hwf : f.wf sig syms = true) (h : checkCfgCleanup O f ids s = true) :
    FuncRef o c (some s.func) (some f) := by
  have F := checkCfgCleanup_facts h
  have sim := cfg_sim hwf F ho hoi c
  obtain ⟨e, e', he, he', hid⟩ := F.head
  intro args hargs
  unfold runFuncO
  dsimp only
  rw [he, he']
  dsimp only
  rw [F.params, hid]
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _)
    (Returns.and (entry_inv hwf F.valid he hargs) (returns_bind {} f.params args)))
    fun env env₀ ⟨e₁, hi, _, hfold⟩ => ?_
  cases e₁
  refine Sim.approx sim (env, none, e.id) (env, none, e.id)
    ⟨rfl, EnvSub.refl _, fun k hk => ?_, hi, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  rw [hfold] at hv
  rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
  · exact defsOf_isSome (param_def (F.params ▸ (List.of_mem_zip hx).1))
  · simp at he₀

end sound

theorem cfgCleanup_stepSound : StepSound .cfgCleanup :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    cfgCleanup_sound ho hoi c hw (by simp only [checkFunc, Bool.and_eq_true] at h; exact h.2)

end Fe.Sonatina.Steps
