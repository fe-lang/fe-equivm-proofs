import Fe.Sonatina.Steps.SchemasInv

/-!
# `sccp_fold` and `known_bits_simplify` (without demand rounds) are sound

The output has the input's blocks; the simulation (`RS`) relates the output and the input at
the same block entered from the same block, the output's environment binding less (`EnvSub`)
and only output values (`DomSub`).  Each side carries its own definedness invariant and L2
(`BlockInv`, `BlockPure`, on its own dominator tree), and the input the known bits (`KBHolds`),
SCCP's constants (`CHolds`) and, for `sccp_fold`, executability and the folded phis (`TPI`).

In a block the output's lines are the input's less the deleted ones (`BF`): a kept statement,
phi operand or terminator reads `σ v` where the input reads `v`, and the two have one value at
that point (`alias_use`), so they step together; a deleted statement steps on the input alone
(pure, total, its result no output value); a statement `sccp_fold` replaces by `is_zero`
computes the input's word by its schema.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-! ## Lemmas -/

theorem _root_.Fe.Sonatina.Inst.args_mapOps (g : Operand → Operand) (i : Inst) :
    (i.mapOps g).args = i.args.map g := by
  cases i <;> simp [Inst.mapOps, Inst.args]

theorem _root_.Fe.Sonatina.Term.succs_mapOps (g : Operand → Operand) (t : Fe.Sonatina.Term) :
    (t.mapOps g).succs = t.succs := by
  cases t <;> simp [Fe.Sonatina.Term.mapOps, Term.succs]

theorem inc_mapPhi (σ : NatMap Operand) (φ : Phi) (q : Nat) :
    inc (mapPhi σ φ) q = (inc φ q).map (subst σ) := by
  unfold inc mapPhi
  simp only [List.find?_map]
  rw [Option.map_map, Option.map_map]
  rfl

/-- Every tree ancestor of an edge's target is reachable, when those of its source are. -/
theorem ancReach_edge {g : Func} (hv : (domTree g).valid g = true) {p d : Nat}
    (hp : AncReach (domTree g) p) (hedge : Edge g p d) : AncReach (domTree g) d := by
  intro a ha
  rcases DomTree.anc_of_edge hv (hp p .refl) hedge ha with rfl | ha'
  · exact (DomTree.valid_edge hv (hp p .refl) hedge).1
  · exact hp a ha'

/-- At the entry, every tree ancestor is reachable. -/
theorem ancReach_entry {g : Func} (hv : (domTree g).valid g = true) {e : Block}
    (he : g.blocks.head? = some e) : AncReach (domTree g) e.id := by
  intro a ha
  rcases ha.inv with rfl | ⟨i, hi, _⟩
  · exact (DomTree.valid_entry hv he).1
  · rw [(DomTree.valid_entry hv he).2] at hi; cases hi

/-- A reachable block without an immediate dominator is the entry, which has no phis. -/
theorem phis_nil_of_root {g : Func} (hwf : g.wf sig syms = true) (hv : (domTree g).valid g = true)
    {b : Nat} {blk : Block} (hb : g.block? b = some blk)
    (hr : ((domTree g).reach.find? b).isSome = true) (hroot : (domTree g).idom.find? b = none) :
    blk.phis = [] := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  rcases hh : g.blocks.head? with _ | e
  · simp [DomTree.valid, hh] at hv
  have hv' := hv
  simp only [DomTree.valid, hh, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Option.isNone_iff_eq_none, beq_iff_eq] at hv'
  rcases hv'.1.2 blk hmem with h | ⟨h, _⟩
  · rw [hid, hr] at h; cases h
  rcases h with h | h
  · have hemem : e ∈ g.blocks := List.mem_of_mem_head? hh
    have := block?_of_mem (Func.wf_ids hwf) hemem
    rw [← h, hid, hb] at this
    cases this
    exact entry_phis hwf hh
  · rw [hid, hroot] at h; cases h

/-- The point at the end of the block a block state was entered from. -/
theorem sidePt_prev {g : Func} (hwf : g.wf sig syms = true) (hv : (domTree g).valid g = true)
    (hs : ssa g (domTree g) = true) {env : Env} {p b : Nat}
    (hi : BlockInv g (domTree g) (env, some p, b)) (hp : BlockPure g (domTree g) (env, some p, b))
    (hanc : AncReach (domTree g) p) {pblk : Block} (hpb : g.block? p = some pblk) :
    SidePt sig syms g env p pblk.body.length := by
  obtain ⟨hw, hpar, _, _, _, hdefs⟩ := hi
  refine ⟨hwf, hv, hs, ⟨pblk, hpb⟩, ⟨hw, fun v hd => ?_⟩, hp pblk hpb, hanc⟩
  rcases hd with hpv | ⟨blk', hb', hph | ⟨j, _, s', hs', hv'⟩⟩ | ⟨d, _, ha, hdef⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpv
    exact hpar q hq
  · exact hdefs p v .refl ⟨blk', hb', Or.inl hph⟩
  · exact hdefs p v .refl ⟨blk', hb', Or.inr ⟨s', List.mem_of_getElem? hs', hv'⟩⟩
  · exact hdefs d v ha hdef

/-- A phi's operand from a reachable predecessor dominates the end of the predecessor. -/
theorem domAt_of_phiUse {g : Func} (hwf : g.wf sig syms = true) {T : DomTree}
    {p : Nat} {pblk : Block} (hpb : g.block? p = some pblk) {v : Nat}
    (h : phiUseOk (defsOf g) T p (.var v) = true) : DomAt g T p pblk.body.length v := by
  rcases phiUseOk_sound (Func.wf_ids hwf) h with hp | ⟨d, ha, hdef⟩
  · exact Or.inl hp
  · by_cases hdp : d = p
    · subst hdp
      obtain ⟨blk', hb', hph | ⟨s', hs', hv'⟩⟩ := hdef
      · exact Or.inr (Or.inl ⟨blk', hb', Or.inl hph⟩)
      · rw [hpb] at hb'; cases hb'
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hs'
        exact Or.inr (Or.inl ⟨pblk, hpb, Or.inr ⟨j, (List.getElem?_eq_some_iff.mp hj).1, s', hj, hv'⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hdp, ha, hdef⟩)

/-- At the entry, the trivial-phi invariant has nothing to hold. -/
theorem tpi_root {f : Func} {X : StepCtx} (hwf : f.wf sig syms = true) (hv : (domTree f).valid f = true)
    {e : Block} (he : f.blocks.head? = some e) (env : Env) : TPI X f env e.id := by
  intro v x _ B hB ha
  have hBe : B = e.id := by
    rcases ha.inv with h | ⟨i, hi, _⟩
    · exact h
    · rw [(DomTree.valid_entry hv he).2] at hi; cases hi
  subst hBe
  rcases mem_defList hB with ⟨h, _⟩ | ⟨b', hb', φ, hφ, h, rfl⟩ | ⟨_, _, _, _, _, h, _⟩
  · cases h
  · have hemem : e ∈ f.blocks := List.mem_of_mem_head? he
    have h1 := block?_of_mem (Func.wf_ids hwf) hb'
    have h2 := block?_of_mem (Func.wf_ids hwf) hemem
    rw [Def.phi.inj h, h1] at h2
    cases h2
    rw [entry_phis hwf he] at hφ
    cases hφ
  · cases h

theorem enterOpt_nil {env : Env} {prev : Option Nat} {blk : Block} (h : blk.phis = []) :
    enterOpt env prev blk = some env := by
  simp [enterOpt, h]

/-- Entering a block whose kept phis read values equal to the input's: the output's environment
    still binds less, and only output values. -/
theorem enter_sub {f' : Func} {σ : NatMap Operand} {env' env : Env} (hsub : EnvSub env' env)
    (hds : DomSub f' env') {ib ob : Block} (hob : ob ∈ f'.blocks) {q : Nat}
    (hS : Sub (fun φ φ' => φ' = mapPhi σ φ ∧ ∀ o, inc φ q = some o → opVal env (subst σ o) = opVal env o)
      (fun φ => (defsOf f').find? φ.dst = none) ib.phis ob.phis)
    (hnd : (ib.phis.map (·.dst)).Nodup) {e₁' e₁ : Env} (he' : enterOpt env' (some q) ob = some e₁')
    (he : enterOpt env (some q) ib = some e₁) : EnvSub e₁' e₁ ∧ DomSub f' e₁' := by
  obtain ⟨vals', hF2', hlen', rfl⟩ := enterOpt_spec he'
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  refine ⟨fun k v hk => ?_, fun k hk => ?_⟩
  · rcases fold_get_cases _ _ _ _ hk with ⟨x, hx, hxk, hxv⟩ | ⟨henv, hkn⟩
    · obtain ⟨φ', hφ', hx1, hgv⟩ := zip_map_forall₂ hF2' hx
      obtain ⟨φ, hφ, rfl, hal⟩ := hS.mem_right φ' hφ'
      simp only [Option.bind_eq_bind, Option.bind_some] at hgv
      obtain ⟨o', hinc', hov'⟩ := Option.bind_eq_some_iff.mp hgv
      rw [inc_mapPhi] at hinc'
      obtain ⟨o, hinc, rfl⟩ := Option.map_eq_some_iff.mp hinc'
      have hov := (hal o hinc) ▸ hsub.opVal hov'
      obtain ⟨o2, v2, hinc2, hov2, hget⟩ := enter_val hF2 hlen hnd hφ
      rw [hinc] at hinc2
      cases hinc2
      rw [hov] at hov2
      cases hov2
      rw [← hxk, hx1, hxv, hx1]
      exact hget
    · rw [fold_get_not _ _ _ ?_]
      · exact hsub k v henv
      rw [enter_keys hlen]
      intro hkm
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hkm
      rcases hS.mem_left φ hφ with hdel | ⟨φ', hφ', rfl, _⟩
      · have := hds φ.dst (by rw [henv]; rfl)
        rw [hdel] at this; cases this
      · apply hkn
        rw [enter_keys hlen']
        exact List.mem_map.mpr ⟨_, hφ', rfl⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, hxk, _⟩ | ⟨henv, _⟩
    · obtain ⟨φ', hφ', hx1, _⟩ := zip_map_forall₂ hF2' hx
      rw [← hxk, hx1]
      exact defsOf_isSome (phi_def hob hφ')
    · exact hds k (by rw [henv]; rfl)

/-- A pure instruction's statement other than `clz` runs to its word. -/
theorem runStmtO_pure_of {o : Oracle} {c : Ctx} {env : Env} {st : Stmt} {p : PureInst}
    (hp : pureInst? st.inst = some p) (hc : noClz p = true) {xs : List Nat}
    (hargs : ArgsAre env p.args xs) : runStmtO o c env st = pure [.int p.bits (p.evalOn xs)] := by
  have hrun : runStmtO o c env st = runInst c env st.inst := by
    unfold runStmtO
    split
    · next heq => rw [heq] at hp; simp [pureInst?] at hp
    · rfl
  rw [hrun, ← pureInst?_toInst hp]
  exact Schemas.runInst_pure (noClz_ne hc) hargs

theorem returns_pure_val {α : Type} {P : α → Prop} {a : α} {x : FeM α} (hx : x = pure a)
    (h : Returns P x) : P a :=
  h default someWorld a someWorld (by rw [hx]; rfl)

/-! ## The simulation -/

section sim

variable {m : Mode} {f : Func} {s : FuncSnap} {F : StepFacts} {pairs : List (Line × Line)}
  {deleted : List Line} {σ : NatMap Operand}

/-- What the simulation uses: the check's facts, the input well formed, SCCP's facts in
    `sccp_fold`. -/
structure SF (sig : Sigs) (syms : List String) (m : Mode) (f : Func) (s : FuncSnap)
    (F : StepFacts) (pairs : List (Line × Line)) (deleted : List Line) (σ : NatMap Operand) :
    Prop where
  A : AF m f s F pairs deleted σ
  wf : f.wf sig syms = true
  mode : m = .exact ∨ m = .sccp
  sccp : m = .sccp → SccpSpec f (ctxOf m f s F)

variable (Sf : SF sig syms m f s F pairs deleted σ)
include Sf

theorem SF.hv : (domTree f).valid f = true := by
  have := Sf.A.ssaIn; simp only [ssaOk, Bool.and_eq_true] at this; exact this.1

theorem SF.hs : ssa f (domTree f) = true := by
  have := Sf.A.ssaIn; simp only [ssaOk, Bool.and_eq_true] at this; exact this.2

theorem SF.hv' : (domTree s.func).valid s.func = true := by
  have := Sf.A.ssaOut; simp only [ssaOk, Bool.and_eq_true] at this; exact this.1

theorem SF.hs' : ssa s.func (domTree s.func) = true := by
  have := Sf.A.ssaOut; simp only [ssaOk, Bool.and_eq_true] at this; exact this.2

theorem SF.wf' : s.func.wf sig syms = true := Sf.A.wf' Sf.wf

theorem SF.cs_empty (h : m ≠ .sccp) : (ctxOf m f s F).cs = .empty := by
  rcases Sf.mode with rfl | rfl
  · rfl
  · exact absurd rfl h

omit Sf in
/-- The input's invariants at point `(b, k)`. -/
structure InPt (sig : Sigs) (syms : List String) (m : Mode) (f : Func) (s : FuncSnap)
    (F : StepFacts) (e : Env) (b k : Nat) : Prop where
  side : SidePt sig syms f e b k
  kb : KBHolds (ctxOf m f s F).K e
  cs : CHolds (ctxOf m f s F).cs e
  sc : m = .sccp → ((ctxOf m f s F).E.find? b).isSome = true ∧ TPI (ctxOf m f s F) f e b

omit Sf in
/-- The relation at a point: the input at `(b, k)`, the output at `(b, k')`. -/
def Mid (sig : Sigs) (syms : List String) (m : Mode) (f : Func) (s : FuncSnap) (F : StepFacts)
    (e' e : Env) (b k k' : Nat) : Prop :=
  EnvSub e' e ∧ DomSub s.func e' ∧ InPt sig syms m f s F e b k ∧ SidePt sig syms s.func e' b k'

/-- An operand a kept statement reads has one value on both sides. -/
theorem SF.stmt_alias {e' e : Env} {b k k' : Nat} (hm : Mid sig syms m f s F e' e b k k') (c : Ctx)
    {ib ob : Block} (hib : f.block? b = some ib) (hob : s.func.block? b = some ob) {st : Stmt}
    (hst : ib.body[k]? = some st) (hst' : ob.body[k']? = some (st.mapOps (subst σ)))
    (hp : (Line.stmt st, Line.stmt (st.mapOps (subst σ))) ∈ pairs) :
    ∀ a ∈ st.inst.args, opVal e (subst σ a) = opVal e a := by
  obtain ⟨hes, _, H, H'⟩ := hm
  have hobm := List.mem_of_find?_eq_some hob
  intro a ha
  have ha' : subst σ a ∈ (st.mapOps (subst σ)).inst.args := by
    simp only [Stmt.mapOps, Inst.args_mapOps]; exact List.mem_map_of_mem ha
  refine alias_use Sf.A Sf.mode H.side H' hes c H.kb H.cs (fun h => (H.sc h).2)
    (fun v hv => ?_) ((opsWf_block Sf.A.opsWf' hobm).2.1 _ (List.mem_of_getElem? hst') _ ha')
    (fun w hw => ?_) (fun v x hv hx => Sf.A.keys _ hp v (hv ▸ ha) x hx)
  · subst hv; exact stmt_operand Sf.wf Sf.hs hib H.side.reach hst ha
  · exact stmt_operand Sf.wf' Sf.hs' hob H'.reach hst' (hw ▸ ha')

/-- A statement keeps the input's invariants. -/
theorem SF.in_step {e : Env} {b k : Nat} (H : InPt sig syms m f s F e b k) (c : Ctx) {ib : Block}
    (hib : f.block? b = some ib) {st : Stmt} (hst : ib.body[k]? = some st) {vals : List Val}
    (hiv : IntVals vals) (hpv : st.inst.pure = true → pureVals e st.inst = some vals)
    (hl : st.dsts.length = vals.length)
    (hkb : KBHolds (ctxOf m f s F).K ((st.dsts.zip vals).foldl bindStep e)) :
    InPt sig syms m f s F ((st.dsts.zip vals).foldl bindStep e) b (k + 1) := by
  refine ⟨⟨Sf.wf, Sf.hv, Sf.hs, H.side.blk, point_succ' Sf.wf hib hst H.side.pi hiv hl,
    pureInv_stmt Sf.wf Sf.hv Sf.hs hib H.side.reach hst H.side.pu hpv hl, H.side.anc⟩, hkb,
    ?_, fun h => ⟨(H.sc h).1, tpi_stmt rfl rfl Sf.hv Sf.hs hib H.side.reach hst (H.sc h).2 _
      fun y hy => (List.of_mem_zip hy).1⟩⟩
  by_cases hms : m = .sccp
  · exact cholds_stmt rfl rfl (Sf.sccp hms) H.side c H.kb H.cs (H.sc hms).1 hib hst hpv hl
  · rw [Sf.cs_empty hms]; exact cholds_empty _

omit Sf in
/-- A statement keeps a side's invariants. -/
theorem SidePt.step {g : Func} {e : Env} {b k : Nat} (H : SidePt sig syms g e b k) {blk : Block}
    (hb : g.block? b = some blk) {st : Stmt} (hst : blk.body[k]? = some st) {vals : List Val}
    (hiv : IntVals vals) (hpv : st.inst.pure = true → pureVals e st.inst = some vals)
    (hl : st.dsts.length = vals.length) :
    SidePt sig syms g ((st.dsts.zip vals).foldl bindStep e) b (k + 1) :=
  ⟨H.wf, H.valid, H.ssa, H.blk, point_succ' H.wf hb hst H.pi hiv hl,
    pureInv_stmt H.wf H.valid H.ssa hb H.reach hst H.pu hpv hl, H.anc⟩

omit Sf in
theorem domSub_step {f' : Func} {e' : Env} (hds : DomSub f' e') {ob : Block} (hob : ob ∈ f'.blocks)
    {st : Stmt} (hst : st ∈ ob.body) (vals : List Val) :
    DomSub f' ((st.dsts.zip vals).foldl bindStep e') := fun k hk => by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
  · exact out_stmt_def hob hst (List.of_mem_zip hx).1
  · exact hds k (by rw [he]; rfl)

/-- A kept statement against the input's. -/
theorem SF.keep_fol {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {b : Nat}
    {ib ob : Block} (hib : f.block? b = some ib) (hob : s.func.block? b = some ob)
    {Q : Env → FeM (List Val) → Prop} {K : Env → FeM (List Val)} {is os : List Stmt}
    {st : Stmt} {k k' : Nat} {e' e : Env} (hsk : ib.body[k]? = some st)
    (hsk' : ob.body[k']? = some (st.mapOps (subst σ)))
    (hp : (Line.stmt st, Line.stmt (st.mapOps (subst σ))) ∈ pairs)
    (hm : Mid sig syms m f s F e' e b k k')
    (ih : ∀ e₁' e₁, Mid sig syms m f s F e₁' e₁ b (k + 1) (k' + 1) →
      Fol Q (runBodyO o c e₁' os) (runBodyO o c e₁ is >>= K)) :
    Fol Q (runBodyO o c e' (st.mapOps (subst σ) :: os)) (runBodyO o c e (st :: is) >>= K) := by
  have hal := Sf.stmt_alias hm c hib hob hsk hsk' hp
  obtain ⟨hes, hds, H, H'⟩ := hm
  have hobm := List.mem_of_find?_eq_some hob
  have hsob := List.mem_of_getElem? hsk'
  have hmach : st.inst.machine = true :=
    Func.machine_block (Func.wf_machine Sf.wf) hib st (List.mem_of_getElem? hsk)
  have hmach' : (st.mapOps (subst σ)).inst.machine = true :=
    Func.machine_block Sf.A.machine' hob _ hsob
  have happ : Approx Eq (runStmtO o c e' (st.mapOps (subst σ))) (runStmtO o c e st) := by
    rw [← runStmtO_mapOps o c st hal]
    exact Approx.runStmtO_sub ho hes H.side.pi.1.int _ hmach'
  simp only [runBodyO, bind_assoc]
  refine Fol.bind (Fol.strengthen (Fol.approx (Approx.strengthen happ
      (Returns.and (returns_runStmtO_pure hoi c H.side.pi.1.int hmach)
        (kb_stmt_step Sf.wf Sf.hs Sf.A.kb hib H.side.reach hsk H.side.pi H.kb)))
      (Q := fun vals y => (IntVals vals ∧ (st.inst.pure = true → pureVals e st.inst = some vals)) ∧
        (st.dsts.length = vals.length → KBHolds (ctxOf m f s F).K ((st.dsts.zip vals).foldl bindStep e)) ∧
        y = (Fe.Sonatina.bind e st.dsts vals >>= fun e₁ => runBodyO o c e₁ is >>= K))
      fun a' a ⟨h1, h2⟩ => ⟨h1 ▸ h2.1, h1 ▸ h2.2, h1 ▸ rfl⟩)
    (returns_runStmtO_pure hoi c H'.pi.1.int hmach')) ?_
  rintro vals y ⟨⟨⟨hiv, hpv⟩, hkbv, rfl⟩, ⟨_, hpv'⟩⟩
  refine Fol.bind (Fol.approx (bind_rel e' e st.dsts vals)
    (Q := fun e₁' y₂ => ∃ e₁, y₂ = (runBodyO o c e₁ is >>= K) ∧
      Mid sig syms m f s F e₁' e₁ b (k + 1) (k' + 1))
    fun a' a ⟨hl, h1, h2⟩ => ⟨a, rfl, ?_⟩) ?_
  · subst h1 h2
    exact ⟨EnvSub.fold hes _, domSub_step hds hobm hsob vals,
      Sf.in_step H c hib hsk hiv hpv hl (hkbv hl), H'.step hob hsk' hiv hpv' hl⟩
  · rintro e₁' y₂ ⟨e₁, rfl, hm₁⟩
    exact ih e₁' e₁ hm₁

/-- A deleted statement: the input steps alone. -/
theorem SF.del_fol {o : Oracle} (c : Ctx) {b : Nat} {ib : Block} (hib : f.block? b = some ib)
    {Q : Env → FeM (List Val) → Prop} {K : Env → FeM (List Val)} {is os : List Stmt}
    {st : Stmt} {k k' : Nat} {e' e : Env} (hsk : ib.body[k]? = some st)
    (hdel : Line.stmt st ∈ deleted) (hm : Mid sig syms m f s F e' e b k k')
    (ih : ∀ e₁, Mid sig syms m f s F e' e₁ b (k + 1) k' →
      Fol Q (runBodyO o c e' os) (runBodyO o c e₁ is >>= K)) :
    Fol Q (runBodyO o c e' os) (runBodyO o c e (st :: is) >>= K) := by
  obtain ⟨hes, hds, H, H'⟩ := hm
  have hd := Sf.A.deletable _ hdel
  simp only [Schemas.deletable, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨hlen, hd⟩ := hd
  rcases hp : pureInst? st.inst with _ | p
  · rw [hp] at hd; cases hd
  have hc : noClz p = true := by
    rw [hp] at hd
    rcases p with ⟨o1, a⟩ | _ | _
    · cases o1 <;> simp_all [noClz]
    · rfl
    · rfl
  have hmem := List.mem_of_find?_eq_some hib
  have hsm := List.mem_of_getElem? hsk
  obtain ⟨xs, hargs, _⟩ := termOf_ok (ε := e) (e := e)
    (G := unfold (.ofListBy (·.id) f.blocks) (defsOf f) (ctxOf m f s F).cs 0) (p := p) fun a ha => by
      have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
      exact H.side.unfold_sound (EnvSub.refl e) c H.cs 0 a ((Func.wf_operands Sf.wf hmem).2.1 st hsm a ha')
        fun w hw => by subst hw; exact stmt_operand Sf.wf Sf.hs hib H.side.reach hsk ha'
  have hrun := runStmtO_pure_of (o := o) (c := c) hp hc hargs
  have hbind : Fe.Sonatina.bind e st.dsts [.int p.bits (p.evalOn xs)] =
      pure ((st.dsts.zip [.int p.bits (p.evalOn xs)]).foldl bindStep e) := by
    unfold Fe.Sonatina.bind
    rw [hlen]
    simp only [List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte]
    rfl
  simp only [runBodyO, hrun, pure_bind, hbind]
  have hpv : st.inst.pure = true → pureVals e st.inst = some [.int p.bits (p.evalOn xs)] :=
    fun _ => pureVals_of (c := c) hp hc hargs
  have hkb := returns_pure_val (runStmtO_pure_of (o := o) (c := c) hp hc hargs)
    (kb_stmt_step Sf.wf Sf.hs Sf.A.kb hib H.side.reach hsk H.side.pi H.kb (o := o) (c := c))
  refine ih _ ⟨fun x v hx => ?_, hds, Sf.in_step H c hib hsk (by simp [IntVals, Val.isInt]) hpv
    (by rw [hlen]; rfl) (hkb (by rw [hlen]; rfl)), H'⟩
  rw [fold_get_not _ _ _ ?_]
  · exact hes x v hx
  intro hxm
  have hxd : x ∈ st.dsts.map (·.1) := by
    have : (st.dsts.zip [Val.int p.bits (p.evalOn xs)]).map (·.1.1) ⊆ st.dsts.map (·.1) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact List.mem_map_of_mem (List.of_mem_zip hz).1
    exact this hxm
  have hfr := Sf.A.fresh x (List.mem_flatMap.mpr ⟨_, hdel, hxd⟩)
  have := hds x (by rw [hx]; rfl)
  rw [hfr] at this; cases this

omit Sf in
theorem envSub_bind1 {e' e : Env} (h : EnvSub e' e) (d : Nat × Ty) {v' v : Val}
    (hv : v'.as d.2 = v.as d.2) :
    EnvSub (([d].zip [v']).foldl bindStep e') (([d].zip [v]).foldl bindStep e) := by
  intro k w hk
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, bindStep,
    env_insert_get] at hk ⊢
  split at hk
  · rw [if_pos ‹_›, ← hv]; exact hk
  · rw [if_neg ‹_›]; exact h k w hk

/-- A statement `sccp_fold` replaces in place by `is_zero`: its schema gives the input's word. -/
theorem SF.repl_fol {o : Oracle} (c : Ctx) {b : Nat} {ib ob : Block} (hib : f.block? b = some ib)
    (hob : s.func.block? b = some ob) {Q : Env → FeM (List Val) → Prop} {K : Env → FeM (List Val)}
    {is os : List Stmt} {st st' : Stmt} {k k' : Nat} {e' e : Env} (hsk : ib.body[k]? = some st)
    (hsk' : ob.body[k']? = some st') (hr : replaceOk (ctxOf m f s F) st st' = true)
    (hm : Mid sig syms m f s F e' e b k k')
    (ih : ∀ e₁' e₁, Mid sig syms m f s F e₁' e₁ b (k + 1) (k' + 1) →
      Fol Q (runBodyO o c e₁' os) (runBodyO o c e₁ is >>= K)) :
    Fol Q (runBodyO o c e' (st' :: os)) (runBodyO o c e (st :: is) >>= K) := by
  obtain ⟨hes, hds, H, H'⟩ := hm
  obtain ⟨hdsts, ⟨x, hx⟩, dd, _, t, t', ht, ht', hce⟩ := replaceOk_spec hr
  have hmem := List.mem_of_find?_eq_some hib
  have hsm := List.mem_of_getElem? hsk
  have hobm := List.mem_of_find?_eq_some hob
  have hsm' := List.mem_of_getElem? hsk'
  -- the input's statement and its term
  unfold instTerm at ht
  rcases hp : pureInst? st.inst with _ | p
  · rw [hp] at ht; cases ht
  rw [hp] at ht
  by_cases hc : noClz p = true
  swap
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at ht
  simp only [hc, ↓reduceIte, Option.some.injEq] at ht
  subst ht
  obtain ⟨xs, hargs, hok⟩ := termOf_ok (ε := e) (e := e)
    (G := unfold (.ofListBy (·.id) f.blocks) (defsOf f) (ctxOf m f s F).cs dd.1) (p := p) fun a ha => by
      have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
      exact H.side.unfold_sound (EnvSub.refl e) c H.cs dd.1 a ((Func.wf_operands Sf.wf hmem).2.1 st hsm a ha')
        fun w hw => by subst hw; exact stmt_operand Sf.wf Sf.hs hib H.side.reach hsk ha'
  -- the output's `is_zero` and its term
  have hp' : pureInst? st'.inst = some (.op1 .isZero x) := by rw [hx]; rfl
  have hxa : x ∈ st'.inst.args := by rw [hx]; exact List.mem_singleton_self _
  rw [hx] at ht'
  simp only [instTerm, pureInst?, noClz, ↓reduceIte, Option.some.injEq] at ht'
  subst ht'
  obtain ⟨xs', hargs', hok'⟩ := termOf_ok (ε := e') (e := e)
    (G := unfold (.ofListBy (·.id) s.func.blocks) (defsOf s.func) (ctxOf m f s F).cs dd.2)
    (p := .op1 .isZero x) fun a ha => by
      simp only [PureInst.args, List.mem_singleton] at ha
      subst ha
      exact H'.unfold_sound hes c H.cs dd.2 _ ((opsWf_block Sf.A.opsWf' hobm).2.1 st' hsm' _ hxa)
        fun w hw => by subst hw; exact stmt_operand Sf.wf' Sf.hs' hob H'.reach hsk' hxa
  have hf : FactsOn (kbOf (ctxOf m f s F).K) (envWord e)
      [termOf (unfold (.ofListBy (·.id) f.blocks) (defsOf f) (ctxOf m f s F).cs dd.1) p,
        termOf (unfold (.ofListBy (·.id) s.func.blocks) (defsOf s.func) (ctxOf m f s F).cs dd.2)
          (.op1 .isZero x)] := factsOn_env H.kb fun a ha => by
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · exact hok.2 a ha
    · exact hok'.2 a ha
  have heq : (termOf (unfold (.ofListBy (·.id) f.blocks) (defsOf f) (ctxOf m f s F).cs dd.1) p).eval
      (envWord e) = (termOf (unfold (.ofListBy (·.id) s.func.blocks) (defsOf s.func)
        (ctxOf m f s F).cs dd.2) (.op1 .isZero x)).eval (envWord e) := checkExact_sound hce hf
  rw [hok.1, hok'.1] at heq
  -- both run, to the same word
  have hrun := runStmtO_pure_of (o := o) (c := c) hp hc hargs
  have hrun' := runStmtO_pure_of (o := o) (c := c) hp' rfl hargs'
  simp only [runBodyO, hrun, hrun', pure_bind, bind_assoc]
  rw [← hdsts]
  by_cases hl : st.dsts.length = 1
  · match hd : st.dsts, hl with
    | [d1], _ =>
      have hb1 : ∀ (env : Env) (v : Val), Fe.Sonatina.bind env [d1] [v] =
          pure (([d1].zip [v]).foldl bindStep env) := fun env v => by
        unfold Fe.Sonatina.bind
        simp only [List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte]
        rfl
      rw [hb1, hb1, pure_bind, pure_bind]
      have hty : d1.2 = .int 256 :=
        ((Func.wf_words Sf.wf).2 ib hmem).2 st hsm d1 (by rw [hd]; exact List.mem_singleton_self _)
      have hlt := evalOn_lt' hargs
      have hlt' := evalOn_lt' hargs'
      refine ih _ _ ⟨envSub_bind1 hes d1 (by rw [hty, Val.as_word hlt, Val.as_word hlt', heq]), ?_,
        ?_, ?_⟩
      · have := domSub_step hds hobm hsm' [Val.int (PureInst.op1 .isZero x).bits
          ((PureInst.op1 .isZero x).evalOn xs')]
        rwa [← hdsts, hd] at this
      · have := Sf.in_step H c hib hsk (vals := [.int p.bits (p.evalOn xs)])
          (by simp [IntVals, Val.isInt]) (fun _ => pureVals_of (c := c) hp hc hargs) (by rw [hd]; rfl)
          (by
            have := returns_pure_val hrun
              (kb_stmt_step Sf.wf Sf.hs Sf.A.kb hib H.side.reach hsk H.side.pi H.kb (o := o) (c := c))
            exact this (by rw [hd]; rfl))
        rwa [hd] at this
      · have := H'.step hob hsk' (vals := [.int (PureInst.op1 .isZero x).bits
          ((PureInst.op1 .isZero x).evalOn xs')]) (by simp [IntVals, Val.isInt])
          (fun _ => pureVals_of (c := c) hp' rfl hargs') (by rw [← hdsts, hd]; rfl)
        rwa [← hdsts, hd] at this
  · have hb0 : ∀ (env : Env) (v : Val), Fe.Sonatina.bind env st.dsts [v] = stuck := fun env v => by
      unfold Fe.Sonatina.bind
      have : (st.dsts.length == [v].length) = false := by simpa using hl
      rw [this]; rfl
    rw [hb0]
    exact Fol.bind (Q := fun _ _ => False) Fol.stuck fun _ _ h => h.elim

omit Sf in
theorem drop_cons_spec {α : Type} {l rest : List α} {a : α} {k : Nat} (h : l.drop k = a :: rest) :
    k < l.length ∧ l[k]? = some a ∧ l.drop (k + 1) = rest := by
  have hlt : k < l.length := by
    rcases Nat.lt_or_ge k l.length with h' | h'
    · exact h'
    · rw [List.drop_eq_nil_of_le h'] at h; cases h
  rw [List.drop_eq_getElem_cons hlt] at h
  simp only [List.cons.injEq] at h
  exact ⟨hlt, by rw [List.getElem?_eq_getElem hlt, h.1], h.2⟩

/-- An output block's statements against the input block's, from points `k` and `k'`. -/
theorem SF.body_fol {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {b : Nat}
    {ib ob : Block} (hib : f.block? b = some ib) (hob : s.func.block? b = some ob)
    (K : Env → FeM (List Val)) :
    ∀ {is os : List Stmt}, Sub (fun st st' => (Line.stmt st, Line.stmt st') ∈ pairs)
      (fun st => Line.stmt st ∈ deleted) is os →
    ∀ (k k' : Nat) (e' e : Env), ib.body.drop k = is → ob.body.drop k' = os →
      k ≤ ib.body.length → k' ≤ ob.body.length → Mid sig syms m f s F e' e b k k' →
      Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ Mid sig syms m f s F e₂' e₂ b ib.body.length ob.body.length)
        (runBodyO o c e' os) (runBodyO o c e is >>= K)
  | _, _, .nil, k, k', e', e, hd, hd', hk, hk', hm => by
    have h1 : k = ib.body.length := by have := List.drop_eq_nil_iff.mp hd; omega
    have h2 : k' = ob.body.length := by have := List.drop_eq_nil_iff.mp hd'; omega
    subst h1 h2
    simp only [runBodyO, pure_bind]
    exact Fol.pure ⟨e, rfl, hm⟩
  | _, _, .keep (a := st) (b := st') hp hS, k, k', e', e, hd, hd', _, _, hm => by
    obtain ⟨hlt, hsk, hdk⟩ := drop_cons_spec hd
    obtain ⟨hlt', hsk', hdk'⟩ := drop_cons_spec hd'
    rcases Sf.A.stmt hp with rfl | ⟨_, hr⟩
    · exact Sf.keep_fol ho hoi c hib hob hsk hsk' hp hm fun e₁' e₁ hm₁ =>
        SF.body_fol ho hoi c hib hob K hS (k + 1) (k' + 1) e₁' e₁ hdk hdk' (by omega) (by omega) hm₁
    · exact Sf.repl_fol c hib hob hsk hsk' hr hm fun e₁' e₁ hm₁ =>
        SF.body_fol ho hoi c hib hob K hS (k + 1) (k' + 1) e₁' e₁ hdk hdk' (by omega) (by omega) hm₁
  | _, _, .drop (a := st) hdel hS, k, k', e', e, hd, hd', _, hk', hm => by
    obtain ⟨hlt, hsk, hdk⟩ := drop_cons_spec hd
    exact Sf.del_fol c hib hsk hdel hm fun e₁ hm₁ =>
      SF.body_fol ho hoi c hib hob K hS (k + 1) k' e' e₁ hdk hd' (by omega) hk' hm₁

omit Sf in
/-- The simulation: the same block entered from the same block, with both sides' invariants. -/
def RS (m : Mode) (f : Func) (s : FuncSnap) (F : StepFacts) (s' s0 : BState) : Prop :=
  s'.2 = s0.2 ∧ EnvSub s'.1 s0.1 ∧ DomSub s.func s'.1 ∧
  BlockInv f (domTree f) s0 ∧ BlockPure f (domTree f) s0 ∧ KBHolds (ctxOf m f s F).K s0.1 ∧
  CHolds (ctxOf m f s F).cs s0.1 ∧ AncReach (domTree f) s0.2.2 ∧
  BlockInv s.func (domTree s.func) s' ∧ BlockPure s.func (domTree s.func) s' ∧
  AncReach (domTree s.func) s0.2.2 ∧
  (∀ p, s0.2.1 = some p → AncReach (domTree f) p ∧ AncReach (domTree s.func) p ∧
    (m = .sccp → edgeExec (ctxOf m f s F).inB (ctxOf m f s F).E (ctxOf m f s F).dead p s0.2.2 = true ∧
      TPI (ctxOf m f s F) f s0.1 p)) ∧
  (m = .sccp → ((ctxOf m f s F).E.find? s0.2.2).isSome = true)

omit Sf in
theorem Sub.mono_mem {α β : Type} {K K' : α → β → Prop} {Dl Dl' : α → Prop} :
    ∀ {l : List α} {l' : List β}, (∀ a ∈ l, ∀ b ∈ l', K a b → K' a b) → (∀ a ∈ l, Dl a → Dl' a) →
      Sub K Dl l l' → Sub K' Dl' l l'
  | _, _, _, _, .nil => .nil
  | _, _, hK, hD, .keep h hs => .keep (hK _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) h)
      (Sub.mono_mem (fun a ha b hb => hK a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        (fun a ha => hD a (List.mem_cons_of_mem _ ha)) hs)
  | _, _, hK, hD, .drop h hs => .drop (hD _ (List.mem_cons_self ..) h)
      (Sub.mono_mem (fun a ha b hb => hK a (List.mem_cons_of_mem _ ha) b hb)
        (fun a ha => hD a (List.mem_cons_of_mem _ ha)) hs)

omit Sf in
theorem Sub.nil_left {α β : Type} {K : α → β → Prop} {Dl : α → Prop} :
    ∀ {l' : List β}, Sub K Dl [] l' → l' = []
  | _, .nil => rfl

omit Sf in
/-- A reachable block without an immediate dominator is the entry. -/
theorem root_is_entry {g : Func} (hv : (domTree g).valid g = true) {b : Nat} {blk : Block}
    (hb : g.block? b = some blk) (hr : ((domTree g).reach.find? b).isSome = true)
    (hroot : (domTree g).idom.find? b = none) : ∃ e, g.blocks.head? = some e ∧ b = e.id := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  cases h0 : g.blocks.head? with
  | none => rw [List.head?_eq_none_iff] at h0; rw [h0] at hmem; cases hmem
  | some e0 =>
    refine ⟨e0, rfl, ?_⟩
    have hv' := hv
    simp only [DomTree.valid, h0, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Option.isNone_iff_eq_none, beq_iff_eq] at hv'
    rcases hv'.1.2 blk hmem with h1 | ⟨h1 | h1, _⟩
    · rw [hid, hr] at h1; cases h1
    · rw [← hid, h1]
    · rw [hid, hroot] at h1; cases h1

/-- Entering the block of a related state. -/
theorem SF.enter_approx {env' env : Env} {prev : Option Nat} {b : Nat}
    (hR : RS m f s F (env', prev, b) (env, prev, b)) (c : Ctx) {ib ob : Block}
    (hib : f.block? b = some ib) (hob : s.func.block? b = some ob) (B : BF pairs deleted ib ob) :
    Approx (fun e₁' e₁ => Mid sig syms m f s F e₁' e₁ b 0 0) (enter env' prev ob) (enter env prev ib) := by
  obtain ⟨_, hes, hds, hbi, hbp, hkb, hcs, hanc, hbi', hbp', hanc', hprev, hexb⟩ := hR
  simp only at hes hds hbi hbp hkb hcs hanc hbi' hbp' hanc' hprev hexb
  have hmem := List.mem_of_find?_eq_some hib
  have hobm := List.mem_of_find?_eq_some hob
  have hid : ib.id = b := by simpa using List.find?_some hib
  have hid' : ob.id = b := by simpa using List.find?_some hob
  have hU := UniqueDefs.of_ssa Sf.hs
  rw [enter_eq, enter_eq]
  refine Approx.lift fun e₁' he₁' => ?_
  -- the input enters, and the output binds less
  obtain ⟨e₁, he₁, hes₁, hds₁, hcs₁, htpi₁⟩ : ∃ e₁, enterOpt env prev ib = some e₁ ∧
      EnvSub e₁' e₁ ∧ DomSub s.func e₁' ∧ CHolds (ctxOf m f s F).cs e₁ ∧
      (m = .sccp → TPI (ctxOf m f s F) f e₁ b) := by
    cases prev with
    | none =>
      have hph := phis_nil_of_root Sf.wf Sf.hv hib hbi.2.2.1 hbi.2.2.2
      have hph' : ob.phis = [] := by
        have := B.phis; rw [hph] at this; exact this.nil_left
      rw [enterOpt_nil hph'] at he₁'
      cases he₁'
      refine ⟨env, enterOpt_nil hph, hes, hds, hcs, fun _ => ?_⟩
      obtain ⟨e0, he0, rfl⟩ := root_is_entry Sf.hv hib hbi.2.2.1 hbi.2.2.2
      exact tpi_root Sf.wf Sf.hv he0 env
    | some q =>
      obtain ⟨e₁, he₁⟩ := enter_total Sf.wf Sf.hs hbi hib
      obtain ⟨hancq, hancq', hsq⟩ := hprev q rfl
      have hqr := hbi.2.2.2.1
      obtain ⟨qblk, hqb, _⟩ := hbi.2.2.2.2.1
      have hqr' := hbi'.2.2.2.1
      obtain ⟨qblk', hqb', _⟩ := hbi'.2.2.2.2.1
      have SP := sidePt_prev Sf.wf Sf.hv Sf.hs hbi hbp hancq hqb
      have SP' := sidePt_prev Sf.wf' Sf.hv' Sf.hs' hbi' hbp' hancq' hqb'
      have hssa := (ssa_block Sf.hs hmem (hid ▸ hbi.2.2.1)).1
      have hssa' := (ssa_block Sf.hs' hobm (hid' ▸ hbi'.2.2.1)).1
      have hS : Sub (fun φ φ' => φ' = mapPhi σ φ ∧ ∀ o, inc φ q = some o →
          opVal env (subst σ o) = opVal env o) (fun φ => (defsOf s.func).find? φ.dst = none)
          ib.phis ob.phis := by
        refine Sub.mono_mem (fun φ hφ φ' hφ' hp => ⟨Sf.A.phi hp, fun o hinc => ?_⟩)
          (fun φ _ hd => Sf.A.fresh _ (List.mem_flatMap.mpr ⟨_, hd, List.mem_singleton_self _⟩))
          B.phis
        have hφe := Sf.A.phi hp
        have hin := inc_mem hinc
        have hin' : (subst σ o, q) ∈ φ'.incoming := by
          rw [hφe]; exact List.mem_map.mpr ⟨(o, q), hin, rfl⟩
        exact alias_use Sf.A Sf.mode SP SP' hes c hkb hcs (fun h => (hsq h).2)
          (fun v hv => domAt_of_phiUse Sf.wf hqb (hv ▸ hssa φ hφ _ hin hqr))
          ((opsWf_block Sf.A.opsWf' hobm).1 φ' hφ' _ hin')
          (fun w hw => domAt_of_phiUse Sf.wf' hqb' (hw ▸ hssa' φ' hφ' _ hin' hqr'))
          (fun v x hv hx => Sf.A.keys _ hp v (by
            simp only [lineOps]; exact List.mem_map.mpr ⟨(o, q), hin, by rw [hv]⟩) x hx)
      obtain ⟨hs₁, hd₁⟩ := enter_sub hes hds hobm hS (hU.phis hmem) he₁' he₁
      refine ⟨e₁, he₁, hs₁, hd₁, ?_, fun h => ?_⟩
      · by_cases hms : m = .sccp
        · exact cholds_enter rfl rfl (Sf.sccp hms) Sf.wf Sf.hs hbi.1 hcs (hexb hms) (hsq hms).1 hib he₁
        · rw [Sf.cs_empty hms]; exact cholds_empty _
      · exact tpi_enter rfl rfl rfl Sf.wf Sf.hv Sf.hs hbi (hsq h).2 (hsq h).1 hib he₁
  refine ⟨e₁, he₁, hes₁, hds₁, ⟨⟨Sf.wf, Sf.hv, Sf.hs, ⟨ib, hib⟩,
      returns_lift_some (P := PointInv f (domTree f) b 0)
        (by rw [← he₁, ← enter_eq]; exact point_zero Sf.wf Sf.hv hbi hib),
      returns_lift_some (P := PureInv f (domTree f) b 0)
        (by rw [← he₁, ← enter_eq]; exact pureInv_enter Sf.wf Sf.hv Sf.hs hbi hbp hib), hanc⟩,
    returns_lift_some (P := KBHolds (ctxOf m f s F).K)
      (by rw [← he₁, ← enter_eq]; exact kb_enter Sf.wf Sf.hs Sf.A.kb hbi.1 hkb hib),
    hcs₁, fun h => ⟨hexb h, htpi₁ h⟩⟩, ⟨Sf.wf', Sf.hv', Sf.hs', ⟨ob, hob⟩,
      returns_lift_some (P := PointInv s.func (domTree s.func) b 0)
        (by rw [← he₁', ← enter_eq]; exact point_zero Sf.wf' Sf.hv' hbi' hob),
      returns_lift_some (P := PureInv s.func (domTree s.func) b 0)
        (by rw [← he₁', ← enter_eq]; exact pureInv_enter Sf.wf' Sf.hv' Sf.hs' hbi' hbp' hob),
      hanc'⟩⟩

omit Sf in
/-- Where the input's run stands once an output block ends. -/
def SQ (m : Mode) (f : Func) (s : FuncSnap) (F : StepFacts) (o : Oracle) (c : Ctx) (b : Nat) :
    Next → FeM (List Val) → Prop
  | .goto e d, y => ∃ t, (∀ I w, y.exec I w = (runFrom o c f t).exec I w) ∧ RS m f s F (e, some b, d) t
  | .done v, y => y = pure v

/-- The terminators, from the ends of the two blocks. -/
theorem SF.term_fol (o : Oracle) (c : Ctx) {b : Nat} {ib ob : Block} (hib : f.block? b = some ib)
    (hob : s.func.block? b = some ob) (B : BF pairs deleted ib ob) {e' e : Env}
    (hm : Mid sig syms m f s F e' e b ib.body.length ob.body.length) :
    Fol (SQ m f s F o c b) (runTerm e' ob.term) (runTerm e ib.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) := by
  obtain ⟨hes, hds, H, H'⟩ := hm
  have hmem := List.mem_of_find?_eq_some hib
  have hobm := List.mem_of_find?_eq_some hob
  have hid : ib.id = b := by simpa using List.find?_some hib
  have hid' : ob.id = b := by simpa using List.find?_some hob
  have ht := Sf.A.term B.term
  have hssa := (ssa_block Sf.hs hmem (hid ▸ H.side.reach)).2.2
  have hssa' := (ssa_block Sf.hs' hobm (hid' ▸ H'.reach)).2.2
  -- the terminators read the same values
  have hal : ∀ a ∈ ib.term.args, opVal e (subst σ a) = opVal e a := by
    intro a ha
    have ha' : subst σ a ∈ ob.term.args := by
      rw [ht, Term.args_mapOps]; exact List.mem_map_of_mem ha
    refine alias_use Sf.A Sf.mode H.side H' hes c H.kb H.cs (fun h => (H.sc h).2)
      (fun v hv => ?_) ((opsWf_block Sf.A.opsWf' hobm).2.2 _ ha') (fun w hw => ?_)
      (fun v x hv hx => Sf.A.keys _ B.term v (hv ▸ ha) x hx)
    · subst hv
      have := hssa _ ha
      rw [hid] at this
      exact useOk_sound (Func.wf_ids Sf.wf) this
    · have := hssa' _ (hw ▸ ha')
      rw [hid'] at this
      exact useOk_sound (Func.wf_ids Sf.wf') this
  have hdef := term_defined Sf.wf Sf.hs hib H.side.reach H.side.pi
  have hrt : runTerm e ob.term = runTerm e ib.term := by rw [ht]; exact runTerm_mapOps _ hal
  have hdef' : ∀ op ∈ ob.term.args, ∃ v, intVal e op = some v := by
    intro op hop
    rw [ht, Term.args_mapOps] at hop
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hop
    obtain ⟨n, hn⟩ := hdef a ha
    exact ⟨(256, n), by unfold intVal; rw [hal a ha]; exact hn⟩
  have happ := approx_runTerm (· == ·) hes ob.term ob.term (termRel_refl _) hdef'
  rw [hrt] at happ
  have hwfT : ib.term.wf f.rets.length = true := by
    have hw := Sf.wf
    unfold Func.wf at hw
    simp only [Bool.and_eq_true, List.all_eq_true] at hw
    exact (hw.2 ib hmem).2
  refine Fol.approx (Approx.strengthen happ (Returns.and (returns_runTerm H.side.pi.1.int ib.term)
    (runTerm_slot H.cs hwfT hdef))) fun n' n ⟨hn, hok, hslot⟩ => ?_
  rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
  · obtain ⟨⟨hea, heb⟩, hdd⟩ := hn
    simp only [beq_iff_eq] at hdd
    subst hdd
    rw [hea, heb]
    rw [heb] at hok
    obtain ⟨_, hd⟩ := hok
    obtain ⟨k, hk, hks⟩ := hslot
    have hd' : d' ∈ ob.term.succs := by rw [ht, Term.succs_mapOps]; exact hd
    have hex : m = .sccp → ((ctxOf m f s F).E.find? d').isSome = true ∧
        edgeExec (ctxOf m f s F).inB (ctxOf m f s F).E (ctxOf m f s F).dead b d' = true :=
      fun h => exec_next (Sf.sccp h) rfl hib (H.sc h).1 hk hks
    refine ⟨(e, some b, d'), fun _ _ => rfl, rfl, hes, hds,
      blockInv_of_point Sf.hv hib H.side.reach H.side.pi hd,
      fun pblk hp => by rw [hib] at hp; cases hp; exact H.side.pu, H.kb, H.cs,
      ancReach_edge Sf.hv H.side.anc ⟨ib, hib, hd⟩,
      blockInv_of_point Sf.hv' hob H'.reach H'.pi hd',
      fun pblk hp => by rw [hob] at hp; cases hp; exact H'.pu,
      ancReach_edge Sf.hv' H'.anc ⟨ob, hob, hd'⟩,
      fun p hp => ?_, fun h => (hex h).1⟩
    simp only [Option.some.injEq] at hp
    subst hp
    exact ⟨H.side.anc, H'.anc, fun h => ⟨(hex h).2, (H.sc h).2⟩⟩
  · subst hn; rfl

/-- One output block against the input's run from a related state. -/
theorem SF.block_fol {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {s' s0 : BState}
    (hR : RS m f s F s' s0) :
    Fol (SQ m f s F o c s'.2.2) (stepBlock o c s.func s'.1 s'.2.1 s'.2.2) (runFrom o c f s0) := by
  obtain ⟨env', prev', b⟩ := s'
  obtain ⟨env, prev, b₀⟩ := s0
  have hbb := hR.1
  simp only [Prod.mk.injEq] at hbb
  obtain ⟨rfl, rfl⟩ := hbb
  unfold stepBlock
  cases hob : s.func.block? b with
  | none => exact Fol.stuck
  | some ob =>
  dsimp only
  obtain ⟨ib, hib, B⟩ := Sf.A.block hob
  rw [runFrom_enter o c hib]
  refine Fol.bind (Fol.approx (Sf.enter_approx hR c hib hob B)
    (Q := fun e₁' y => ∃ e₁, y = inRun o c f b ib e₁ ∧ Mid sig syms m f s F e₁' e₁ b 0 0)
    fun a' a h => ⟨a, rfl, h⟩) ?_
  rintro e₁' _ ⟨e₁, rfl, hm⟩
  unfold inRun
  refine Fol.bind (Sf.body_fol ho hoi c hib hob (fun e => runTerm e ib.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) B.body 0 0 e₁' e₁ rfl rfl (Nat.zero_le _) (Nat.zero_le _) hm)
    fun e₂' y ⟨e₂, hy, hm₂⟩ => ?_
  subst hy
  exact Sf.term_fol o c hib hob B hm₂

theorem SF.sim {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    Sim o c s.func f (RS m f s F) := by
  intro s' s0 hR I w' w hw
  have h := Sf.block_fol ho hoi c hR I w' w hw
  revert h
  rcases (stepBlock o c s.func s'.1 s'.2.1 s'.2.2).exec I w' with _ | (e' | ⟨n, w₁'⟩)
  · intro _; trivial
  · exact id
  · rintro ⟨y₁, w₁, hy, hq, hw₁⟩
    cases n with
    | goto env d =>
      obtain ⟨t, ht, hR'⟩ := hq
      exact ⟨t, w₁, hy.trans (ht I w₁), hR', hw₁⟩
    | done v =>
      simp only [SQ] at hq
      subst hq
      exact ⟨w₁, by rw [hy, Fe.M.exec_pure], hw₁⟩

/-- The output function approximates the input function on integers. -/
theorem SF.sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  have sim := Sf.sim ho hoi c
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he' : s.func.blocks.head? with
  | none => exact Approx.stuck _
  | some e' =>
  -- the entries have one id
  obtain ⟨e, he, hid⟩ : ∃ e, f.blocks.head? = some e ∧ e'.id = e.id := by
    cases hf : f.blocks with
    | nil =>
      have := Sf.A.len; rw [hf] at this
      cases hg : s.func.blocks with
      | nil => rw [hg] at he'; cases he'
      | cons _ _ => rw [hg] at this; simp at this
    | cons x l =>
      refine ⟨x, rfl, ?_⟩
      have := Sf.A.ids
      rw [hf] at this
      cases hg : s.func.blocks with
      | nil => rw [hg] at he'; cases he'
      | cons y l' =>
        rw [hg] at this he'
        simp only [List.head?_cons, Option.some.injEq] at he'
        subst he'
        simp only [List.map_cons, List.cons.injEq] at this
        exact this.1.symm
  rw [he]
  dsimp only
  rw [Sf.A.params, hid]
  have hU := UniqueDefs.of_ssa Sf.hs
  have hi'R : Returns (fun env => BlockInv s.func (domTree s.func) (env, none, e.id))
      (Fe.Sonatina.bind {} f.params args) := by
    have := entry_inv Sf.wf' Sf.hv' he' hargs
    rw [Sf.A.params, hid] at this
    exact this
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _)
    (Returns.and (Returns.and (entry_inv Sf.wf Sf.hv he hargs) hi'R)
      (returns_bind {} f.params args)))
    fun env env₀ ⟨e₁, ⟨hi, hi'⟩, _, hfold⟩ => ?_
  cases e₁
  refine Sim.approx sim (env, none, e.id) (env, none, e.id)
    ⟨rfl, EnvSub.refl _, fun k hk => ?_, hi, trivial, ?_, ?_, ancReach_entry Sf.hv he, ?_, trivial,
      ?_, (fun p hp => by cases hp), fun h => ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    rw [hfold] at hv
    rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
    · exact defsOf_isSome (param_def (Sf.A.params ▸ (List.of_mem_zip hx).1))
    · simp at he₀
  · -- the parameters have no claims
    intro v n hvn
    rw [hfold] at hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
    · have := kb_param Sf.A.kb (defsOf_find hU (param_def (List.of_mem_zip hx).1))
      show (kbOf (kbMap F) x.1.1).Sat n
      rw [this]
      exact sat_unknown n
    · simp at he₀
  · intro v c0 n hcv hvn
    by_cases hms : m = .sccp
    · rw [hfold] at hvn
      rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
      · have hcl := (Sf.sccp hms).claims _ c0 hcv
        have hp : (ctxOf m f s F).inD.find? x.1.1 = some .param :=
          defsOf_find hU (param_def (List.of_mem_zip hx).1)
        rw [hp] at hcl
        cases hcl
      · simp at he₀
    · rw [Sf.cs_empty hms] at hcv; simp at hcv
  · exact hi'
  · rw [← hid]
    exact ancReach_entry Sf.hv' he'
  · have := (Sf.sccp h).closed
    unfold execClosed at this
    simp only [Bool.and_eq_true, Option.any_eq_true] at this
    rw [he] at this
    simpa using this.1

end sim

/-! ## The two step kinds -/

/-- The shared check accepting a step, in exact or SCCP mode, with SCCP's facts in the latter:
    the output function approximates the well-formed input function on integers. -/
theorem aliasReject_sound {m : Mode} (hm : m = .exact ∨ m = .sccp) {f : Func}
    {ids : Option (List (List Nat))} {s : FuncSnap} {F : StepFacts} (hwf : f.wf sig syms = true)
    (h : aliasReject m f ids s F = none) (hsc : m = .sccp → SccpSpec f (ctxOf m f s F))
    {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  obtain ⟨_, pairs, deleted, σ, _, A⟩ := aliasReject_spec h
  exact SF.sound (sig := sig) (syms := syms) ⟨A, hwf, hm, hsc⟩ ho hoi c

/-- A `known_bits_simplify` step the checker accepts is sound (demand rounds are switched off,
    `demandRounds`). -/
theorem knownBitsSimplify_sound {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : checkKnownBitsSimplify f ids s F = true)
    {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  unfold checkKnownBitsSimplify kbsReject kbsRejectWith at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · exact aliasReject_sound (Or.inl rfl) hwf (Option.isNone_iff_eq_none.mp h) (fun h => by cases h)
      ho hoi c
  · simp [demandRounds] at h

/-- An `sccp_fold` step the checker accepts is sound. -/
theorem sccpFold_sound {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (hwf : f.wf sig syms = true) (h : checkSccpFold f ids s F = true)
    {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some s.func) (some f) := by
  unfold checkSccpFold sccpReject at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  next hs =>
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hs
  exact aliasReject_sound (Or.inr rfl) hwf (Option.isNone_iff_eq_none.mp h)
    (fun _ => sccpSpec_of hs) ho hoi c

theorem knownBitsSimplify_stepSound : StepSound .knownBitsSimplify :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    knownBitsSimplify_sound hw (by simpa only [checkFunc] using h) ho hoi c

theorem sccpFold_stepSound : StepSound .sccpFold :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    sccpFold_sound hw (by simpa only [checkFunc] using h) ho hoi c

end Fe.Sonatina.Steps.Schemas
