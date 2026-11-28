import Fe.Sonatina.Stage3.Place.FixTerm

/-!
# The terminal fixed buffer obligation

`FnUnp.fixObl`: `FixK` at every terminal fixed buffer site (rule S6).  From the site, H
allocates the buffer and `SR` holds (`fixSiteStep`); the rest of the site's block and every block
after it (the reach set, by `runBlocksO.fixpoint_induct`: `sfxBlocks`) run statement by
statement (`sfxWalk`: pure statements, stores through the buffer) and end in a halt H excuses
or a jump to a block after the site.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Lean.Order

theorem fixStmtOk_cases {O : Orig} {M : List Nat} {t : Nat} {s : HStmt}
    (h : fixStmtOk O M t s = true) :
    sfxPure s.inst = true ∨ ∃ a v, ((∃ t', s.inst = .base (.mstore a v t')) ∨
      s.inst = .base (.evm .mstore [a, v]) ∨ s.inst = .base (.evm .mstore8 [a, v])) ∧
      fixInM M a = true := by
  unfold fixStmtOk at h
  split at h
  all_goals first
    | (left; rename_i hi; rw [hi]; rfl)
    | (right; rename_i a v t' hi; exact ⟨a, v, Or.inl ⟨t', hi⟩, h⟩)
    | (right; rename_i a v hi; exact ⟨a, v, Or.inr (Or.inl hi), h⟩)
    | (right; rename_i a v hi; exact ⟨a, v, Or.inr (Or.inr hi), h⟩)
    | cases h

section rel

variable {S : SecFacts} {fn : Fn} {kt base n t : Nat} {b : HBlock} {j : Nat} {L : List Nat}
  {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}

theorem SR.mono (hR : SR S fn kt base n t b j L g hst w envH envM) {L' : List Nat}
    (hL : ∀ x ∈ L', x ∈ L) : SR S fn kt base n t b j L' g hst w envH envM :=
  { hR with vals := fun x hx => hR.vals x (hL x hx) }

end rel

theorem enter_other {env env₁ : HEnv} {p : Option Nat} {db : HBlock}
    (h : H.enter env p db = some env₁) {y : Nat} (hy : y ∉ db.phis.map (·.dst)) :
    env₁[y]? = env[y]? := by
  simp only [H.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, -, hbv⟩ := h
  exact bindVals_other hbv (by simpa [List.map_map, Function.comp_def] using hy)

section defs

variable (P : HSection) (I : Fe.EVM.Env) (S : SecFacts)

/-- H's run of the statements `rest` of block `b` and on, after a site, against the machine's
    result: it halts in an outcome that excuses it. -/
def STail (fn : Fn) (b : HBlock) (rest : List HStmt) (envH : HEnv) (hst : H.State)
    (r : Except (Exit World) (List Val × World)) : Prop :=
  ∃ ob, ExecBody P I envH rest hst ob ∧ match ob with
    | .halt o => Excuses o r
    | .cont env₂ st₂ => ∃ o, TermRun P I fn.f b env₂ st₂ (.halt o) ∧ Excuses o r

/-- A run of machine block `id` after the site, entered from `prev`, at the region start of a
    block after the site entered by H from block `pb` with `SR`: H halts excusing it. -/
def RBQ (fn : Fn) (kt base n t : Nat) (bt : HBlock) (env : Env) (prev : Option Nat) (id : Nat)
    (w : World) (r : Except (Exit World) (List Val × World)) : Prop :=
  ∀ db ∈ fn.f.blocks, ∀ dblk, fn.start db = some (id, dblk) → db.id ∈ fixR fn.f bt →
    ∀ pb ∈ fn.f.blocks, PrevOk fn (some pb.id) prev → ∀ g hst envH,
      SR S fn kt base n t pb pb.body.length (liveOut fn.f fn.L pb) g hst w envH env →
      stepTerm I envH hst pb.term = .goto db.id →
      ∃ o, ExecBlocks P I fn.f envH (some pb.id) db.id hst (.halt o) ∧ Excuses o r

end defs

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- One statement after the site, pure or a store. -/
theorem FnUnp.sfxStmt {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds))
    {kt base n t : Nat} {bt : HBlock} {it : Nat} (hF : FixSite fn bt it t)
    (hok : fixStmtOk ((secX src r).origAt fn.k) (fixM fn.f t) t s = true)
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b i (fn.live b i) g hst w envH envM) (O : Oracle) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ ∀ res, (runBodyO O cM envM pre).exec I w = some res →
      (∃ o, (∀ rest, ExecBody src I envH (s :: rest) hst (.halt o)) ∧ Excuses o res) ∨
      ∃ envM' w', res = .ok (envM', w') ∧ ∃ envH' hst',
        SR (secS src r efp) fn kt base n t b (i + 1) (fn.live b (i + 1)) g hst' w' envH' envM' ∧
        ∀ rest o, ExecBody src I envH' rest hst' o → ExecBody src I envH (s :: rest) hst o := by
  rcases fixStmtOk_cases hok with hpure | ⟨a, v, hkind, hinM⟩
  · obtain ⟨pre, h1, h2, h3⟩ := U.sfxPureStep hS hcM I hb hs hp hstm hpure hF hR O
    refine ⟨pre, h1, h2, fun res hres => ?_⟩
    rcases h3 res hres with h | ⟨envM', w', h4, envH', h5, h6⟩
    · exact Or.inl h
    · exact Or.inr ⟨envM', w', h4, envH', hst, h5, h6⟩
  · exact U.sfxStoreStep hS I hb hs hp hstm hkind hinM hR O

/-- The walk after the site, in the site's block or a block after it. -/
theorem FnUnp.sfxWalk {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (I : Fe.EVM.Env) {bt : HBlock} {it t : Nat} (hF : FixSite fn bt it t) {kt base n : Nat}
    {O : Oracle} {G : Env → Option Nat → Nat → FeM (List Val)}
    (hG : ∀ env prev id w r', (G env prev id).exec I w = some r' →
      RBQ src I (secS src r efp) fn kt base n t bt env prev id w r')
    {b : HBlock} (hb : b ∈ fn.f.blocks) (hRb : b.id ∈ fixR fn.f bt ∨ b = bt) {j₀ : Nat}
    (hok : ∀ j s, j₀ ≤ j → b.body[j]? = some s →
      fixStmtOk ((secX src r).origAt fn.k) (fixM fn.f t) t s = true)
    (htm : fixTermOk ((secX src r).origAt fn.k) (fixM fn.f t) t b.term = true) :
    ∀ k j, j + k = b.body.length → j₀ ≤ j → ∀ mb ms cs, fn.pos b j = some (mb, ms, cs) →
    ∀ mblk, fn.c.mf.block? mb = some mblk → ∀ g hst w envH envM,
      SR (secS src r efp) fn kt base n t b j (fn.live b j) g hst w envH envM →
      ∀ res, (runBodyO O cM envM ms >>= fun e => termK G mb e mblk.term).exec I w = some res →
        STail src I fn b (b.body.drop j) envH hst res := by
  intro k
  induction k with
  | zero =>
    intro j hj _ mb ms cs hp mblk hmb g hst w envH envM hR res h
    simp only [Nat.add_zero] at hj
    subst hj
    rw [List.drop_length]
    obtain ⟨mb₀, mblk₀, tbk, ms₀, cs₀, dss, tblk, -, hpos, htb, -, htblk, hto, -⟩ := U.walkOk hb
    rw [hpos] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rw [htblk] at hmb
    cases hmb
    refine ⟨.cont envH hst, ExecBody.nil, ?_⟩
    simp only [termK_eq] at h
    have h' : ((runBodyO O cM envM ms₀ >>= fun e => runTerm e mblk.term) >>= fun
        | .goto env dest => G env (some tbk) dest
        | .done vals => pure vals).exec I w = some res := by simp only [bind_assoc]; exact h
    cases htb' : b.term with
    | returnCode o l =>
      rcases exec_bind_some h' with ⟨e', h1, rfl⟩ | ⟨nx, w₁, h1, -⟩
      · obtain ⟨o', ho, hx⟩ := U.sfxTermCode I cM hb htb' (htb' ▸ hto) O hR h1
        exact ⟨o', Or.inr (Or.inr ⟨o', ho, rfl⟩), Excuses.of_error hx⟩
      · obtain ⟨o', ho, hx⟩ := U.sfxTermCode I cM hb htb' (htb' ▸ hto) O hR h1
        exact ⟨o', Or.inr (Or.inr ⟨o', ho, rfl⟩), Excuses.of_ok hx _⟩
    | base tm =>
      rw [htb'] at hto
      simp only [termOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hto
      obtain ⟨rfl, hmt⟩ := hto
      simp only [runBodyO, pure_bind] at h'
      rcases exec_bind_some h' with ⟨e', h1, rfl⟩ | ⟨nx, w₁, h1, h2⟩
      · rcases U.sfxTermBase I hb htb' hmt htm hR h1 with ⟨o', ho, hx⟩ | ⟨_, _, heq, _⟩
        · exact ⟨o', Or.inr (Or.inr ⟨o', ho, rfl⟩), Excuses.of_error hx⟩
        · cases heq
      · rcases U.sfxTermBase I hb htb' hmt htm hR h1 with ⟨o', ho, hx⟩ |
          ⟨d, d', heq, hgo, hbm, hsucc⟩
        · exact ⟨o', Or.inr (Or.inr ⟨o', ho, rfl⟩), Excuses.of_ok hx _⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, hw1⟩ := heq
          rw [hw1] at h2
          obtain ⟨db, hdb, hid⟩ := U.shape'.2.2.2.2.2.2.2.2.2.2.2 b hb d hsucc
          obtain ⟨mbd, mblkd, _, _, _, _, _, hstd, -⟩ := U.walkOk hdb
          have hstd' := hstd
          simp only [Fn.start, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at hstd'
          obtain ⟨mb', hmb', mblk', -, rfl, rfl⟩ := hstd'
          rw [hid, hbm] at hmb'
          cases hmb'
          have hdR : db.id ∈ fixR fn.f bt := by
            rw [hid]
            rcases hRb with hR' | rfl
            · obtain ⟨cb, hcb, hsc, -, -⟩ := (U.s6 hF).reach _ hR'
              rw [U.blk hb] at hcb
              cases hcb
              exact hsc d hsucc
            · exact succs_fixR fn.f _ hsucc
          obtain ⟨o', hx, hxo⟩ := hG envM (some tbk) d' w res h2 db hdb mblk' hstd hdR b hb
            (fun p hp => ⟨tbk, by cases hp; exact htb, rfl⟩) g hst envH
            (hR.mono fun x hx => by rw [U.liveEnd hb, mem_nset]; exact List.mem_append_right _ hx)
            (by rw [hid]; exact hgo)
          exact ⟨o', Or.inl ⟨d, hgo, by rw [← hid]; exact hx⟩, hxo⟩
  | succ k ih =>
    intro j hj hj₀ mb ms cs hp mblk hmb g hst w envH envM hR res h
    obtain ⟨s, hs⟩ : ∃ s, b.body[j]? = some s :=
      ⟨b.body[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨vm', mb', ms', ds, hstm, hp'⟩ := pos_succ hp hs (U.walks hb)
    obtain ⟨pre, rfl, hmm, hT⟩ := U.sfxStmt hS hcM I hb hs hp hstm hF (hok j s hj₀ hs) hR O
    rw [hmm] at hp'
    rw [drop_cons hs]
    rw [runBodyO_append, bind_assoc] at h
    rcases exec_bind_some h with ⟨e', h1, rfl⟩ | ⟨envM₁, w₁, h1, h2⟩
    · rcases hT _ h1 with ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
      · exact ⟨.halt o, hall _, Excuses.of_error hx⟩
      · cases heq
    · rcases hT _ h1 with ⟨o, hall, hx⟩ | ⟨envM', w', heq, envH', hst', hR', hc⟩
      · exact ⟨.halt o, hall _, Excuses.of_ok hx res⟩
      · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨ob, hbody, hk⟩ := ih (j + 1) (by omega) (by omega) mb ms' _ hp' mblk hmb g hst' w₁
          envH' envM₁ hR' res h2
        exact ⟨ob, hc _ _ hbody, hk⟩

/-- The blocks after the site, by fixpoint induction. -/
theorem FnUnp.sfxBlocks {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (I : Fe.EVM.Env) {bt : HBlock} {it t : Nat} (hF : FixSite fn bt it t) {kt base n : Nat}
    (O : Oracle) :
    ∀ env prev id w res, (runBlocksO O cM fn.c.mf env prev id).exec I w = some res →
      RBQ src I (secS src r efp) fn kt base n t bt env prev id w res := by
  have hnd := U.defsNodup
  refine runBlocksO.fixpoint_induct O cM fn.c.mf
    (fun G => ∀ env prev id w res, (G env prev id).exec I w = some res →
      RBQ src I (secS src r efp) fn kt base n t bt env prev id w res) ?_ ?_
  · exact Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
        ∀ prev id w res, (G prev id).exec I w = some res →
          RBQ src I (secS src r efp) fn kt base n t bt env prev id w res)
      fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
        ∀ id w res, (G id).exec I w = some res →
          RBQ src I (secS src r efp) fn kt base n t bt env prev id w res)
      fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
        ∀ w res, x.exec I w = some res →
          RBQ src I (secS src r efp) fn kt base n t bt env prev id w res)
      fun id => admissible_endsAt I _
  · intro G hG env prev id w res h db hdb dblk hstart hdR pb hpb hprev g hst envH hR hgo
    have hblk := start_block hstart
    simp only [stepBlock, hblk, bind_assoc] at h
    rcases exec_bind_some h with ⟨e', h1, -⟩ | ⟨env₁, w₁, h1, h2⟩
    · obtain ⟨a, ha⟩ := Quiet.enter env prev dblk I w _ h1
      cases ha
    · have hw := Quiet.world (Quiet.enter env prev dblk) h1
      subst hw
      set gE : Ghost := ⟨g.j, fun bb => bb < hst.blocks.size ∧ g.j bb < W,
        fun bb => bb < hst.blocks.size ∧ g.j bb < W⟩ with hgE
      have hedge : EdgeRel (secS src r efp) fn gE hst (some pb.id) db envH env := by
        refine ⟨pb, hpb, rfl, stepTerm_succ hgo, fun x hx => ?_⟩
        obtain ⟨v, m, e1, e2, e3, e4, e5, e6⟩ := hR.vals x hx
        refine ⟨v, m, e1, e2, e3, e4, e5, ?_⟩
        cases v with
        | int => trivial
        | ptr bb o => exact Or.inl ⟨e5.1, e6 bb o rfl⟩
      obtain ⟨envH₁, he, hE₁⟩ := U.phiObl hS I db hdb id dblk hstart (some pb.id) prev gE hst envH
        env w env₁ hedge hprev h1
      have hR₁ : SR (secS src r efp) fn kt base n t db 0 (fn.live db 0) g hst w envH₁ env₁ := by
        refine ⟨hR.world, hR.bsz, hR.exact, hR.zero, fun x hx => ?_, hR.hkt, hR.ksz, hR.jt, hR.bn,
          hR.buf, U.fixEdge I pb hpb envH hst db.id hR.q hgo db hdb rfl envH₁ he,
          fun y hy v hv => ?_⟩
        · obtain ⟨v, m, e1, e2, e3, e4, e5, e6⟩ := hE₁ x hx
          refine ⟨v, m, e1, e2, e3, e4, e5, fun bb o hvo => ?_⟩
          subst hvo
          rcases e6 with hh | ⟨hl, -⟩
          · exact hh.2
          · exact hl.2
        · have hyn : y ∉ db.phis.map (·.dst) := by
            intro hm
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
            rcases (U.s6 hF).just _ hy with ht | ⟨b', hb', s', hs', hy', -⟩
            · obtain ⟨st, hst0, htd⟩ := U.siteDef hF
              exact phi_stmt hnd hdb hF.1 hp (List.mem_of_getElem? hst0) (ht ▸ htd)
            · exact phi_stmt hnd hdb hb' hp hs' hy'
          rw [enter_other he hyn] at hv
          exact hR.must y hy v hv
      obtain ⟨cb, hcb, -, hcok, hctm⟩ := (U.s6 hF).reach _ hdR
      rw [U.blk hdb] at hcb
      cases hcb
      have h2' : (runBodyO O cM env₁ dblk.body >>= fun e => termK G id e dblk.term).exec I w =
          some res := by simp only [termK_eq]; exact h2
      obtain ⟨ob, hbody, hk⟩ := U.sfxWalk hS hcM I hF hG hdb (Or.inl hdR) (j₀ := 0)
        (fun j s _ hs => hcok s (List.mem_of_getElem? hs)) hctm db.body.length 0 (by omega) le_rfl
        id dblk.body (fn.cs db.id) (pos_zero hstart) dblk hblk g hst w envH₁ env₁ hR₁ res h2'
      rw [List.drop_zero] at hbody
      cases ob with
      | halt o => exact ⟨o, .bodyHalt (U.blk hdb) he hbody, hk⟩
      | cont env₂ st₂ =>
        obtain ⟨o, hrun, hx⟩ := hk
        rcases hrun with ⟨d, hd, hr⟩ | ⟨vals, _, hfo⟩ | ⟨o', ho, hfo⟩
        · exact ⟨o, .goto (U.blk hdb) he hbody hd hr, hx⟩
        · cases hfo
        · injection hfo with hoo
          subst hoo
          exact ⟨_, .halt (U.blk hdb) he hbody ho, hx⟩

/-- The terminal fixed buffer obligation. -/
theorem FnUnp.fixObl {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (I : Fe.EVM.Env) (CP : Oracle → Prop) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {a : Operand} {x : Nat} {tx : Ty}
    (hi : s.inst = .base (.malloc a)) (hd : s.dsts = [(x, tx)]) {base : Nat} {rule : FixedRule}
    (hl : fr.mallocs.lookup x = some (.fixed base rule)) {vm' : VM} {mb' : Nat} {ms' : List Stmt}
    {ds : List Nat} (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds)) :
    FixK src I cM (secS src r efp) (secX src r).derived CP FixInv fn b i mb ms := by
  intro O _ g₀ hst₀ g hst w envH envM hI hE hQ B hB mblk hmblk res hres
  obtain ⟨hF, hmb, hms, hsite⟩ := U.fixSiteStep hS I hb hs hp hi hd hl hstm hI hE hQ
  rw [hmb, hms] at hstm
  rw [drop_cons hs]
  rcases hsite with hex | ⟨n, g', hst', envH', hR, hexec⟩
  · exact ⟨.halt .exhausted, hex _, Or.inr (Or.inl rfl)⟩
  · obtain ⟨vm'', mb'', ms'', ds'', hstm', hp'⟩ := pos_succ hp hs (U.walks hb)
    rw [hstm] at hstm'
    simp only [Option.some.injEq, Prod.mk.injEq] at hstm'
    obtain ⟨-, rfl, rfl, -⟩ := hstm'
    have hG : ∀ env prev id w r', (B env prev id).exec I w = some r' →
        RBQ src I (secS src r efp) fn hst.blocks.size base n x b env prev id w r' :=
      fun env prev id w r' h => U.sfxBlocks hS hcM I hF O env prev id w r' (hB env prev id w r' h)
    have h6 := U.s6 hF
    obtain ⟨ob, hbody, hk⟩ := U.sfxWalk hS hcM I hF hG hb (Or.inr rfl) (j₀ := i + 1)
      (fun j s' hj hs' => h6.rest s' (by
        rw [List.mem_iff_getElem?]
        exact ⟨j - (i + 1), by rw [List.getElem?_drop, show i + 1 + (j - (i + 1)) = j by omega]; exact hs'⟩))
      h6.term (b.body.length - (i + 1)) (i + 1)
      (by have := (List.getElem?_eq_some_iff.mp hs).1; omega) le_rfl mb ms _ hp' mblk hmblk g' hst' w
      envH' envM hR res hres
    refine ⟨ob, hexec _ _ hbody, ?_⟩
    cases ob with
    | halt o => exact hk
    | cont env₂ st₂ =>
      obtain ⟨o, hrun, hx⟩ := hk
      exact ⟨.halt o, hrun, Or.inl ⟨o, rfl, hx⟩⟩

end unp

end Fe.Sonatina.Stage3.Place
