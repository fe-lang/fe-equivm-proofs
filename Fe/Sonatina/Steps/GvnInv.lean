import Fe.Sonatina.Steps.SchemasInv

/-!
# GVN's certificate holds along the input's run

For a `gvn_rewrite` step the schema checker runs in the mode `gvn cls pts` on the input with the
inserted phis (`GvnRewrite.lean`), and checks the certificate on it (`Mode.certOk`).  Along a run
of that input, at every point `(b, k)`:

- `GInv`: each class pair `(v, r)` whose value `v` dominates the point has `v` equal to `r`.  A pair
  is established where `v` is bound: a pure statement, its operands through their
  representatives, equals `r`'s statement (L2) or `r` by a schema; a phi equals `r` from the
  predecessor the run came from, the operands' representatives equal at that predecessor's end.
  It stays: `r`'s definition dominates `v`'s (`StepCtx.before`), so neither is rebound while `v`
  dominates the point.  This is CompCertSSA's argument; cycles of pairs through phis need no
  order, each pair resting on the pairs at the predecessor's end.
- `PInv`: each inserted phi `ψ` of block `Q` with term `t` holds `t`'s value, where `ψ` dominates
  the point: entering `Q` from `p`, `ψ` takes its operand from `p`, which is `t` with `Q`'s phis
  replaced by their operands from `p` (`ptOk`), and `t`'s atoms, phis of `Q` or above `Q`, are not
  rebound inside `Q`'s region.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-! ## The invariants -/

/-- GVN's classes hold at the point `(b, k)`: each pair whose value dominates the point. -/
def GInv (f : Func) (cls : List (Nat × Operand)) (e : Env) (b k : Nat) : Prop :=
  ∀ v r, (v, r) ∈ cls → DomAt f (domTree f) b k v → opVal e (.var v) = opVal e r

/-- The inserted phis hold their terms at the point `(b, k)`. -/
def PInv (f : Func) (pts : List (Nat × Nat × Term)) (e : Env) (b k : Nat) : Prop :=
  ∀ ψ Q t, (ψ, Q, t) ∈ pts → DomAt f (domTree f) b k ψ →
    ∃ n, e[ψ]? = some (.int 256 n) ∧ TermOk e t n

/-- A word for every value dominating the point. -/
def Words (f : Func) (e : Env) (b k : Nat) : Prop :=
  ∀ w, DomAt f (domTree f) b k w → ∃ n, e[w]? = some (.int 256 n) ∧ n < W

/-- An immediate, or a value dominating the point. -/
def OpAt (f : Func) (b k : Nat) (o : Operand) : Prop :=
  ∀ w, o = .var w → DomAt f (domTree f) b k w

theorem SidePt.words {g : Func} {e : Env} {b k : Nat} (S : SidePt sig syms g e b k) :
    Words g e b k := fun w hw => by
  obtain ⟨n, h1, _, h3⟩ := S.bound (EnvSub.refl e) hw
  exact ⟨n, h1, h3⟩

/-! ## Dominance from definitions -/

/-- A value dominates the point if its definition does. -/
theorem domAt_of_def {g : Func} (hn : (g.blocks.map (·.id)).Nodup) {T : DomTree} {b k w : Nat}
    {d : Def} (hd : (w, d) ∈ defList g)
    (h : d = .param ∨ (∃ B, d = .phi B ∧ T.Anc B b) ∨ (∃ B j, d = .stmt B j ∧ Before T B j b k)) :
    DomAt g T b k w := by
  rcases mem_defList hd with ⟨rfl, hp⟩ | ⟨bb, hbb, φ, hφ, rfl, rfl⟩ | ⟨bb, hbb, j, s, hs, rfl, hv⟩
  · exact Or.inl hp
  · rcases h with h | ⟨B, hB, ha⟩ | ⟨B, j, hB, _⟩
    · cases h
    · cases hB
      by_cases hbe : bb.id = b
      · subst hbe
        exact Or.inr (Or.inl ⟨bb, block?_of_mem hn hbb, Or.inl (List.mem_map_of_mem hφ)⟩)
      · exact Or.inr (Or.inr ⟨bb.id, hbe, ha, bb, block?_of_mem hn hbb,
          Or.inl (List.mem_map_of_mem hφ)⟩)
    · cases hB
  · rcases h with h | ⟨B, hB, _⟩ | ⟨B, j', hB, hbef⟩
    · cases h
    · cases hB
    · simp only [Def.stmt.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      rcases hbef with ⟨hne, ha⟩ | ⟨hbe, hj⟩
      · exact Or.inr (Or.inr ⟨bb.id, hne, ha, bb, block?_of_mem hn hbb,
          Or.inr ⟨s, List.mem_of_getElem? hs, hv⟩⟩)
      · subst hbe
        exact Or.inr (Or.inl ⟨bb, block?_of_mem hn hbb, Or.inr ⟨j, hj, s, hs, hv⟩⟩)

theorem anc_of_before {T : DomTree} {d j b k : Nat} (h : Before T d j b k) : T.Anc d b := by
  rcases h with ⟨_, ha⟩ | ⟨rfl, _⟩
  · exact ha
  · exact .refl

section ctx

variable {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
  (hU : UniqueDefs f) (hn : (f.blocks.map (·.id)).Nodup) {e0 : Nat}
  (hroot : (domTree f).idom.find? e0 = none)

include hD hT hU hn hroot

/-- `before x v`: where `v` dominates the point, so does `x`. -/
theorem before_domAt {b k : Nat} (hbroot : (domTree f).Anc e0 b) {x : Operand} {v : Nat}
    (h : X.before x v = true) (hv : DomAt f (domTree f) b k v) : OpAt f b k x := by
  intro w hw
  subst hw
  simp only [StepCtx.before, hD] at h
  rcases hdw : (defsOf f).find? w with _ | dw <;> rw [hdw] at h
  · simp at h
  rcases hdv : (defsOf f).find? v with _ | dv <;> rw [hdv] at h
  · rcases dw <;> simp at h
  have hw' := defsOf_mem hdw
  have hv' := defsOf_mem hdv
  refine domAt_of_def hn hw' ?_
  rw [hT] at h
  rcases dw with _ | d | ⟨d, j⟩
  · exact Or.inl rfl
  · right; left
    refine ⟨d, rfl, ?_⟩
    rcases dv with _ | bv | ⟨bv, kv⟩ <;> simp only [Bool.false_eq_true] at h
    · exact (DomTree.anc_sound h).trans (anc_of_domAt_phi hU hv hv')
    · exact (DomTree.anc_sound h).trans (anc_of_before (before_of_domAt hU hv hv'))
  · right; right
    refine ⟨d, j, rfl, ?_⟩
    rcases dv with _ | bv | ⟨bv, kv⟩ <;> simp only [Bool.false_eq_true,
      Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    · have hbv := anc_of_domAt_phi hU hv hv'
      have had := DomTree.anc_sound h.2
      refine Or.inl ⟨fun hdb => ?_, had.trans hbv⟩
      subst hdb
      exact h.1 (DomTree.anc_antisymm hroot hbroot hbv had).symm
    · refine before_trans hroot hbroot ?_ (before_of_domAt hU hv hv')
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, DomTree.anc_sound h2⟩
      · exact Or.inl ⟨h1, h2⟩

variable {cls : List (Nat × Operand)} (hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true)

include hcl

/-- A representative has the operand's value, at a point where the classes hold. -/
theorem gRoot_ok {b k : Nat} (hbroot : (domTree f).Anc e0 b) {e : Env} (hG : GInv f cls e b k) :
    ∀ n o, o.wf = true → OpAt f b k o →
      opVal e (gRoot (.ofList cls) n o) = opVal e o ∧ (gRoot (.ofList cls) n o).wf = true ∧
        OpAt f b k (gRoot (.ofList cls) n o)
  | 0, _, hw, h => ⟨rfl, hw, h⟩
  | _ + 1, .imm _ _, hw, h => ⟨rfl, hw, h⟩
  | n + 1, .var v, hw, h => by
    simp only [gRoot]
    split
    · next r hr =>
      rw [NatMap.find?_ofList] at hr
      have hm := mem_of_lookup hr
      have hvd := h v rfl
      have hro := before_domAt hD hT hU hn hroot hbroot (hcl v r hm).2 hvd
      obtain ⟨h1, h2, h3⟩ := gRoot_ok hbroot hG n r (hcl v r hm).1 hro
      exact ⟨h1.trans (hG v r hm hvd).symm, h2, h3⟩
    · exact ⟨rfl, hw, h⟩

/-- An operand's term through its representative evaluates to its word. -/
theorem gTerm_ok {b k : Nat} (hbroot : (domTree f).Anc e0 b) {e : Env} (hG : GInv f cls e b k)
    (hW : Words f e b k) {o : Operand} (hw : o.wf = true) (ho : OpAt f b k o) :
    ∃ n, opVal e o = some (.int 256 n) ∧ n < W ∧ TermOk e (gTerm (.ofList cls) o) n := by
  obtain ⟨h1, h2, h3⟩ := gRoot_ok hD hT hU hn hroot hcl hbroot hG 16 o hw ho
  unfold gTerm
  revert h1 h2 h3
  cases gRoot (.ofList cls) 16 o with
  | var u =>
    intro h1 _ h3
    obtain ⟨n, hn', hlt⟩ := hW u (h3 u rfl)
    refine ⟨n, ?_, hlt, termOk_atom hn' hlt⟩
    rw [← h1]; simp [opVal, hn']
  | imm bits w =>
    intro h1 h2 _
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    obtain ⟨rfl, hlt⟩ := h2
    exact ⟨w, by rw [← h1]; rfl, hlt, termOk_lit hlt⟩

end ctx

/-! ## The certificate's checks -/

theorem clsOk_spec {X : StepCtx} {cls : List (Nat × Operand)} (h : X.clsOk cls = true) :
    ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true ∧ X.pairOk (.ofList cls) v r = true := by
  intro v r hm
  have := List.all_eq_true.mp h (v, r) hm
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A pair of a statement's result. -/
theorem pairOk_stmt {X : StepCtx} {C : NatMap Operand} {v : Nat} {r : Operand} {B j : Nat}
    (h : X.pairOk C v r = true) (hv : X.inD.find? v = some (.stmt B j)) :
    ∃ st p, defStmt X.inB X.inD v = some st ∧ pureInst? st.inst = some p ∧ noClz p = true ∧
      checkExact (kbOf X.K) (termOf (gTerm C) p) (X.repTerm C r) = true := by
  simp only [StepCtx.pairOk, hv] at h
  rcases hst : defStmt X.inB X.inD v with _ | st
  · rw [hst] at h; cases h
  rw [hst] at h
  simp only [Option.bind_some] at h
  rcases hp : pureInst? st.inst with _ | p
  · rw [hp] at h; cases h
  rw [hp, Option.any_some, Bool.and_eq_true] at h
  exact ⟨st, p, rfl, hp, h.1, h.2⟩

/-- A pair of a phi's result. -/
theorem pairOk_phi {X : StepCtx} {C : NatMap Operand} {v : Nat} {r : Operand} {B : Nat}
    (h : X.pairOk C v r = true) (hv : X.inD.find? v = some (.phi B)) :
    ∃ φ, phiOf X.inB B v = some φ ∧
      ((∃ w ψ, r = .var w ∧ X.inD.find? w = some (.phi B) ∧ phiOf X.inB B w = some ψ ∧
        ∀ ob ∈ φ.incoming, ∃ o, inc ψ ob.2 = some o ∧ gTerm C ob.1 = gTerm C o) ∨
      (X.above B r = true ∧ ∀ ob ∈ φ.incoming, gTerm C ob.1 = gTerm C r)) := by
  simp only [StepCtx.pairOk, hv] at h
  rcases hφ : phiOf X.inB B v with _ | φ
  · rw [hφ] at h; cases h
  rw [hφ, Option.any_some, Bool.or_eq_true] at h
  refine ⟨φ, rfl, ?_⟩
  rcases h with h | h
  · left
    cases r with
    | imm => cases h
    | var w =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hw, h⟩ := h
      rcases hψ : phiOf X.inB B w with _ | ψ
      · rw [hψ] at h; cases h
      rw [hψ, Option.any_some, List.all_eq_true] at h
      refine ⟨w, ψ, rfl, hw, hψ, fun ob hob => ?_⟩
      have := h ob hob
      rcases hi : inc ψ ob.2 with _ | o
      · rw [hi] at this; cases this
      rw [hi, Option.any_some, beq_iff_eq] at this
      exact ⟨o, rfl, this⟩
  · right
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    exact ⟨h.1, h.2⟩

theorem pairOk_param {X : StepCtx} {C : NatMap Operand} {v : Nat} {r : Operand}
    (h : X.pairOk C v r = true) (hv : X.inD.find? v = some .param) : False := by
  simp [StepCtx.pairOk, hv] at h

/-- `before r v` for a statement's result `v`: `r` dominates the statement. -/
theorem before_stmtPt {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hn : (f.blocks.map (·.id)).Nodup) {r : Operand} {v B j : Nat} (h : X.before r v = true)
    (hv : X.inD.find? v = some (.stmt B j)) : OpAt f B j r := by
  intro w hw
  subst hw
  simp only [StepCtx.before, hv] at h
  rw [hD] at h
  rcases hdw : (defsOf f).find? w with _ | dw <;> rw [hdw] at h
  · simp at h
  refine domAt_of_def hn (defsOf_mem hdw) ?_
  rw [hT] at h
  rcases dw with _ | d | ⟨d, j'⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨d, rfl, DomTree.anc_sound h⟩)
  · simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      decide_eq_true_eq] at h
    refine Or.inr (Or.inr ⟨d, j', rfl, ?_⟩)
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, DomTree.anc_sound h2⟩
    · exact Or.inr ⟨h1, h2⟩

/-! ## Statements -/

section stmt

variable {f : Func}

/-- A value dominating the point is no result of the statement there. -/
theorem notRes (hU : UniqueDefs f) {b k : Nat} {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) {u : Nat} (hu : DomAt f (domTree f) b k u) :
    u ∉ st.dsts.map (·.1) := by
  intro hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  rcases before_of_domAt hU hu (hid ▸ stmt_def hmem hst hd) with ⟨h, _⟩ | ⟨_, h⟩
  · exact h rfl
  · exact Nat.lt_irrefl _ h

theorem keys_sub (st : Stmt) (vals : List Val) :
    ∀ x ∈ (st.dsts.zip vals).map (·.1.1), x ∈ st.dsts.map (·.1) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map_of_mem (List.of_mem_zip hz).1

theorem opVal_stmt (hU : UniqueDefs f) {b k : Nat} {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) (vals : List Val) {e : Env} {o : Operand}
    (ho : OpAt f b k o) : opVal ((st.dsts.zip vals).foldl bindStep e) o = opVal e o := by
  cases o with
  | var u => exact fold_get_not _ _ _ fun hm => notRes hU hb hst (ho u rfl) (keys_sub st vals u hm)
  | imm => rfl

theorem domAt_succ {T : DomTree} {b k u : Nat} (hu : DomAt f T b k u) : DomAt f T b (k + 1) u := by
  rcases hu with h | ⟨blk, hb, h | ⟨j, hj, s, hs, hv⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨blk, hb, Or.inl h⟩)
  · exact Or.inr (Or.inl ⟨blk, hb, Or.inr ⟨j, by omega, s, hs, hv⟩⟩)
  · exact Or.inr (Or.inr h)

theorem domAt_of_succ {T : DomTree} {b k u : Nat} {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) (hu : DomAt f T b (k + 1) u)
    (hn : u ∉ st.dsts.map (·.1)) : DomAt f T b k u := by
  rcases hu with h | ⟨blk', hb', h | ⟨j, hj, s, hs, hv⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨blk', hb', Or.inl h⟩)
  · rw [hb] at hb'
    cases hb'
    by_cases hjk : j = k
    · subst hjk
      rw [hst] at hs
      cases hs
      exact absurd hv hn
    · exact Or.inr (Or.inl ⟨blk, hb, Or.inr ⟨j, by omega, s, hs, hv⟩⟩)
  · exact Or.inr (Or.inr h)

theorem pureInv_pred {T : DomTree} {b k : Nat} {e : Env} (h : PureInv f T b (k + 1) e) :
    PureInv f T b k e := fun d j blk s hd hs hp hr hbef => h d j blk s hd hs hp hr (by
  rcases hbef with h' | ⟨rfl, hj⟩
  · exact Or.inl h'
  · exact Or.inr ⟨rfl, by omega⟩)

theorem words_pred {b k : Nat} {e : Env} (h : Words f e b (k + 1)) : Words f e b k :=
  fun w hw => h w (domAt_succ hw)

end stmt

section rep

variable {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks) (hD : X.inD = defsOf f)
  (hT : X.T = domTree f) (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true) {e0 : Nat}
  (hroot : (domTree f).idom.find? e0 = none) {cls : List (Nat × Operand)}
  (hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true)

include hB hD hT hwf hs hroot hcl

/-- A representative's term evaluates to its word, at a point where the classes and L2 hold. -/
theorem repTerm_ok (c : Ctx) {b k : Nat} (hbroot : (domTree f).Anc e0 b)
    (hanc : AncReach (domTree f) b) {e : Env} (hG : GInv f cls e b k) (hW : Words f e b k)
    (hpu : PureInv f (domTree f) b k e) {r : Operand} (hrw : r.wf = true) (hr : OpAt f b k r) :
    ∃ n, opVal e r = some (.int 256 n) ∧ n < W ∧ TermOk e (X.repTerm (.ofList cls) r) n := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have G : ∀ {o : Operand}, o.wf = true → OpAt f b k o →
      ∃ n, opVal e o = some (.int 256 n) ∧ n < W ∧ TermOk e (gTerm (.ofList cls) o) n :=
    fun hw ho => gTerm_ok hD hT hU hn hroot hcl hbroot hG hW hw ho
  cases r with
  | imm bits w =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrw
    obtain ⟨rfl, hlt⟩ := hrw
    exact ⟨w, rfl, hlt, termOk_lit hlt⟩
  | var w =>
    simp only [StepCtx.repTerm]
    split
    · next q hq =>
      split
      · next hc =>
        obtain ⟨st, hst, hp⟩ := Option.bind_eq_some_iff.mp hq
        rw [hB, hD] at hst
        obtain ⟨d0, j0, blk0, hdef, hb0, hj0, hwd⟩ := defStmt_spec hn hst
        have hbef := before_of_domAt hU (hr w rfl) hdef
        have hreach : ((domTree f).reach.find? d0).isSome = true := hanc d0 (anc_of_before hbef)
        have hh := hpu d0 j0 blk0 st hb0 hj0 (pureInst?_pure hp hc) hreach hbef
        have hmem0 := List.mem_of_find?_eq_some hb0
        have hsm : st ∈ blk0.body := List.mem_of_getElem? hj0
        obtain ⟨xs, hargs, hok⟩ := termOf_ok (ε := e) (e := e) (G := gTerm (.ofList cls)) (p := q)
          fun a ha => by
            have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
            obtain ⟨n, h1, h2, h3⟩ := G ((Func.wf_operands hwf hmem0).2.1 st hsm a ha')
              (fun w' hw' => by
                subst hw'
                exact domAt_trans hroot hbroot (stmt_operand hwf hs hb0 hreach hj0 ha') hbef)
            exact ⟨n, by simp [intVal, h1], h2, h3⟩
        have hty := ((Func.wf_words hwf).2 blk0 hmem0).2 st hsm
        refine ⟨_, ?_, evalOn_lt' hargs, hok⟩
        simp [opVal, pureHolds_val (c := c) hp hc hargs hh hty hwd]
      · exact G hrw hr
    · exact G hrw hr

end rep

/-- A statement keeps the classes, and establishes those of its result: for any classes whose
    representatives dominate their values and whose statement pairs `pairOk` justifies. -/
theorem ginv_stmt_of {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) (hwf : f.wf sig syms = true)
    (hs : ssa f (domTree f) = true) {F : StepFacts} {cls : List (Nat × Operand)}
    (hK : X.K = kbMap F)
    (hok : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true ∧
      ∀ B j, X.inD.find? v = some (.stmt B j) → X.pairOk (.ofList cls) v r = true)
    (c : Ctx) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (hG : GInv f cls e b k) {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) {vals : List Val}
    (S' : SidePt sig syms f ((st.dsts.zip vals).foldl bindStep e) b (k + 1))
    (hK' : KBHolds (kbMap F) ((st.dsts.zip vals).foldl bindStep e)) :
    GInv f cls ((st.dsts.zip vals).foldl bindStep e) b (k + 1) := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e1, _, hroot', hbroot⟩ := S.root
  have hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true := fun v r h =>
    ⟨(hok v r h).1, (hok v r h).2.1⟩
  set e' := (st.dsts.zip vals).foldl bindStep e
  have hW' : Words f e' b k := words_pred S'.words
  have hG' : GInv f cls e' b k := fun v r hvr hv => by
    rw [opVal_stmt hU hb hst vals (fun w hw => by cases hw; exact hv),
      opVal_stmt hU hb hst vals (before_domAt hD hT hU hn hroot' hbroot (hcl v r hvr).2 hv)]
    exact hG v r hvr hv
  intro v r hvr hdom
  by_cases hres : v ∈ st.dsts.map (·.1)
  swap
  · exact hG' v r hvr (domAt_of_succ hb hst hdom hres)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hres
  have hdefv := hid ▸ stmt_def hmem hst hd
  have hfind : X.inD.find? d.1 = some (.stmt b k) := hD ▸ defsOf_find hU hdefv
  obtain ⟨hrw, hbef, hpair⟩ := hok d.1 r hvr
  obtain ⟨st', p, hst', hp, hc, hce⟩ := pairOk_stmt (hpair b k hfind) hfind
  rw [hB, hD] at hst'
  obtain ⟨d0, j0, blk0, hdef0, hb0, hj0, _⟩ := defStmt_spec hn hst'
  obtain ⟨h1, h2⟩ := Def.stmt.inj (hU.fn hdef0 hdefv)
  subst d0 j0
  rw [hb] at hb0
  cases hb0
  rw [hst] at hj0
  cases hj0
  have hsm : st ∈ blk.body := List.mem_of_getElem? hst
  have G : ∀ {o : Operand}, o.wf = true → OpAt f b k o →
      ∃ n, opVal e' o = some (.int 256 n) ∧ n < W ∧ TermOk e' (gTerm (.ofList cls) o) n :=
    fun hw ho => gTerm_ok hD hT hU hn hroot' hcl hbroot hG' hW' hw ho
  obtain ⟨xs, hargs, hok1⟩ := termOf_ok (ε := e') (e := e') (G := gTerm (.ofList cls)) (p := p)
    fun a ha => by
      have ha' : a ∈ st.inst.args := by rw [pureInst?_args hp]; exact ha
      obtain ⟨n, h1, h2, h3⟩ := G ((Func.wf_operands hwf hmem).2.1 st hsm a ha')
        (fun w hw => by subst hw; exact stmt_operand hwf hs hb S.reach hst ha')
      exact ⟨n, by simp [intVal, h1], h2, h3⟩
  have hh := S'.pu b k blk st hb hst (pureInst?_pure hp hc) S.reach (Or.inr ⟨rfl, Nat.lt_succ_self k⟩)
  have hty := ((Func.wf_words hwf).2 blk hmem).2 st hsm
  have hval := pureHolds_val (c := c) hp hc hargs hh hty hres
  obtain ⟨nr, hrv, _, hrt⟩ := repTerm_ok hB hD hT hwf hs hroot' hcl c hbroot S.anc hG' hW'
    (pureInv_pred S'.pu) hrw (before_stmtPt hD hT hn hbef hfind)
  have heq := checkExact_sound hce (factsOn_env (hK ▸ hK') fun a ha => by
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · exact hok1.2 a ha
    · exact hrt.2 a ha)
  rw [hok1.1, hrt.1] at heq
  rw [hrv, ← heq]
  simp [opVal, hval]


/-- A statement keeps the classes, and establishes those of its result. -/
theorem ginv_stmt {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) (hwf : f.wf sig syms = true)
    (hs : ssa f (domTree f) = true) {F : StepFacts} {cls : List (Nat × Operand)}
    (hK : X.K = kbMap F) (hok : X.clsOk cls = true) (c : Ctx) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (hG : GInv f cls e b k) {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) {vals : List Val}
    (S' : SidePt sig syms f ((st.dsts.zip vals).foldl bindStep e) b (k + 1))
    (hK' : KBHolds (kbMap F) ((st.dsts.zip vals).foldl bindStep e)) :
    GInv f cls ((st.dsts.zip vals).foldl bindStep e) b (k + 1) :=
  ginv_stmt_of hB hD hT hwf hs hK (fun v r h => ⟨(clsOk_spec hok v r h).1,
    (clsOk_spec hok v r h).2.1, fun _ _ _ => (clsOk_spec hok v r h).2.2⟩) c S hG hb hst S' hK'


/-! ## Entering a block -/

section enter

variable {f : Func}

/-- A phi's operand from a reachable predecessor dominates the predecessor's end. -/
theorem domAt_phiUse (hwf : f.wf sig syms = true) {T : DomTree} {p : Nat} {pblk : Block}
    (hpb : f.block? p = some pblk) {v : Nat} (h : phiUseOk (defsOf f) T p (.var v) = true) :
    DomAt f T p pblk.body.length v := by
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

/-- Defined in an ancestor-or-self of `q`: dominates `q`'s end. -/
theorem domAt_end_of_anc {T : DomTree} {q d u : Nat} {qblk : Block} (hqb : f.block? q = some qblk)
    (ha : T.Anc d q) (hdef : DefinedIn f d u) : DomAt f T q qblk.body.length u := by
  by_cases hdq : d = q
  · subst hdq
    obtain ⟨blk', hb', hph | ⟨s', hs', hv'⟩⟩ := hdef
    · exact Or.inr (Or.inl ⟨blk', hb', Or.inl hph⟩)
    · rw [hqb] at hb'; cases hb'
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hs'
      exact Or.inr (Or.inl ⟨qblk, hqb, Or.inr ⟨j, (List.getElem?_eq_some_iff.mp hj).1, s', hj, hv'⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hdq, ha, hdef⟩)

/-- Entering `b` from `q`: a value dominating `b`'s start, no phi of `b`, dominates `q`'s end. -/
theorem domAt_enter (hv : (domTree f).valid f = true) {env : Env} {q b : Nat}
    (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block} (hqb : f.block? q = some qblk)
    {blk : Block} (hb : f.block? b = some blk) {u : Nat} (hu : DomAt f (domTree f) b 0 u)
    (hn : u ∉ blk.phis.map (·.dst)) : DomAt f (domTree f) q qblk.body.length u := by
  obtain ⟨_, _, _, hqr, hedge, _⟩ := hi
  rcases hu with hp | ⟨blk', hb', hph | ⟨j, hj, _⟩⟩ | ⟨d, hne, ha, hdef⟩
  · exact Or.inl hp
  · rw [hb] at hb'; cases hb'; exact absurd hph hn
  · exact absurd hj (Nat.not_lt_zero _)
  · rcases DomTree.anc_of_edge hv hqr hedge ha with h | h
    · exact absurd h hne
    · exact domAt_end_of_anc hqb h hdef

/-- What `above b` gives: an immediate, a parameter, or defined in a strict ancestor of `b`; so,
    entering `b` from `q`, it dominates `q`'s end and is no phi of `b`. -/
theorem above_enter {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hwf : f.wf sig syms = true) (hU : UniqueDefs f) (hv : (domTree f).valid f = true) {env : Env} {q b : Nat}
    (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block} (hqb : f.block? q = some qblk)
    {blk : Block} (hb : f.block? b = some blk) {x : Operand} (h : X.above b x = true) :
    OpAt f q qblk.body.length x ∧ ∀ w, x = .var w → w ∉ blk.phis.map (·.dst) := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hnot : ∀ w, x = .var w → w ∉ blk.phis.map (·.dst) := by
    intro w hw hm
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hm
    have hdφ := hid ▸ phi_def hmem hφ
    rcases above_spec h _ hw with hp | ⟨d, hne, _, hd | ⟨j, hd⟩⟩
    · rw [hD] at hp; cases hU.fn (defsOf_mem hp) hdφ
    · rw [hD] at hd; exact hne (Def.phi.inj (hU.fn (defsOf_mem hd) hdφ))
    · rw [hD] at hd; cases hU.fn (defsOf_mem hd) hdφ
  refine ⟨fun w hw => ?_, hnot⟩
  obtain ⟨_, _, _, hqr, hedge, _⟩ := hi
  rcases above_spec h w hw with hp | ⟨d, hne, ha, hd | ⟨j, hd⟩⟩
  · rw [hD] at hp
    rcases mem_defList (defsOf_mem hp) with ⟨_, hpm⟩ | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, _, h1, _⟩
    · exact Or.inl hpm
    · cases h1
    · cases h1
  · rw [hT] at ha
    rw [hD] at hd
    rcases DomTree.anc_of_edge hv hqr hedge ha with h' | h'
    · exact absurd h' hne
    · refine domAt_end_of_anc hqb h' ?_
      rcases mem_defList (defsOf_mem hd) with ⟨h1, _⟩ | ⟨bb, hbb, φ, hφ, h1, rfl⟩ | ⟨_, _, _, _, _, h1, _⟩
      · cases h1
      · cases h1
        exact ⟨bb, block?_of_mem (Func.wf_ids hwf) hbb, Or.inl (List.mem_map_of_mem hφ)⟩
      · cases h1
  · rw [hT] at ha
    rw [hD] at hd
    rcases DomTree.anc_of_edge hv hqr hedge ha with h' | h'
    · exact absurd h' hne
    · refine domAt_end_of_anc hqb h' ?_
      rcases mem_defList (defsOf_mem hd) with ⟨h1, _⟩ | ⟨_, _, _, _, h1, _⟩ | ⟨bb, hbb, k, s, hs, h1, hw'⟩
      · cases h1
      · cases h1
      · simp only [Def.stmt.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨bb, block?_of_mem (Func.wf_ids hwf) hbb, Or.inr ⟨s, List.mem_of_getElem? hs, hw'⟩⟩

end enter

/-- A representative of a value defined in a strict ancestor of `b` is no phi of `b`. -/
theorem before_not_phi {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hT : X.T = domTree f)
    (hU : UniqueDefs f) {e0 : Nat} (hroot : (domTree f).idom.find? e0 = none) {b : Nat}
    (hbroot : (domTree f).Anc e0 b) {u v d : Nat} (h : X.before (.var u) v = true)
    (hu : X.inD.find? u = some (.phi b)) (hd : DefinedIn f d v) (hne : d ≠ b)
    (ha : (domTree f).Anc d b) : False := by
  have hbd : X.T.anc b d = true := by
    rcases definedIn_def hd with h' | ⟨j, h'⟩
    · have hv : X.inD.find? v = some (.phi d) := hD ▸ defsOf_find hU h'
      simpa [StepCtx.before, hu, hv] using h
    · have hv : X.inD.find? v = some (.stmt d j) := hD ▸ defsOf_find hU h'
      simpa [StepCtx.before, hu, hv] using h
  rw [hT] at hbd
  exact hne (DomTree.anc_antisymm hroot hbroot ha (DomTree.anc_sound hbd))

/-- The phi of value `v` in block `b`. -/
theorem phiOf_spec {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks) {b v : Nat}
    {φ : Phi} (h : phiOf X.inB b v = some φ) :
    ∃ blk, f.block? b = some blk ∧ φ ∈ blk.phis ∧ φ.dst = v := by
  simp only [phiOf, hB, NatMap.find?_ofListBy] at h
  obtain ⟨blk, hb, hf⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨blk, hb, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- Entering a block from a reached predecessor keeps the classes, and establishes those of its
    phis. -/
theorem ginv_enter {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) (hwf : f.wf sig syms = true)
    (hs : ssa f (domTree f) = true) {cls : List (Nat × Operand)} (hok : X.clsOk cls = true)
    {env : Env} {q b : Nat} (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block}
    (hqb : f.block? q = some qblk) (SP : SidePt sig syms f env q qblk.body.length)
    (hGq : GInv f cls env q qblk.body.length) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) : GInv f cls e₁ b 0 := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have hv := SP.valid
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e1, _, hroot, hbrootq⟩ := SP.root
  have hbroot : (domTree f).Anc e1.id b := hid ▸ DomTree.valid_root hv (by assumption) hmem
    (hid ▸ hi.2.2.1)
  have hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true := fun v r h =>
    ⟨(clsOk_spec hok v r h).1, (clsOk_spec hok v r h).2.1⟩
  have G : ∀ {o : Operand}, o.wf = true → OpAt f q qblk.body.length o →
      ∃ n, opVal env o = some (.int 256 n) ∧ n < W ∧ TermOk env (gTerm (.ofList cls) o) n :=
    fun hw ho => gTerm_ok hD hT hU hn hroot hcl hbrootq hGq SP.words hw ho
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  have hkeep : ∀ u, u ∉ blk.phis.map (·.dst) →
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[u]? = env[u]? :=
    fun u hu => fold_get_not _ _ _ (by rw [hkeys]; exact hu)
  have hqr := hi.2.2.2.1
  have hssa := (ssa_block hs hmem (hid ▸ hi.2.2.1)).1
  have phival : ∀ φ ∈ blk.phis, ∃ o n, (o, q) ∈ φ.incoming ∧ inc φ q = some o ∧ o.wf = true ∧
      OpAt f q qblk.body.length o ∧ opVal env o = some (.int 256 n) ∧
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[φ.dst]? =
        some (.int 256 n) := by
    intro φ hφ
    obtain ⟨o, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hφ
    have hin := inc_mem hinc
    have how := (Func.wf_operands hwf hmem).1 φ hφ _ hin
    have hoat : OpAt f q qblk.body.length o := fun w hw =>
      domAt_phiUse hwf hqb (hw ▸ hssa φ hφ _ hin hqr)
    obtain ⟨n, hn1, _, _⟩ := G how hoat
    refine ⟨o, n, hin, hinc, how, hoat, hn1, ?_⟩
    rw [hget, ((Func.wf_words hwf).2 blk hmem).1 φ hφ, phi_val_word hwf hmem hφ hin hi.1 hov]
    rw [hov] at hn1
    exact congrArg some (Option.some.inj hn1)
  intro v r hvr hdom
  obtain ⟨hrw, hbef, hpair⟩ := clsOk_spec hok v r hvr
  by_cases hph : v ∈ blk.phis.map (·.dst)
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
    have hdefv := hid ▸ phi_def hmem hφ
    have hfind : X.inD.find? φ.dst = some (.phi b) := hD ▸ defsOf_find hU hdefv
    obtain ⟨φ', hφ', hcase⟩ := pairOk_phi hpair hfind
    obtain ⟨blk', hb', hφm', hφd'⟩ := phiOf_spec hB hφ'
    rw [hb] at hb'
    cases hb'
    have hφφ : φ' = φ := List.inj_on_of_nodup_map (hU.phis hmem) hφm' hφ hφd'
    subst hφφ
    obtain ⟨o, n, hin, _, how, hoat, hov, hget⟩ := phival φ' hφ
    obtain ⟨n', ho1, _, hot⟩ := G how hoat
    rw [hov] at ho1
    cases ho1
    rcases hcase with ⟨w, ψ, rfl, _, hψ, hall⟩ | ⟨hab, hall⟩
    · obtain ⟨blk'', hb'', hψm, hψd⟩ := phiOf_spec hB hψ
      rw [hb] at hb''
      cases hb''
      obtain ⟨o', hinc', hgt⟩ := hall (o, q) hin
      obtain ⟨o'', m, _, hinc'', how', hoat', hov', hget'⟩ := phival ψ hψm
      rw [hinc'] at hinc''
      cases hinc''
      obtain ⟨m', hm1, _, hmt⟩ := G how' hoat'
      rw [hov'] at hm1
      cases hm1
      have hnm : n = m := by rw [← hot.1, ← hmt.1, hgt]
      subst hnm
      show (List.foldl bindStep env _)[φ'.dst]? = (List.foldl bindStep env _)[w]?
      rw [hget, ← hψd, hget']
    · obtain ⟨hrat, hrnot⟩ := above_enter hD hT hwf hU hv hi hqb hb hab
      obtain ⟨m, hm1, _, hmt⟩ := G hrw hrat
      have hnm : n = m := by rw [← hot.1, ← hmt.1, hall (o, q) hin]
      subst hnm
      show (List.foldl bindStep env _)[φ'.dst]? = _
      rw [hget]
      cases r with
      | imm => exact hm1.symm
      | var u =>
        show _ = (List.foldl bindStep env _)[u]?
        rw [hkeep u (hrnot u rfl)]
        exact hm1.symm
  · have hvq := domAt_enter hv hi hqb hb hdom hph
    have hrq := before_domAt hD hT hU hn hroot hbrootq hbef hvq
    have hrnot : ∀ u, r = .var u → u ∉ blk.phis.map (·.dst) := by
      intro u hu hum
      subst hu
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hum
      have hfu : X.inD.find? φ.dst = some (.phi b) := hD ▸ defsOf_find hU (hid ▸ phi_def hmem hφ)
      rcases hdom with hp | ⟨blk', hb', hph' | ⟨j, hj, _⟩⟩ | ⟨d, hne, ha, hdef⟩
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
        exact pairOk_param hpair (hD ▸ defsOf_find hU (param_def hp'))
      · rw [hb] at hb'; cases hb'; exact hph hph'
      · exact absurd hj (Nat.not_lt_zero _)
      · exact before_not_phi hD hT hU hroot hbroot hbef hfu hdef hne ha
    have h1 := hGq v r hvr hvq
    show (List.foldl bindStep env _)[v]? = opVal (List.foldl bindStep env _) r
    rw [hkeep v hph]
    cases r with
    | imm => exact h1
    | var u =>
      show _ = (List.foldl bindStep env _)[u]?
      rw [hkeep u (hrnot u rfl)]
      exact h1

/-! ## Terms -/

theorem Term.eval_congr {ρ ρ' : Nat → Nat} :
    ∀ t : Term, (∀ a, t.hasAtom a = true → ρ a = ρ' a) → t.eval ρ = t.eval ρ'
  | .atom v, h => by simp [Term.eval, h v (by simp [Term.hasAtom])]
  | .lit _, _ => rfl
  | .op1 o a, h => by
    simp only [Term.eval]
    rw [Term.eval_congr a fun x hx => h x (by simp [Term.hasAtom, hx])]
  | .op2 o a b, h => by
    simp only [Term.eval]
    rw [Term.eval_congr a fun x hx => h x (by simp [Term.hasAtom, hx]),
      Term.eval_congr b fun x hx => h x (by simp [Term.hasAtom, hx])]
  | .op3 o a b c, h => by
    simp only [Term.eval]
    rw [Term.eval_congr a fun x hx => h x (by simp [Term.hasAtom, hx]),
      Term.eval_congr b fun x hx => h x (by simp [Term.hasAtom, hx]),
      Term.eval_congr c fun x hx => h x (by simp [Term.hasAtom, hx])]

theorem Term.mem_atoms {a : Nat} : ∀ t : Term, t.hasAtom a = true → a ∈ t.atoms
  | .atom v, h => by simp only [Term.hasAtom, beq_iff_eq] at h; simp [Term.atoms, h]
  | .lit _, h => by simp [Term.hasAtom] at h
  | .op1 _ x, h => by simp only [Term.atoms]; exact Term.mem_atoms x (by simpa [Term.hasAtom] using h)
  | .op2 _ x y, h => by
    simp only [Term.hasAtom, Bool.or_eq_true] at h
    simp only [Term.atoms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Term.mem_atoms x h)
    · exact Or.inr (Term.mem_atoms y h)
  | .op3 _ x y z, h => by
    simp only [Term.hasAtom, Bool.or_eq_true] at h
    simp only [Term.atoms, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (Term.mem_atoms x h))
    · exact Or.inl (Or.inr (Term.mem_atoms y h))
    · exact Or.inr (Term.mem_atoms z h)

theorem termOk_congr {e e' : Env} {t : Term} {n : Nat}
    (h : ∀ a, t.hasAtom a = true → e'[a]? = e[a]?) (ht : TermOk e t n) : TermOk e' t n := by
  refine ⟨?_, fun a ha => ?_⟩
  · rw [← ht.1]
    exact Term.eval_congr t fun a ha => by simp only [envWord, h a ha]
  · rw [h a ha]; exact ht.2 a ha

/-- What `ptOk` checks of an inserted phi. -/
theorem ptOk_spec {X : StepCtx} {pts : List (Nat × Nat × Term)} (h : X.ptOk pts = true) :
    ∀ ψ Q t, (ψ, Q, t) ∈ pts → X.inD.find? ψ = some (.phi Q) ∧
      (∀ a ∈ t.atoms, X.inD.find? a = some (.phi Q) ∨ X.above Q (.var a) = true) ∧
      ∃ φ, phiOf X.inB Q ψ = some φ ∧ ∀ ob ∈ φ.incoming,
        (∃ ψ' Qt, ob.1 = .var ψ' ∧ (NatMap.ofList pts).find? ψ' = some Qt ∧
          checkExact (kbOf X.K) (substPhis X Q ob.2 t) Qt.2 = true) ∨
        ∃ d, checkExact (kbOf X.K) (substPhis X Q ob.2 t) (unfold X.inB X.inD X.cs d ob.1) = true := by
  intro ψ Q t hm
  have := List.all_eq_true.mp h (ψ, Q, t) hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at this
  obtain ⟨⟨⟨hψ, _⟩, hat⟩, hφ⟩ := this
  refine ⟨hψ, hat, ?_⟩
  rcases hp : phiOf X.inB Q ψ with _ | φ
  · rw [hp] at hφ; cases hφ
  rw [hp, Option.any_some, List.all_eq_true] at hφ
  refine ⟨φ, rfl, fun ob hob => ?_⟩
  have h1 := hφ ob hob
  simp only [Bool.or_eq_true, List.any_eq_true] at h1
  rcases h1 with h1 | ⟨d, _, hd⟩
  · left
    cases ho : ob.1 with
    | imm => rw [ho] at h1; cases h1
    | var ψ' =>
      rw [ho] at h1
      simp only at h1
      rcases hq : (NatMap.ofList pts).find? ψ' with _ | Qt
      · rw [hq] at h1; cases h1
      rw [hq, Option.any_some] at h1
      exact ⟨ψ', Qt, rfl, hq, h1⟩
  · exact Or.inr ⟨d, hd⟩

/-! ## The inserted phis -/

section pinv

variable {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks) (hD : X.inD = defsOf f)
  (hT : X.T = domTree f) (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true)

include hD hT hwf in
/-- The atoms of an inserted phi's term, phis of its block `Q` or above `Q`, dominate every point
    `Q` dominates. -/
theorem atoms_domAt {e0 : Nat} (hroot : (domTree f).idom.find? e0 = none) {b k Q : Nat}
    (hbroot : (domTree f).Anc e0 b) {t : Term}
    (hat : ∀ a ∈ t.atoms, X.inD.find? a = some (.phi Q) ∨ X.above Q (.var a) = true)
    (hQb : (domTree f).Anc Q b) : ∀ a, t.hasAtom a = true → DomAt f (domTree f) b k a := by
  intro a ha
  have hn := Func.wf_ids hwf
  rcases hat a (Term.mem_atoms t ha) with h | h
  · exact domAt_of_def hn (defsOf_mem (hD ▸ h)) (Or.inr (Or.inl ⟨Q, rfl, hQb⟩))
  · rcases above_spec h a rfl with hp | ⟨d, hne, had, hd | ⟨j, hd⟩⟩
    · exact domAt_of_def hn (defsOf_mem (hD ▸ hp)) (Or.inl rfl)
    · rw [hT] at had
      exact domAt_of_def hn (defsOf_mem (hD ▸ hd)) (Or.inr (Or.inl ⟨d, rfl, had.trans hQb⟩))
    · rw [hT] at had
      refine domAt_of_def hn (defsOf_mem (hD ▸ hd)) (Or.inr (Or.inr ⟨d, j, rfl, Or.inl ⟨?_, had.trans hQb⟩⟩))
      intro hdb
      subst hdb
      exact hne (DomTree.anc_antisymm hroot hbroot hQb had).symm

include hD hT hwf hs in
/-- A statement keeps the inserted phis' terms. -/
theorem pinv_stmt {pts : List (Nat × Nat × Term)} (hok : X.ptOk pts = true) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (hP : PInv f pts e b k) {blk : Block} (hb : f.block? b = some blk)
    {st : Stmt} (hst : blk.body[k]? = some st) (vals : List Val) :
    PInv f pts ((st.dsts.zip vals).foldl bindStep e) b (k + 1) := by
  have hU := UniqueDefs.of_ssa hs
  obtain ⟨e1, _, hroot, hbroot⟩ := S.root
  intro ψ Q t hm hdom
  obtain ⟨hψ, hat, _⟩ := ptOk_spec hok ψ Q t hm
  have hψd := defsOf_mem (hD ▸ hψ)
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hnr : ψ ∉ st.dsts.map (·.1) := fun hr => by
    obtain ⟨d, hd, hdd⟩ := List.mem_map.mp hr
    cases hU.fn hψd (hdd ▸ hid ▸ stmt_def hmem hst hd)
  have hdk := domAt_of_succ hb hst hdom hnr
  obtain ⟨n, hn1, hok'⟩ := hP ψ Q t hm hdk
  have hQb := anc_of_domAt_phi hU hdk hψd
  have hat' := atoms_domAt hD hT hwf hroot (k := k) hbroot hat hQb
  refine ⟨n, ?_, termOk_congr (fun a ha => fold_get_not _ _ _ fun hm' =>
    notRes hU hb hst (hat' a ha) (keys_sub st vals a hm')) hok'⟩
  rw [fold_get_not _ _ _ fun hm' => notRes hU hb hst hdk (keys_sub st vals ψ hm')]
  exact hn1

include hwf hs in
/-- What entering a block from `q` binds one of its phis to: its operand's word from `q`. -/
theorem enter_phi {env : Env} {q b : Nat} (hi : BlockInv f (domTree f) (env, some q, b))
    {qblk : Block} (hqb : f.block? q = some qblk) (hW : Words f env q qblk.body.length)
    {blk : Block} (hb : f.block? b = some blk) {vals : List Val}
    (hF2 : List.Forall₂ (fun phi v => (some q >>= inc phi >>= opVal env) = some v) blk.phis vals)
    (hlen : (blk.phis.map fun phi => (phi.dst, phi.ty)).length = vals.length) {φ : Phi}
    (hφ : φ ∈ blk.phis) :
    ∃ o n, (o, q) ∈ φ.incoming ∧ inc φ q = some o ∧ o.wf = true ∧ OpAt f q qblk.body.length o ∧
      opVal env o = some (.int 256 n) ∧ n < W ∧
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[φ.dst]? =
        some (.int 256 n) := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hssa := (ssa_block hs hmem (hid ▸ hi.2.2.1)).1
  obtain ⟨o, val, hinc, hov, hget⟩ := enter_val hF2 hlen (hU.phis hmem) hφ
  have hin := inc_mem hinc
  have how := (Func.wf_operands hwf hmem).1 φ hφ _ hin
  have hoat : OpAt f q qblk.body.length o := fun w hw =>
    domAt_phiUse hwf hqb (hw ▸ hssa φ hφ _ hin hi.2.2.2.1)
  have hword : ∃ n, opVal env o = some (.int 256 n) ∧ n < W := by
    cases o with
    | var u =>
      obtain ⟨n, h1, h2⟩ := hW u (hoat u rfl)
      exact ⟨n, by simp [opVal, h1], h2⟩
    | imm bits w =>
      simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at how
      obtain ⟨rfl, hlt⟩ := how
      exact ⟨w, rfl, hlt⟩
  obtain ⟨n, hn1, hlt⟩ := hword
  refine ⟨o, n, hin, hinc, how, hoat, hn1, hlt, ?_⟩
  rw [hget, ((Func.wf_words hwf).2 blk hmem).1 φ hφ, phi_val_word hwf hmem hφ hin hi.1 hov]
  rw [hov] at hn1
  exact congrArg some (Option.some.inj hn1)

/-- A term evaluates on entering `b` from `q` as the term with `b`'s phis replaced by their
    operands from `q` before. -/
theorem substPhis_eval {b q : Nat} {env e₁ : Env} :
    ∀ t : Term, (∀ a, t.hasAtom a = true →
      (X.inD.find? a = some (.phi b) → (phiArgTerm X b q a).eval (envWord env) = envWord e₁ a % W) ∧
      (X.inD.find? a ≠ some (.phi b) → envWord e₁ a = envWord env a)) →
    t.eval (envWord e₁) = (substPhis X b q t).eval (envWord env)
  | .atom a, h => by
    have ha := h a (by simp [Term.hasAtom])
    simp only [substPhis]
    by_cases hp : X.inD.find? a = some (.phi b)
    · simp only [hp, beq_self_eq_true, ↓reduceIte, Term.eval]
      exact (ha.1 hp).symm
    · have : (X.inD.find? a == some (.phi b)) = false := by simpa using hp
      simp only [this, Bool.false_eq_true, ↓reduceIte, Term.eval, ha.2 hp]
  | .lit _, _ => rfl
  | .op1 o x, h => by
    simp only [substPhis, Term.eval]
    rw [substPhis_eval x fun a ha => h a (by simp [Term.hasAtom, ha])]
  | .op2 o x y, h => by
    simp only [substPhis, Term.eval]
    rw [substPhis_eval x fun a ha => h a (by simp [Term.hasAtom, ha]),
      substPhis_eval y fun a ha => h a (by simp [Term.hasAtom, ha])]
  | .op3 o x y z, h => by
    simp only [substPhis, Term.eval]
    rw [substPhis_eval x fun a ha => h a (by simp [Term.hasAtom, ha]),
      substPhis_eval y fun a ha => h a (by simp [Term.hasAtom, ha]),
      substPhis_eval z fun a ha => h a (by simp [Term.hasAtom, ha])]

/-- The atoms of a term with `b`'s phis replaced: atoms of the term that are no phis of `b`, or of
    a phi's replacement. -/
theorem substPhis_atoms {b q : Nat} {x : Nat} :
    ∀ t : Term, (substPhis X b q t).hasAtom x = true → ∃ a, t.hasAtom a = true ∧
      ((X.inD.find? a ≠ some (.phi b) ∧ x = a) ∨
        (X.inD.find? a = some (.phi b) ∧ (phiArgTerm X b q a).hasAtom x = true))
  | .atom a, h => by
    simp only [substPhis] at h
    by_cases hp : X.inD.find? a = some (.phi b)
    · simp only [hp, beq_self_eq_true, ↓reduceIte] at h
      exact ⟨a, by simp [Term.hasAtom], Or.inr ⟨hp, h⟩⟩
    · have : (X.inD.find? a == some (.phi b)) = false := by simpa using hp
      simp only [this, Bool.false_eq_true, ↓reduceIte, Term.hasAtom, beq_iff_eq] at h
      exact ⟨a, by simp [Term.hasAtom], Or.inl ⟨hp, h.symm⟩⟩
  | .lit _, h => by simp [substPhis, Term.hasAtom] at h
  | .op1 o y, h => by
    simp only [substPhis, Term.hasAtom] at h
    obtain ⟨a, ha, h'⟩ := substPhis_atoms y h
    exact ⟨a, by simp [Term.hasAtom, ha], h'⟩
  | .op2 o y z, h => by
    simp only [substPhis, Term.hasAtom, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨a, ha, h'⟩ := substPhis_atoms y h
      exact ⟨a, by simp [Term.hasAtom, ha], h'⟩
    · obtain ⟨a, ha, h'⟩ := substPhis_atoms z h
      exact ⟨a, by simp [Term.hasAtom, ha], h'⟩
  | .op3 o y z w, h => by
    simp only [substPhis, Term.hasAtom, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · obtain ⟨a, ha, h'⟩ := substPhis_atoms y h
      exact ⟨a, by simp [Term.hasAtom, ha], h'⟩
    · obtain ⟨a, ha, h'⟩ := substPhis_atoms z h
      exact ⟨a, by simp [Term.hasAtom, ha], h'⟩
    · obtain ⟨a, ha, h'⟩ := substPhis_atoms w h
      exact ⟨a, by simp [Term.hasAtom, ha], h'⟩

omit hB hD hT hs in
include hwf in
/-- A phi of block `Q` is one of the phis of `Q`'s block. -/
theorem phi_of_def {Q a : Nat} {blk : Block} (hb : f.block? Q = some blk)
    (h : (a, Def.phi Q) ∈ defList f) : ∃ φa ∈ blk.phis, φa.dst = a := by
  have hn := Func.wf_ids hwf
  rcases mem_defList h with ⟨h1, _⟩ | ⟨bb, hbb, φa, hφa, h1, h2⟩ | ⟨_, _, _, _, _, h1, _⟩
  · cases h1
  · have hQ : Q = bb.id := Def.phi.inj h1
    subst hQ
    rw [block?_of_mem hn hbb] at hb
    cases hb
    exact ⟨φa, hφa, h2.symm⟩
  · cases h1

include hB hD hT hwf hs in
/-- Entering a block from a reached predecessor keeps the inserted phis' terms, and establishes
    those of its own. -/
theorem pinv_enter {F : StepFacts} (hK : X.K = kbMap F) (hcs : X.cs = .empty)
    {pts : List (Nat × Nat × Term)} (hok : X.ptOk pts = true) (c : Ctx) {env : Env} {q b : Nat}
    (hi : BlockInv f (domTree f) (env, some q, b)) {qblk : Block} (hqb : f.block? q = some qblk)
    (SP : SidePt sig syms f env q qblk.body.length) (hKq : KBHolds (kbMap F) env)
    (hPq : PInv f pts env q qblk.body.length) {blk : Block} (hb : f.block? b = some blk)
    {e₁ : Env} (he : enterOpt env (some q) blk = some e₁) (hW₁ : Words f e₁ b 0) :
    PInv f pts e₁ b 0 := by
  have hU := UniqueDefs.of_ssa hs
  have hn := Func.wf_ids hwf
  have hv := SP.valid
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e1, he1, hroot, hbrootq⟩ := SP.root
  have hbroot : (domTree f).Anc e1.id b := hid ▸ DomTree.valid_root hv he1 hmem (hid ▸ hi.2.2.1)
  have hW := SP.words
  obtain ⟨vals, hF2, hlen, rfl⟩ := enterOpt_spec he
  have hkeys := enter_keys hlen
  have hkeep : ∀ u, u ∉ blk.phis.map (·.dst) →
      (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[u]? = env[u]? :=
    fun u hu => fold_get_not _ _ _ (by rw [hkeys]; exact hu)
  -- a value whose definition is no phi of `b` is no phi of `b`
  have hnotphi : ∀ u, X.inD.find? u ≠ some (.phi b) → u ∉ blk.phis.map (·.dst) := by
    intro u hu hm
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hm
    exact hu (hD ▸ defsOf_find hU (hid ▸ phi_def hmem hφ))
  intro ψ Q t hm hdom
  obtain ⟨hψ, hat, φ, hφ, hinc⟩ := ptOk_spec hok ψ Q t hm
  have hψd := defsOf_mem (hD ▸ hψ)
  have hQb := anc_of_domAt_phi hU hdom hψd
  by_cases hQ : Q = b
  · subst hQ
    obtain ⟨blk', hb', hφm, hφd⟩ := phiOf_spec hB hφ
    rw [hb] at hb'
    cases hb'
    obtain ⟨o, n, hin, _, how, hoat, hov, hlt, hget⟩ :=
      enter_phi hwf hs hi hqb hW hb hF2 hlen hφm
    -- the term on entry is its substituted form before
    have hsub : t.eval (envWord (((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl
        bindStep env)) = (substPhis X Q q t).eval (envWord env) := by
      refine substPhis_eval t fun a ha => ⟨fun hpa => ?_, fun hpa => ?_⟩
      · obtain ⟨φa, hφa, rfl⟩ := phi_of_def hwf hb (defsOf_mem (hD ▸ hpa))
        obtain ⟨oa, na, _, hinca, howa, _, hova, hlta, hgeta⟩ :=
          enter_phi hwf hs hi hqb hW hb hF2 hlen hφa
        have hpo : phiOf X.inB Q φa.dst = some φa := by
          simp only [phiOf, hB, NatMap.find?_ofListBy]
          exact Option.bind_eq_some_iff.mpr ⟨blk, hb, find?_dst (hU.phis hmem) hφa⟩
        simp only [phiArgTerm, hpo, Option.bind_some, hinca]
        rw [show envWord _ φa.dst = na by simp [envWord, hgeta], Nat.mod_eq_of_lt hlta]
        cases oa with
        | var u =>
          simp only [Term.eval, envWord]
          simp only [opVal] at hova
          rw [hova, Nat.mod_eq_of_lt hlta]
        | imm bits w =>
          simp only [opVal, Option.some.injEq, Val.int.injEq] at hova
          obtain ⟨_, rfl⟩ := hova
          simp [Term.eval, Nat.mod_eq_of_lt hlta]
      · simp only [envWord, hkeep a (hnotphi a hpa)]
    -- the substituted term's value is the operand's
    have hatq : ∀ x, (substPhis X Q q t).hasAtom x = true → ∃ m, env[x]? = some (.int 256 m) ∧ m < W := by
      intro x hx
      obtain ⟨a, ha, h1 | ⟨hpa, h2⟩⟩ := substPhis_atoms t hx
      · obtain ⟨hpa, hxa⟩ := h1
        rw [hxa]
        rcases hat a (Term.mem_atoms t ha) with h' | h'
        · exact absurd h' hpa
        · exact hW a ((above_enter hD hT hwf hU hv hi hqb hb h').1 a rfl)
      · obtain ⟨φa, hφa, rfl⟩ := phi_of_def hwf hb (defsOf_mem (hD ▸ hpa))
        obtain ⟨oa, _, _, hinca, _, hoata, _⟩ := enter_phi hwf hs hi hqb hW hb hF2 hlen hφa
        have hpo : phiOf X.inB Q φa.dst = some φa := by
          simp only [phiOf, hB, NatMap.find?_ofListBy]
          exact Option.bind_eq_some_iff.mpr ⟨blk, hb, find?_dst (hU.phis hmem) hφa⟩
        simp only [phiArgTerm, hpo, Option.bind_some, hinca] at h2
        cases oa with
        | var u =>
          simp only [Term.hasAtom, beq_iff_eq] at h2
          subst h2
          exact hW u (hoata u rfl)
        | imm => simp [Term.hasAtom] at h2
    have hval : (substPhis X Q q t).eval (envWord env) = n := by
      rcases hinc (o, q) hin with ⟨ψ', Qt, ho, hq', hce⟩ | ⟨d, hce⟩
      · simp only at ho
        subst ho
        rw [NatMap.find?_ofList] at hq'
        have hm' := mem_of_lookup hq'
        obtain ⟨n', hn1', hok'⟩ := hPq ψ' Qt.1 Qt.2 hm' (hoat ψ' rfl)
        simp only [opVal] at hov
        rw [hov] at hn1'
        cases hn1'
        rw [← hok'.1]
        exact checkExact_sound hce (factsOn_env (hK ▸ hKq) fun a ha => by
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · exact hatq a ha
          · exact hok'.2 a ha)
      · rw [hB, hD] at hce
        obtain ⟨n', hn1', _, hok'⟩ := SP.unfold_sound (EnvSub.refl env) c (cs := X.cs)
          (hcs ▸ cholds_empty env) d o how hoat
        rw [opVal_of_intVal hn1'] at hov
        cases hov
        rw [← hok'.1]
        exact checkExact_sound hce (factsOn_env (hK ▸ hKq) fun a ha => by
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · exact hatq a ha
          · exact hok'.2 a ha)
    refine ⟨n, by rw [← hφd]; exact hget, ⟨by rw [hsub, hval], fun a ha => ?_⟩⟩
    obtain ⟨m, hm1, hm2⟩ := hW₁ a (atoms_domAt hD hT hwf hroot (k := 0) hbroot hat .refl a ha)
    exact ⟨m, hm1, hm2⟩
  · -- `ψ` is a phi of a strict ancestor of `b`
    have hψb : ψ ∉ blk.phis.map (·.dst) :=
      hnotphi ψ fun h => hQ (Def.phi.inj (Option.some.inj (hψ.symm.trans h)))
    obtain ⟨n, hn1, hok'⟩ := hPq ψ Q t hm (domAt_enter hv hi hqb hb hdom hψb)
    refine ⟨n, by rw [hkeep ψ hψb]; exact hn1, termOk_congr (fun a ha => hkeep a ?_) hok'⟩
    refine hnotphi a fun hpa => ?_
    rcases hat a (Term.mem_atoms t ha) with h' | h'
    · exact hQ (Def.phi.inj (Option.some.inj (h'.symm.trans hpa)))
    · rcases above_spec h' a rfl with hp | ⟨d, hne, had, hd | ⟨j, hd⟩⟩
      · rw [hp] at hpa; cases hpa
      · rw [hd] at hpa
        cases hpa
        rw [hT] at had
        exact hne (DomTree.anc_antisymm hroot hbroot hQb had).symm
      · rw [hd] at hpa; cases hpa

end pinv

/-! ## A replacement the certificate justifies -/

/-- At a point where the input reads `v`, the certificate's justification of `v ↦ x` gives both one
    value. -/
theorem entryGvn_sound {f : Func} {X : StepCtx} (hB : X.inB = .ofListBy (·.id) f.blocks)
    (hD : X.inD = defsOf f) (hT : X.T = domTree f) {F : StepFacts} (hK : X.K = kbMap F)
    (hcs : X.cs = .empty) {cls : List (Nat × Operand)} {pts : List (Nat × Nat × Term)}
    (hcok : X.clsOk cls = true) (hpok : X.ptOk pts = true) (c : Ctx) {e : Env} {b k : Nat}
    (S : SidePt sig syms f e b k) (hKe : KBHolds (kbMap F) e) (hG : GInv f cls e b k)
    (hP : PInv f pts e b k) {v : Nat} (hv : DomAt f (domTree f) b k v) {x : Operand}
    (hxw : x.wf = true) (h : entryGvn X cls pts v x = true) : opVal e x = opVal e (.var v) := by
  have hU := S.uniq
  have hn := Func.wf_ids S.wf
  obtain ⟨e1, _, hroot, hbroot⟩ := S.root
  have hcl : ∀ v r, (v, r) ∈ cls → r.wf = true ∧ X.before r v = true := fun v r h =>
    ⟨(clsOk_spec hcok v r h).1, (clsOk_spec hcok v r h).2.1⟩
  unfold entryGvn at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hgt, hbef⟩ | h
  · obtain ⟨nv, hv1, _, hvt⟩ := gTerm_ok hD hT hU hn hroot hcl hbroot hG S.words (o := .var v) rfl
      (fun w hw => by cases hw; exact hv)
    obtain ⟨nx, hx1, _, hxt⟩ := gTerm_ok hD hT hU hn hroot hcl hbroot hG S.words hxw
      (before_domAt hD hT hU hn hroot hbroot hbef hv)
    have : nv = nx := by rw [← hvt.1, ← hxt.1, hgt]
    rw [hx1, hv1, this]
  · cases x with
    | imm => cases h
    | var ψ =>
      simp only at h
      rcases hq : (NatMap.ofList pts).find? ψ with _ | Qt
      · rw [hq] at h; cases h
      rw [hq, Option.any_some, Bool.and_eq_true] at h
      obtain ⟨hbl, hd⟩ := h
      rw [NatMap.find?_ofList] at hq
      have hm : (ψ, Qt.1, Qt.2) ∈ pts := mem_of_lookup hq
      obtain ⟨hψ, _, _⟩ := ptOk_spec hpok ψ Qt.1 Qt.2 hm
      -- `ψ`'s block dominates `v`'s, so `ψ` dominates the point
      have hQb : (domTree f).Anc Qt.1 b := by
        unfold StepCtx.blockOf at hbl
        rw [hD] at hbl
        rcases hdv : (defsOf f).find? v with _ | dv <;> rw [hdv] at hbl
        · cases hbl
        rcases dv with _ | B | ⟨B, j⟩
        · cases hbl
        · rw [Option.any_some, hT] at hbl
          exact (DomTree.anc_sound hbl).trans (anc_of_domAt_phi hU hv (defsOf_mem hdv))
        · rw [Option.any_some, hT] at hbl
          exact (DomTree.anc_sound hbl).trans (anc_of_before (before_of_domAt hU hv (defsOf_mem hdv)))
      have hψd := domAt_of_def (T := domTree f) (k := k) hn (defsOf_mem (hD ▸ hψ))
        (Or.inr (Or.inl ⟨Qt.1, rfl, hQb⟩))
      obtain ⟨nψ, hψ1, hψt⟩ := hP ψ Qt.1 Qt.2 hm hψd
      obtain ⟨nv, hv1, _, hvt⟩ := tin_ok hB hD S c (hcs ▸ cholds_empty e) hv
      obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hd
      rcases ht : X.tin d v with _ | tv
      · rw [ht] at hd; cases hd
      rw [ht, Option.any_some] at hd
      have hok := hvt d tv ht
      have heq := checkExact_sound hd (factsOn_env (hK ▸ hKe) fun a ha => by
        simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at ha
        rcases ha with ha | ha
        · exact hok.2 a ha
        · exact hψt.2 a ha)
      rw [hok.1, hψt.1] at heq
      show e[ψ]? = e[v]?
      rw [hψ1, hv1, heq]

/-! ## The entry -/

theorem words_of_point {f : Func} {e : Env} {b k : Nat} (h : PointInv f (domTree f) b k e) :
    Words f e b k := fun w hw => by
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (h.2 w hw)
  obtain ⟨n, hn, rfl⟩ := h.1 w val hval
  exact ⟨n, hval, hn⟩

/-- At the entry, a value dominating the start is a parameter. -/
theorem domAt_root {f : Func} {b : Nat} (hroot : (domTree f).idom.find? b = none) {blk : Block}
    (hb : f.block? b = some blk) (hph : blk.phis = []) {v : Nat} (h : DomAt f (domTree f) b 0 v) :
    v ∈ f.params.map (·.1) := by
  rcases h with hp | ⟨blk', hb', hph' | ⟨j, hj, _⟩⟩ | ⟨d, hne, ha, _⟩
  · exact hp
  · rw [hb] at hb'; cases hb'; rw [hph] at hph'; cases hph'
  · exact absurd hj (Nat.not_lt_zero _)
  · rcases ha.inv with h' | ⟨i, hi, _⟩
    · exact absurd h' hne
    · rw [hroot] at hi; cases hi

theorem ginv_root {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hs : ssa f (domTree f) = true)
    {cls : List (Nat × Operand)} (hok : X.clsOk cls = true) (e : Env) {b : Nat}
    (hroot : (domTree f).idom.find? b = none) {blk : Block} (hb : f.block? b = some blk)
    (hph : blk.phis = []) : GInv f cls e b 0 := by
  intro v r hvr hdom
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (domAt_root hroot hb hph hdom)
  exact (pairOk_param (clsOk_spec hok _ r hvr).2.2
    (hD ▸ defsOf_find (UniqueDefs.of_ssa hs) (param_def hp))).elim

theorem pinv_root {f : Func} {X : StepCtx} (hD : X.inD = defsOf f) (hs : ssa f (domTree f) = true)
    {pts : List (Nat × Nat × Term)} (hok : X.ptOk pts = true) (e : Env) {b : Nat}
    (hroot : (domTree f).idom.find? b = none) {blk : Block} (hb : f.block? b = some blk)
    (hph : blk.phis = []) : PInv f pts e b 0 := by
  intro ψ Q t hm hdom
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (domAt_root hroot hb hph hdom)
  obtain ⟨hψ, _⟩ := ptOk_spec hok ψ Q t hm
  have := (UniqueDefs.of_ssa hs).fn (hpe ▸ param_def hp) (defsOf_mem (hD ▸ hψ))
  cases this

end Fe.Sonatina.Steps.Schemas
