import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.L2

/-!
# The known-bits invariant (design §3.3, ruling 8)

Facts `F` that `kbFactsOk` accepts on a well-formed function in strict SSA hold all along every
run of it: at every block state the run reaches, and at every point of its block, each value
the environment binds satisfies its known-bits claim (`KBHolds`, `kb_reaches`, `kb_point`).

No L2 is needed: a claim is about one value, a value is bound only by its own definition
(unique definitions), and a definition binds a value that satisfies the claim, since the claim
is no stronger than the transfer of the claims of its operands (a pure statement: `transfer_sound`)
or their meet (a phi: `meetAll_sound`).  A parameter, or a result of a statement that is not
pure, has no claim.

The bridge from `pureInst?` to `Inst.pure` (`pureInst?_pure`) is here for the proofs that use L2.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina Fe.Sonatina.Steps KB

/-! ## The bridge to L2's purity -/

/-- A pure instruction of the schemas other than `clz` is pure for L2. -/
theorem pureInst?_pure {i : Inst} {p : PureInst} (h : pureInst? i = some p) (hc : noClz p = true) :
    i.pure = true := by
  unfold pureInst? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | rfl | simp [noClz] at hc

theorem pureInst?_args {i : Inst} {p : PureInst} (h : pureInst? i = some p) : i.args = p.args := by
  unfold pureInst? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-! ## Lookups -/

theorem lookup_mem {α : Type} : ∀ {l : List (Nat × α)} {k : Nat} {v : α},
    l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: l, k, v, h => by
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h; exact List.mem_cons_self ..
    · have : (k == a) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_of_mem {α : Type} : ∀ {l : List (Nat × α)}, (l.map (·.1)).Nodup →
    ∀ {k : Nat} {v : α}, (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => nomatch h
  | (a, b) :: l, hn, k, v, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with e | h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      simp [List.lookup]
    · have hk : k ≠ a := fun e => hn.1 (by rw [← e]; exact List.mem_map.mpr ⟨(k, v), h', rfl⟩)
      have : (k == a) = false := by simpa using hk
      simp only [List.lookup, this]
      exact lookup_of_mem hn.2 h'

variable {f : Func}

theorem defsOf_find (hu : UniqueDefs f) {v : Nat} {d : Def} (h : (v, d) ∈ defList f) :
    (defsOf f).find? v = some d := by
  rw [defsOf, NatMap.find?_ofList]; exact lookup_of_mem hu h

theorem blocks_find {b : Nat} {blk : Block} (hb : f.block? b = some blk) :
    (NatMap.ofListBy (·.id) f.blocks).find? b = some blk := by
  rw [NatMap.find?_ofListBy]; exact hb

theorem find?_dst {l : List Phi} (hn : (l.map (·.dst)).Nodup) {φ : Phi} (hφ : φ ∈ l) :
    l.find? (·.dst == φ.dst) = some φ := by
  rcases h : l.find? (·.dst == φ.dst) with _ | φ'
  · exact absurd hφ (by simpa using List.find?_eq_none.mp h φ)
  · have hd : φ'.dst = φ.dst := by simpa using List.find?_some h
    rw [h, List.inj_on_of_nodup_map hn (List.mem_of_find?_eq_some h) hφ hd]

/-! ## The claims -/

/-- The claims: every value bound to a word satisfies its claim. -/
def KBHolds (K : NatMap KB) (env : Env) : Prop :=
  ∀ v n, env[v]? = some (.int 256 n) → (kbOf K v).Sat n

theorem kbMap_find {F : StepFacts} {v : Nat} {c : KB} (h : (kbMap F).find? v = some c) :
    ∃ e ∈ F.knownBits, e.1 = v ∧ c = ⟨e.2.1, e.2.2⟩ := by
  rw [kbMap, NatMap.find?_ofList] at h
  obtain ⟨e, he, he'⟩ := List.mem_map.mp (lookup_mem h)
  exact ⟨e, he, (Prod.mk.inj he').1, (Prod.mk.inj he').2.symm⟩

theorem unknown_le (d : KB) : KB.unknown.le d = true := by simp [KB.unknown, KB.le]

variable {B : NatMap Block} {D : NatMap Def} {F : StepFacts}

theorem kbFactsOk_all (hk : kbFactsOk B D F = true) {e : Nat × Nat × Nat} (he : e ∈ F.knownBits) :
    (⟨e.2.1, e.2.2⟩ : KB).valid = true ∧ (match D.find? e.1 with
      | some (.phi b) => (phiOf B b e.1).any fun p =>
          (⟨e.2.1, e.2.2⟩ : KB).le (meetAll (kbMap F) (p.incoming.map (·.1)))
      | some (.stmt _ _) => ((defStmt B D e.1).bind fun s => pureInst? s.inst).any fun p =>
          (⟨e.2.1, e.2.2⟩ : KB).le (transferOf (kbMap F) p)
      | _ => false) = true := by
  unfold kbFactsOk at hk
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  exact hk.2 e he

/-- A phi's claim is no stronger than the meet of its operands' claims. -/
theorem kb_phi (hk : kbFactsOk B D F = true) {v b : Nat} {p : Phi} (hd : D.find? v = some (.phi b))
    (hp : phiOf B b v = some p) :
    (kbOf (kbMap F) v).le (meetAll (kbMap F) (p.incoming.map (·.1))) = true := by
  unfold kbOf
  rcases h : (kbMap F).find? v with _ | c
  · exact unknown_le _
  · obtain ⟨e, he, rfl, rfl⟩ := kbMap_find h
    have := kbFactsOk_all hk he
    simp only [hd, hp, Option.any_some, Bool.and_eq_true] at this
    exact this.2

/-- A statement's claim: none unless the statement is pure, and no stronger than the transfer
    of its operands' claims. -/
theorem kb_stmt (hk : kbFactsOk B D F = true) {v : Nat} {s : Stmt} (hd : defStmt B D v = some s) :
    match pureInst? s.inst with
    | some p => (kbOf (kbMap F) v).le (transferOf (kbMap F) p) = true
    | none => kbOf (kbMap F) v = KB.unknown := by
  have hD : ∃ b k, D.find? v = some (.stmt b k) := by
    unfold defStmt at hd; split at hd
    · exact ⟨_, _, ‹_›⟩
    · cases hd
  obtain ⟨b, k, hD⟩ := hD
  unfold kbOf
  rcases h : (kbMap F).find? v with _ | c
  · split
    · exact unknown_le _
    · rfl
  · obtain ⟨e, he, rfl, rfl⟩ := kbMap_find h
    have := kbFactsOk_all hk he
    simp only [hD, hd, Option.bind_some, Bool.and_eq_true] at this
    split
    · next p hp => simpa [hp] using this.2
    · next hp => simp [hp] at this

theorem kb_param (hk : kbFactsOk B D F = true) {v : Nat} (hd : D.find? v = some .param) :
    kbOf (kbMap F) v = KB.unknown := by
  unfold kbOf
  rcases h : (kbMap F).find? v with _ | c
  · rfl
  · obtain ⟨e, he, rfl, rfl⟩ := kbMap_find h
    have := kbFactsOk_all hk he
    simp [hd] at this

/-! ## Soundness of the facts of operands -/

theorem opVal_of_intVal {env : Env} {o : Operand} {n : Nat} (h : intVal env o = some (256, n)) :
    opVal env o = some (.int 256 n) := by
  unfold intVal at h
  split at h
  · next bits value hv => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [hv, h.1, h.2]
  · cases h

/-- An operand that evaluates to a word satisfies its fact. -/
theorem opFact_sat {K : NatMap KB} {env : Env} (hw : EnvW env) (hkb : KBHolds K env) {o : Operand}
    (ho : o.wf = true) {n : Nat} (h : intVal env o = some (256, n)) : n < W ∧ (opFact K o).Sat n := by
  have hv := opVal_of_intVal h
  cases o with
  | var v =>
    obtain ⟨m, hm, e⟩ := hw v _ hv
    cases e
    exact ⟨hm, hkb v n hv⟩
  | imm bits w =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
    simp only [opVal, Option.some.injEq, Val.int.injEq] at hv
    obtain ⟨_, rfl⟩ := hv
    refine ⟨ho.2, ?_⟩
    simp only [opFact, Nat.mod_eq_of_lt ho.2]
    exact sat_exact ho.2
  | undef => simp [Operand.wf] at ho

/-- The meet over a list of operands holds of the value of any of them. -/
theorem meetAll_sound {K : NatMap KB} {n : Nat} {os : List Operand} {o : Operand} (ho : o ∈ os)
    (h : (opFact K o).Sat n) : (meetAll K os).Sat n := by
  have fold : ∀ (l : List Operand) (acc : KB), (acc.Sat n ∨ ∃ x ∈ l, (opFact K x).Sat n) →
      (l.foldl (fun a x => meet a (opFact K x)) acc).Sat n := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons x l ih =>
      intro acc h
      refine ih _ ?_
      rcases h with h | ⟨y, hy, hs⟩
      · exact Or.inl (meet_sound (Or.inl h))
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl (meet_sound (Or.inr hs))
        · exact Or.inr ⟨y, hy, hs⟩
  cases os with
  | nil => cases ho
  | cons x l =>
    unfold meetAll
    rcases List.mem_cons.mp ho with rfl | ho
    · exact fold l _ (Or.inl h)
    · exact fold l _ (Or.inr ⟨o, ho, h⟩)

theorem evalOn_lt {p : PureInst} {xs : List Nat}
    (h : List.Forall₂ (fun _ x => x < W) p.args xs) : p.evalOn xs < W := by
  rcases p with ⟨o, a⟩ | ⟨o, a, b⟩ | ⟨o, a, b, m⟩ <;> simp only [PureInst.args] at h
  · rcases h with _ | ⟨hx, _ | _⟩; exact Op1.eval_lt o hx
  · rcases h with _ | ⟨hx, _ | ⟨hy, _ | _⟩⟩; exact Op2.eval_lt o hx hy
  · rcases h with _ | ⟨_, _ | ⟨_, _ | ⟨hz, _ | _⟩⟩⟩; exact Op3.eval_lt o hz

/-- The transfer of the operands' facts holds of the value. -/
theorem transfer_sound {K : NatMap KB} {p : PureInst} {xs : List Nat}
    (h : List.Forall₂ (fun o x => x < W ∧ (opFact K o).Sat x) p.args xs) :
    (transferOf K p).Sat (p.evalOn xs) := by
  rcases p with ⟨o, a⟩ | ⟨o, a, b⟩ | ⟨o, a, b, m⟩ <;> simp only [PureInst.args] at h
  · rcases h with _ | ⟨⟨hx, ha⟩, _ | _⟩; exact transfer1_sound o hx ha
  · rcases h with _ | ⟨⟨hx, ha⟩, _ | ⟨⟨hy, hb⟩, _ | _⟩⟩; exact transfer2_sound o hx hy ha hb
  · rcases h with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩; exact transfer3_sound o (opFact K a) (opFact K b) (opFact K m) _ _ _

/-! ## A statement -/

theorem forall₂_of_forall {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ bs, List.Forall₂ R l bs
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := forall₂_of_forall (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, .cons hb hbs⟩

/-- A pure statement whose operands are words runs to its word. -/
theorem runStmtO_pureInst {o : Oracle} {c : Ctx} {env : Env} {s : Stmt} {p : PureInst}
    (hp : pureInst? s.inst = some p) {xs : List Nat} (hargs : ArgsAre env p.args xs) :
    Returns (fun vals => vals = [.int p.bits (p.evalOn xs)]) (runStmtO o c env s) := by
  have hrun : runStmtO o c env s = runInst c env s.inst := by
    unfold runStmtO
    split
    · next heq => rw [heq] at hp; simp [pureInst?] at hp
    · rfl
  rw [hrun, ← pureInst?_toInst hp]
  by_cases hc : ∃ a, p = .op1 .clz a
  · obtain ⟨a, rfl⟩ := hc
    simp only [PureInst.args, ArgsAre] at hargs
    rcases hargs with _ | ⟨⟨ha, _⟩, _ | _⟩
    intro I w r w' h
    simp only [PureInst.toInst] at h
    rw [runInst_clz ha] at h
    split at h
    · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
    · cases h
  · rw [Schemas.runInst_pure (fun a e => hc ⟨a, e⟩) hargs]
    exact Returns.pure rfl

variable {sig : Sigs} {syms : List String} {T : DomTree}

/-- A statement keeps the claims. -/
theorem kb_stmt_step (hwf : f.wf sig syms = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {o : Oracle} {c : Ctx}
    {b k : Nat} {blk : Block} (hb : f.block? b = some blk) (hr : (T.reach.find? b).isSome = true)
    {st : Stmt} (hst : blk.body[k]? = some st) {env : Env} (hpi : PointInv f T b k env)
    (hkb : KBHolds (kbMap F) env) :
    Returns (fun vals => st.dsts.length = vals.length →
        KBHolds (kbMap F) ((st.dsts.zip vals).foldl bindStep env)) (runStmtO o c env st) := by
  have hu := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hsm : st ∈ blk.body := List.mem_of_getElem? hst
  have htys := ((Func.wf_words hwf).2 blk hmem).2 st hsm
  have hops := (Func.wf_operands hwf hmem).2.1 st hsm
  have hkl : k < blk.body.length := (List.getElem?_eq_some_iff.mp hst).1
  have huses := uses_defined hwf hs hb hr hkl.le hpi
  simp only [usesAt, hst] at huses
  -- every result of `st` is defined by `st`
  have hdef : ∀ d ∈ st.dsts, defStmt (.ofListBy (·.id) f.blocks) (defsOf f) d.1 = some st := by
    intro d hd
    have := defsOf_find hu (stmt_def hmem hst hd)
    simp only [defStmt, this, hid, blocks_find hb, Option.bind_some, hst]
  -- the bound values satisfy their claims: a word bound to each result
  have bound : ∀ vals : List Val, (∀ d ∈ st.dsts, ∀ v ∈ vals, ∀ n, v.as d.2 = .int 256 n →
      (kbOf (kbMap F) d.1).Sat n) → st.dsts.length = vals.length →
      KBHolds (kbMap F) ((st.dsts.zip vals).foldl bindStep env) := by
    intro vals hv _ v n hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, hxv⟩ | ⟨he, _⟩
    · exact hv x.1 (List.of_mem_zip hx).1 x.2 (List.of_mem_zip hx).2 n hxv.symm
    · exact hkb v n he
  cases hp : pureInst? st.inst with
  | none =>
    refine fun _ _ vals _ _ hl => bound vals (fun d hd _ _ n _ => ?_) hl
    have := kb_stmt hk (hdef d hd)
    simp only [hp] at this
    rw [this]; exact sat_unknown n
  | some p =>
    rw [pureInst?_args hp] at huses hops
    obtain ⟨xs, hxs⟩ := forall₂_of_forall
      (R := fun o x => intVal env o = some (256, x) ∧ o.wf = true)
      fun a ha => let ⟨n, hn⟩ := huses a ha; ⟨n, hn, hops a ha⟩
    have hargs : ArgsAre env p.args xs := List.Forall₂.imp (fun _ _ h =>
      ⟨by rw [evalOperand_eq, opVal_of_intVal h.1]; rfl, (opFact_sat hpi.1 hkb h.2 h.1).1⟩) hxs
    have hfacts : List.Forall₂ (fun o x => x < W ∧ (opFact (kbMap F) o).Sat x) p.args xs :=
      List.Forall₂.imp (fun _ _ h => opFact_sat hpi.1 hkb h.2 h.1) hxs
    have hlt := evalOn_lt (List.Forall₂.imp (fun _ _ h => h.1) hfacts)
    refine Returns.mono (runStmtO_pureInst hp hargs) fun vals hvals hl =>
      bound vals (fun d hd v hv n hvn => ?_) hl
    subst hvals
    rcases List.mem_singleton.mp hv with rfl
    rw [htys d hd, Val.as_word hlt] at hvn
    cases hvn
    have := kb_stmt hk (hdef d hd)
    simp only [hp] at this
    exact KB.Sat.le (transfer_sound hfacts) this

/-- A block's first `k` statements keep the definedness invariant and the claims. -/
theorem kb_take (hwf : f.wf sig syms = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (hr : (T.reach.find? b).isSome = true) {env₁ : Env}
    (h₀ : PointInv f T b 0 env₁ ∧ KBHolds (kbMap F) env₁) :
    ∀ k, k ≤ blk.body.length → Returns (fun env => PointInv f T b k env ∧ KBHolds (kbMap F) env)
      (runBodyO o c env₁ (blk.body.take k))
  | 0, _ => by simp only [List.take_zero, runBodyO]; exact Returns.pure h₀
  | k + 1, hkl => by
    have hlt : k < blk.body.length := by omega
    have hsk : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hsk, Option.toList_some, runBodyO_append]
    refine Returns.bind (kb_take hwf hs hk hoi c hb hr h₀ k (by omega)) fun env ⟨hpi, hkb⟩ => ?_
    have hm := (Func.machine_block (Func.wf_machine hwf) hb).2.1 _ (List.mem_of_getElem? hsk)
    simp only [runBodyO]
    refine Returns.bind (Returns.and (returns_runStmtO hoi c hpi.1.int hm)
      (kb_stmt_step hwf hs hk hb hr hsk hpi hkb)) fun vals ⟨hiv, hkv⟩ =>
      Returns.bind (returns_bind env _ vals) fun env₂ ⟨hl, he⟩ => Returns.pure ?_
    subst he
    exact ⟨point_succ' hwf hb hsk hpi hiv hl, hkv hl⟩

theorem zip_map_forall₂ {α β γ : Type} {R : α → β → Prop} {g : α → γ} {l : List α} {vs : List β}
    (h : List.Forall₂ R l vs) : ∀ {x}, x ∈ (l.map g).zip vs → ∃ a ∈ l, x.1 = g a ∧ R a x.2 := by
  induction h with
  | nil => intro x hx; simp at hx
  | @cons a v l vs hr _ ih =>
    intro x hx
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨a, List.mem_cons_self .., rfl, hr⟩
    · obtain ⟨a', ha', h1, h2⟩ := ih hx
      exact ⟨a', List.mem_cons_of_mem _ ha', h1, h2⟩

/-- An operand of a well-formed function that has a value has a word. -/
theorem opVal_word {env : Env} (hw : EnvW env) {o : Operand} (ho : o.wf = true) {val : Val}
    (h : opVal env o = some val) : ∃ m, val = .int 256 m ∧ intVal env o = some (256, m) := by
  cases o with
  | var v =>
    obtain ⟨m, _, rfl⟩ := hw v val h
    exact ⟨m, rfl, by simp only [intVal, opVal] at h ⊢; rw [h]⟩
  | imm bits w =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq] at ho
    obtain ⟨rfl, _⟩ := ho
    simp only [opVal, Option.some.injEq] at h
    exact ⟨w, h.symm, rfl⟩
  | undef => simp [Operand.wf] at ho

/-- Entering a block keeps the claims: each phi takes a value of one of its operands. -/
theorem kb_enter (hwf : f.wf sig syms = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {env : Env}
    {prev : Option Nat} {b : Nat} (hw : EnvW env) (hkb : KBHolds (kbMap F) env) {blk : Block}
    (hb : f.block? b = some blk) : Returns (KBHolds (kbMap F)) (enter env prev blk) := by
  have hu := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have htys := ((Func.wf_words hwf).2 blk hmem).1
  have hops := (Func.wf_operands hwf hmem).1
  rw [enter_eq]
  refine Returns.lift fun env' h => ?_
  unfold enterOpt at h
  rcases hm : blk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env) with _ | vals
  · rw [hm] at h; cases h
  rw [hm] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    intro v n hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, hxv⟩ | ⟨he, _⟩
    · obtain ⟨φ, hφ, hx1, hgv⟩ := zip_map_forall₂ (mapM_option_forall₂ hm) hx
      cases prev with
      | none => simp at hgv
      | some p =>
        simp only [Option.bind_eq_bind, Option.bind_some] at hgv
        obtain ⟨o', hinc, hov⟩ := Option.bind_eq_some_iff.mp hgv
        unfold inc at hinc
        rcases hf : φ.incoming.find? (·.2 == p) with _ | ⟨o'', q⟩ <;> rw [hf] at hinc <;>
          simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hinc
        subst hinc
        have hin := List.mem_of_find?_eq_some hf
        obtain ⟨m, hm2, hiv⟩ := opVal_word hw (hops φ hφ _ hin) hov
        obtain ⟨hmW, hsat⟩ := opFact_sat hw hkb (hops φ hφ _ hin) hiv
        rw [hx1, hm2] at hxv
        simp only [htys φ hφ] at hxv
        rw [as_word rfl hmW] at hxv
        cases hxv
        rw [hx1]
        have hD := defsOf_find hu (phi_def hmem hφ)
        have hphi : phiOf (.ofListBy (·.id) f.blocks) blk.id φ.dst = some φ := by
          simp only [phiOf, hid, blocks_find hb, Option.bind_some, find?_dst (hu.phis hmem) hφ]
        exact KB.Sat.le (meetAll_sound (List.mem_map.mpr ⟨_, hin, rfl⟩) hsat) (kb_phi hk hD hphi)
    · exact hkb v n he
  · cases h

/-- A block goes to a block state where the claims hold. -/
theorem kb_step (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {s : BState} (hi : BlockInv f T s) (hkb : KBHolds (kbMap F) s.1) :
    Returns (fun n => match n with
      | .goto env _ => KBHolds (kbMap F) env
      | .done _ => True) (stepBlock o c f s.1 s.2.1 s.2.2) := by
  obtain ⟨env, prev, b⟩ := s
  unfold stepBlock
  cases hb : f.block? b with
  | none => exact Returns.stuck _
  | some blk =>
    have hterm := (Func.machine_block (Func.wf_machine hwf) hb).2.2
    refine Returns.bind (Returns.and (point_zero hwf hv hi hb) (kb_enter hwf hs hk hi.1 hkb hb))
      fun env₁ h₀ => ?_
    have hbody := kb_take hwf hs hk hoi c hb hi.2.2.1 h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    refine Returns.bind hbody fun env₂ ⟨hpi, hkb₂⟩ => ?_
    refine Returns.mono (returns_runTerm hpi.1.int blk.term hterm) fun n hn => ?_
    cases n with
    | done _ => trivial
    | goto env' d =>
      obtain ⟨rfl, _⟩ := hn
      exact hkb₂

/-- **The known-bits invariant**, at block states.  Facts `F` that `kbFactsOk` accepts on a
    well-formed function in strict SSA: run it from its entry, its parameters bound to
    integers, with calls by an oracle that returns integers on integers; at every block state
    the run reaches, each value bound to a word satisfies its claim. -/
theorem kb_reaches (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {e : Block} (he : f.blocks.head? = some e)
    {args : List Val} (hargs : IntVals args) {I : ExecutionEnv} {w w₀ : World} {env₀ : Env}
    (h₀ : (bind {} f.params args).exec I w = some (.ok (env₀, w₀)))
    {s : BState} (hr : Reaches o c f (env₀, none, e.id) s) :
    BlockInv f T s ∧ KBHolds (kbMap F) s.1 := by
  have hu := UniqueDefs.of_ssa hs
  induction hr with
  | start =>
    refine ⟨entry_inv hwf hv he hargs I w env₀ w₀ h₀, ?_⟩
    obtain ⟨_, rfl⟩ := returns_bind {} f.params args I w env₀ w₀ h₀
    intro v n hvn
    rcases fold_get_cases _ _ _ _ hvn with ⟨x, hx, rfl, _⟩ | ⟨he', _⟩
    · rw [kb_param hk (defsOf_find hu (param_def (List.of_mem_zip hx).1))]
      exact sat_unknown n
    · simp at he'
  | step _ hx ih =>
    exact ⟨stepBlock_inv hwf hv hoi c ih.1 _ _ _ _ hx, kb_step hwf hv hs hk hoi c ih.1 ih.2 _ _ _ _ hx⟩

/-- **The known-bits invariant**, at every point: before statement `k` of the block of a block
    state the run reaches, each value bound to a word satisfies its claim. -/
theorem kb_point (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    (hk : kbFactsOk (.ofListBy (·.id) f.blocks) (defsOf f) F = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {e : Block} (he : f.blocks.head? = some e)
    {args : List Val} (hargs : IntVals args) {I : ExecutionEnv} {w w₀ : World} {env₀ : Env}
    (h₀ : (bind {} f.params args).exec I w = some (.ok (env₀, w₀)))
    {s : BState} (hr : Reaches o c f (env₀, none, e.id) s) {blk : Block}
    (hb : f.block? s.2.2 = some blk) {k : Nat} (hkl : k ≤ blk.body.length) :
    Returns (KBHolds (kbMap F))
      (enter s.1 s.2.1 blk >>= fun env₁ => runBodyO o c env₁ (blk.body.take k)) := by
  obtain ⟨hi, hkb⟩ := kb_reaches hwf hv hs hk hoi c he hargs h₀ hr
  refine Returns.bind (Returns.and (point_zero hwf hv hi hb) (kb_enter hwf hs hk hi.1 hkb hb))
    fun env₁ h₀' => ?_
  exact Returns.mono (kb_take hwf hs hk hoi c hb hi.2.2.1 h₀' k hkl) fun _ h => h.2

end Fe.Sonatina.Steps.Schemas
