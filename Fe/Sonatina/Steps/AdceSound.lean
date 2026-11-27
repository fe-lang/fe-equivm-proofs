import Fe.Sonatina.Steps.BranchCanonSound

/-!
# `adce` is sound

The simulation (`AR`) relates the output and the input at the same block, entered from the same
block or, where the output's block has no phis, from another: the output's environment binds
less (`EnvSub`) and only output values (`DomSub`), the input carries the definedness invariant
(`BlockInv`).  In a block, an output statement steps with the same input statement, and the
input steps alone through a removed one (total on the words the definedness invariant gives,
without a change of the world, `total_dead`; its results are no output values).  Where the
output's terminator goes to `t` and the input's to `d`, a bypass, the input runs on alone from
`d` to `t` through the blocks of the check's order, each a step to a later one or to `t`
(`ad_walk`), so it gets there, with the world as it was and only values the output does not have
bound anew.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## Removable instructions are total -/

theorem Total.mono {α : Type} {P Q : α → Prop} {x : FeM α} (h : Total P x)
    (hPQ : ∀ a, P a → Q a) : Total Q x := fun I w => by
  obtain ⟨a, hx, hp⟩ := h I w; exact ⟨a, hx, hPQ a hp⟩

theorem total_read (op : EvmOp) (ws : List UInt256) (h : op.readArity = some ws.length) :
    Total (fun vals => IntVals vals ∧ vals.length = 1) (op.run ws) := by
  intro I w
  cases op <;> simp only [EvmOp.readArity, reduceCtorEq, Option.some.injEq] at h <;>
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, ws⟩⟩⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at h <;> (try omega) <;>
    simp [EvmOp.run, Fe.EVM.selfAddress, Fe.EVM.balance, Fe.EVM.origin, Fe.EVM.caller,
      Fe.EVM.callvalue, Fe.EVM.calldataload, Fe.EVM.calldatasize, Fe.EVM.codesize,
      Fe.EVM.gasprice, Fe.EVM.extcodesize, Fe.EVM.extcodehash, Fe.EVM.returndatasize,
      Fe.EVM.blockhash, Fe.EVM.coinbase, Fe.EVM.timestamp, Fe.EVM.blockNumber,
      Fe.EVM.prevrandao, Fe.EVM.gaslimit, Fe.EVM.chainid, Fe.EVM.selfbalance, Fe.EVM.basefee,
      Fe.EVM.blobhash, Fe.EVM.blobbasefee, Fe.EVM.cload, Fe.EVM.mload, Fe.EVM.sload,
      Fe.EVM.tload, Fe.EVM.keccak256, IntVals, word, Val.isInt]
  all_goals (split_ifs <;> simp)

theorem intVals_bool (b : Bool) : IntVals [bool b] := rfl

/-- A removable instruction whose operands are words runs, without a change of the world, to as
    many integers as it gives. -/
theorem total_dead (c : Ctx) {env : Env} {i : Inst} {n : Nat} (hd : i.deadRes = some n)
    (ha : ∀ op ∈ i.args, ∃ x, intVal env op = some (256, x)) :
    Total (fun vals => IntVals vals ∧ vals.length = n) (runInst c env i) := by
  have pure_ok : i.pure = true → ∀ vals, pureVals env i = some vals → IntVals vals →
      vals.length = n → Total (fun vals => IntVals vals ∧ vals.length = n) (runInst c env i) :=
    fun hp vals hv hi hl => by rw [runInst_pure c env i hp, hv]; exact Total.pure ⟨hi, hl⟩
  cases i <;> simp only [Inst.deadRes, reduceCtorEq, Option.some.injEq] at hd <;> try subst hd
  case bin op a b =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    obtain ⟨y, hy⟩ := ha b (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, pairOpt, hx, hy]; rfl) (by simp [IntVals, Val.isInt]) rfl
  case cmp op a b =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    obtain ⟨y, hy⟩ := ha b (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, pairOpt, hx, hy]; rfl) (intVals_bool _) rfl
  case isZero a =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, hx]; rfl) (intVals_bool _) rfl
  case not a =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, hx]; rfl) (by simp [IntVals, Val.isInt]) rfl
  case neg a =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, hx]; rfl) (by simp [IntVals, Val.isInt]) rfl
  case ctz a =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, hx]; rfl) (by simp [IntVals, Val.isInt]) rfl
  case cast op a ty =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, hx]; rfl) (by simp [IntVals, Val.isInt]) rfl
  case ovf op a b =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    obtain ⟨y, hy⟩ := ha b (by simp [Inst.args])
    exact pure_ok rfl _ (by simp [pureVals, pairOpt, hx, hy]; rfl) (by simp [IntVals, Val.isInt, bool]) rfl
  case select cnd a b =>
    obtain ⟨x, hx⟩ := ha cnd (by simp [Inst.args])
    obtain ⟨va, hva⟩ := ha a (by simp [Inst.args])
    obtain ⟨vb, hvb⟩ := ha b (by simp [Inst.args])
    have hoa : ∃ v, opVal env a = some v ∧ v.isInt = true := by
      unfold intVal at hva; revert hva; rcases opVal env a with _ | (_ | _) <;> simp [Val.isInt]
    have hob : ∃ v, opVal env b = some v ∧ v.isInt = true := by
      unfold intVal at hvb; revert hvb; rcases opVal env b with _ | (_ | _) <;> simp [Val.isInt]
    obtain ⟨v, hv, hvi⟩ : ∃ v, opVal env (if x = 0 then b else a) = some v ∧ v.isInt = true := by
      split
      · exact hob
      · exact hoa
    exact pure_ok rfl [v] (by simp [pureVals, hx]; exact hv) (by simp [IntVals, hvi]) rfl
  case sat op a b ty =>
    obtain ⟨x, hx⟩ := ha a (by simp [Inst.args])
    obtain ⟨y, hy⟩ := ha b (by simp [Inst.args])
    simp only [runInst, evalInt_eq, hx, hy, lift, pure_bind]
    exact Total.pure ⟨rfl, rfl⟩
  case keccakWords ws =>
    simp only [runInst]
    refine Total.bind (Total.mapM (P := fun _ _ => True) fun o ho => ?_) fun _ _ => Total.pure ⟨rfl, rfl⟩
    obtain ⟨x, hx⟩ := ha o ho
    simp only [evalWord, evalInt_eq, hx, lift, pure_bind]
    exact Total.pure trivial
  case evm op args =>
    split at hd
    · next har =>
      simp only [Option.some.injEq] at hd
      subst hd
      simp only [runInst]
      refine Total.bind (Total.mapM (P := fun _ _ => True) fun o ho => ?_) fun ws hws => ?_
      · obtain ⟨x, hx⟩ := ha o ho
        simp only [evalWord, evalInt_eq, hx, lift, pure_bind]
        exact Total.pure trivial
      · exact total_read op ws (by rw [har, hws.length_eq])
    · cases hd

/-! ## What the check gives -/

/-- What an `adce` check accepting `f` to `f'` gives. -/
structure AFacts (f f' : Func) : Prop where
  params : f'.params = f.params
  machine' : f'.machine = true
  valid : (domTree f).valid f = true
  ssa : ssa f (domTree f) = true
  entry : ∀ e', f'.blocks.head? = some e' → ∃ e, f.blocks.head? = some e ∧ e'.id = e.id
  blocks : ∀ b' ∈ f'.blocks, (ACtx.of f f').blockOk b' = true

theorem checkAdce_facts {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : Schemas.StepFacts} (h : checkAdce f ids s F = true) : AFacts f s.func := by
  unfold checkAdce at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  rcases ids with _ | ids
  · simp at h
  cases he : f.blocks.head? with
  | none => simp [he] at h
  | some e =>
  cases he' : s.func.blocks.head? with
  | none => simp [he, he'] at h
  | some e' =>
  simp only [he, he', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hid, _⟩, hp⟩, hm⟩, hv⟩, hs⟩, hb⟩, _⟩, _⟩ := h
  exact ⟨hp, hm, hv, hs, fun e₁ h₁ => ⟨e, he, by rw [he'] at h₁; cases h₁; exact hid⟩, hb⟩

section facts

variable {f f' : Func}

theorem ACtx.B_find (b : Nat) : (ACtx.of f f').B.find? b = f.block? b := by
  simp only [ACtx.of, NatMap.find?_ofListBy, Func.block?]

theorem ACtx.B'_find (b : Nat) : (ACtx.of f f').B'.find? b = f'.block? b := by
  simp only [ACtx.of, NatMap.find?_ofListBy, Func.block?]

theorem ACtx.OD_eq : (ACtx.of f f').OD = defsOf f' := rfl

theorem block_id {g : Func} {b : Nat} {blk : Block} (h : g.block? b = some blk) : blk.id = b := by
  simpa using List.find?_some h

/-- An output block and the input block of its id, as the check relates them. -/
theorem ad_block (F : AFacts f f') {b : Nat} {ob : Block} (hob : f'.block? b = some ob) :
    ∃ ib, f.block? b = some ib ∧ (∀ φ ∈ ob.phis, φ ∈ ib.phis) ∧
      (∀ φ ∈ ib.phis, φ ∈ ob.phis ∨ (defsOf f').find? φ.dst = none) ∧
      adBodyOk (defsOf f') ob.body ib.body = true ∧
      termRel (ACtx.of f f').slotOk ob.term ib.term = true := by
  have hm := List.mem_of_find?_eq_some hob
  have hid := block_id hob
  have h := F.blocks ob hm
  unfold ACtx.blockOk at h
  rw [ACtx.B_find, hid] at h
  split at h
  · next ib hib =>
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, hasPhi, List.any_eq_true,
      decide_eq_true_eq, exists_eq_right, freshV, Option.isNone_iff_eq_none] at h
    exact ⟨ib, hib, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

end facts

/-! ## Bindings the output does not see -/

/-- `e₂` agrees with `e` on the values of the output. -/
def OutAgree (f' : Func) (e e₂ : Env) : Prop :=
  ∀ k, ((defsOf f').find? k).isSome = true → e₂[k]? = e[k]?

theorem OutAgree.refl (f' : Func) (e : Env) : OutAgree f' e e := fun _ _ => rfl

theorem OutAgree.trans {f' : Func} {e₁ e₂ e₃ : Env} (h₁ : OutAgree f' e₁ e₂)
    (h₂ : OutAgree f' e₂ e₃) : OutAgree f' e₁ e₃ := fun k hk => (h₂ k hk).trans (h₁ k hk)

/-- An output environment below `e` stays below an agreeing `e₂`. -/
theorem OutAgree.sub {f' : Func} {e' e e₂ : Env} (h : OutAgree f' e e₂) (hs : EnvSub e' e)
    (hd : DomSub f' e') : EnvSub e' e₂ := fun k v hv => by
  rw [h k (hd k (by rw [hv]; rfl))]; exact hs k v hv

/-- Binding values the output does not define keeps the agreement. -/
theorem fold_fresh {f' : Func} (l : List ((Nat × Ty) × Val)) (e : Env)
    (h : ∀ x ∈ l, (defsOf f').find? x.1.1 = none) : OutAgree f' e (l.foldl bindStep e) :=
  fun k hk => fold_get_not l e k fun hm => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    rw [h x hx] at hk; cases hk

/-! ## The input runs removed work -/

section total

variable {sig : Sigs} {syms : List String} {f f' : Func}

/-- A removable statement of a block the input reaches, from the point before it: the input
    runs it and binds its results, without a change of the world, to the point after it. -/
theorem total_stmt (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true)
    {k : Nat} {s : Stmt} (hsk : blk.body[k]? = some s) {e : Env}
    (hpi : PointInv f (domTree f) b k e) (hrem : removable (defsOf f') s = true) (o : Oracle)
    (c : Ctx) :
    Total (fun e₁ => PointInv f (domTree f) b (k + 1) e₁ ∧ OutAgree f' e e₁)
      (runStmtO o c e s >>= fun vals => Fe.Sonatina.bind e s.dsts vals) := by
  unfold removable at hrem
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, freshV,
    Option.isNone_iff_eq_none] at hrem
  obtain ⟨hd, hfr⟩ := hrem
  have hk : k < blk.body.length := (List.getElem?_eq_some_iff.mp hsk).1
  have hargs : ∀ op ∈ s.inst.args, ∃ x, intVal e op = some (256, x) := fun op hop =>
    uses_defined hwf hs hb hr (Nat.le_of_lt hk) hpi op (by unfold usesAt; rw [hsk]; exact hop)
  have hrun : runStmtO o c e s = runInst c e s.inst := by
    unfold runStmtO
    split
    · next heq => rw [heq] at hd; simp [Inst.deadRes] at hd
    · rfl
  rw [hrun]
  refine Total.bind (total_dead c hd hargs) fun vals ⟨hiv, hl⟩ => ?_
  have hbind : Fe.Sonatina.bind e s.dsts vals = pure ((s.dsts.zip vals).foldl bindStep e) := by
    unfold Fe.Sonatina.bind
    simp only [hl, beq_self_eq_true, ↓reduceIte]
    congr 1
  rw [hbind]
  refine Total.pure ⟨point_succ' hwf hb hsk hpi hiv hl.symm, fold_fresh _ _ fun x hx => ?_⟩
  exact hfr x.1 (List.of_mem_zip hx).1

/-- The statements of a block the input reaches from `k` on, all removable. -/
theorem total_body (hwf : f.wf sig syms = true) (hs : ssa f (domTree f) = true) {b : Nat}
    {blk : Block} (hb : f.block? b = some blk) (hr : ((domTree f).reach.find? b).isSome = true)
    (hall : ∀ s ∈ blk.body, removable (defsOf f') s = true) (o : Oracle) (c : Ctx) :
    ∀ (is : List Stmt) (k : Nat) (e : Env), blk.body.drop k = is → k ≤ blk.body.length →
      PointInv f (domTree f) b k e →
      Total (fun e₂ => PointInv f (domTree f) b blk.body.length e₂ ∧ OutAgree f' e e₂)
        (runBodyO o c e is)
  | [], k, e, hd, _, hpi => by
    have : k = blk.body.length := by have := List.drop_eq_nil_iff.mp hd; omega
    subst this
    exact Total.pure ⟨hpi, OutAgree.refl _ _⟩
  | s :: is, k, e, hd, _, hpi => by
    have hlt : k < blk.body.length := by
      rcases Nat.lt_or_ge k blk.body.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; cases hd
    rw [List.drop_eq_getElem_cons hlt] at hd
    simp only [List.cons.injEq] at hd
    obtain ⟨hsk, hdk⟩ := hd
    have hsk' : blk.body[k]? = some s := by rw [List.getElem?_eq_getElem hlt, hsk]
    have h1 := total_stmt hwf hs hb hr hsk' hpi (hall s (List.mem_of_getElem? hsk')) o c (f' := f')
    simp only [runBodyO]
    rw [← bind_assoc]
    refine Total.bind h1 fun e₁ ⟨hpi₁, ha₁⟩ => ?_
    exact Total.mono (total_body hwf hs hb hr hall o c is (k + 1) e₁ hdk (by omega) hpi₁)
      fun e₂ ⟨h₂, ha₂⟩ => ⟨h₂, ha₁.trans ha₂⟩

/-- A terminator that goes on, its operands integers: it goes to one of its successors. -/
theorem total_term {e : Env} {t : Term} (ht : t.isGoto = true)
    (hdef : ∀ op ∈ t.args, ∃ v, intVal e op = some v) :
    Total (fun n => ∃ d, n = .goto e d ∧ d ∈ t.succs) (runTerm e t) := by
  cases t with
  | jump d => exact Total.pure ⟨d, rfl, List.mem_singleton_self _⟩
  | br cnd nz z =>
    obtain ⟨v, hv⟩ := hdef cnd (List.mem_singleton_self _)
    unfold runTerm
    refine Total.bind (P := fun _ => True) (by rw [evalInt_eq, hv]; exact Total.lift rfl trivial)
      fun x _ => ?_
    rcases x with ⟨_, n⟩
    exact Total.pure ⟨_, rfl, by split <;> simp [Term.succs]⟩
  | brTable sc dflt cs =>
    cases dflt with
    | none => simp [Term.isGoto] at ht
    | some d =>
    obtain ⟨vs, hvs⟩ := hdef sc (List.mem_cons_self ..)
    unfold runTerm
    refine Total.bind (P := fun _ => True) (by rw [evalInt_eq, hvs]; exact Total.lift rfl trivial)
      fun x _ => ?_
    rcases x with ⟨_, v⟩
    dsimp only
    refine Total.bind (P := fun vals => List.Forall₂ (fun c p => p.2 = c.2) cs vals)
      (Total.mapM fun cse hc => ?_) fun vals hvals => ?_
    · rcases cse with ⟨o, dest⟩
      obtain ⟨vo, hvo⟩ := hdef o (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      exact Total.bind (P := fun _ => True) (by rw [evalInt_eq, hvo]; exact Total.lift rfl trivial)
        fun y _ => Total.pure rfl
    · cases hf : (vals.find? (·.1 == v)).map (·.2) with
      | none => exact Total.pure ⟨d, rfl, by simp [Term.succs]⟩
      | some x =>
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hf
        obtain ⟨c, hc, hpc⟩ := forall₂_mem_right hvals (List.mem_of_find?_eq_some hp)
        refine Total.pure ⟨_, rfl, ?_⟩
        simp only [Term.succs, Option.toList_some, List.mem_append, List.mem_singleton,
          List.mem_map]
        exact Or.inr ⟨c, hc, hpc.symm⟩
  | _ => simp [Term.isGoto] at ht

/-- A block a bypassed path crosses, entered from a predecessor: the input runs it, without a
    change of the world, to one of its successors, binding only values the output does not
    define. -/
theorem total_cross (hwf : f.wf sig syms = true) (F : AFacts f f') {r : Nat} {blk : Block}
    (hb : f.block? r = some blk) (hc : (ACtx.of f f').crossOk blk = true) {e : Env} {p : Nat}
    (hi : BlockInv f (domTree f) (e, some p, r)) (o : Oracle) (c : Ctx) :
    Total (fun n => ∃ e₂ x, n = .goto e₂ x ∧ OutAgree f' e e₂ ∧
        BlockInv f (domTree f) (e₂, some r, x)) (stepBlock o c f e (some p) r) := by
  unfold ACtx.crossOk at hc
  simp only [Bool.and_eq_true, List.all_eq_true, freshV, Option.isNone_iff_eq_none,
    ACtx.OD_eq] at hc
  obtain ⟨⟨⟨_, hph⟩, hbody⟩, hgo⟩ := hc
  have hr : ((domTree f).reach.find? r).isSome = true := hi.2.2.1
  obtain ⟨e₁, he₁⟩ := enter_total hwf F.ssa hi hb
  have hpi₀ : PointInv f (domTree f) r 0 e₁ := returns_lift_some (P := PointInv f (domTree f) r 0)
    (by rw [← he₁, ← enter_eq]; exact point_zero hwf F.valid hi hb)
  have ha₁ : OutAgree f' e e₁ := by
    obtain ⟨vals, _, hl, rfl⟩ := enterOpt_spec he₁
    refine fold_fresh _ _ fun x hx => ?_
    have := (List.of_mem_zip hx).1
    obtain ⟨φ, hφ, hx1⟩ := List.mem_map.mp this
    rw [← hx1]; exact hph φ hφ
  unfold stepBlock
  rw [hb]
  dsimp only
  rw [enter_eq, he₁]
  simp only [lift, pure_bind]
  have hbt := total_body hwf F.ssa hb hr hbody o c blk.body 0 e₁ rfl (Nat.zero_le _) hpi₀
  refine Total.bind hbt fun e₂ ⟨hpi₂, ha₂⟩ => ?_
  have hdef : ∀ op ∈ blk.term.args, ∃ v, intVal e₂ op = some v := fun op hop => by
    obtain ⟨n, hn⟩ := term_defined hwf F.ssa hb hr hpi₂ op hop
    exact ⟨_, hn⟩
  refine Total.mono (total_term hgo hdef) fun n ⟨x, hn, hx⟩ => ?_
  subst hn
  exact ⟨e₂, x, rfl, ha₁.trans ha₂, blockInv_of_point F.valid hb hr hpi₂ hx⟩

/-- The input from a block of the check's order runs on, without a change of the world, to `t`,
    binding only values the output does not define. -/
theorem ad_walk (hwf : f.wf sig syms = true) (F : AFacts f f') (o : Oracle) (c : Ctx) {t : Nat} :
    ∀ L, (ACtx.of f f').chainOk t L = true → ∀ r ∈ L, ∀ e p,
      BlockInv f (domTree f) (e, some p, r) → ∀ I w, ∃ e₂ q,
        (runFrom o c f (e, some p, r)).exec I w = (runFrom o c f (e₂, some q, t)).exec I w ∧
        BlockInv f (domTree f) (e₂, some q, t) ∧ OutAgree f' e e₂
  | [], _, r, hr, _, _, _, _, _ => nomatch hr
  | r₀ :: rest, hch, r, hr, e, p, hi, I, w => by
    unfold ACtx.chainOk at hch
    simp only [Bool.and_eq_true] at hch
    obtain ⟨hhd, hrest⟩ := hch
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [ACtx.B_find] at hhd
      split at hhd
      · next blk hb =>
        simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
          List.contains_iff_mem] at hhd
        obtain ⟨hc, hsucc⟩ := hhd
        obtain ⟨n, hn, e₂, x, rfl, ha, hi₂⟩ := total_cross hwf F hb hc hi o c I w
        have hstep := runFrom_goto (s := (e, some p, r)) hn
        have hx : x ∈ blk.term.succs := by
          obtain ⟨_, _, _, _, ⟨qb, hqb, hs⟩, _⟩ := hi₂
          rw [hb] at hqb; cases hqb; exact hs
        rcases hsucc x hx with rfl | hxr
        · exact ⟨e₂, r, hstep, hi₂, ha⟩
        · obtain ⟨e₃, q, h3, hi₃, ha₃⟩ := ad_walk hwf F o c rest hrest x hxr e₂ r hi₂ I w
          exact ⟨e₃, q, hstep.trans h3, hi₃, ha.trans ha₃⟩
      · cases hhd
    · exact ad_walk hwf F o c rest hrest r hr e p hi I w

end total

/-! ## The simulation -/

section sim

variable {sig : Sigs} {syms : List String} {f f' : Func}

/-- Block `b` of `g`, if there is one, has no phis. -/
def NoPhis (g : Func) (b : Nat) : Prop := ∀ blk, g.block? b = some blk → blk.phis = []

/-- The simulation: the same block, entered from the same block, or from another where the
    output's block has no phis; entered from nowhere, the input's block has no phis. -/
def AR (f f' : Func) (s' s : BState) : Prop :=
  s'.2.2 = s.2.2 ∧ (s'.2.1 = s.2.1 ∨ (∃ q, s.2.1 = some q) ∧ NoPhis f' s'.2.2) ∧
    (s.2.1 = none → NoPhis f s.2.2) ∧ EnvSub s'.1 s.1 ∧ DomSub f' s'.1 ∧
    BlockInv f (domTree f) s

/-- The relation before statement `k` of block `b`. -/
def AMid (f f' : Func) (e' e : Env) (b k : Nat) : Prop :=
  EnvSub e' e ∧ DomSub f' e' ∧ PointInv f (domTree f) b k e ∧
    ((domTree f).reach.find? b).isSome = true

/-- Where the input's run stands once an output block ends. -/
def AQ (o : Oracle) (c : Ctx) (f f' : Func) (b : Nat) : Next → FeM (List Val) → Prop
  | .goto e d, y => ∃ t, y = runFrom o c f t ∧ AR f f' (e, some b, d) t
  | .done v, y => y = pure v

theorem forall₂_of_mem_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {vs : List β}, List.Forall₂ R l vs → ∀ {a : α} {b : β}, (a, b) ∈ l.zip vs →
      R a b
  | _, _, .nil, _, _, h => nomatch h
  | _ :: _, _ :: _, .cons hr hl, a, b, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with e | h
    · cases e; exact hr
    · exact forall₂_of_mem_zip hl h

theorem zip_phi_mem {env : Env} {prev : Option Nat} {phis : List Phi} {vals : List Val}
    (hF : List.Forall₂ (fun phi v => (prev >>= inc phi >>= opVal env) = some v) phis vals)
    {x : (Nat × Ty) × Val} (hx : x ∈ (phis.map fun phi => (phi.dst, phi.ty)).zip vals) :
    ∃ φ ∈ phis, x.1 = (φ.dst, φ.ty) ∧ (prev >>= inc φ >>= opVal env) = some x.2 := by
  rw [List.zip_map_left] at hx
  obtain ⟨⟨φ, v⟩, hz, rfl⟩ := List.mem_map.mp hx
  exact ⟨φ, (List.of_mem_zip hz).1, rfl, forall₂_of_mem_zip hF hz⟩

/-- Entering an output block and the input block of its id from related states. -/
theorem ad_enter (hwf : f.wf sig syms = true) (F : AFacts f f') {b : Nat} {ob ib : Block}
    (hob : f'.block? b = some ob) (hib : f.block? b = some ib)
    (hsub : ∀ φ ∈ ob.phis, φ ∈ ib.phis)
    (hfr : ∀ φ ∈ ib.phis, φ ∈ ob.phis ∨ (defsOf f').find? φ.dst = none)
    {env' env : Env} {prev' prev : Option Nat} (hR : AR f f' (env', prev', b) (env, prev, b)) :
    Approx (fun e₁' e₁ => AMid f f' e₁' e₁ b 0) (enter env' prev' ob) (enter env prev ib) := by
  obtain ⟨_, hprev, hnone, hes, hds, hbi⟩ := hR
  simp only at hprev hnone hes hds hbi
  have hU := UniqueDefs.of_ssa F.ssa
  have hibm := List.mem_of_find?_eq_some hib
  have hobm := List.mem_of_find?_eq_some hob
  have hnd := hU.phis hibm
  rw [enter_eq, enter_eq]
  refine Approx.lift fun e₁' he₁' => ?_
  -- the output binds output values only
  have hds₁ : DomSub f' e₁' := by
    obtain ⟨vals', _, _, rfl⟩ := enterOpt_spec he₁'
    intro k hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
    · rw [List.zip_map_left] at hx
      obtain ⟨⟨φ, _⟩, hz, rfl⟩ := List.mem_map.mp hx
      exact defsOf_isSome (phi_def hobm (List.of_mem_zip hz).1)
    · exact hds k (by rw [he]; rfl)
  have finish : ∀ e₁, enterOpt env prev ib = some e₁ → EnvSub e₁' e₁ →
      ∃ e₂, enterOpt env prev ib = some e₂ ∧ AMid f f' e₁' e₂ b 0 := fun e₁ he₁ hsub₁ =>
    ⟨e₁, he₁, hsub₁, hds₁, returns_lift_some (P := PointInv f (domTree f) b 0)
      (by rw [← he₁, ← enter_eq]; exact point_zero hwf F.valid hbi hib), hbi.2.2.1⟩
  cases prev with
  | none =>
    have hnp := hnone rfl ib hib
    have hnp' : ob.phis = [] := List.eq_nil_iff_forall_not_mem.mpr fun φ hφ => by
      have := hsub φ hφ; rw [hnp] at this; cases this
    have he : enterOpt env none ib = some env := by simp [enterOpt, hnp]
    have he' : enterOpt env' prev' ob = some env' := by simp [enterOpt, hnp']
    rw [he'] at he₁'; cases he₁'
    exact finish env he hes
  | some q =>
    obtain ⟨e₁, he₁⟩ := enter_total hwf F.ssa hbi hib
    refine finish e₁ he₁ ?_
    obtain ⟨vals', hF', hl', rfl⟩ := enterOpt_spec he₁'
    obtain ⟨vals, hF, hl, rfl⟩ := enterOpt_spec he₁
    intro k v hk
    rcases fold_get_cases _ _ _ _ hk with ⟨x, hx, rfl, rfl⟩ | ⟨hk', hkn⟩
    · rcases hprev with hpp | ⟨_, hnp'⟩
      · subst hpp
        obtain ⟨φ, hφ, hx1, hx2⟩ := zip_phi_mem hF' hx
        obtain ⟨o, v₀, ho, hv₀, hget⟩ := enter_val hF hl hnd (hsub φ hφ)
        simp only [Option.bind_eq_bind, Option.bind_some, ho] at hx2
        have := hes.opVal hx2
        rw [hv₀] at this
        cases this
        rw [hx1]
        exact hget
      · rw [hnp' ob hob] at hx; simp at hx
    · have hkd : ((defsOf f').find? k).isSome = true := hds k (by rw [hk']; rfl)
      rw [fold_get_not _ _ k ?_]
      · exact hes k v hk'
      · intro hm
        rw [enter_keys hl] at hm
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hm
        rcases hfr φ hφ with hφo | hfresh
        · exact hkn (by rw [enter_keys hl']; exact List.mem_map_of_mem hφo)
        · rw [hfresh] at hkd; cases hkd

/-- An output block's statements against the input block's, from point `k`. -/
theorem ad_stmts (hwf : f.wf sig syms = true) (F : AFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block} (hb : f.block? b = some blk) {ob : Block}
    (hob : ob ∈ f'.blocks) (K : Env → FeM (List Val)) :
    ∀ (is os : List Stmt) (k : Nat) (e' e : Env), blk.body.drop k = is → k ≤ blk.body.length →
      adBodyOk (defsOf f') os is = true → (∀ s ∈ os, s ∈ ob.body) → AMid f f' e' e b k →
      Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ AMid f f' e₂' e₂ b blk.body.length)
        (runBodyO o c e' os) (runBodyO o c e is >>= K)
  | [], os, k, e', e, hd, hk, hok, _, hm => by
    have hkl : k = blk.body.length := by
      have := List.drop_eq_nil_iff.mp hd; omega
    subst hkl
    cases os with
    | nil => simp only [runBodyO, pure_bind]; exact Fol.pure ⟨e, rfl, hm⟩
    | cons _ _ => simp [adBodyOk] at hok
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
    obtain ⟨hes, hds, hpi, hr⟩ := hm
    have hmach : s.inst.machine = true :=
      Func.machine_block (Func.wf_machine hwf) hb s (List.mem_of_getElem? hsk)
    -- the input alone through a removed statement
    have removed : removable (defsOf f') s = true →
        ∀ os', adBodyOk (defsOf f') os' is = true → (∀ s ∈ os', s ∈ ob.body) →
        Fol (fun e₂' y => ∃ e₂, y = K e₂ ∧ AMid f f' e₂' e₂ b blk.body.length)
          (runBodyO o c e' os') (runBodyO o c e (s :: is) >>= K) := by
      intro hrem os' hok' hin'
      simp only [runBodyO, bind_assoc]
      rw [← bind_assoc]
      refine Fol.total (total_stmt hwf F.ssa hb hr hsk hpi hrem o c) fun e₁ ⟨hpi₁, ha₁⟩ => ?_
      exact ad_stmts hwf F ho hoi c hb hob K is os' (k + 1) e' e₁ hdk (by omega) hok' hin'
        ⟨ha₁.sub hes hds, hds, hpi₁, hr⟩
    cases os with
    | nil =>
      simp only [adBodyOk, Bool.and_eq_true] at hok
      exact removed hok.1 [] hok.2 (fun _ h => nomatch h)
    | cons s' os =>
      simp only [adBodyOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨rfl, hok⟩ | ⟨hrem, hok⟩
      · -- the same statement on both sides
        have hsob : s' ∈ ob.body := hin s' (List.mem_cons_self ..)
        simp only [runBodyO, bind_assoc]
        refine Fol.bind (Fol.approx (Approx.strengthen (Approx.runStmtO_sub ho hes hpi.1.int s' hmach)
            (returns_runStmtO hoi c hpi.1.int hmach))
          (Q := fun vals y => IntVals vals ∧
            y = (Fe.Sonatina.bind e s'.dsts vals >>= fun e₁ => runBodyO o c e₁ is >>= K))
          fun a' a ⟨h1, h2⟩ => ⟨h1 ▸ h2, h1 ▸ rfl⟩) ?_
        rintro vals y ⟨hiv, rfl⟩
        refine Fol.bind (Fol.approx (bind_rel e' e s'.dsts vals)
          (Q := fun e₁' y₂ => ∃ e₁, y₂ = (runBodyO o c e₁ is >>= K) ∧ AMid f f' e₁' e₁ b (k + 1))
          fun a' a ⟨hl, h1, h2⟩ => ⟨a, rfl, ?_⟩) ?_
        · subst h1 h2
          refine ⟨EnvSub.fold hes _, fun k' hk' => ?_, point_succ' hwf hb hsk hpi hiv hl, hr⟩
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hk'
          rcases fold_get_cases _ _ _ _ hv' with ⟨x, hx, rfl, _⟩ | ⟨he, _⟩
          · exact out_stmt_def hob hsob (List.of_mem_zip hx).1
          · exact hds k' (by rw [he]; rfl)
        · rintro e₁' y₂ ⟨e₁, rfl, hm₁⟩
          exact ad_stmts hwf F ho hoi c hb hob K is os (k + 1) e₁' e₁ hdk (by omega) hok
            (fun s hs => hin s (List.mem_cons_of_mem _ hs)) hm₁
      · exact removed hrem (s' :: os) hok hin

/-- `Fol.approx` where the input's continuation runs on alone to where `Q` holds. -/
theorem Fol.approx_walk {α : Type} {S : α → α → Prop} {Q : α → FeM (List Val) → Prop}
    {x' x : FeM α} {k : α → FeM (List Val)} (hx : Approx S x' x)
    (hk : ∀ a' a, S a' a → ∀ I w, ∃ y₁, (k a).exec I w = y₁.exec I w ∧ Q a' y₁) :
    Fol Q x' (x >>= k) := by
  intro I w' w hw
  have h := hx I w' w hw
  rw [Fe.M.exec_bind]
  revert h
  rcases x'.exec I w' with _ | (e' | ⟨a', w₁'⟩) <;> rcases x.exec I w with _ | (e | ⟨a, w₁⟩) <;>
    simp only [ResRel, imp_self, IsEmpty.forall_iff]
  · intro h; exact ⟨e, rfl, h⟩
  · intro h
    obtain ⟨y₁, hy, hq⟩ := hk a' a h.1 I w₁
    exact ⟨y₁, w₁, hy, hq, h.2⟩

/-- A terminator the check accepts against the input's: the same target, or a bypass the input
    runs to the output's target. -/
theorem ad_term (hwf : f.wf sig syms = true) (F : AFacts f f') (o : Oracle) (c : Ctx) {b : Nat}
    {ib : Block} (hib : f.block? b = some ib) {t' : Term}
    (ht : termRel (ACtx.of f f').slotOk t' ib.term = true) {e' e : Env}
    (hm : AMid f f' e' e b ib.body.length) :
    Fol (AQ o c f f' b) (runTerm e' t') (runTerm e ib.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) := by
  obtain ⟨hes, hds, hpi, hr⟩ := hm
  have hdef : ∀ op ∈ ib.term.args, ∃ v, intVal e op = some v := fun op hop => by
    obtain ⟨n, hn⟩ := term_defined hwf F.ssa hib hr hpi op hop
    exact ⟨_, hn⟩
  have happ := Approx.strengthen (approx_runTerm _ hes t' ib.term ht hdef)
    (returns_runTerm hpi.1.int ib.term)
  refine Fol.approx_walk happ fun n' n ⟨hn, hok⟩ I w => ?_
  rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only [NextTgt] at hn
  · obtain ⟨⟨rfl, rfl⟩, hsl⟩ := hn
    obtain ⟨_, hd⟩ := hok
    have hbi := blockInv_of_point F.valid hib hr hpi hd
    simp only [ACtx.slotOk, Bool.or_eq_true, beq_iff_eq] at hsl
    rcases hsl with rfl | hby
    · exact ⟨_, rfl, _, rfl, rfl, Or.inl rfl, fun h => by simp at h, hes, hds, hbi⟩
    · simp only [ACtx.bypassOk, Bool.and_eq_true, List.contains_iff_mem] at hby
      obtain ⟨⟨_, hnp⟩, hdL, hch⟩ := hby
      obtain ⟨e₂, q, hx, hbi₂, ha⟩ := ad_walk hwf F o c _ hch d hdL _ b hbi I w
      refine ⟨runFrom o c f (e₂, some q, d'), hx, _, rfl, rfl, Or.inr ⟨⟨q, rfl⟩, ?_⟩,
        fun h => by simp at h, ha.sub hes hds, hds, hbi₂⟩
      intro ob hob
      simp only [ACtx.noPhis', ACtx.B'_find, hob, Option.all_some, List.isEmpty_iff] at hnp
      exact hnp
  · subst hn; exact ⟨pure _, rfl, rfl⟩

/-- One output block against the input's run from a related state. -/
theorem ad_block_fol (hwf : f.wf sig syms = true) (F : AFacts f f') {o : Oracle}
    (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) {s' s : BState} (hR : AR f f' s' s) :
    Fol (AQ o c f f' s'.2.2) (stepBlock o c f' s'.1 s'.2.1 s'.2.2) (runFrom o c f s) := by
  obtain ⟨env', prev', b⟩ := s'
  obtain ⟨env, prev, b₀⟩ := s
  have hbb : b = b₀ := hR.1
  subst hbb
  unfold stepBlock
  cases hob : f'.block? b with
  | none => exact Fol.stuck
  | some ob =>
  dsimp only
  have hobm := List.mem_of_find?_eq_some hob
  obtain ⟨ib, hib, hsub, hfr, hbody, hterm⟩ := ad_block F hob
  rw [runFrom_enter o c hib]
  refine Fol.bind (Fol.approx (ad_enter hwf F hob hib hsub hfr hR)
    (Q := fun e₁' y => ∃ e₁, y = inRun o c f b ib e₁ ∧ AMid f f' e₁' e₁ b 0)
    fun a' a h => ⟨a, rfl, h⟩) ?_
  rintro e₁' _ ⟨e₁, rfl, hm⟩
  unfold inRun
  have := ad_stmts hwf F ho hoi c hib hobm (fun e => runTerm e ib.term >>= fun
      | .goto e d => runFrom o c f (e, some b, d)
      | .done v => pure v) ib.body ob.body 0 e₁' e₁ rfl (Nat.zero_le _) hbody (fun _ h => h) hm
  refine Fol.bind this fun e₂' y ⟨e₂, hy, hm₂⟩ => ?_
  subst hy
  exact ad_term hwf F o c hib hterm hm₂

theorem ad_sim (hwf : f.wf sig syms = true) (F : AFacts f f') {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) : Sim o c f' f (AR f f') := by
  intro s' s hR I w' w hw
  have h := ad_block_fol hwf F ho hoi c hR I w' w hw
  revert h
  rcases (stepBlock o c f' s'.1 s'.2.1 s'.2.2).exec I w' with _ | (e' | ⟨n, w₁'⟩)
  · intro _; trivial
  · exact id
  · rintro ⟨y₁, w₁, hy, hq, hw₁⟩
    cases n with
    | goto env d =>
      obtain ⟨t, rfl, hR'⟩ := hq
      exact ⟨t, w₁, hy, hR', hw₁⟩
    | done v =>
      simp only [AQ] at hq
      subst hq
      exact ⟨w₁, by rw [hy, Fe.M.exec_pure], hw₁⟩

/-- An `adce` step is sound: the output function, its calls run by an oracle that approximates
    itself and returns integers on integers, approximates the well-formed input function on
    integers. -/
theorem adce_sound {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx)
    {ids : Option (List (List Nat))} {s : FuncSnap} {F : Schemas.StepFacts}
    (hwf : f.wf sig syms = true) (h : checkAdce f ids s F = true) :
    FuncRef o c (some s.func) (some f) := by
  have Fa := checkAdce_facts h
  have sim := ad_sim hwf Fa ho hoi c
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he' : s.func.blocks.head? with
  | none => exact Approx.stuck _
  | some e' =>
  obtain ⟨e, he, hid⟩ := Fa.entry e' he'
  rw [he]
  dsimp only
  rw [Fa.params, hid]
  have hnp : NoPhis f e.id := fun blk hblk => by
    have : f.block? e.id = some e := by
      cases hf : f.blocks with
      | nil => rw [hf] at he; cases he
      | cons x l =>
        rw [hf] at he
        simp only [List.head?_cons, Option.some.injEq] at he
        subst he
        simp [Func.block?, hf]
    rw [this] at hblk; cases hblk
    exact entry_phis hwf he
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _)
    (Returns.and (entry_inv hwf Fa.valid he hargs) (returns_bind {} f.params args)))
    fun env env₀ ⟨e₁, hi, _, hfold⟩ => ?_
  cases e₁
  refine Sim.approx sim (env, none, e.id) (env, none, e.id)
    ⟨rfl, Or.inl rfl, fun _ => hnp, EnvSub.refl _, fun k hk => ?_, hi⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  rw [hfold] at hv
  rcases fold_get_cases _ _ _ _ hv with ⟨x, hx, rfl, _⟩ | ⟨he₀, _⟩
  · exact defsOf_isSome (param_def (Fa.params ▸ (List.of_mem_zip hx).1))
  · simp at he₀

end sim

theorem adce_stepSound : StepSound .adce :=
  StepSound.of_func fun _ _ _ _ c ho hoi _ _ _ _ _ hw h =>
    adce_sound ho hoi c hw (by simpa only [checkFunc] using h)

end Fe.Sonatina.Steps
