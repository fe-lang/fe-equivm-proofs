import Fe.Sonatina.Stage3.Place.Fns

/-!
# The entry, block entry and terminator obligations of a placed function

From `check`, each function `mkFn` gives satisfies `EntryObl` (`FnUnp.entryObl`: the machine
entry is the region start of the source entry or a block that only jumps there, and related
arguments bind related parameters), `PhiObl` (`FnUnp.phiObl`: the machine's phis, entered from the
block a source predecessor's region ends in, take related values) and `TermObl`
(`FnUnp.termObl`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Helpers -/

theorem exec_mapM_quiet {α β : Type} {f : α → FeM β} (hf : ∀ a, Quiet (f a)) :
    ∀ {l : List α} {I : Fe.EVM.Env} {w w' : World} {vs : List β},
      (l.mapM f).exec I w = some (.ok (vs, w')) →
      w' = w ∧ List.Forall₂ (fun a v => (f a).exec I w = some (.ok (v, w))) l vs
  | [], I, w, w', vs, h => by
    simp only [List.mapM_nil, Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, .nil⟩
  | a :: l, I, w, w', vs, h => by
    rw [List.mapM_cons] at h
    rcases exec_bind_some h with ⟨e, h1, he⟩ | ⟨b, w₁, h1, h2⟩
    · cases he
    · have hw := Quiet.world (hf a) h1
      subst hw
      rcases exec_bind_some h2 with ⟨e, h3, he⟩ | ⟨bs, w₂, h3, h4⟩
      · cases he
      · simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        obtain ⟨rfl, hF⟩ := exec_mapM_quiet hf h3
        exact ⟨rfl, .cons h1 hF⟩

theorem mapM_some_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = some b) →
      ∃ bs, l.mapM f = some bs ∧ List.Forall₂ (fun a b => f a = some b) l bs
  | [], _ => ⟨[], rfl, .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs, hF⟩ := mapM_some_of (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: bs, ?_, .cons hb hF⟩
    simp [List.mapM_cons, hb, hbs]

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by cases h
  | (k, v) :: l, a, b, h => by
    unfold List.lookup at h
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      subst h
      have : a = k := by simpa using he
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem pairwise_ne {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a
  | [], _, a, ha, _, _, _ => by cases ha
  | x :: l, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | ha' <;> rcases List.mem_cons.mp hb with h2 | hb'
    · exact absurd (h1.trans h2.symm) hab
    · subst h1; exact Or.inl (h.1 b hb')
    · subst h2; exact Or.inr (h.1 a ha')
    · exact pairwise_ne h.2 a ha' b hb' hab

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | [], [], .nil, _, h => by cases h
  | x :: _, y :: _, .cons hr hs, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right hs h
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- The incoming entry a machine phi takes from the block `tp` a source predecessor `p`'s region
    ends in is the image of the source phi's entry from `p`: the machine phi's blocks are
    distinct, and no other source block's region ends in `tp`. -/
theorem incoming_find {vm : VM} {tb : NatMap Nat} {inc minc : List (Operand × Nat)} {p tp : Nat}
    (hF : List.Forall₂ (fun (a b : Operand × Nat) => mop vm a.1 = some b.1 ∧ tb.find? a.2 = some b.2)
      inc minc)
    (hnd : (minc.map (·.2)).Nodup) (htp : tb.find? p = some tp)
    (hinj : ∀ b, tb.find? b = some tp → b = p) {mo : Operand × Nat}
    (hm : minc.find? (·.2 == tp) = some mo) :
    ∃ o, inc.find? (·.2 == p) = some (o, p) ∧ mop vm o = some mo.1 := by
  have hmo := List.mem_of_find?_eq_some hm
  have hmt : mo.2 = tp := by simpa using List.find?_some hm
  obtain ⟨a, ha, ha1, ha2⟩ := forall₂_mem_right hF hmo
  rw [hmt] at ha2
  have hap : a.2 = p := hinj _ ha2
  obtain ⟨⟨o₀, p₀⟩, hf0⟩ : ∃ x, inc.find? (·.2 == p) = some x := by
    cases h : inc.find? (·.2 == p) with
    | some x => exact ⟨x, rfl⟩
    | none =>
      rw [List.find?_eq_none] at h
      exact absurd (by simpa using hap) (h a ha)
  have hp0 : p₀ = p := by simpa using List.find?_some hf0
  subst hp0
  obtain ⟨b, hb, hb1, hb2⟩ := forall₂_mem hF (List.mem_of_find?_eq_some hf0)
  rw [htp] at hb2
  have hbe : b = mo := by
    have h1 := find?_of_nodup (fun y : Operand × Nat => y.2) hnd hb
    rw [← Option.some.inj hb2] at h1
    rw [h1] at hm
    exact Option.some.inj hm
  subst hbe
  exact ⟨o₀, hf0, hb1⟩

theorem walk_tb_mem {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} {vm' : VM} {tbk : Nat} {ms' : List Stmt} {dss : List (List Nat)} {bs : List Nat},
    walk c true vm l mb ms cs = some (vm', tbk, ms', dss, bs) → tbk = mb ∨ tbk ∈ bs
  | [], mb, ms, cs, vm', tbk, ms', dss, bs, h => by
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.1.symm
  | s :: rest, mb, ms, cs, vm', tbk, ms', dss, bs, h => by
    rw [walk_cons] at h
    rcases hc : calleeOf s cs with ⟨callee?, cs₀⟩
    rw [hc] at h
    dsimp only at h
    obtain ⟨⟨vm₁, mb₁, ms₁, ds₁⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨vm₂, tb₂, ms₂, dss₂, bs₂⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rcases walk_tb_mem h2 with h3 | h3
    · subst h3
      unfold entered
      by_cases hm : mb = tb₂
      · exact Or.inl hm.symm
      · right
        simp only [beq_iff_eq]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact Or.inr (List.mem_append_right _ h3)

theorem blockLower_tb_mem {c : FCtx} {vm : VM} {rets : List Ty} {b : HBlock} {cs : List Nat}
    {vm' : VM} {tbk : Nat} {dss : List (List Nat)} {bs : List Nat}
    (h : blockLower c true vm rets b cs = some (vm', tbk, dss, bs)) : tbk ∈ bs := by
  obtain ⟨mb, mblk, ms, bsw, tblk, -, -, hw, -, -, rfl⟩ := blockLower_some h
  rcases walk_tb_mem hw with h | h
  · subst h; exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h


theorem length_dedupB_le : ∀ (l : List Nat), l.dedupB.length ≤ l.length
  | [] => le_refl _
  | y :: ys => by
    simp only [List.dedupB]
    have := length_dedupB_le ys
    split <;> simp only [List.length_cons] <;> omega

theorem mem_dedupB {x : Nat} : ∀ {l : List Nat}, x ∈ l.dedupB ↔ x ∈ l
  | [] => by simp [List.dedupB]
  | y :: ys => by
    simp only [List.dedupB]
    split
    · next h =>
      rw [mem_dedupB, List.mem_cons]
      refine ⟨Or.inr, fun h' => h'.elim (fun e => ?_) id⟩
      subst e
      exact mem_dedupB.mp (List.elem_iff.mp h)
    · rw [List.mem_cons, mem_dedupB, List.mem_cons]

theorem nodupB_nodup : ∀ {l : List Nat}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | y :: ys, h => by
    simp only [nodupB, List.dedupB, beq_iff_eq] at h
    split at h
    · have := length_dedupB_le ys
      simp only [List.length_cons] at h
      omega
    · next hc =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      refine List.nodup_cons.mpr ⟨fun hy => hc ?_, nodupB_nodup (by simp [nodupB, h])⟩
      exact List.elem_iff.mpr (mem_dedupB.mpr hy)

/-- What `phisOk` checks, phi by phi. -/
theorem phisOk_get {c : FCtx} {vm : VM} {tb : NatMap Nat} {ps mps : List Phi}
    (h : phisOk c vm tb ps mps = true) : ps.length = mps.length ∧
    ∀ (j : Nat) (p mp : Phi), ps[j]? = some p → mps[j]? = some mp →
      vm.find? p.dst = some (.var mp.dst) ∧ mp.ty = w256 ∧ Ty.value p.ty = true ∧
      (∀ x ∈ p.incoming, (c.tyOf x.1).any (sameW · p.ty) = true) ∧
      (mp.incoming.map (·.2)).Nodup ∧
      List.Forall₂ (fun (a b : Operand × Nat) => mop vm a.1 = some b.1 ∧ tb.find? a.2 = some b.2)
        p.incoming mp.incoming := by
  simp only [phisOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun j p mp hp hmp => ?_⟩
  have h2 := h.2 (p, mp) (mem_zip_of hp hmp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩ := h2
  refine ⟨h1, h2, h3, fun x hx => h4 x hx, nodupB_nodup h6, ?_⟩
  refine (mapM_some_forall₂ h7).imp fun a b hab => ?_
  obtain ⟨o, b'⟩ := a
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hab
  obtain ⟨o', ho', b'', hb'', rfl⟩ := hab
  exact ⟨ho', hb''⟩


theorem exists_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ bs, List.Forall₂ R l bs
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := exists_forall₂ (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, .cons hb hbs⟩

/-- H's entry into block `db` from `p`, when each phi has an entry from `p` with a value. -/
theorem henter_some {env : HEnv} {p : Nat} {db : HBlock} {vs : List H.Val}
    (h : List.Forall₂ (fun (phi : Phi) v => ∃ o, phi.incoming.find? (·.2 == p) = some (o, p) ∧
      evalOp env o = some v) db.phis vs) :
    H.enter env (some p) db = bindVals env (db.phis.map fun phi => (phi.dst, phi.ty)) vs := by
  unfold H.enter
  suffices hm : ∀ (l : List Phi) (vs : List H.Val), List.Forall₂ (fun (phi : Phi) v =>
      ∃ o, phi.incoming.find? (·.2 == p) = some (o, p) ∧ evalOp env o = some v) l vs →
      l.mapM (fun phi => do
        let p ← (some p : Option Nat)
        let (o, _) ← phi.incoming.find? (·.2 == p)
        evalOp env o) = some vs by
    rw [hm _ _ h]; rfl
  intro l vs hl
  induction hl with
  | nil => rfl
  | cons hr _ ih =>
    obtain ⟨o, hf, hv⟩ := hr
    simp at ih
    simp [List.mapM_cons, hf, hv, ih]


section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.declParam (U : FnUnp src low r fn fr fl e me be rs) {p : Nat × Ty}
    (hp : p ∈ fn.f.params) : (declsOf fn.f).find? p.1 = some p.2 := by
  unfold declsOf
  rw [NatMap.find?_ofList]
  refine lookup_of_nodup ?_ (List.mem_append_left _ hp)
  have : (fn.f.params ++ fn.f.blocks.flatMap fun b =>
      b.phis.map (fun p => (p.dst, p.ty)) ++ b.body.flatMap (·.dsts)).map (·.1) = fn.f.defs := by
    simp [HFunc.defs, List.map_flatMap, Function.comp_def]
  rw [this]; exact U.shape'.2.2.2.2.2.2.2.2.1

theorem FnUnp.declPhi (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {p : Phi} (hp : p ∈ b.phis) : (declsOf fn.f).find? p.dst = some p.ty := by
  unfold declsOf
  rw [NatMap.find?_ofList]
  refine lookup_of_nodup (p := (p.dst, p.ty)) ?_ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨b, hb, List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩))
  have : (fn.f.params ++ fn.f.blocks.flatMap fun b =>
      b.phis.map (fun p => (p.dst, p.ty)) ++ b.body.flatMap (·.dsts)).map (·.1) = fn.f.defs := by
    simp [HFunc.defs, List.map_flatMap, Function.comp_def]
  rw [this]; exact U.shape'.2.2.2.2.2.2.2.2.1

theorem FnUnp.paramsNodup (U : FnUnp src low r fn fr fl e me be rs) :
    (fn.f.params.map (·.1)).Nodup :=
  U.shape'.2.2.2.2.2.2.2.2.1.sublist (by unfold HFunc.defs; exact List.sublist_append_left _ _)

theorem FnUnp.mparamsNodup (U : FnUnp src low r fn fr fl e me be rs) :
    (fn.c.mf.params.map (·.1)).Nodup :=
  U.shape'.2.2.2.2.2.2.2.2.2.2.1.sublist (by unfold mdefs; exact List.sublist_append_left _ _)

/-- The function's entry. -/
theorem FnUnp.entryObl {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (I : Fe.EVM.Env) : EntryObl I (secS src r efp) fn := by
  obtain ⟨hpl, hmpw, hpv, -, -, -, he0, hj, -, -, -, -⟩ := U.shape'
  have heb : e ∈ fn.f.blocks := mem_of_head U.he
  obtain ⟨mb₀, mblk₀, _, _, _, _, _, hst, -⟩ := U.walkOk heb
  have hst' := hst
  simp only [Fn.start, U.hbe, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at hst'
  obtain ⟨mblk, hmblk, rfl, rfl⟩ := hst'
  refine ⟨e, me, be, mblk, U.he, U.hme, hst, ?_, ?_⟩
  · rcases hj with h | h
    · exact Or.inl h
    · simp only [jumpOnly, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
      exact Or.inr ⟨h.1.1, h.1.2, h.2⟩
  · intro args vs g hst envM w hA hb
    obtain ⟨hvl, hal, hrel⟩ := hA
    simp only [Fe.Sonatina.bind] at hb
    split at hb
    · next hlen =>
      simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      simp only [beq_iff_eq] at hlen
      have hbv : bindVals {} fn.f.params vs = some ((fn.f.params.zip vs).foldl
          (fun env (q : (Nat × Ty) × H.Val) => env.insert q.1.1 q.2) {}) := by
        unfold bindVals
        rw [if_pos]
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨hvl.symm, fun q hq => ?_⟩
        obtain ⟨i, hqi⟩ := List.mem_iff_getElem?.mp hq
        rw [List.getElem?_zip_eq_some] at hqi
        obtain ⟨a, ha⟩ := get_of_len hqi.1 hal.symm
        obtain ⟨m, -, hf, -⟩ := hrel i q.1 q.2 a hqi.1 hqi.2 ha
        exact hf
      refine ⟨_, hbv, he0, ?_⟩
      intro x hx
      have hlv := U.rules.live
      simp only [liveOkAt, Bool.and_eq_true, U.he, List.all_eq_true, List.any_eq_true,
        beq_iff_eq] at hlv
      rw [U.hL] at hx
      obtain ⟨p, hp, rfl⟩ := hlv.2 x hx
      obtain ⟨j, hpj⟩ := List.mem_iff_getElem?.mp hp
      obtain ⟨v, hvj⟩ := get_of_len hpj hvl.symm
      obtain ⟨a, haj⟩ := get_of_len hpj hal.symm
      obtain ⟨mp, hmpj⟩ := get_of_len hpj hpl
      obtain ⟨m, rfl, hf, hvr, hvo, hor⟩ := hrel j p v a hpj hvj haj
      have hvmp : fn.F.vm.find? p.1 = some (.var mp.1) := by
        have := U.params
        simp only [paramsOk, List.all_eq_true, beq_iff_eq] at this
        rw [U.vm]; exact this (p, mp) (mem_zip_of hpj hmpj)
      have hmW : m < W := vrel_lt hvr hf (by simpa using List.all_eq_true.mp hpv p hp)
      refine ⟨v, m, ?_, ⟨p.2, by rw [U.hF]; exact U.declParam hp, hf⟩, ?_, hvr, hvo, hor⟩
      · exact foldl_insert_get (fun q : (Nat × Ty) × H.Val => q.1.1) (fun q => q.2)
          (fn.f.params.zip vs) {} (by rw [map_fst_zip_key (·.1) _ _ hvl.symm]; exact U.paramsNodup)
          (p, v) (mem_zip_of hpj hvj)
      · rw [hvmp]
        simp only [Option.bind_some, mval]
        have := foldl_insert_get (fun q : (Nat × Ty) × Val => q.1.1) (fun q => q.2.as q.1.2)
          (fn.c.mf.params.zip args) {} (by rw [map_fst_zip_key (·.1) _ _ hlen]; exact U.mparamsNodup)
          (mp, .int 256 m) (mem_zip_of hmpj haj)
        simp only at this
        rw [this]
        have hw : mp.2 = w256 := by
          simpa using List.all_eq_true.mp hmpw mp (List.mem_of_getElem? hmpj)
        rw [hw]
        simp only [W] at hmW
        simpa [Val.as, Ty.bits, w256] using hmW
    · cases hb

/-- No two source blocks' regions end in the same machine block (their blocks are distinct). -/
theorem FnUnp.tbInj (U : FnUnp src low r fn fr fl e me be rs) {p₁ p₂ t : Nat}
    (h₁ : fn.tb.find? p₁ = some t) (h₂ : fn.tb.find? p₂ = some t) : p₁ = p₂ := by
  rw [U.htb, U.tbOf, NatMap.find?_ofList] at h₁ h₂
  obtain ⟨x₁, hx₁, he₁⟩ := List.mem_map.mp (lookup_mem h₁)
  obtain ⟨x₂, hx₂, he₂⟩ := List.mem_map.mp (lookup_mem h₂)
  have hin : ∀ x ∈ rs, x.2.1 ∈ x.2.2.2 := by
    intro x hx
    obtain ⟨⟨b, cs⟩, -, hbl⟩ := forall₂_mem_right (mapM_some_forall₂ U.regions) hx
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hbl
    obtain ⟨⟨vm', tbk, dss, bs⟩, hbl, rfl⟩ := hbl
    exact blockLower_tb_mem hbl
  have hd := distinct_nodup U.dist
  rw [List.nodup_append] at hd
  have hnd := List.nodup_flatMap.mp hd.2.1
  by_cases hx : x₁ = x₂
  · subst hx
    simp only [Prod.mk.injEq] at he₁ he₂
    rw [← he₁.1, ← he₂.1]
  · have t₁ := hin x₁ hx₁
    have t₂ := hin x₂ hx₂
    simp only [Prod.mk.injEq] at he₁ he₂
    rw [he₁.2] at t₁
    rw [he₂.2] at t₂
    rcases pairwise_ne hnd.2 x₁ hx₁ x₂ hx₂ hx with hdj | hdj
    · exact absurd t₂ (hdj t₁)
    · exact absurd t₁ (hdj t₂)

/-- Rule S3's certificate at a phi: its operands' origins are its own. -/
theorem FnUnp.origPhi (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {p : Phi} (hp : p ∈ b.phis) {o : Operand} {q : Nat} (hx : (o, q) ∈ p.incoming) :
    ∀ a ∈ origOf fn.F.O o, a ∈ origOf fn.F.O (.var p.dst) := by
  have h := U.rules.orig
  simp only [origOk, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h.2 b hb).1 p hp (o, q) hx
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h1
  rw [U.hF]; exact h1

/-- Rule S8's certificate at a phi: a derived operand makes it derived. -/
theorem FnUnp.derPhi {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (hz : secZ src r = true) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {p : Phi} (hp : p ∈ b.phis) {o : Operand} {q : Nat} (hx : (o, q) ∈ p.incoming)
    (hd : (secX src r).derived.op fn.k o = true) : fn.F.D p.dst = true := by
  have h := hS.der hz
  unfold derivedOk at h
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have hf : (fn.k, fn.f, withCallees fr fn.f) ∈ derivedInput (secP src r) := by
    have := mem_placed (r := r) U.hf
    rw [← U.hfr] at this
    exact List.mem_map.mpr ⟨_, this, rfl⟩
  have hwj : (withCallees fr fn.f)[j]? = some (withCallees.go b.body ((fr.calls[j]?).getD [])) := by
    unfold withCallees
    rw [List.getElem?_map, List.getElem?_zipIdx, hj]; simp
  have h1 := ((h _ hf).2 _ (mem_zip_of hj hwj)).1.1 p hp
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · have : p.incoming.any (fun x => (secX src r).derived.op fn.k x.1) = true :=
      List.any_eq_true.mpr ⟨(o, q), hx, hd⟩
    rw [this] at h1; cases h1
  · rw [U.hF]; exact h1

/-- One phi of block `db`, entered from source predecessor `pb`, against the machine phi at its
    place, whose entry from the block `pb`'s region ends in is `mo`: the source phi's entry from
    `pb` has a value of the phi's type related to `mo`'s word. -/
theorem FnUnp.phiOne {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {db pb : HBlock} (hdb : db ∈ fn.f.blocks)
    (hsucc : db.id ∈ pb.term.succs) {mblk : Block}
    (hph : phisOk fn.c fn.F.vm fn.tb db.phis mblk.phis = true) {tp : Nat}
    (htp : fn.tb.find? pb.id = some tp) {g : Ghost} {hst : H.State} {envH : HEnv} {envM : Env}
    (hE : EnvRel (secS src r efp).z fn.F g hst envH envM (liveOut fn.f fn.L pb))
    {j : Nat} {p mp : Phi} (hp : db.phis[j]? = some p) (hmp : mblk.phis[j]? = some mp)
    {mo : Operand × Nat} (hmo : mp.incoming.find? (·.2 == tp) = some mo) :
    ∃ o vH m, p.incoming.find? (·.2 == pb.id) = some (o, pb.id) ∧ evalOp envH o = some vH ∧
      mval envM mo.1 = some m ∧ vH.fits p.ty = true ∧
      VRel g (secS src r efp).z (fn.F.D p.dst) vH m ∧ ValOk hst vH ∧
      OrigOk g hst fn.F.R fn.F.fpf (origOf fn.F.O (.var p.dst)) vH := by
  obtain ⟨-, -, -, hty, hnd, hF⟩ := (phisOk_get hph).2 j p mp hp hmp
  obtain ⟨o, hfo, hmop⟩ := incoming_find hF hnd htp (fun b hb => U.tbInj hb htp) hmo
  have hom : (o, pb.id) ∈ p.incoming := List.mem_of_find?_eq_some hfo
  have hpm : p ∈ db.phis := List.mem_of_getElem? hp
  obtain ⟨ta, hta, hsw⟩ : ∃ ta, fn.c.tyOf o = some ta ∧ sameW ta p.ty = true := by
    have := hty _ hom
    cases h : fn.c.tyOf o with
    | none => rw [h] at this; cases this
    | some ta => rw [h] at this; exact ⟨ta, rfl, this⟩
  have hlive : ∀ y, o = .var y → y ∈ liveOut fn.f fn.L pb := by
    intro y hy
    subst hy
    unfold liveOut
    rw [mem_nset]
    refine List.mem_flatMap.mpr ⟨db.id, hsucc, ?_⟩
    rw [U.blk hdb]
    refine List.mem_append_right _ ?_
    unfold varsOf phiOps
    exact List.mem_filterMap.mpr ⟨.var y, List.mem_filterMap.mpr ⟨p, hpm, by rw [hfo]; rfl⟩, rfl⟩
  have hdecl : fn.F.decls = fn.c.decls := by rw [U.hF, U.hc]; rfl
  obtain ⟨vH, m, hev, hfit, hmv, hvr, hvo, hor⟩ := opnd_rel hE hdecl rfl hlive hta hmop
  refine ⟨o, vH, m, hfo, hev, hmv, fits_sameW (sameW_symm hsw) hfit, ?_, hvo,
    hor.mono (U.origPhi hdb hpm hom)⟩
  cases vH with
  | int => exact hvr
  | ptr b' o' =>
    refine ⟨hvr.1, fun hz => ?_⟩
    have hd := hvr.2 hz
    have hop : (secX src r).derived.op fn.k o = fn.F.dOp o := by
      cases o <;> simp [Frame.dOp, Derived.op, U.hF, frameOf]
    exact U.derPhi hS hz hdb hpm hom (by rw [hop]; exact hd)

/-- No machine phi of a block defines the machine value of a value live into it from elsewhere
    (`clobberOk`'s phi part). -/
theorem FnUnp.clobPhi (U : FnUnp src low r fn fr fl e me be rs) {db : HBlock} (hdb : db ∈ fn.f.blocks)
    {mblk : Block} (hph : phisOk fn.c fn.F.vm fn.tb db.phis mblk.phis = true) {x : Nat}
    (hx : x ∈ liveGet fn.L db.id) (hn : x ∉ db.phis.map (·.dst)) :
    ∀ m ∈ mblk.phis.map (·.dst), fn.F.vm.find? x ≠ some (.var m) := by
  intro m hm heq
  obtain ⟨mp, hmp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨j, hmpj⟩ := List.mem_iff_getElem?.mp hmp
  obtain ⟨hlen, hpj⟩ := phisOk_get hph
  obtain ⟨p, hpj'⟩ := get_of_len hmpj hlen.symm
  obtain ⟨hvm, -⟩ := hpj j p mp hpj' hmpj
  have h := U.rules.clob
  simp only [clobberOk, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h db hdb).1
  rw [U.vm] at heq hvm
  rw [U.hL] at hx
  rw [Bool.not_eq_true', List.any_eq_false] at h1
  apply h1 x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  refine ⟨hn, List.any_eq_true.mpr ⟨mp.dst, List.mem_filterMap.mpr ⟨p, List.mem_of_getElem? hpj',
    by simp [hvm]⟩, by simp [heq]⟩⟩

theorem FnUnp.phiDstsNodup (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) : (b.phis.map (·.dst)).Nodup := by
  refine U.shape'.2.2.2.2.2.2.2.2.1.sublist ?_
  unfold HFunc.defs
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  refine List.Sublist.trans ?_ (sublist_flatMap (f := fun b : HBlock =>
    b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) hb)
  exact List.sublist_append_left _ _

theorem FnUnp.mphiDstsNodup (U : FnUnp src low r fn fr fl e me be rs) {mb : Nat} {mblk : Block}
    (hmb : fn.c.mf.block? mb = some mblk) : (mblk.phis.map (·.dst)).Nodup := by
  have hmem : mblk ∈ fn.c.mf.blocks := List.mem_of_find?_eq_some hmb
  refine U.shape'.2.2.2.2.2.2.2.2.2.2.1.sublist ?_
  unfold mdefs
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  refine List.Sublist.trans ?_ (sublist_flatMap (f := fun b : Block =>
    b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) hmem)
  exact List.sublist_append_left _ _

/-- Every block's entry. -/
theorem FnUnp.phiObl {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) (I : Fe.EVM.Env) : PhiObl I (secS src r efp) fn := by
  intro db hdb mb mblk hstart pH prev g hst envH envM w env₁ hedge hprev hen
  have hmb := start_block hstart
  have hph : phisOk fn.c fn.F.vm fn.tb db.phis mblk.phis = true := by
    have h := U.phis
    simp only [phisAllOk, List.all_eq_true] at h
    have h1 := h db hdb
    simp only [Fn.start, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hstart
    obtain ⟨mb', hmb', mblk', hmblk', rfl, rfl⟩ := hstart
    simp only [hmb', Option.bind_eq_bind, Option.bind_some, hmblk'] at h1
    rw [U.vm, U.htb]; exact h1
  obtain ⟨hlen, hpj⟩ := phisOk_get hph
  have hlive0 : ∀ x ∈ fn.live db 0, x ∈ liveGet fn.L db.id := by
    intro x hx
    have h := U.rules.live
    simp only [liveOkAt, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem,
      decide_eq_true_eq] at h
    have hpL : fn.pts = pointsOf fn.f (liveRec fr fn.f) := by rw [U.hpts, U.hL]
    unfold Fn.live at hx
    rw [hpL] at hx
    rw [U.hL]
    exact h.1 db hdb x hx
  cases pH with
  | none =>
    obtain ⟨hnil, hE⟩ := hedge
    have hmnil : mblk.phis = [] := List.length_eq_zero_iff.mp (by rw [← hlen, hnil]; rfl)
    rw [enter_nil hmnil] at hen
    simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hen
    obtain ⟨rfl, -⟩ := hen
    exact ⟨envH, by simp [H.enter, hnil, bindVals], hE.mono hlive0⟩
  | some pid =>
    obtain ⟨pb, hpb, rfl, hsucc, hE⟩ := hedge
    obtain ⟨tp, htp, rfl⟩ := hprev pb.id rfl
    unfold Fe.Sonatina.enter at hen
    rcases exec_bind_some hen with ⟨e, h1, he⟩ | ⟨vals, w₁, h1, h2⟩
    · cases he
    obtain ⟨hw₁, hF⟩ := exec_mapM_quiet (fun phi => by
      repeat (first | exact Quiet.evalOperand _ _ | exact Quiet.stuck | split)) h1
    subst w₁
    -- The machine's phi values.
    have hmach : ∀ (j : Nat) (mp : Phi) (v : Val), mblk.phis[j]? = some mp → vals[j]? = some v →
        ∃ mo, mp.incoming.find? (·.2 == tp) = some mo ∧
          (evalOperand envM mo.1).exec I w = some (.ok (v, w)) := by
      intro j mp v hmp hv
      have hrun := forall₂_get hF hmp hv
      dsimp only at hrun
      split at hrun
      · next o q hfind => exact ⟨(o, q), hfind, hrun⟩
      · cases hrun
    have hvl : mblk.phis.length = vals.length := hF.length_eq
    simp only [Fe.Sonatina.bind] at h2
    split at h2
    · simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      -- H's phi values.
      have hone : ∀ (j : Nat) (p : Phi), db.phis[j]? = some p → ∃ mp v mo o vH m,
          mblk.phis[j]? = some mp ∧ vals[j]? = some v ∧ mp.incoming.find? (·.2 == tp) = some mo ∧
          p.incoming.find? (·.2 == pb.id) = some (o, pb.id) ∧ evalOp envH o = some vH ∧
          mval envM mo.1 = some m ∧ v = .int 256 m ∧ vH.fits p.ty = true ∧
          VRel g (secS src r efp).z (fn.F.D p.dst) vH m ∧ ValOk hst vH ∧
          OrigOk g hst fn.F.R fn.F.fpf (origOf fn.F.O (.var p.dst)) vH := by
        intro j p hp
        obtain ⟨mp, hmp⟩ := get_of_len hp hlen
        obtain ⟨v, hv⟩ := get_of_len hmp hvl
        obtain ⟨mo, hfind, hrun⟩ := hmach j mp v hmp hv
        obtain ⟨o, vH, m, hfo, hev, hmv, hfit, hvr, hvo, hor⟩ :=
          U.phiOne hS hdb hsucc hph htp hE hp hmp hfind
        have hvm : v = .int 256 m := by
          rw [mval_eval hmv] at hrun
          simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hrun
          exact hrun.1.symm
        exact ⟨mp, v, mo, o, vH, m, hmp, hv, hfind, hfo, hev, hmv, hvm, hfit, hvr, hvo, hor⟩
      obtain ⟨valsH, hFH⟩ := exists_forall₂ (R := fun (phi : Phi) v => ∃ o,
          phi.incoming.find? (·.2 == pb.id) = some (o, pb.id) ∧ evalOp envH o = some v)
        (l := db.phis) (fun p hp => by
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
          obtain ⟨_, _, _, o, vH, _, _, _, _, hfo, hev, _⟩ := hone j p hj
          exact ⟨vH, o, hfo, hev⟩)
      have hval : ∀ (j : Nat) (p : Phi) (vH : H.Val), db.phis[j]? = some p → valsH[j]? = some vH →
          ∃ mp m, mblk.phis[j]? = some mp ∧ vals[j]? = some (.int 256 m) ∧ vH.fits p.ty = true ∧
            fn.F.vm.find? p.dst = some (.var mp.dst) ∧ mp.ty = w256 ∧
            VRel g (secS src r efp).z (fn.F.D p.dst) vH m ∧ ValOk hst vH ∧
            OrigOk g hst fn.F.R fn.F.fpf (origOf fn.F.O (.var p.dst)) vH := by
        intro j p vH hp hvH
        obtain ⟨mp, v, mo, o, vH', m, hmp, hv, -, hfo, hev, -, rfl, hfit, hvr, hvo, hor⟩ := hone j p hp
        obtain ⟨o', hfo', hev'⟩ := forall₂_get hFH hp hvH
        rw [hfo] at hfo'
        cases hfo'
        rw [hev] at hev'
        cases hev'
        obtain ⟨hvmp, hmty, -⟩ := hpj j p mp hp hmp
        exact ⟨mp, m, hmp, hv, hfit, hvmp, hmty, hvr, hvo, hor⟩
      have hlH : db.phis.length = valsH.length := hFH.length_eq
      have hbv : bindVals envH (db.phis.map fun phi => (phi.dst, phi.ty)) valsH =
          some (((db.phis.map fun phi => (phi.dst, phi.ty)).zip valsH).foldl
            (fun env (q : (Nat × Ty) × H.Val) => env.insert q.1.1 q.2) envH) := by
        unfold bindVals
        rw [if_pos]
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.length_map]
        refine ⟨hlH, fun q hq => ?_⟩
        obtain ⟨i, hqi⟩ := List.mem_iff_getElem?.mp hq
        rw [List.getElem?_zip_eq_some, List.getElem?_map] at hqi
        obtain ⟨h1, h2⟩ := hqi
        cases hpi : db.phis[i]? with
        | none => rw [hpi] at h1; cases h1
        | some p =>
          rw [hpi] at h1
          simp only [Option.map_some, Option.some.injEq] at h1
          rw [← h1]
          obtain ⟨_, _, _, _, hfit, _⟩ := hval i p q.2 hpi h2
          exact hfit
      refine ⟨_, (henter_some hFH).trans hbv, ?_⟩
      intro x hx
      have hxL := hlive0 x hx
      by_cases hd : x ∈ db.phis.map (·.dst)
      · obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hd
        obtain ⟨j, hpj'⟩ := List.mem_iff_getElem?.mp hpm
        obtain ⟨vH, hvH⟩ := get_of_len hpj' hlH
        obtain ⟨mp, m, hmp, hv, hfit, hvmp, hmty, hvr, hvo, hor⟩ := hval j p vH hpj' hvH
        have hmW : m < W := vrel_lt hvr hfit ((hpj j p mp hpj' hmp).2.2.1)
        refine ⟨vH, m, ?_, ⟨p.ty, by rw [U.hF]; exact U.declPhi hdb hpm, hfit⟩, ?_, hvr, hvo, hor⟩
        · refine foldl_insert_get (fun q : (Nat × Ty) × H.Val => q.1.1) (fun q => q.2)
            ((db.phis.map fun phi => (phi.dst, phi.ty)).zip valsH) envH ?_ ((p.dst, p.ty), vH)
            (mem_zip_of (by rw [List.getElem?_map, hpj']; rfl) hvH)
          rw [map_fst_zip_key (fun x : Nat × Ty => x.1) _ _ (by rw [List.length_map]; exact hlH), List.map_map]
          exact U.phiDstsNodup hdb
        · rw [hvmp]
          simp only [Option.bind_some, mval]
          have := foldl_insert_get (fun q : (Nat × Ty) × Val => q.1.1) (fun q => q.2.as q.1.2)
            ((mblk.phis.map fun phi => (phi.dst, phi.ty)).zip vals) envM
            (by rw [map_fst_zip_key (fun x : Nat × Ty => x.1) _ _ (by rw [List.length_map]; exact hvl), List.map_map]
                exact U.mphiDstsNodup hmb)
            ((mp.dst, mp.ty), .int 256 m) (mem_zip_of (by rw [List.getElem?_map, hmp]; rfl) hv)
          simp only at this
          rw [this, hmty]
          simp only [W] at hmW
          simpa [Val.as, Ty.bits, w256] using hmW
      · have hxo : x ∈ liveOut fn.f fn.L pb := by
          unfold liveOut
          rw [mem_nset]
          refine List.mem_flatMap.mpr ⟨db.id, hsucc, ?_⟩
          rw [U.blk hdb]
          refine List.mem_append_left _ (List.mem_filter.mpr ⟨hxL, ?_⟩)
          simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
          intro q hq he
          exact hd (List.mem_map.mpr ⟨q, hq, he⟩)
        obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := hE x hxo
        refine ⟨v, m, ?_, h2, ?_, h4, h5, h6⟩
        · rw [bindVals_other hbv (by rw [List.map_map]; exact hd)]; exact h1
        · rw [mval_keep (ds := mblk.phis.map (·.dst)) ?_ (U.clobPhi hdb hph hxL hd)]
          · exact h3
          · intro q hq
            refine foldl_insert_away (fun q : (Nat × Ty) × Val => q.1.1) (fun q => q.2.as q.1.2) _ _
              fun a ha e => hq ?_
            rw [← e]
            have := (List.of_mem_zip ha).1
            obtain ⟨mp, hmp, he⟩ := List.mem_map.mp this
            rw [← he]
            exact List.mem_map_of_mem hmp
    · cases h2

end unp

end Fe.Sonatina.Stage3.Place
