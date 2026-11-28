import Fe.Sonatina.Stage3.Place.FixInv

/-!
# H's runs keep `FixInv`

The three obligations `FnOk.qEntry`, `qStep`, `qEdge` for `Q := FixInv` (`FnUnp.fixEntry`,
`FnUnp.fixStep`, `FnUnp.fixEdge`): from what H's rules bind (`execBody_one`, `bindVals_find`,
`H.enter`), each value of the function defined once (`HFunc.defs` distinct), and rule S6 at each
terminal fixed buffer (`s6Site_eq`: the must-origin set is justified member by member, the reach
set closed under successors and without the site's block).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Integers -/

/-- The value is not a pointer. -/
def IsInt (v : H.Val) : Prop := ∀ b o, v ≠ .ptr b o

theorem binVal_int {st : H.State} {op : BinOp} {x y v : H.Val}
    (hop : !(op == .add || op == .sub || op == .or || op == .xor || op == .and) = true)
    (h : binVal st op x y = some v) : IsInt v := by
  intro b o hv; subst hv
  unfold binVal at h
  split at h
  · cases h
  · split at h <;> simp_all [ptrBin]

theorem castVal_int {st : H.State} {op : CastOp} {x v : H.Val} {t : Ty}
    (hk : !keepsPtr op t = true) (h : castVal st op x t = some v) : IsInt v := by
  intro b o hv; subst hv
  unfold castVal at h
  split at h
  · cases h
  · split at h <;> simp_all [keepsPtr]

theorem ofSonatina_int : ∀ {l : List Sonatina.Val} {vs : List H.Val}, l.mapM ofSonatina = some vs →
    ∀ v ∈ vs, IsInt v
  | [], vs, h, v, hv => by simp at h; subst h; cases hv
  | a :: l, vs, h, v, hv => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    rcases List.mem_cons.mp hv with rfl | hv
    · cases a <;> simp [ofSonatina] at hx; subst hx; intro b o h; cases h
    · exact ofSonatina_int hxs v hv

/-- The results of a statement `intStmt` names are integers. -/
theorem intStmt_int {c : H.Ctx} {I : Fe.EVM.Env} {env : HEnv} {st st' : H.State} {s : HStmt}
    {vals : List H.Val} (hi : intStmt s = true) (h : stepInst c I env st s.inst = .ok vals st') :
    ∀ v ∈ vals, IsInt v := by
  rcases s with ⟨dsts, inst⟩
  simp only [intStmt] at hi h
  cases inst with
  | base i =>
    cases i <;> simp only [stepInst] at hi h
    all_goals (repeat' split at h)
    all_goals (try simp only [IRes.ok.injEq, reduceCtorEq] at h)
    all_goals (try (obtain ⟨rfl, -⟩ := h))
    all_goals (try (intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl <;> intro b o hh <;> cases hh))
    all_goals (try (intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; intro b o hh; cases hh))
    all_goals first
      | (simp at hi; done)
      | (exact binVal_int hi ‹_› _ _ rfl)
      | (exact castVal_int hi ‹_› _ _ rfl)
      | (intro v hv; exact absurd hv List.not_mem_nil)
      | skip
    all_goals (simp only [evmH] at h; repeat' split at h)
    all_goals (try simp only [IRes.ok.injEq, reduceCtorEq] at h)
    all_goals (try simp only [liftFe] at h)
    all_goals (repeat' split at h)
    all_goals (try simp only [IRes.ok.injEq, reduceCtorEq] at h)
    all_goals (try (obtain ⟨rfl, -⟩ := h))
    all_goals first
      | (exact ofSonatina_int ‹_›)
      | (simp_all; done)
  | gep => simp at hi
  | mloadBytes a l =>
    simp only [stepInst] at h
    all_goals (repeat' split at h)
    all_goals (try simp only [IRes.ok.injEq, reduceCtorEq] at h)
    all_goals (try (obtain ⟨rfl, -⟩ := h))
    all_goals (intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; intro b o hh; cases hh)
  | truncNuw a t =>
    simp only [stepInst] at h
    all_goals (repeat' split at h)
    all_goals (try simp only [IRes.ok.injEq, reduceCtorEq] at h)
    all_goals (try (obtain ⟨rfl, -⟩ := h))
    all_goals (intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; intro b o hh; cases hh)

/-- A value of a type narrower than a word is an integer. -/
theorem fits_narrow {v : H.Val} {t : Ty} (h : v.fits t = true) (ht : t.bits < 256) : IsInt v := by
  intro b o hv; subst hv
  cases t <;> simp_all [H.Val.fits, Ty.bits]

/-! ## What H binds -/

/-- H's run of one statement that goes on: it bound the statement's results to values that an
    `stepInst` step gives, or to an allocation's pointer, or to a call's results. -/
theorem execBody_one {P : HSection} {I : Fe.EVM.Env} {envH envH' : HEnv} {s : HStmt}
    {hst hst' : H.State} (h : ExecBody P I envH [s] hst (.cont envH' hst')) :
    ∃ vals, bindVals envH s.dsts vals = some envH' ∧
      (stepInst P.ctx I envH hst s.inst = .ok vals hst' ∨ (∃ ty, s.inst = .base (.alloca ty)) ∨
       (∃ a, s.inst = .base (.malloc a)) ∨ ∃ g args, s.inst = .base (.call g args)) := by
  cases h with
  | step hi hb hr => cases hr; exact ⟨_, hb, Or.inl hi⟩
  | alloca hs _ _ _ hb hr => cases hr; exact ⟨_, hb, Or.inr (Or.inl ⟨_, hs⟩)⟩
  | malloc hs _ _ _ _ hb hr => cases hr; exact ⟨_, hb, Or.inr (Or.inr (Or.inl ⟨_, hs⟩))⟩
  | call hs _ _ hb hr => cases hr; exact ⟨_, hb, Or.inr (Or.inr (Or.inr ⟨_, _, hs⟩))⟩

theorem foldl_insert_find {y : Nat} {v : H.Val} :
    ∀ (l : List ((Nat × Ty) × H.Val)) (env : HEnv),
      (l.foldl (fun env (d, v) => env.insert d.1 v) env)[y]? = some v →
      (∃ q ∈ l, q.1.1 = y ∧ q.2 = v) ∨ (env[y]? = some v ∧ ∀ q ∈ l, q.1.1 ≠ y)
  | [], _, h => Or.inr ⟨h, fun _ hq => by cases hq⟩
  | q :: l, env, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insert_find l _ h with ⟨q', hq', h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
    · by_cases hk : q.1.1 = y
      · subst hk
        rw [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at h1
        exact Or.inl ⟨q, List.mem_cons_self .., rfl, h1⟩
      · rw [Std.TreeMap.getElem?_insert] at h1
        simp only [compare_eq_iff_eq, hk, ↓reduceIte] at h1
        exact Or.inr ⟨h1, fun q' hq' => by
          rcases List.mem_cons.mp hq' with rfl | hq'
          · exact hk
          · exact h2 q' hq'⟩

/-- A value bound by `bindVals`: one of its own, of its declaration's type, or an old one. -/
theorem bindVals_find {env env' : HEnv} {dsts : List (Nat × Ty)} {vals : List H.Val}
    (h : bindVals env dsts vals = some env') {y : Nat} {v : H.Val} (hy : env'[y]? = some v) :
    (∃ d ∈ dsts, d.1 = y ∧ v.fits d.2 = true ∧ v ∈ vals) ∨
      (env[y]? = some v ∧ y ∉ dsts.map (·.1)) := by
  unfold bindVals at h
  split at h
  · next hc =>
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    rcases foldl_insert_find _ _ hy with ⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩
    · have hm := List.of_mem_zip hq
      have hf := hc.2 q hq
      subst h1 h2
      exact Or.inl ⟨q.1, hm.1, rfl, hf, hm.2⟩
    · refine Or.inr ⟨h1, fun hm => ?_⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
      obtain ⟨u, hu⟩ : ∃ u, vals[i]? = some u := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        exact ⟨vals[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      exact h2 (d, u) (mem_zip_of hi hu) rfl
  · cases h

/-- `bindVals` binds each of its declarations. -/
theorem bindVals_bound {env env' : HEnv} {dsts : List (Nat × Ty)} {vals : List H.Val}
    (h : bindVals env dsts vals = some env') {y : Nat} (hy : y ∈ dsts.map (·.1)) :
    (env'[y]?).isSome := by
  unfold bindVals at h
  split at h
  · next hc =>
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨u, hu⟩ : ∃ u, vals[i]? = some u := ⟨vals[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have key : ∀ (l : List ((Nat × Ty) × H.Val)) (env : HEnv), (∃ q ∈ l, q.1.1 = d.1) →
        ((l.foldl (fun env (d, v) => env.insert d.1 v) env)[d.1]?).isSome := by
      intro l
      induction l with
      | nil => intro _ h; obtain ⟨_, h, _⟩ := h; cases h
      | cons q l ih =>
        intro env h
        rw [List.foldl_cons]
        by_cases h' : ∃ q ∈ l, q.1.1 = d.1
        · exact ih _ h'
        · obtain ⟨q', hq', he⟩ := h
          rcases List.mem_cons.mp hq' with rfl | hq'
          · rw [foldl_insert_other l _ (fun p hp e => h' ⟨p, hp, e⟩)]
            simp [← he]
          · exact absurd ⟨q', hq', he⟩ h'
    exact key _ _ ⟨(d, u), mem_zip_of hi hu, rfl⟩
  · cases h

/-! ## Each value defined once -/

theorem flatMap_unique {α β : Type} {g : α → List β} {y : β} :
    ∀ {l : List α} {a a' : α}, (l.flatMap g).Nodup → a ∈ l → a' ∈ l → y ∈ g a → y ∈ g a' → a = a'
  | [], _, _, _, h, _, _, _ => by cases h
  | x :: l, a, a', hn, ha, ha', hy, hy' => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp ha with rfl | ha1 <;> rcases List.mem_cons.mp ha' with rfl | ha2
    · rfl
    · exact absurd rfl (hn.2.2 y hy y (List.mem_flatMap.mpr ⟨a', ha2, hy'⟩))
    · exact absurd rfl (hn.2.2 y hy' y (List.mem_flatMap.mpr ⟨a, ha1, hy⟩))
    · exact flatMap_unique hn.2.1 ha1 ha2 hy hy'

theorem flatMap_index {α β : Type} {g : α → List β} {y : β} :
    ∀ {l : List α} {i j : Nat} {a a' : α}, (l.flatMap g).Nodup → l[i]? = some a → l[j]? = some a' →
      y ∈ g a → y ∈ g a' → i = j
  | [], _, _, _, _, _, h, _, _, _ => by simp at h
  | x :: l, i, j, a, a', hn, ha, ha', hy, hy' => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha ha'
      subst ha
      exact absurd rfl (hn.2.2 y hy y (List.mem_flatMap.mpr ⟨a', List.mem_of_getElem? ha', hy'⟩))
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha ha'
      subst ha'
      exact absurd rfl (hn.2.2 y hy' y (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hy⟩))
    · simp only [List.getElem?_cons_succ] at ha ha'
      rw [flatMap_index hn.2.1 ha ha' hy hy']

theorem nodup_flatMap_mem {α β : Type} {g : α → List β} :
    ∀ {l : List α} {a : α}, (l.flatMap g).Nodup → a ∈ l → (g a).Nodup
  | [], _, _, h => by cases h
  | x :: l, a, hn, ha => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hn.1
    · exact nodup_flatMap_mem hn.2.1 ha

theorem map_unique {α β : Type} {g : α → β} :
    ∀ {l : List α} {a a' : α}, (l.map g).Nodup → a ∈ l → a' ∈ l → g a = g a' → a = a'
  | [], _, _, _, h, _, _ => by cases h
  | x :: l, a, a', hn, ha, ha', he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with rfl | ha1 <;> rcases List.mem_cons.mp ha' with rfl | ha2
    · rfl
    · exact absurd (he ▸ List.mem_map_of_mem ha2) hn.1
    · exact absurd (he.symm ▸ List.mem_map_of_mem ha1) hn.1
    · exact map_unique hn.2 ha1 ha2 he

/-- The definitions of a block: its phis' and its statements'. -/
def blockDefs (b : HBlock) : List Nat := b.phis.map (·.dst) ++ b.body.flatMap HStmt.defs

theorem defs_eq (f : HFunc) :
    f.defs = f.params.map (·.1) ++ f.blocks.flatMap blockDefs := rfl

section uniq

variable {f : HFunc} (hnd : f.defs.Nodup)
include hnd

theorem blocks_nodup : (f.blocks.flatMap blockDefs).Nodup := by
  have h := hnd
  rw [defs_eq, List.nodup_append] at h; exact h.2.1

theorem block_unique {b b' : HBlock} (hb : b ∈ f.blocks) (hb' : b' ∈ f.blocks) {y : Nat}
    (hy : y ∈ blockDefs b) (hy' : y ∈ blockDefs b') : b = b' :=
  flatMap_unique (blocks_nodup hnd) hb hb' hy hy'

omit hnd in
theorem stmt_in_block {b : HBlock} {s : HStmt} (hs : s ∈ b.body) {y : Nat} (hy : y ∈ s.defs) :
    y ∈ blockDefs b :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hy⟩)

theorem stmt_unique {b b' : HBlock} (hb : b ∈ f.blocks) (hb' : b' ∈ f.blocks) {s s' : HStmt}
    (hs : s ∈ b.body) (hs' : s' ∈ b'.body) {y : Nat} (hy : y ∈ s.defs) (hy' : y ∈ s'.defs) :
    b = b' ∧ s = s' := by
  obtain rfl := block_unique hnd hb hb' (stmt_in_block hs hy) (stmt_in_block hs' hy')
  refine ⟨rfl, ?_⟩
  have h1 := nodup_flatMap_mem (blocks_nodup hnd) hb
  unfold blockDefs at h1
  rw [List.nodup_append] at h1
  exact flatMap_unique h1.2.1 hs hs' hy hy'

theorem stmt_index {b : HBlock} (hb : b ∈ f.blocks) {i j : Nat} {s s' : HStmt}
    (hs : b.body[i]? = some s) (hs' : b.body[j]? = some s') {y : Nat} (hy : y ∈ s.defs)
    (hy' : y ∈ s'.defs) : i = j := by
  have h1 := nodup_flatMap_mem (blocks_nodup hnd) hb
  unfold blockDefs at h1
  rw [List.nodup_append] at h1
  exact flatMap_index h1.2.1 hs hs' hy hy'

theorem param_stmt {y : Nat} (hp : y ∈ f.params.map (·.1)) {b : HBlock} (hb : b ∈ f.blocks)
    {s : HStmt} (hs : s ∈ b.body) (hy : y ∈ s.defs) : False := by
  have h := hnd
  rw [defs_eq, List.nodup_append] at h
  exact h.2.2 y hp y (List.mem_flatMap.mpr ⟨b, hb, stmt_in_block hs hy⟩) rfl

theorem param_phi {y : Nat} (hp : y ∈ f.params.map (·.1)) {b : HBlock} (hb : b ∈ f.blocks)
    {p : Phi} (hpb : p ∈ b.phis) (hy : p.dst = y) : False := by
  have h := hnd
  rw [defs_eq, List.nodup_append] at h
  exact h.2.2 y hp y (List.mem_flatMap.mpr ⟨b, hb, List.mem_append_left _
    (List.mem_map.mpr ⟨p, hpb, hy⟩)⟩) rfl

theorem phi_stmt {b b' : HBlock} (hb : b ∈ f.blocks) (hb' : b' ∈ f.blocks) {p : Phi}
    (hpb : p ∈ b.phis) {s : HStmt} (hs : s ∈ b'.body) (hy : p.dst ∈ s.defs) : False := by
  have hy1 : p.dst ∈ blockDefs b := List.mem_append_left _ (List.mem_map.mpr ⟨p, hpb, rfl⟩)
  obtain rfl := block_unique hnd hb hb' hy1 (stmt_in_block hs hy)
  have h1 := nodup_flatMap_mem (blocks_nodup hnd) hb
  unfold blockDefs at h1
  rw [List.nodup_append] at h1
  exact h1.2.2 _ (List.mem_map.mpr ⟨p, hpb, rfl⟩) _ (List.mem_flatMap.mpr ⟨s, hs, hy⟩) rfl

theorem phi_unique {b b' : HBlock} (hb : b ∈ f.blocks) (hb' : b' ∈ f.blocks) {p p' : Phi}
    (hp : p ∈ b.phis) (hp' : p' ∈ b'.phis) (he : p.dst = p'.dst) : p = p' := by
  have hy1 : p.dst ∈ blockDefs b := List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hy2 : p.dst ∈ blockDefs b' := List.mem_append_left _ (List.mem_map.mpr ⟨p', hp', he.symm⟩)
  obtain rfl := block_unique hnd hb hb' hy1 hy2
  have h1 := nodup_flatMap_mem (blocks_nodup hnd) hb
  unfold blockDefs at h1
  rw [List.nodup_append] at h1
  exact map_unique h1.1 hp hp' he

theorem params_unique {p p' : Nat × Ty} (hp : p ∈ f.params) (hp' : p' ∈ f.params)
    (he : p.1 = p'.1) : p = p' := by
  have h := hnd
  rw [defs_eq, List.nodup_append] at h
  exact map_unique h.1 hp hp' he

end uniq

theorem dsts_unique {s : HStmt} (hn : (s.dsts.map (·.1)).Nodup) {d d' : Nat × Ty} (hd : d ∈ s.dsts)
    (hd' : d' ∈ s.dsts) (he : d.1 = d'.1) : d = d' :=
  map_unique hn hd hd' he

/-- Where an integer operand comes from. -/
theorem mem_intOperands {f : HFunc} {y : Nat} (h : y ∈ intOperands f) :
    (∃ p ∈ f.params, p.1 = y ∧ p.2.bits < 256) ∨
    (∃ b ∈ f.blocks, ∃ p ∈ b.phis, p.dst = y ∧ p.ty.bits < 256) ∨
    (∃ b ∈ f.blocks, ∃ s ∈ b.body, y ∈ s.defs ∧
      (intStmt s = true ∨ ∃ d ∈ s.dsts, d.1 = y ∧ d.2.bits < 256)) := by
  unfold intOperands at h
  simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at h
  rcases h with ⟨p, hp, hpy⟩ | ⟨b, hb, h⟩
  · split at hpy
    · next hlt => simp only [Option.some.injEq] at hpy; exact Or.inl ⟨p, hp, hpy, hlt⟩
    · cases hpy
  · rcases h with ⟨p, hp, hpy⟩ | ⟨s, hs, h⟩
    · split at hpy
      · next hlt => simp only [Option.some.injEq] at hpy; exact Or.inr (Or.inl ⟨b, hb, p, hp, hpy, hlt⟩)
      · cases hpy
    · refine Or.inr (Or.inr ⟨b, hb, s, hs, ?_⟩)
      split at h
      · next hi => exact ⟨h, Or.inl hi⟩
      · obtain ⟨d, hd, hdy⟩ := List.mem_filterMap.mp h
        split at hdy
        · next hlt =>
          simp only [Option.some.injEq] at hdy
          exact ⟨List.mem_map.mpr ⟨d, hd, hdy⟩, Or.inr ⟨d, hd, hdy, hlt⟩⟩
        · cases hdy

/-! ## Rule S6 unpacked -/

def fixInM (M : List Nat) (a : Operand) : Bool :=
  match a with
  | .var y => M.contains y
  | .imm .. => false

def fixNoT (O : Orig) (t : Nat) (a : Operand) : Bool := !(origOf O a).contains (t + 1)

/-- The statements allowed after a terminal fixed buffer (`s6Site`'s `stmtOk`). -/
def fixStmtOk (O : Orig) (M : List Nat) (t : Nat) (s : HStmt) : Bool :=
  match s.inst with
  | .base (.bin ..) | .base (.not _) | .base (.neg _) | .base (.clz _) | .base (.ctz _)
  | .base (.ovf ..) | .base (.sat ..) | .base (.cast ..) | .base (.blackBox _)
  | .base (.symAddr _) | .base (.symSize _) | .gep .. | .truncNuw .. => true
  | .base (.cmp _ x y) => fixNoT O t x && fixNoT O t y
  | .base (.isZero x) => fixNoT O t x
  | .base (.mstore a _ _) => fixInM M a
  | .base (.evm .mstore [a, _]) | .base (.evm .mstore8 [a, _]) => fixInM M a
  | _ => false

/-- The terminators allowed after a terminal fixed buffer (`s6Site`'s `termOk`). -/
def fixTermOk (O : Orig) (M : List Nat) (t : Nat) (tm : HTerm) : Bool :=
  match tm with
  | .base (.jump _) | .base .evmStop | .base .evmInvalid | .base .unreachable | .returnCode .. => true
  | .base (.br c _ _) => fixNoT O t c
  | .base (.brTable s _ cs) => fixNoT O t s && cs.all (fixNoT O t ·.1)
  | .base (.evmReturn a l) | .base (.evmRevert a l) => fixInM M a || isZeroImm l
  | _ => false

theorem s6Site_eq (O : Orig) (f : HFunc) (b : HBlock) (k t : Nat) :
    s6Site O f b k t =
      (((fixM f t).all fun y => y == t || f.blocks.any fun b => b.body.any fun s =>
          s.defs.contains y && mustStep (intOperands f) (fixM f t) s) &&
        ((fixR f b).all fun c => match f.block? c with
          | some cb => cb.term.succs.all (fixR f b).contains &&
              cb.body.all (fixStmtOk O (fixM f t) t) && fixTermOk O (fixM f t) t cb.term
          | none => false) &&
        (b.body.drop (k + 1)).all (fixStmtOk O (fixM f t) t) &&
        fixTermOk O (fixM f t) t b.term) := rfl

/-- What rule S6 gives at a terminal fixed buffer. -/
structure S6At (O : Orig) (f : HFunc) (b : HBlock) (k t : Nat) : Prop where
  just : ∀ y ∈ fixM f t, y = t ∨ ∃ b' ∈ f.blocks, ∃ s ∈ b'.body, y ∈ s.defs ∧
    mustStep (intOperands f) (fixM f t) s = true
  reach : ∀ c ∈ fixR f b, ∃ cb, f.block? c = some cb ∧ (∀ d ∈ cb.term.succs, d ∈ fixR f b) ∧
    (∀ s ∈ cb.body, fixStmtOk O (fixM f t) t s = true) ∧ fixTermOk O (fixM f t) t cb.term = true
  rest : ∀ s ∈ b.body.drop (k + 1), fixStmtOk O (fixM f t) t s = true
  term : fixTermOk O (fixM f t) t b.term = true

theorem s6At {O : Orig} {f : HFunc} {b : HBlock} {k t : Nat} (h : s6Site O f b k t = true) :
    S6At O f b k t := by
  rw [s6Site_eq] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun y hy => ?_, fun c hc => ?_, h3, h4⟩
  · have := h1 y hy
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
      List.contains_iff_mem] at this
    rcases this with h | ⟨b', hb', s, hs, hy', hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨b', hb', s, hs, hy', hm⟩
  · have := h2 c hc
    revert this
    cases hcb : f.block? c with
    | none => simp
    | some cb =>
      intro this
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at this
      exact ⟨cb, rfl, this.1.1, this.1.2, this.2⟩

theorem reachIter_start (f : HFunc) : ∀ (n : Nat) (R : List Nat), ∀ x ∈ R, x ∈ reachIter f n R
  | 0, _, _, hx => hx
  | n + 1, R, x, hx => by
    unfold reachIter
    dsimp only
    split
    · exact hx
    · exact reachIter_start f n _ x (by rw [mem_nset]; exact List.mem_append_left _ hx)

theorem succs_fixR (f : HFunc) (b : HBlock) {d : Nat} (hd : d ∈ b.term.succs) : d ∈ fixR f b :=
  reachIter_start f _ _ d (by rw [mem_nset]; exact hd)

theorem fixStmtOk_malloc {O : Orig} {M : List Nat} {t : Nat} {s : HStmt} {a : Operand}
    (hi : s.inst = .base (.malloc a)) : fixStmtOk O M t s = false := by
  simp [fixStmtOk, hi]

/-- A statement of the must-origin closure that H steps reads a bound member of the set. -/
theorem mustStep_bound {c : H.Ctx} {I : Fe.EVM.Env} {env : HEnv} {st st' : H.State}
    {Iv M : List Nat} {s : HStmt} {vals : List H.Val} (hm : mustStep Iv M s = true)
    (h : stepInst c I env st s.inst = .ok vals st') : ∃ y ∈ M, (env[y]?).isSome := by
  have key : ∀ a : Operand, (match a with | .var y => M.contains y | .imm .. => false) = true →
      (evalOp env a).isSome → ∃ y ∈ M, (env[y]?).isSome := by
    intro a ha he
    cases a with
    | imm => simp at ha
    | var y => exact ⟨y, by simpa using ha, by simpa [evalOp] using he⟩
  unfold mustStep at hm
  split at hm
  · next bt b' idxs hi =>
    refine key b' hm ?_
    rw [hi] at h
    simp only [stepInst] at h
    cases e : evalOp env b' with
    | none => simp [e] at h
    | some _ => rfl
  · next a b' hi =>
    rw [hi] at h
    simp only [stepInst] at h
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some _ =>
      cases eb : evalOp env b' with
      | none => simp [ea, eb] at h
      | some _ =>
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hm
        rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩
        · exact key a hm (by simp [ea])
        · exact key b' hm (by simp [eb])
  · next a b' hi =>
    rw [hi] at h
    simp only [stepInst] at h
    simp only [Bool.and_eq_true] at hm
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some _ => exact key a hm.1 (by simp [ea])
  · next op a t hi =>
    rw [hi] at h
    simp only [stepInst] at h
    simp only [Bool.and_eq_true] at hm
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some _ => exact key a hm.2 (by simp [ea])
  · next a hi =>
    rw [hi] at h
    simp only [stepInst] at h
    cases ea : evalOp env a with
    | none => simp [ea] at h
    | some _ => exact key a hm (by simp [ea])
  · cases hm

theorem mapM_snd {env : HEnv} {w : H.Val → Nat} :
    ∀ {cases : List (Operand × Nat)} {vals : List (Nat × Nat)},
      cases.mapM (fun x => (evalOp env x.1).map (w ·, x.2)) = some vals →
      ∀ p ∈ vals, p.2 ∈ cases.map (·.2)
  | [], vals, h, p, hp => by simp at h; subst h; cases hp
  | x :: cases, vals, h, p, hp => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨q, ⟨v, hv, rfl⟩, rest, hrest, rfl⟩ := h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mapM_snd hrest p hp)

/-- H goes only to a successor of its terminator. -/
theorem stepTerm_succ {I : Fe.EVM.Env} {env : HEnv} {st : H.State} {t : HTerm} {d : Nat}
    (h : stepTerm I env st t = .goto d) : d ∈ t.succs := by
  cases t with
  | returnCode o l =>
    simp only [stepTerm] at h
    split at h <;> cases h
  | base t =>
    cases t <;> simp only [stepTerm] at h
    all_goals (repeat' split at h)
    all_goals (try simp only [TRes.goto.injEq, reduceCtorEq] at h)
    all_goals (try subst h)
    all_goals (try simp [HTerm.succs, Term.succs]; done)
    rcases orElse_eq_some ‹_› with h1 | ⟨-, h1⟩
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h1
      simp only [HTerm.succs, Term.succs]
      exact List.mem_append_right _ (mapM_snd ‹_› p (List.mem_of_find?_eq_some hp))
    · simp [HTerm.succs, Term.succs, h1]

/-! ## The obligations -/

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.defsNodup (U : FnUnp src low r fn fr fl e me be rs) : fn.f.defs.Nodup :=
  U.shape'.2.2.2.2.2.2.2.2.1

/-- Rule S6 at a terminal fixed buffer of the function. -/
theorem FnUnp.s6 (U : FnUnp src low r fn fr fl e me be rs) {bt : HBlock} {it t : Nat}
    (hF : FixSite fn bt it t) : S6At ((secX src r).origAt fn.k) fn.f bt it t := by
  obtain ⟨hbt, st, a, tx, hst, hi, hd, hfx⟩ := hF
  have h := U.rules.s6
  simp only [ruleS6, List.all_eq_true] at h
  have h1 := h bt hbt (st, it) (mem_zipIdx_of_getElem? hst)
  rw [U.frec] at hfx
  simp only [hi, hd, hfx, Bool.not_true, Bool.false_or] at h1
  exact s6At h1

/-- The site's block is not among the blocks after it. -/
theorem FnUnp.notR (U : FnUnp src low r fn fr fl e me be rs) {bt : HBlock} {it t : Nat}
    (hF : FixSite fn bt it t) : bt.id ∉ fixR fn.f bt := by
  intro h
  obtain ⟨cb, hcb, -, hok, -⟩ := (U.s6 hF).reach _ h
  obtain ⟨hbt, st, a, tx, hst, hi, -, -⟩ := hF
  rw [U.blk hbt] at hcb
  cases hcb
  have := hok st (List.mem_of_getElem? hst)
  rw [fixStmtOk_malloc hi] at this
  cases this

theorem FnUnp.siteDef (U : FnUnp src low r fn fr fl e me be rs) {bt : HBlock} {it t : Nat}
    (hF : FixSite fn bt it t) : ∃ st, bt.body[it]? = some st ∧ t ∈ st.defs := by
  obtain ⟨-, st, a, tx, hst, -, hd, -⟩ := hF
  exact ⟨st, hst, by simp [HStmt.defs, hd]⟩

/-- A statement's step keeps the integer operands integers. -/
theorem FnUnp.intStep (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {s : HStmt} (hs : s ∈ b.body) {envH envH' : HEnv} {vals : List H.Val} {c : H.Ctx}
    {I : Fe.EVM.Env} {hst : H.State} (hI : IntEnv fn.f envH)
    (hbv : bindVals envH s.dsts vals = some envH')
    (hk : (∃ st', stepInst c I envH hst s.inst = .ok vals st') ∨ (∃ ty, s.inst = .base (.alloca ty)) ∨
       (∃ a, s.inst = .base (.malloc a)) ∨ ∃ g args, s.inst = .base (.call g args)) :
    IntEnv fn.f envH' := by
  have hnd := U.defsNodup
  intro y hy v hv
  rcases bindVals_find hbv hv with ⟨d, hd, rfl, hfit, -⟩ | ⟨hold, -⟩
  · have hys : d.1 ∈ s.defs := List.mem_map.mpr ⟨d, hd, rfl⟩
    rcases mem_intOperands hy with ⟨p, hp, hpy, -⟩ | ⟨b', hb', p, hp, hpy, -⟩ |
        ⟨b', hb', s', hs', hy', hk'⟩
    · exact (param_stmt hnd (List.mem_map.mpr ⟨p, hp, hpy⟩) hb hs hys).elim
    · exact (phi_stmt hnd hb' hb hp hs (by rw [hpy]; exact hys)).elim
    · obtain ⟨-, rfl⟩ := stmt_unique hnd hb' hb hs' hs hy' hys
      rcases hk' with hint | ⟨d', hd', hdy, hlt⟩
      · rcases hk with ⟨st', hstep⟩ | ⟨ty, hi⟩ | ⟨a, hi⟩ | ⟨g, args, hi⟩
        · exact intStmt_int hint hstep v (by
            rcases List.mem_iff_getElem?.mp hd with ⟨i, hi⟩
            exact (bindVals_find hbv hv).elim (fun ⟨_, _, _, _, hvm⟩ => hvm) (fun ⟨_, hn⟩ =>
              absurd hys hn))
        all_goals simp [intStmt, hi] at hint
      · obtain rfl := dsts_unique (U.dsts_nodup hb hs) hd hd' hdy.symm
        exact fits_narrow hfit hlt
  · exact hI y hy v hold

theorem FnUnp.fixEntry (U : FnUnp src low r fn fr fl e me be rs) :
    ∀ e', fn.f.blocks.head? = some e' → ∀ vs envH, bindVals {} fn.f.params vs = some envH →
      ∀ envH₁, H.enter envH none e' = some envH₁ → FixInv fn e' 0 envH₁ := by
  intro e' he' vs envH hbv envH₁ hen
  have hnd := U.defsNodup
  rw [U.he] at he'
  cases he'
  have hph : e.phis = [] := U.shape'.2.2.2.2.2.2.1
  have h1 : envH₁ = envH := by
    simp only [H.enter, hph, List.mapM_nil, List.map_nil, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, bindVals, List.length_nil, beq_self_eq_true, List.zip_nil_left,
      List.all_nil, Bool.and_self, ite_true, List.foldl_nil, Option.some.injEq] at hen
    exact hen.symm
  subst h1
  have hpar : ∀ y v, envH₁[y]? = some v → ∃ p ∈ fn.f.params, p.1 = y ∧ v.fits p.2 = true := by
    intro y v hv
    rcases bindVals_find hbv hv with ⟨d, hd, hdy, hf, -⟩ | ⟨h0, -⟩
    · exact ⟨d, hd, hdy, hf⟩
    · simp at h0
  refine ⟨fun y hy v hv => ?_, fun bt it t hF => ⟨fun ht => ?_, fun _ y hy => ?_⟩⟩
  · obtain ⟨p, hp, rfl, hf⟩ := hpar y v hv
    rcases mem_intOperands hy with ⟨p', hp', hpy, hlt⟩ | ⟨b', hb', q, hq, hqy, -⟩ |
        ⟨b', hb', s', hs', hy', -⟩
    · obtain rfl := params_unique hnd hp hp' hpy.symm
      exact fits_narrow hf hlt
    · exact (param_phi hnd (List.mem_map.mpr ⟨p, hp, rfl⟩) hb' hq hqy).elim
    · exact (param_stmt hnd (List.mem_map.mpr ⟨p, hp, rfl⟩) hb' hs' hy').elim
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ht
    obtain ⟨p, hp, hpt, -⟩ := hpar t v hv
    obtain ⟨st, hst, htd⟩ := U.siteDef hF
    exact (param_stmt hnd (List.mem_map.mpr ⟨p, hp, hpt⟩) hF.1 (List.mem_of_getElem? hst) htd).elim
  · cases hv : envH₁[y]? with
    | none => rfl
    | some v =>
      obtain ⟨p, hp, hpy, -⟩ := hpar y v hv
      rcases (U.s6 hF).just y hy with rfl | ⟨b', hb', s', hs', hy', -⟩
      · obtain ⟨st, hst, htd⟩ := U.siteDef hF
        exact (param_stmt hnd (List.mem_map.mpr ⟨p, hp, hpy⟩) hF.1 (List.mem_of_getElem? hst) htd).elim
      · exact (param_stmt hnd (List.mem_map.mpr ⟨p, hp, hpy⟩) hb' hs' hy').elim

theorem FnUnp.fixStep (U : FnUnp src low r fn fr fl e me be rs) (I : Fe.EVM.Env) :
    ∀ b ∈ fn.f.blocks, ∀ i s, b.body[i]? = some s → ∀ envH hst envH' hst', FixInv fn b i envH →
      ExecBody src I envH [s] hst (.cont envH' hst') → FixInv fn b (i + 1) envH' := by
  intro b hb i s hs envH hst envH' hst' hQ hx
  have hnd := U.defsNodup
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  obtain ⟨vals, hbv, hk⟩ := execBody_one hx
  refine ⟨U.intStep hb hsm hQ.1 hbv (hk.imp_left fun h => ⟨_, h⟩), fun bt it t hF => ⟨fun ht => ?_,
    fun hn y hy => ?_⟩⟩
  · by_cases htd : t ∈ s.dsts.map (·.1)
    · exact Or.inr ⟨i, Nat.lt_succ_self i, s, hs, htd⟩
    · rw [bindVals_other hbv htd] at ht
      rcases (hQ.2 bt it t hF).1 ht with h | ⟨j, hj, s', hs', htj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, s', hs', htj⟩
  · have htd : t ∉ s.dsts.map (·.1) := fun h => by
      have := bindVals_bound hbv h
      rw [hn] at this; cases this
    have hn0 : envH[t]? = none := by rw [← bindVals_other hbv htd]; exact hn
    have hM := (hQ.2 bt it t hF).2 hn0
    by_cases hyd : y ∈ s.dsts.map (·.1)
    · exfalso
      rcases (U.s6 hF).just y hy with rfl | ⟨b', hb', s', hs', hy', hm⟩
      · exact htd hyd
      · obtain ⟨-, rfl⟩ := stmt_unique hnd hb' hb hs' hsm hy' hyd
        rcases hk with hstep | ⟨ty, hi⟩ | ⟨a, hi⟩ | ⟨g, args, hi⟩
        · obtain ⟨y', hy'M, hb'⟩ := mustStep_bound hm hstep
          rw [hM y' hy'M] at hb'; cases hb'
        all_goals simp [mustStep, hi] at hm
    · rw [bindVals_other hbv hyd]; exact hM y hy

theorem FnUnp.fixEdge (U : FnUnp src low r fn fr fl e me be rs) (I : Fe.EVM.Env) :
    ∀ b ∈ fn.f.blocks, ∀ envH hst d, FixInv fn b b.body.length envH →
      stepTerm I envH hst b.term = .goto d → ∀ db ∈ fn.f.blocks, db.id = d →
      ∀ envH₁, H.enter envH (some b.id) db = some envH₁ → FixInv fn db 0 envH₁ := by
  intro b hb envH hst d hQ hgo db hdb hid envH₁ hen
  have hnd := U.defsNodup
  simp only [H.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at hen
  obtain ⟨vals, -, hbv⟩ := hen
  have hphi : ∀ y, y ∈ (db.phis.map fun phi => (phi.dst, phi.ty)).map (·.1) →
      ∃ p ∈ db.phis, p.dst = y := by
    intro y hy
    simp only [List.map_map, List.mem_map, Function.comp] at hy
    exact hy
  have hnot : ∀ y, (∃ b' ∈ fn.f.blocks, ∃ s ∈ b'.body, y ∈ s.defs) →
      y ∉ (db.phis.map fun phi => (phi.dst, phi.ty)).map (·.1) := by
    intro y ⟨b', hb', s, hs, hy⟩ hm
    obtain ⟨p, hp, rfl⟩ := hphi y hm
    exact phi_stmt hnd hdb hb' hp hs hy
  have hsite : ∀ bt it t, FixSite fn bt it t → t ∉ (db.phis.map fun phi => (phi.dst, phi.ty)).map (·.1) :=
    fun bt it t hF => by
      obtain ⟨st, hst, htd⟩ := U.siteDef hF
      exact hnot t ⟨bt, hF.1, st, List.mem_of_getElem? hst, htd⟩
  refine ⟨fun y hy v hv => ?_, fun bt it t hF => ⟨fun ht => ?_, fun hn y hy => ?_⟩⟩
  · rcases bindVals_find hbv hv with ⟨q, hq, rfl, hf, -⟩ | ⟨hold, -⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      rcases mem_intOperands hy with ⟨p', hp', hpy, -⟩ | ⟨b', hb', p', hp', hpy, hlt⟩ |
          ⟨b', hb', s', hs', hy', -⟩
      · exact (param_phi hnd (List.mem_map.mpr ⟨p', hp', hpy⟩) hdb hp rfl).elim
      · obtain rfl := phi_unique hnd hdb hb' hp hp' hpy.symm
        exact fits_narrow hf hlt
      · exact (phi_stmt hnd hdb hb' hp hs' hy').elim
    · exact hQ.1 y hy v hold
  · rw [bindVals_other hbv (hsite bt it t hF)] at ht
    have hd : d ∈ b.term.succs := stepTerm_succ hgo
    refine Or.inl ?_
    rw [hid]
    rcases (hQ.2 bt it t hF).1 ht with hR | ⟨j, -, s', hs', htj⟩
    · obtain ⟨cb, hcb, hsucc, -, -⟩ := (U.s6 hF).reach _ hR
      rw [U.blk hb] at hcb
      cases hcb
      exact hsucc d hd
    · obtain ⟨st, hst, htd⟩ := U.siteDef hF
      obtain ⟨rfl, -⟩ := stmt_unique hnd hb hF.1 (List.mem_of_getElem? hs') (List.mem_of_getElem? hst)
        htj htd
      exact succs_fixR fn.f b hd
  · have hn0 : envH[t]? = none := by rw [← bindVals_other hbv (hsite bt it t hF)]; exact hn
    have hyn : y ∉ (db.phis.map fun phi => (phi.dst, phi.ty)).map (·.1) := by
      rcases (U.s6 hF).just y hy with rfl | ⟨b', hb', s', hs', hy', -⟩
      · exact hsite bt it y hF
      · exact hnot y ⟨b', hb', s', hs', hy'⟩
    rw [bindVals_other hbv hyn]
    exact (hQ.2 bt it t hF).2 hn0 y hy

end unp

end Fe.Sonatina.Stage3.Place
