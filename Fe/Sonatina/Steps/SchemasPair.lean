import Fe.Sonatina.Steps.KnownBitsInv
import Fe.Sonatina.Steps.CoalesceSound

/-!
# What the alias check of `known_bits_simplify`, `sccp_fold` and `scalar_canonicalize` gives

The shared check (`aliasReject`) accepting `f` to `s.func` gives, block for block (`AF`,
`aliasReject_spec`, `AF.block`): the output block of each id has the input block's phis, in
order, less some, each with `σ` applied to its operands; the input block's statements likewise,
or, in `sccp_fold` and `scalar_canonicalize`, replaced in place (`replaceOk`); the input block's
terminator with `σ`
applied.  The lines left over are deleted (`deletable`) and define no value of the output; the
values `σ` maps that a kept line reads have justified entries (`entryOk`).  `pairUp` is a merge
of the output's lines into the input's (`Merge`), split by kind (`Merge.split`) into phis,
statements and terminator (`Sub`).
-/

namespace Fe.Sonatina

deriving instance ReflBEq, LawfulBEq for Operand
deriving instance ReflBEq, LawfulBEq for Ty
deriving instance ReflBEq, LawfulBEq for BinOp, CmpOp, OvfOp, SatOp, CastOp, EvmOp
deriving instance ReflBEq, LawfulBEq for Inst
deriving instance ReflBEq, LawfulBEq for Fe.Sonatina.Term
deriving instance ReflBEq, LawfulBEq for Phi
deriving instance ReflBEq, LawfulBEq for Stmt

end Fe.Sonatina

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina Fe.Sonatina.Steps

/-! ## Merges -/

/-- The input lines `l` with the output lines `l'` merged in, in order: each output line paired
    with an input line (`P`, input first), the input lines left over deleted (`D`). -/
inductive Merge {α : Type} : List α → List α → List (α × α) → List α → Prop
  | nil (l : List α) : Merge l [] [] l
  | pair {x y : α} {l l' : List α} {P : List (α × α)} {D : List α} :
      Merge l l' P D → Merge (x :: l) (y :: l') ((x, y) :: P) D
  | skip {x : α} {l l' : List α} {P : List (α × α)} {D : List α} :
      Merge l l' P D → Merge (x :: l) l' P (x :: D)

theorem pairUp_merge : ∀ (ins outs : List (Nat × Line)) {r : List (Line × Line) × List Line},
    pairUp ins outs = some r → Merge (ins.map (·.2)) (outs.map (·.2)) r.1 r.2
  | ins, [], r, h => by
    simp only [pairUp, Option.some.injEq] at h; subst h; exact .nil _
  | [], _ :: _, r, h => by simp [pairUp] at h
  | (i, L) :: ins, (i', L') :: outs, r, h => by
    simp only [pairUp] at h
    split at h
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .pair (pairUp_merge ins outs hr')
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .skip (pairUp_merge ins ((i', L') :: outs) hr')

theorem Merge.head {α : Type} : ∀ {l l' : List α} {P : List (α × α)} {D : List α},
    Merge l l' P D → ∀ {y : α} {l'' : List α}, l' = y :: l'' → ∃ x ∈ l, (x, y) ∈ P
  | _, _, _, _, .nil _, _, _, h => by cases h
  | _, _, _, _, .pair (x := x) _, _, _, h => by
    cases h; exact ⟨x, List.mem_cons_self .., List.mem_cons_self ..⟩
  | _, _, _, _, .skip hm, _, _, h => by
    obtain ⟨x, hx, hp⟩ := hm.head h
    exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

/-- A merge whose pairs keep a kind `k` splits at the boundary of the lines of kind `k`. -/
theorem Merge.split {α : Type} (k : α → Bool) : ∀ {l l' : List α} {P : List (α × α)} {D : List α},
    Merge l l' P D → (∀ p ∈ P, k p.1 = k p.2) →
    ∀ {A B A' B' : List α}, l = A ++ B → l' = A' ++ B' → (∀ a ∈ A, k a = true) →
      (∀ b ∈ B, k b = false) → (∀ a ∈ A', k a = true) → (∀ b ∈ B', k b = false) →
      ∃ P₁ D₁ P₂ D₂, Merge A A' P₁ D₁ ∧ Merge B B' P₂ D₂ ∧ P = P₁ ++ P₂ ∧ D = D₁ ++ D₂
  | _, _, _, _, .nil l, _, A, B, A', B', hl, hl', _, _, _, _ => by
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hl'.symm
    exact ⟨[], A, [], B, .nil A, .nil B, rfl, hl⟩
  | _, _, _, _, .pair (x := x) (y := y) (l := l) (l' := l') (P := P) hm, hk, A, B, A', B', hl, hl',
      hA, hB, hA', hB' => by
    have hxy := hk (x, y) (List.mem_cons_self ..)
    have hk' : ∀ p ∈ P, k p.1 = k p.2 := fun p hp => hk p (List.mem_cons_of_mem _ hp)
    cases A with
    | cons a A₀ =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      cases A' with
      | cons a' A₀' =>
        simp only [List.cons_append, List.cons.injEq] at hl'
        obtain ⟨rfl, rfl⟩ := hl'
        obtain ⟨P₁, D₁, P₂, D₂, h₁, h₂, rfl, rfl⟩ :=
          hm.split k hk' rfl rfl (fun a ha => hA a (List.mem_cons_of_mem _ ha)) hB
            (fun a ha => hA' a (List.mem_cons_of_mem _ ha)) hB'
        exact ⟨(x, y) :: P₁, D₁, P₂, D₂, h₁.pair, h₂, rfl, rfl⟩
      | nil =>
        simp only [List.nil_append] at hl'
        have h1 := hA x (List.mem_cons_self ..)
        have h2 := hB' y (hl' ▸ List.mem_cons_self ..)
        simp only at hxy
        rw [h1, h2] at hxy; cases hxy
    | nil =>
      simp only [List.nil_append] at hl
      cases A' with
      | cons a' A₀' =>
        simp only [List.cons_append, List.cons.injEq] at hl'
        obtain ⟨rfl, _⟩ := hl'
        have h1 := hB x (hl ▸ List.mem_cons_self ..)
        have h2 := hA' y (List.mem_cons_self ..)
        simp only at hxy
        rw [h1, h2] at hxy; cases hxy
      | nil =>
        simp only [List.nil_append] at hl'
        subst hl hl'
        exact ⟨[], [], _, _, .nil [], hm.pair, rfl, rfl⟩
  | _, _, _, _, .skip (x := x) (l := l) (l' := l') hm, hk, A, B, A', B', hl, hl', hA, hB, hA', hB' => by
    cases A with
    | cons a A₀ =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      obtain ⟨P₁, D₁, P₂, D₂, h₁, h₂, rfl, rfl⟩ :=
        hm.split k hk rfl hl' (fun a ha => hA a (List.mem_cons_of_mem _ ha)) hB hA' hB'
      exact ⟨P₁, x :: D₁, P₂, D₂, h₁.skip, h₂, rfl, rfl⟩
    | nil =>
      simp only [List.nil_append] at hl
      cases A' with
      | cons a' A₀' =>
        obtain ⟨z, hz, hp⟩ := (Merge.skip (x := x) hm).head (hl'.trans (List.cons_append ..))
        have h1 := hB z (hl ▸ hz)
        have h2 := hA' a' (List.mem_cons_self ..)
        have := hk _ hp
        simp only at this
        rw [h1, h2] at this; cases this
      | nil =>
        simp only [List.nil_append] at hl'
        subst hl hl'
        exact ⟨[], [], _, _, .nil [], hm.skip, rfl, rfl⟩

/-- Two lists, the second the first less some elements and the rest related by `K`, in order. -/
inductive Sub {α β : Type} (K : α → β → Prop) (Dl : α → Prop) : List α → List β → Prop
  | nil : Sub K Dl [] []
  | keep {a : α} {b : β} {l : List α} {l' : List β} : K a b → Sub K Dl l l' → Sub K Dl (a :: l) (b :: l')
  | drop {a : α} {l : List α} {l' : List β} : Dl a → Sub K Dl l l' → Sub K Dl (a :: l) l'

theorem Sub.all_drop {α β : Type} {K : α → β → Prop} {Dl : α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, Dl a) → Sub K Dl l []
  | [], _ => .nil
  | a :: l, h => .drop (h a (List.mem_cons_self ..)) (Sub.all_drop fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem Merge.sub {α β γ : Type} {F : α → γ} {G : β → γ} {K : α → β → Prop} {Dl : α → Prop} :
    ∀ {l l' : List γ} {P : List (γ × γ)} {D : List γ}, Merge l l' P D →
    ∀ {xs : List α} {ys : List β}, l = xs.map F → l' = ys.map G →
      (∀ a b, (F a, G b) ∈ P → K a b) → (∀ a, F a ∈ D → Dl a) → Sub K Dl xs ys
  | _, _, _, _, .nil _, xs, ys, hl, hl', _, hD => by
    have : ys = [] := List.map_eq_nil_iff.mp hl'.symm
    subst this hl
    exact Sub.all_drop fun a ha => hD a (List.mem_map_of_mem ha)
  | _, _, _, _, .pair hm, xs, ys, hl, hl', hK, hD => by
    cases xs with
    | nil => cases hl
    | cons a xs =>
      cases ys with
      | nil => cases hl'
      | cons b ys =>
        simp only [List.map_cons, List.cons.injEq] at hl hl'
        obtain ⟨rfl, rfl⟩ := hl
        obtain ⟨rfl, rfl⟩ := hl'
        exact .keep (hK a b (List.mem_cons_self ..)) (hm.sub rfl rfl
          (fun a b h => hK a b (List.mem_cons_of_mem _ h)) hD)
  | _, _, _, _, .skip hm, xs, ys, hl, hl', hK, hD => by
    cases xs with
    | nil => cases hl
    | cons a xs =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact .drop (hD a (List.mem_cons_self ..)) (hm.sub rfl hl' hK
        fun a h => hD a (List.mem_cons_of_mem _ h))

theorem Sub.mem_right {α β : Type} {K : α → β → Prop} {Dl : α → Prop} :
    ∀ {l : List α} {l' : List β}, Sub K Dl l l' → ∀ b ∈ l', ∃ a ∈ l, K a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .keep (a := a) hk hs, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨a, List.mem_cons_self .., hk⟩
    · obtain ⟨a', ha', hk'⟩ := hs.mem_right b h
      exact ⟨a', List.mem_cons_of_mem _ ha', hk'⟩
  | _, _, .drop _ hs, b, h => by
    obtain ⟨a', ha', hk'⟩ := hs.mem_right b h
    exact ⟨a', List.mem_cons_of_mem _ ha', hk'⟩

theorem Sub.mem_left {α β : Type} {K : α → β → Prop} {Dl : α → Prop} :
    ∀ {l : List α} {l' : List β}, Sub K Dl l l' → ∀ a ∈ l, Dl a ∨ ∃ b ∈ l', K a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .keep (b := b) hk hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr ⟨b, List.mem_cons_self .., hk⟩
    · rcases hs.mem_left a h with h | ⟨b', hb', hk'⟩
      · exact Or.inl h
      · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', hk'⟩
  | _, _, .drop hd hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hd
    · exact hs.mem_left a h

/-! ## The lines of a block -/

/-- A block's lines: its phis, statements and terminator. -/
def blockLines (b : Block) : List Line := b.phis.map Line.phi ++ b.body.map Line.stmt ++ [Line.term b.term]

def _root_.Fe.Sonatina.Steps.Line.kind : Line → Nat
  | .phi _ => 0
  | .stmt _ => 1
  | .term _ => 2

theorem mapLine_kind (σ : NatMap Operand) (L : Line) : (mapLine σ L).kind = L.kind := by
  cases L <;> rfl

theorem lineEq_kind {L L' : Line} (h : lineEq L L' = true) : L.kind = L'.kind := by
  cases L <;> cases L' <;> simp [lineEq] at h <;> rfl

/-- A merge of two blocks' lines whose pairs keep the kind of a line and delete no terminator:
    phis with phis, statements with statements, the terminators paired. -/
theorem merge_block {ib ob : Block} {P : List (Line × Line)} {D : List Line}
    (h : Merge (blockLines ib) (blockLines ob) P D) (hk : ∀ p ∈ P, p.1.kind = p.2.kind)
    (hd : ∀ L ∈ D, L.kind ≠ 2) :
    Sub (fun φ φ' => (Line.phi φ, Line.phi φ') ∈ P) (fun φ => Line.phi φ ∈ D) ib.phis ob.phis ∧
    Sub (fun s s' => (Line.stmt s, Line.stmt s') ∈ P) (fun s => Line.stmt s ∈ D) ib.body ob.body ∧
    (Line.term ib.term, Line.term ob.term) ∈ P := by
  unfold blockLines at h
  rw [List.append_assoc, List.append_assoc] at h
  have hk0 : ∀ p ∈ P, (p.1.kind == 0) = (p.2.kind == 0) := fun p hp => by rw [hk p hp]
  have isPhi : ∀ (l : List Phi), ∀ a ∈ l.map Line.phi, (a.kind == 0) = true := fun l a ha => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; rfl
  have notPhi : ∀ (l : List Stmt) (t : Fe.Sonatina.Term), ∀ b ∈ l.map Line.stmt ++ [Line.term t],
      (b.kind == 0) = false := fun l t b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb; rfl
    · rw [List.mem_singleton.mp hb]; rfl
  obtain ⟨P₁, D₁, P₂, D₂, h₁, h₂, rfl, rfl⟩ := h.split (fun L => L.kind == 0) hk0 rfl rfl
    (isPhi ib.phis) (notPhi ib.body ib.term) (isPhi ob.phis) (notPhi ob.body ob.term)
  have hk1 : ∀ p ∈ P₂, (p.1.kind == 1) = (p.2.kind == 1) := fun p hp => by
    rw [hk p (List.mem_append_right _ hp)]
  have isStmt : ∀ (l : List Stmt), ∀ a ∈ l.map Line.stmt, (a.kind == 1) = true := fun l a ha => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; rfl
  have notStmt : ∀ (t : Fe.Sonatina.Term), ∀ b ∈ [Line.term t], (b.kind == 1) = false := fun t b hb => by
    rw [List.mem_singleton.mp hb]; rfl
  obtain ⟨P₃, D₃, P₄, D₄, h₃, h₄, rfl, rfl⟩ := h₂.split (fun L => L.kind == 1) hk1 rfl rfl
    (isStmt ib.body) (notStmt ib.term) (isStmt ob.body) (notStmt ob.term)
  refine ⟨h₁.sub rfl rfl (fun a b h => List.mem_append_left _ h)
      (fun a h => List.mem_append_left _ h),
    h₃.sub rfl rfl (fun a b h => List.mem_append_right _ (List.mem_append_left _ h))
      (fun a h => List.mem_append_right _ (List.mem_append_left _ h)), ?_⟩
  refine List.mem_append_right _ (List.mem_append_right _ ?_)
  cases h₄ with
  | pair hm => exact List.mem_cons_self ..
  | skip hm => exact absurd rfl (hd _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_cons_self ..))))

/-! ## The pairing of the two snapshots -/

theorem foldlM_pairs (g : Block × List Nat → Block × List Nat → Option (List (Line × Line) × List Line))
    : ∀ (l : List ((Block × List Nat) × (Block × List Nat))) (acc r : List (Line × Line) × List Line),
    l.foldlM (fun acc bb => (g bb.1 bb.2).map fun r => (acc.1 ++ r.1, acc.2 ++ r.2)) acc = some r →
    (∀ p ∈ acc.1, p ∈ r.1) ∧ (∀ L ∈ acc.2, L ∈ r.2) ∧
    ∀ x ∈ l, ∃ r', g x.1 x.2 = some r' ∧ (∀ p ∈ r'.1, p ∈ r.1) ∧ ∀ L ∈ r'.2, L ∈ r.2
  | [], acc, r, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun _ h => h, fun _ h => nomatch h⟩
  | x :: l, acc, r, h => by
    simp only [List.foldlM_cons] at h
    rcases hg : g x.1 x.2 with _ | r₀
    · rw [hg] at h; simp at h
    rw [hg] at h
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨h1, h2, h3⟩ := foldlM_pairs g l _ r h
    refine ⟨fun p hp => h1 p (List.mem_append_left _ hp),
      fun L hL => h2 L (List.mem_append_left _ hL), fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨r₀, hg, fun p hp => h1 p (List.mem_append_right _ hp),
        fun L hL => h2 L (List.mem_append_right _ hL)⟩
    · exact h3 y hy

theorem idsFit_get {bs : List Block} {ids : List (List Nat)} (h : idsFit bs ids = true) :
    ids.length = bs.length ∧ ∀ i (hi : i < bs.length) (hi' : i < ids.length),
      ids[i].length = lineCount bs[i] := by
  unfold idsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi hi' => ?_⟩
  have hz : (bs[i], ids[i]) ∈ bs.zip ids := by
    have hl : i < (bs.zip ids).length := by simp [hi, hi']
    have := List.getElem_mem hl
    rwa [List.getElem_zip] at this
  simpa using h.2 _ hz

theorem idLines_snd {b : Block} {ids : List Nat} (h : ids.length = lineCount b) :
    (idLines b ids).map (·.2) = blockLines b := by
  unfold idLines blockLines
  apply List.map_snd_zip
  simp [lineCount] at h ⊢; omega

/-- What the pairing gives: the blocks in order with their ids, each block's lines a merge. -/
theorem pairFunc_spec {f : Func} {ids : List (List Nat)} {s : FuncSnap}
    {pairs : List (Line × Line)} {deleted : List Line}
    (h : pairFunc f ids s = some (pairs, deleted)) :
    f.blocks.length = s.func.blocks.length ∧ f.blocks.map (·.id) = s.func.blocks.map (·.id) ∧
      ∀ i (hi : i < f.blocks.length) (hi' : i < s.func.blocks.length), ∃ P D,
        Merge (blockLines f.blocks[i]) (blockLines s.func.blocks[i]) P D ∧ (∀ p ∈ P, p ∈ pairs) ∧
          ∀ L ∈ D, L ∈ deleted := by
  unfold pairFunc at h
  split at h
  swap
  · cases h
  next hc =>
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hlen, hfi⟩, hfo⟩, hids⟩ := hc
  obtain ⟨hil, hi⟩ := idsFit_get hfi
  obtain ⟨hol, ho⟩ := idsFit_get hfo
  obtain ⟨_, _, h3⟩ := foldlM_pairs (fun a b => pairUp (idLines a.1 a.2) (idLines b.1 b.2)) _ _ _ h
  refine ⟨hlen, hids, fun i h1 h2 => ?_⟩
  have h3' : i < ids.length := by omega
  have h4' : i < s.insts.length := by omega
  have hmem : ((f.blocks[i], ids[i]), (s.func.blocks[i], s.insts[i])) ∈
      (f.blocks.zip ids).zip (s.func.blocks.zip s.insts) := by
    have hl : i < ((f.blocks.zip ids).zip (s.func.blocks.zip s.insts)).length := by simp; omega
    have := List.getElem_mem hl
    simp only [List.getElem_zip] at this
    exact this
  obtain ⟨r', hr', hP, hD⟩ := h3 _ hmem
  have hm := pairUp_merge _ _ hr'
  rw [idLines_snd (hi i h1 h3'), idLines_snd (ho i h2 h4')] at hm
  exact ⟨r'.1, r'.2, hm, hP, hD⟩

/-! ## The facts the check gives -/

/-- The check's context. -/
abbrev ctxOf (m : Mode) (f : Func) (s : FuncSnap) (F : StepFacts) : StepCtx :=
  StepCtx.of f s F m.sccp?

/-- What `aliasReject m f ids s F = none` gives, with the pairs, the deleted lines and `σ`. -/
structure AF (m : Mode) (f : Func) (s : FuncSnap) (F : StepFacts) (pairs : List (Line × Line))
    (deleted : List Line) (σ : NatMap Operand) : Prop where
  name : s.func.name = f.name
  params : s.func.params = f.params
  rets : s.func.rets = f.rets
  machine' : s.func.machine = true
  opsWf' : opsWf s.func = true
  wordTyped' : s.func.wordTyped = true
  cfgOk' : s.func.cfgOk = true
  termWf' : ∀ b ∈ s.func.blocks, b.term.wf s.func.rets.length = true
  len : f.blocks.length = s.func.blocks.length
  ids : f.blocks.map (·.id) = s.func.blocks.map (·.id)
  merge : ∀ i (hi : i < f.blocks.length) (hi' : i < s.func.blocks.length), ∃ P D,
    Merge (blockLines f.blocks[i]) (blockLines s.func.blocks[i]) P D ∧ (∀ p ∈ P, p ∈ pairs) ∧
      ∀ L ∈ D, L ∈ deleted
  ssaIn : ssaOk f = true
  ssaOut : ssaOk s.func = true
  deletable : ∀ L ∈ deleted, deletable L = true
  changed : ∀ p ∈ pairs, lineEq (mapLine σ p.1) p.2 = true ∨
    ((m = .sccp ∨ m = .scalar) ∧ ∃ a b, p = (Line.stmt a, Line.stmt b) ∧
      replaceOk m (ctxOf m f s F) a b = true)
  kb : kbFactsOk (ctxOf m f s F).inB (ctxOf m f s F).inD F = true
  keys : ∀ p ∈ pairs, ∀ v, Operand.var v ∈ lineOps p.1 → ∀ x, σ.find? v = some x →
    entryOk (ctxOf m f s F) m (deleted.flatMap lineDefs) 3 v x = true
  fresh : ∀ v ∈ deleted.flatMap lineDefs, (defsOf s.func).find? v = none

theorem kbFactsOk_nil {B : NatMap Block} {D : NatMap Def} {F : StepFacts}
    (h : F.knownBits.isEmpty = true) : kbFactsOk B D F = true := by
  unfold kbFactsOk
  rw [List.isEmpty_iff.mp h]
  rfl

theorem find?_none_iff {α : Type} {p : α → Bool} {l : List α} : l.find? p = none ↔ ∀ a ∈ l, p a = false := by
  rw [List.find?_eq_none]; simp

theorem aliasReject_spec {m : Mode} {f : Func} {ids : Option (List (List Nat))} {s : FuncSnap}
    {F : StepFacts} (h : aliasReject m f ids s F = none) :
    ∃ is pairs deleted σ, ids = some is ∧ AF m f s F pairs deleted σ := by
  unfold aliasReject at h
  rcases ids with _ | is
  · cases h
  try dsimp only at h
  split at h
  · cases h
  next hfr =>
  simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hfr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hp⟩, hr⟩, hm⟩, hops⟩, hwt⟩, hcfg⟩, hterm⟩, _⟩, _⟩ := hfr
  split at h
  · cases h
  next pairs deleted hpf =>
  try dsimp only at h
  split at h
  · cases h
  next σ hσ =>
  try dsimp only at h
  split at h
  · cases h
  next hsi =>
  split at h
  · cases h
  next hso =>
  split at h
  · cases h
  next hdel =>
  split at h
  · cases h
  next hch =>
  split at h
  · cases h
  next hkb =>
  split at h
  · cases h
  next hnd =>
  split at h
  · cases h
  next hns =>
  split at h
  · cases h
  next hfresh =>
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hsi hso hdel hch hkb hfresh
  obtain ⟨hlen, hids, hmerge⟩ := pairFunc_spec hpf
  refine ⟨is, pairs, deleted, σ, rfl, hn, hp, hr, hm, hops, hwt, hcfg, hterm, hlen, hids, hmerge,
    hsi, hso, fun L hL => List.all_eq_true.mp hdel L hL, fun p hp => ?_, ?_, ?_, ?_⟩
  · have := List.all_eq_true.mp (show linesOk m _ σ pairs = true from hch) p hp
    simp only [Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · right
      obtain ⟨L, L'⟩ := p
      cases m <;> cases L <;> cases L' <;> simp only [Bool.false_eq_true] at h1
      · exact ⟨Or.inl rfl, _, _, rfl, h1⟩
      · exact ⟨Or.inr rfl, _, _, rfl, h1⟩
  · simp only [Bool.or_eq_true] at hkb
    rcases hkb with hkb | hkb
    · exact kbFactsOk_nil hkb
    · exact hkb
  · intro p hp v hv x hx
    have hkey : v ∈ sigmaKeys pairs σ := by
      unfold sigmaKeys
      refine List.mem_flatMap.mpr ⟨p, hp, List.mem_filterMap.mpr ⟨.var v, hv, ?_⟩⟩
      simp [hx]
    have := (find?_none_iff.mp hns) v hkey
    simp only [hx, Option.any_some, Bool.not_eq_false'] at this
    exact this
  · intro v hv
    have := List.all_eq_true.mp hfresh v hv
    simpa [StepCtx.of] using this

/-! ## Block by block -/

section blocks

variable {m : Mode} {f : Func} {s : FuncSnap} {F : StepFacts} {pairs : List (Line × Line)}
  {deleted : List Line} {σ : NatMap Operand}

/-- What the check gives of an input block and the output block of its id. -/
structure BF (pairs : List (Line × Line)) (deleted : List Line) (ib ob : Block) : Prop where
  id : ob.id = ib.id
  phis : Sub (fun φ φ' => (Line.phi φ, Line.phi φ') ∈ pairs) (fun φ => Line.phi φ ∈ deleted)
    ib.phis ob.phis
  body : Sub (fun s s' => (Line.stmt s, Line.stmt s') ∈ pairs) (fun s => Line.stmt s ∈ deleted)
    ib.body ob.body
  term : (Line.term ib.term, Line.term ob.term) ∈ pairs

theorem Sub.mono {α β : Type} {K K' : α → β → Prop} {Dl Dl' : α → Prop}
    (hK : ∀ a b, K a b → K' a b) (hD : ∀ a, Dl a → Dl' a) :
    ∀ {l : List α} {l' : List β}, Sub K Dl l l' → Sub K' Dl' l l'
  | _, _, .nil => .nil
  | _, _, .keep h hs => .keep (hK _ _ h) (Sub.mono hK hD hs)
  | _, _, .drop h hs => .drop (hD _ h) (Sub.mono hK hD hs)

theorem AF.kinds (A : AF m f s F pairs deleted σ) : ∀ p ∈ pairs, p.1.kind = p.2.kind := by
  intro p hp
  rcases A.changed p hp with h | ⟨_, a, b, rfl, _⟩
  · rw [← mapLine_kind σ p.1]; exact lineEq_kind h
  · rfl

theorem AF.notTerm (A : AF m f s F pairs deleted σ) : ∀ L ∈ deleted, L.kind ≠ 2 := by
  intro L hL
  have := A.deletable L hL
  cases L <;> simp_all [Schemas.deletable, Line.kind]

/-- The input block of an output block's id, and what the check gives of the two. -/
theorem AF.block (A : AF m f s F pairs deleted σ) {b : Nat} {ob : Block}
    (h : s.func.block? b = some ob) : ∃ ib, f.block? b = some ib ∧ BF pairs deleted ib ob := by
  refine find_zip (P := fun ob ib => BF pairs deleted ib ob) A.len.symm (fun p hp => ?_) h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have hi1 : i < s.func.blocks.length := by simp at hi; omega
  have hi2 : i < f.blocks.length := by simp at hi; omega
  simp only [List.getElem_zip]
  have hid : s.func.blocks[i].id = f.blocks[i].id := by
    have := congrArg (·[i]?) A.ids
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
      Option.map_some, Option.some.injEq] at this
    exact this.symm
  obtain ⟨P, D, hm, hP, hD⟩ := A.merge i hi2 hi1
  obtain ⟨h1, h2, h3⟩ := merge_block hm (fun p hp => A.kinds p (hP p hp))
    (fun L hL => A.notTerm L (hD L hL))
  exact ⟨hid, hid, Sub.mono (fun _ _ h => hP _ h) (fun _ h => hD _ h) h1,
    Sub.mono (fun _ _ h => hP _ h) (fun _ h => hD _ h) h2, hP _ h3⟩

theorem lineEq_phi {φ φ' : Phi} (h : lineEq (Line.phi φ) (Line.phi φ') = true) : φ = φ' := by
  simpa [lineEq] using h

theorem lineEq_stmt {a b : Stmt} (h : lineEq (Line.stmt a) (Line.stmt b) = true) : a = b := by
  simpa [lineEq] using h

theorem lineEq_term {a b : Fe.Sonatina.Term} (h : lineEq (Line.term a) (Line.term b) = true) :
    a = b := by
  simpa [lineEq] using h

/-- A phi of the input with σ applied to its operands. -/
def mapPhi (σ : NatMap Operand) (φ : Phi) : Phi :=
  { φ with incoming := φ.incoming.map fun ob => (subst σ ob.1, ob.2) }

theorem AF.phi (A : AF m f s F pairs deleted σ) {φ φ' : Phi}
    (h : (Line.phi φ, Line.phi φ') ∈ pairs) : φ' = mapPhi σ φ := by
  rcases A.changed _ h with h | ⟨_, a, b, he, _⟩
  · exact (lineEq_phi h).symm
  · cases he

theorem AF.stmt (A : AF m f s F pairs deleted σ) {a b : Stmt}
    (h : (Line.stmt a, Line.stmt b) ∈ pairs) :
    b = a.mapOps (subst σ) ∨ ((m = .sccp ∨ m = .scalar) ∧ replaceOk m (ctxOf m f s F) a b = true) := by
  rcases A.changed _ h with h | ⟨hm, a', b', he, hr⟩
  · exact Or.inl (lineEq_stmt h).symm
  · simp only [Prod.mk.injEq, Line.stmt.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact Or.inr ⟨hm, hr⟩

theorem AF.term (A : AF m f s F pairs deleted σ) {a b : Fe.Sonatina.Term}
    (h : (Line.term a, Line.term b) ∈ pairs) : b = a.mapOps (subst σ) := by
  rcases A.changed _ h with h | ⟨_, a', b', he, _⟩
  · exact (lineEq_term h).symm
  · cases he

/-- The input's unfolding a replacement's term was built with. -/
def InUnfold (X : StepCtx) (b : Stmt) (G : Operand → Term) : Prop :=
  (∃ d, G = unfold X.inB X.inD X.cs d) ∨ G = unfoldStop X.inB X.inD X.cs (opVars b.inst.args) 3

theorem replaceOk_spec {m : Mode} {X : StepCtx} {a b : Stmt} (h : replaceOk m X a b = true) :
    a.dsts = b.dsts ∧ ∃ p p' G d', pureInst? a.inst = some p ∧ noClz p = true ∧
      pureInst? b.inst = some p' ∧ noClz p' = true ∧ InUnfold X b G ∧
      checkExact (kbOf X.K) (termOf G p) (termOf (unfold X.outB X.outD X.cs d') p') = true := by
  unfold replaceOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨hd, _⟩, hc⟩ := h
  refine ⟨hd, ?_⟩
  have out : ∀ {G : Operand → Term} {t : Option Term} {d' : Nat}, InUnfold X b G →
      (∀ t₀, t = some t₀ → ∃ p, pureInst? a.inst = some p ∧ noClz p = true ∧ t₀ = termOf G p) →
      (match t, instTerm X.outB X.outD X.cs d' b.inst with
        | some t, some t' => checkExact (kbOf X.K) t t'
        | _, _ => false) = true →
      ∃ p p' G d', pureInst? a.inst = some p ∧ noClz p = true ∧
        pureInst? b.inst = some p' ∧ noClz p' = true ∧ InUnfold X b G ∧
        checkExact (kbOf X.K) (termOf G p) (termOf (unfold X.outB X.outD X.cs d') p') = true := by
    intro G t d' hG ht hc
    rcases t with _ | t₀
    · cases hc
    rcases hi : instTerm X.outB X.outD X.cs d' b.inst with _ | t'
    · rw [hi] at hc; cases hc
    rw [hi] at hc
    obtain ⟨p, hp, hpc, rfl⟩ := ht t₀ rfl
    unfold instTerm at hi
    split at hi
    · next p' hp' =>
      split at hi
      · next hc' =>
        simp only [Option.some.injEq] at hi
        subst hi
        exact ⟨p, p', G, d', hp, hpc, hp', hc', hG, hc⟩
      · cases hi
    · cases hi
  have inT : ∀ {G : Operand → Term} {t₀ : Term},
      (match pureInst? a.inst with
        | some p => if noClz p = true then some (termOf G p) else none
        | none => none) = some t₀ →
      ∃ p, pureInst? a.inst = some p ∧ noClz p = true ∧ t₀ = termOf G p := by
    intro G t₀ h
    split at h
    · next p hp =>
      split at h
      · next hpc => simp only [Option.some.injEq] at h; exact ⟨p, hp, hpc, h.symm⟩
      · cases h
    · cases h
  rcases hc with ⟨dd, _, hc⟩ | hc
  · exact out (Or.inl ⟨dd.1, rfl⟩) (fun t₀ ht => inT (by unfold instTerm at ht; exact ht)) hc
  · exact out (Or.inr rfl) (fun t₀ ht => inT (by unfold instTermStop at ht; exact ht)) hc

/-! ## The output is well formed -/

theorem inst_wf_mapOps {sig : Sigs} {syms : List String} {n : Nat} {g : Operand → Operand} {i : Inst}
    (h : i.wf sig syms n = true) (hm : (i.mapOps g).machine = true)
    (ho : (i.mapOps g).args.all Operand.wf = true) : (i.mapOps g).wf sig syms n = true := by
  unfold Inst.wf at h ⊢
  rw [hm, ho]
  simp only [Bool.true_and]
  simp only [Bool.and_eq_true] at h
  have h := h.2
  cases i with
  | evm op args => cases op <;> simp_all [Inst.mapOps]
  | _ => simp_all [Inst.mapOps]

theorem opsWf_block {g : Func} (h : opsWf g = true) {b : Block} (hb : b ∈ g.blocks) :
    (∀ φ ∈ b.phis, ∀ p ∈ φ.incoming, p.1.wf = true) ∧ (∀ st ∈ b.body, ∀ o ∈ st.inst.args, o.wf = true) ∧
      ∀ o ∈ b.term.args, o.wf = true := by
  unfold opsWf at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨(h b hb).1.1, (h b hb).1.2, (h b hb).2⟩

theorem cfgOk_ids {g : Func} (h : g.cfgOk = true) : (g.blocks.map (·.id)).Nodup := by
  unfold Func.cfgOk at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    exact distinct_nodup h.1.2

/-- The output of an accepted step is well formed under the input's signatures and symbols. -/
theorem AF.wf' {sig : Sigs} {syms : List String} (A : AF m f s F pairs deleted σ)
    (hwf : f.wf sig syms = true) : s.func.wf sig syms = true := by
  unfold Func.wf
  rw [A.machine', A.wordTyped', A.cfgOk']
  simp only [Bool.true_and]
  refine List.all_eq_true.mpr fun ob hob => ?_
  obtain ⟨hph, hbo, hte⟩ := opsWf_block A.opsWf' hob
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨hph, fun st' hst' => ?_⟩, A.termWf' ob hob⟩
  have hblk := block?_of_mem (cfgOk_ids A.cfgOk') hob
  obtain ⟨ib, hib, B⟩ := A.block hblk
  obtain ⟨st, hst, hp⟩ := B.body.mem_right st' hst'
  have hm' : st'.inst.machine = true := Func.machine_of_mem A.machine' hob st' hst'
  have ho' : st'.inst.args.all Operand.wf = true := List.all_eq_true.mpr (hbo st' hst')
  rcases A.stmt hp with rfl | ⟨_, hr⟩
  · have hiw : st.inst.wf sig syms st.dsts.length = true := by
      unfold Func.wf at hwf
      simp only [Bool.and_eq_true, List.all_eq_true] at hwf
      exact (hwf.2 ib (List.mem_of_find?_eq_some hib)).1.2 st hst
    exact inst_wf_mapOps hiw hm' ho'
  · obtain ⟨_, _, p', _, _, _, _, hp', _⟩ := replaceOk_spec hr
    unfold Inst.wf
    rw [hm', ho', ← pureInst?_toInst hp']
    rcases p' with ⟨o, _⟩ | ⟨o, _, _⟩ | ⟨o, _, _, _⟩ <;> cases o <;> rfl

end blocks

end Fe.Sonatina.Steps.Schemas
