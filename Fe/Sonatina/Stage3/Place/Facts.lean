import Fe.Sonatina.Stage3.Place.Fns
import Fe.Sonatina.Stage3.Place.Obl

/-!
# The rules of S at one statement

What the section's and the function's checks give at the statement the walk reaches, in the
form the pattern lemmas take it: the section facts (rules S1, S4, S5, the bound `F0`), an
`alloca`'s range and rule A1 (`FnUnp.allocaFacts`), a heap `evm_malloc`'s section
(`FnUnp.heapFacts`), and a call's callee with its parameters, footprint and rule A2
(`FnUnp.callFacts`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Lists -/

theorem flatMap_sublist_flatMap {α β : Type} {f g : α → List β} (h : ∀ a, List.Sublist (f a) (g a)) :
    ∀ l : List α, List.Sublist (l.flatMap f) (l.flatMap g)
  | [] => List.Sublist.slnil
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a).append (flatMap_sublist_flatMap h l)

theorem foldl_max_ge_init : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], _ => le_rfl
  | x :: l, a => le_trans (le_max_left a x) (foldl_max_ge_init l (max a x))

theorem foldl_max_ge_mem : ∀ {l : List Nat} {x : Nat} (a : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by cases h
  | y :: l, x, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (foldl_max_ge_init l _)
    · exact foldl_max_ge_mem (l := l) (max a y) h

theorem foldl_max_lt {B : Nat} : ∀ {l : List Nat} {a : Nat}, a < B → (∀ x ∈ l, x < B) →
    l.foldl max a < B
  | [], _, ha, _ => ha
  | y :: l, a, ha, hl => foldl_max_lt (l := l) (a := max a y) (max_lt ha (hl y (List.mem_cons_self ..)))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

theorem placed_keys (src : HSection) (r : Record) : ((placed src r).map (·.1)).Nodup := by
  unfold placed
  rw [List.map_map]
  have : ∀ (l : List HFunc) (n : Nat), ((l.zipIdx n).map ((·.1) ∘ fun (q : HFunc × Nat) =>
      (q.2, q.1, (r.funcs[q.2]?).getD { name := q.1.name }))).Nodup ∧
      ∀ y ∈ (l.zipIdx n).map ((·.1) ∘ fun (q : HFunc × Nat) =>
        (q.2, q.1, (r.funcs[q.2]?).getD { name := q.1.name })), n ≤ y := by
    intro l
    induction l with
    | nil => intro n; simp
    | cons a l ih =>
      intro n
      obtain ⟨h1, h2⟩ := ih (n + 1)
      simp only [List.zipIdx_cons, List.map_cons, List.nodup_cons, Function.comp, List.mem_cons]
      refine ⟨⟨fun hm => ?_, h1⟩, fun y hy => ?_⟩
      · have := h2 n hm; omega
      · rcases hy with rfl | hy
        · exact le_rfl
        · have := h2 y hy; omega
  exact (this src.module.funcs 0).1

/-! ## The callee places of the walk -/

theorem calleeOf_sfx (s : HStmt) (cs : List Nat) : List.IsSuffix (calleeOf s cs).2 cs := by
  unfold calleeOf
  split
  · exact List.tail_suffix cs
  · exact List.suffix_refl cs

theorem walkTo_cs {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs₀ : List Nat} {i : Nat} {mb₁ : Nat} {ms₁ : List Stmt} {cs₁ : List Nat},
    walkTo c vm l mb ms cs₀ i = some (mb₁, ms₁, cs₁) → List.IsSuffix cs₁ cs₀
  | _, _, _, _, 0, _, _, _, h => by
    simp only [walkTo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact List.suffix_refl _
  | [], _, _, _, _ + 1, _, _, _, h => by simp [walkTo] at h
  | s :: rest, mb, ms, cs₀, i + 1, mb₁, ms₁, cs₁, h => by
    simp only [walkTo] at h
    split at h
    · exact (walkTo_cs h).trans (calleeOf_sfx s cs₀)
    · cases h

/-- The statement the walk reaches is the one at its index in `withCallees`, with the callee
    place the walk gives it. -/
theorem go_get {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs₀ : List Nat} {i : Nat} {mb₁ : Nat} {ms₁ : List Stmt} {cs₁ : List Nat} {s : HStmt},
    walkTo c vm l mb ms cs₀ i = some (mb₁, ms₁, cs₁) → l[i]? = some s →
    (withCallees.go l cs₀)[i]? = some (s, (calleeOf s cs₁).1)
  | [], _, _, _, _, _, _, _, _, _, hs => by simp at hs
  | t :: rest, mb, ms, cs₀, 0, mb₁, ms₁, cs₁, s, hw, hs => by
    simp only [walkTo, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    rw [go_cons]; rfl
  | t :: rest, mb, ms, cs₀, i + 1, mb₁, ms₁, cs₁, s, hw, hs => by
    simp only [walkTo] at hw
    split at hw
    · rw [go_cons, List.getElem?_cons_succ]
      exact go_get hw (by simpa using hs)
    · cases hw

/-- The arguments of a call statement. -/
def callArgs (i : HInst) : Option (List Operand) :=
  match i with
  | .base (.call _ args) => some args
  | _ => none

theorem calleeOf_eq (s : HStmt) (cs : List Nat) :
    calleeOf s cs = if (callArgs s.inst).isSome then (cs.head?, cs.tail) else (none, cs) := by
  unfold calleeOf callArgs
  split <;> split <;> simp_all

/-- A call the walk gives a callee place is one of `callSites`' pairs of its block. -/
theorem go_zip : ∀ {l : List HStmt} {cs : List Nat} {s : HStmt} {kg : Nat} {gn : String}
    {args : List Operand}, (s, some kg) ∈ withCallees.go l cs → s.inst = .base (.call gn args) →
    (kg, args) ∈ cs.zip (l.filterMap fun s => callArgs s.inst)
  | [], _, _, _, _, _, h, _ => by simp [withCallees.go] at h
  | t :: rest, cs, s, kg, gn, args, h, hi => by
    rw [go_cons, List.mem_cons] at h
    cases hcl : callArgs t.inst with
    | none =>
      rw [calleeOf_eq, hcl] at h
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Prod.mk.injEq,
        reduceCtorEq, and_false, false_or] at h
      rw [List.filterMap_cons, hcl]
      exact go_zip h hi
    | some a' =>
      rw [calleeOf_eq, hcl] at h
      simp only [Option.isSome_some, ite_true, Prod.mk.injEq] at h
      rw [List.filterMap_cons, hcl]
      rcases h with ⟨rfl, hk⟩ | h
      · rw [hi] at hcl
        simp only [callArgs, Option.some.injEq] at hcl
        subst hcl
        cases cs with
        | nil => cases hk
        | cons c cs' =>
          simp only [List.head?_cons, Option.some.injEq] at hk
          subst hk
          simp
      · cases cs with
        | nil => exact absurd (go_zip h hi) (by simp)
        | cons c cs' =>
          simp only [List.tail_cons] at h
          exact List.mem_cons_of_mem _ (go_zip h hi)

/-! ## The rules, one site at a time -/

theorem hints_callee {src : HSection} {low : Module} {r : Record} (hh : hintsOk src low r = true)
    {fr : FuncRec} (hfr : fr ∈ r.funcs) {l : List Nat} (hl : l ∈ fr.calls) {kg : Nat}
    (hk : kg ∈ l) :
    ∃ g, src.module.funcs[kg]? = some g ∧ firstOf (·.name) src.module.funcs kg g.name = true := by
  simp only [hintsOk, Bool.and_eq_true, List.all_eq_true] at hh
  have hu : kg ∈ (r.funcs.flatMap fun fr => fr.calls.flatten).dedupB :=
    mem_dedupB.mpr (List.mem_flatMap.mpr ⟨fr, hfr, List.mem_flatten.mpr ⟨l, hl, hk⟩⟩)
  have := hh.2 kg hu
  revert this
  cases hg : src.module.funcs[kg]? with
  | none => simp
  | some g => intro h; exact ⟨g, rfl, h⟩

theorem derivedOk_call {fs : List (Nat × HFunc × List (List (HStmt × Option Nat)))} {D : Derived}
    (h : derivedOk fs D = true) {k : Nat} {f : HFunc} {bss : List (List (HStmt × Option Nat))}
    (hf : (k, f, bss) ∈ fs) {b : HBlock} {ss : List (HStmt × Option Nat)}
    (hb : (b, ss) ∈ f.blocks.zip bss) {s : HStmt} {kg : Nat} (hs : (s, some kg) ∈ ss)
    {gn : String} {args : List Operand} (hi : s.inst = .base (.call gn args)) {j : Nat}
    {a : Operand} (ha : args[j]? = some a) (hd : D.op k a = true) : D.param kg j = true := by
  unfold derivedOk at h
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  have h1 := ((h _ hf).2 _ hb).1.2 _ hs
  simp only [hi, List.all_eq_true] at h1
  have := h1.2 (a, j) (mem_zipIdx_of_getElem? ha)
  simpa [hd] using this

theorem derivedOk_param {fs : List (Nat × HFunc × List (List (HStmt × Option Nat)))} {D : Derived}
    (h : derivedOk fs D = true) {k : Nat} {f : HFunc} {bss : List (List (HStmt × Option Nat))}
    (hf : (k, f, bss) ∈ fs) {j : Nat} {p : Nat × Ty} (hp : f.params[j]? = some p)
    (hd : D.param k j = true) : D.has k p.1 = true := by
  unfold derivedOk at h
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  have := (h _ hf).1 (p, j) (mem_zipIdx_of_getElem? hp)
  simpa [hd] using this

theorem flagsOk_call {F : Flags} {fr : FuncRec} {f : HFunc} {O : Orig} (h : flagsOk F fr f O = true)
    {kg : Nat} {args : List Operand} (hm : (kg, args) ∈ callSites fr f) {j : Nat} {a : Operand}
    (ha : args[j]? = some a) (ho : origOf O a ≠ []) : flagged F kg j = true := by
  unfold flagsOk callFlags at h
  simp only [List.all_eq_true, List.mem_map] at h
  refine h _ ⟨(kg, args), hm, rfl⟩ j (List.mem_map.mpr ⟨(a, j), List.mem_filter.mpr
    ⟨mem_zipIdx_of_getElem? ha, ?_⟩, rfl⟩)
  simpa [List.isEmpty_iff] using ho

theorem origOk_param {fr : FuncRec} {F : Flags} {k : Nat} {f : HFunc} {O : Orig}
    (h : origOk fr F k f O = true) {j : Nat} {p : Nat × Ty} (hp : f.params[j]? = some p)
    (hfl : flagged F k j = true) : 0 ∈ origOf O (.var p.1) := by
  unfold origOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 (p, j) (mem_zipIdx_of_getElem? hp)
  simpa [hfl] using this

theorem fpOk_get {P : List (Nat × HFunc × FuncRec)} {ranges : NatMap (NatMap Range)} {fp : FP}
    (h : fpOk (fpInput P ranges) fp = true) {k : Nat} {f : HFunc} {fr : FuncRec}
    (hm : (k, f, fr) ∈ P) :
    (∀ x ∈ ownRanges ((ranges.find? k).getD .empty) f, x ∈ fpOf fp k) ∧
    ∀ kg ∈ callees fr f, ∀ x ∈ fpOf fp kg, x ∈ fpOf fp k := by
  unfold fpOk fpInput at h
  simp only [List.all_eq_true, List.mem_map, Bool.and_eq_true, List.contains_iff_mem] at h
  have := h _ ⟨(k, f, fr), hm, rfl⟩
  exact ⟨this.1, this.2⟩

theorem ruleS7_call {R : NatMap Range} {fr : FuncRec} {P : FP} {O : Orig}
    {pts : NatMap (List (List Nat))} {f : HFunc} (h : ruleS7 R fr P O pts f = true) {b : HBlock}
    {j : Nat} (hj : f.blocks[j]? = some b) {ss : List (HStmt × Option Nat)}
    (hw : (withCallees fr f)[j]? = some ss) {i : Nat} {s : HStmt} {kg : Nat}
    (hsi : ss[i]? = some (s, some kg)) {gn : String} {args : List Operand}
    (hi : s.inst = .base (.call gn args)) :
    ∀ y, ((y ∈ ptsAt pts b.id (i + 1) ∧ y ∉ s.defs) ∨ Operand.var y ∈ args) →
      ∀ o ∈ origOf O (.var y), o = 0 ∨ ∃ rr, R.find? (o - 1) = some rr ∧ ∀ r ∈ fpOf P kg, Disj rr r := by
  unfold ruleS7 at h
  simp only [List.all_eq_true] at h
  have h1 := h (b, ss) (mem_zip_of hj hw) ((s, some kg), i) (mem_zipIdx_of_getElem? hsi)
  simp only [hi, List.all_eq_true, List.mem_append, List.mem_filter, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h1
  intro y hy o ho
  have h2 := h1 y (by
    rcases hy with ⟨hy1, hy2⟩ | hy
    · exact Or.inl ⟨hy1, hy2⟩
    · exact Or.inr (List.mem_filterMap.mpr ⟨_, hy, rfl⟩)) o ho
  simp only [Bool.or_eq_true, beq_iff_eq, Option.any_eq_true, List.all_eq_true,
    disjoint_iff] at h2
  rcases h2 with h2 | ⟨rr, hrr, hd⟩
  · exact Or.inl h2
  · exact Or.inr ⟨rr, hrr, hd⟩

theorem ruleS7_alloca {R : NatMap Range} {fr : FuncRec} {P : FP} {O : Orig}
    {pts : NatMap (List (List Nat))} {f : HFunc} (h : ruleS7 R fr P O pts f = true) {b : HBlock}
    {j : Nat} (hj : f.blocks[j]? = some b) {ss : List (HStmt × Option Nat)}
    (hw : (withCallees fr f)[j]? = some ss) {i : Nat} {s : HStmt} {c : Option Nat}
    (hsi : ss[i]? = some (s, c)) {t : Ty} {x : Nat} {tx : Ty} (hi : s.inst = .base (.alloca t))
    (hd : s.dsts = [(x, tx)]) :
    ∀ r, R.find? x = some r → ∀ y ∈ ptsAt pts b.id (i + 1), y ≠ x → ∀ o ∈ origOf O (.var y),
      o ≠ 0 → ∀ r', R.find? (o - 1) = some r' → Disj r r' := by
  unfold ruleS7 at h
  simp only [List.all_eq_true] at h
  have h1 := h (b, ss) (mem_zip_of hj hw) ((s, c), i) (mem_zipIdx_of_getElem? hsi)
  intro r hr y hy hyx o ho ho0 r' hr'
  simp only [hi, hd, hr] at h1
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · rcases h1 y hy with h2 | h2
    · exact absurd h2 hyx
    · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Option.any_eq_true] at h2
      rcases h2 o ho with h3 | ⟨r'', hr'', hd⟩
      · exact absurd h3 ho0
      · rw [hr'] at hr''; cases hr''
        exact (disjoint_iff _ _).mp hd

/-- The `withCallees` entry of block place `j`. -/
theorem withCallees_get {fr : FuncRec} {f : HFunc} {j : Nat} {b : HBlock}
    (hj : f.blocks[j]? = some b) :
    (withCallees fr f)[j]? = some (withCallees.go b.body ((fr.calls[j]?).getD [])) := by
  unfold withCallees
  rw [List.getElem?_map, List.getElem?_zipIdx, hj]
  simp

/-! ## The section's rules -/

section sec

variable {src : HSection} {low : Module} {efp : Option Nat} {r : Record}

/-- Rules S4 and S5. -/
theorem SecChecked.s45' (hS : SecChecked src low efp r) :
    (hasHeap (secP src r) = true → ∀ x ∈ secRs src r, x.2 ≤ efp.getD 0) ∧
    (∀ e, efp = some e → e < 2 ^ 32) ∧
    (∀ k f fr, (k, f, fr) ∈ secP src r → ∀ y b u v, (y, Malloc.heap b u v) ∈ fr.mallocs →
      b < 2 ^ 32) ∧
    ∀ x ∈ secRs src r, x.2 < 2 ^ 32 := by
  have h := hS.s45
  unfold ruleS45 at h
  dsimp only at h
  split at h
  · cases h
  · next hc1 =>
    split at h
    · cases h
    · next hc2 =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false,
        List.all_eq_true, decide_eq_true_eq, Classical.not_not] at hc1 hc2
      refine ⟨fun hh => hc1 hh, fun e he => by rw [he] at hc2; simpa using hc2.1.1, ?_, hc2.2⟩
      intro k f fr hm y b u v hy
      exact hc2.1.2 b (List.mem_flatMap.mpr ⟨(k, f, fr), hm, List.mem_map.mpr ⟨(y, .heap b u v), hy, rfl⟩⟩)

/-- Rule S1, with a heap. -/
theorem SecChecked.s1' (hS : SecChecked src low efp r) (hh : hasHeap (secP src r) = true) :
    ∃ e, efp = some e ∧ 0x60 ≤ e ∧ ∀ x ∈ secRs src r, Disj (0x40, 0x60) x := by
  have h := hS.s1
  unfold ruleS1 at h
  split at h
  · cases h
  · rw [if_pos hh] at h
    cases hefp : efp with
    | none => rw [hefp] at h; cases h
    | some e =>
      rw [hefp] at h
      simp only at h
      by_cases h1 : e < 0x60
      · rw [if_pos h1] at h; cases h
      · rw [if_neg h1] at h
        by_cases h2 : (secRs src r).all (disjoint (0x40, 0x60)) = true
        · exact ⟨e, rfl, by omega, fun x hx => (disjoint_iff _ _).mp (List.all_eq_true.mp h2 x hx)⟩
        · rw [if_neg h2] at h; cases h

theorem secF0_mem {P : List (Nat × HFunc × FuncRec)} {x : Nat}
    (hx : x ∈ P.flatMap fun (_, _, fr) => fr.mallocs.map fun (_, m) => match m with
      | .heap b _ _ => b
      | .fixed _ _ => 0) :
    x = 0 ∨ ∃ k f fr, (k, f, fr) ∈ P ∧ ∃ y u v, (y, Malloc.heap x u v) ∈ fr.mallocs := by
  obtain ⟨⟨k, f, fr⟩, hm, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨⟨y, m⟩, hy, rfl⟩ := List.mem_map.mp hx
  cases m with
  | heap b u v => exact Or.inr ⟨k, f, fr, hm, y, u, v, hy⟩
  | fixed => exact Or.inl rfl

/-- The bound of the heap bases is below `2 ^ 32` (S5). -/
theorem SecChecked.F0_lt (hS : SecChecked src low efp r) : (secS src r efp).F0 < 2 ^ 32 := by
  obtain ⟨-, he, hb, -⟩ := hS.s45'
  show secF0 (secP src r) efp < 2 ^ 32
  unfold secF0
  refine foldl_max_lt ?_ fun x hx => ?_
  · cases hefp : efp with
    | none => simp
    | some e => simpa using he e hefp
  · rcases secF0_mem hx with rfl | ⟨k, f, fr, hm, y, u, v, hy⟩
    · norm_num
    · exact hb k f fr hm y x u v hy

theorem secS_e_le : (secS src r efp).e ≤ (secS src r efp).F0 := by
  show efp.getD 0 ≤ secF0 (secP src r) efp
  exact foldl_max_ge_init _ _

theorem minBase_le {k : Nat} {f : HFunc} {fr : FuncRec} (hm : (k, f, fr) ∈ secP src r) {y b : Nat}
    {u : Option Nat} {v : Bool} (hy : (y, Malloc.heap b u v) ∈ fr.mallocs) :
    b ≤ (secS src r efp).F0 := by
  show b ≤ secF0 (secP src r) efp
  exact foldl_max_ge_mem _ (List.mem_flatMap.mpr ⟨(k, f, fr), hm,
    List.mem_map.mpr ⟨(y, .heap b u v), hy, rfl⟩⟩)

theorem hasHeap_of {P : List (Nat × HFunc × FuncRec)} {k : Nat} {f : HFunc} {fr : FuncRec}
    (hm : (k, f, fr) ∈ P) {x b : Nat} {u : Option Nat} {v : Bool}
    (hl : fr.mallocs.lookup x = some (.heap b u v)) {blk : HBlock} (hb : blk ∈ f.blocks)
    {s : HStmt} (hs : s ∈ blk.body) {tx : Ty} (hd : s.dsts = [(x, tx)]) : hasHeap P = true := by
  unfold hasHeap
  refine List.any_eq_true.mpr ⟨(k, f, fr), hm, List.any_eq_true.mpr ⟨(x, .heap b u v),
    lookup_mem hl, ?_⟩⟩
  simp only [Bool.true_and, List.any_eq_true]
  exact ⟨blk, hb, s, hs, by simp [HStmt.defs, hd]⟩

/-- The `alloca` ranges of the section's function at place `k`. -/
theorem rangesAt_eq {k : Nat} {f : HFunc} {fr : FuncRec} (hm : (k, f, fr) ∈ secP src r) :
    (secX src r).rangesAt k = rangesOf r fr src.module.structs f := by
  have e : (secX src r).ranges = (placed src r).foldl (fun M (q : Nat × HFunc × FuncRec) =>
      M.insert q.1 (rangesOf r q.2.2 src.module.structs q.2.1)) .empty := by
    unfold secX facts
    split <;> rfl
  unfold Facts.rangesAt
  rw [e, natMap_foldl_get (fun q : Nat × HFunc × FuncRec => q.1)
    (fun q => rangesOf r q.2.2 src.module.structs q.2.1) _ _ (placed_keys src r) _ hm]
  rfl

end sec

/-! ## Statements with distinct definitions -/

/-- The statements of `f`, block after block. -/
def stmtsOf (f : HFunc) : List HStmt := f.blocks.flatMap (·.body)

theorem stmtsOf_mem {f : HFunc} {b : HBlock} (hb : b ∈ f.blocks) {s : HStmt} (hs : s ∈ b.body) :
    s ∈ stmtsOf f := List.mem_flatMap.mpr ⟨b, hb, hs⟩

theorem stmtsOf_nodup {f : HFunc} (h : f.defs.Nodup) : ((stmtsOf f).flatMap HStmt.defs).Nodup := by
  refine h.sublist ?_
  unfold stmtsOf HFunc.defs
  rw [List.flatMap_assoc]
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact flatMap_sublist_flatMap (fun b => List.sublist_append_right _ _) _

/-- In a list of statements whose definitions are distinct, a value is the definition of one
    statement at most, and its last after it. -/
theorem defs_split {l : List HStmt} (hnd : (l.flatMap HStmt.defs).Nodup) {s : HStmt} (hs : s ∈ l)
    {x : Nat} (hx : x ∈ s.defs) : ∃ l₁ l₂, l = l₁ ++ s :: l₂ ∧ ∀ s' ∈ l₂, x ∉ s'.defs := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
  refine ⟨l₁, l₂, rfl, fun s' hs' hx' => ?_⟩
  rw [List.flatMap_append, List.flatMap_cons] at hnd
  have h2 := (List.nodup_append.mp hnd).2.1
  exact (List.nodup_append.mp h2).2.2 x hx x (List.mem_flatMap.mpr ⟨s', hs', hx'⟩) rfl

/-- The range of an `alloca` site, from `rangesOf` (distinct definitions). -/
theorem rangesOf_find {prec : Record} {fr : FuncRec} {structs : List (String × List Ty)} {f : HFunc}
    (hnd : f.defs.Nodup) {b : HBlock} (hb : b ∈ f.blocks) {s : HStmt} (hs : s ∈ b.body) {t : Ty}
    {x : Nat} {tx : Ty} (hi : s.inst = .base (.alloca t)) (hd : s.dsts = [(x, tx)]) {loc : Loc}
    {n : Nat} (hl : fr.allocas.lookup x = some loc) (hn : sizeOf structs sizeFuel t = some n) :
    (rangesOf prec fr structs f).find? x =
      some (prec.wordAddr loc.word, prec.wordAddr loc.word + n) := by
  let upd : NatMap Range → HStmt → NatMap Range := fun R s => match s.inst, s.dsts with
    | .base (.alloca t), [(x, _)] => match fr.allocas.lookup x, sizeOf structs sizeFuel t with
      | some loc, some n => R.insert x (prec.wordAddr loc.word, prec.wordAddr loc.word + n)
      | _, _ => R
    | _, _ => R
  have e : rangesOf prec fr structs f = (stmtsOf f).foldl upd .empty := by
    unfold rangesOf stmtsOf
    rw [List.foldl_flatMap]
    rfl
  have away : ∀ (R : NatMap Range) (s' : HStmt), x ∉ s'.defs → (upd R s').find? x = R.find? x := by
    intro R s' hx
    simp only [upd]
    split
    · next t' y ty' hi' hd' =>
      split
      · rw [NatMap.find?_insert]
        have : y ≠ x := fun e => hx (by simp [HStmt.defs, hd', e])
        rw [if_neg (Ne.symm this)]
      · rfl
    · rfl
  have aways : ∀ (l : List HStmt) (R : NatMap Range), (∀ s' ∈ l, x ∉ s'.defs) →
      (l.foldl upd R).find? x = R.find? x := by
    intro l
    induction l with
    | nil => intro R _; rfl
    | cons a l ih =>
      intro R h
      rw [List.foldl_cons, ih _ (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')),
        away R a (h a (List.mem_cons_self ..))]
  have hx : x ∈ s.defs := by simp [HStmt.defs, hd]
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ := defs_split (stmtsOf_nodup hnd) (stmtsOf_mem hb hs) hx
  rw [e, hl₁, List.foldl_append, List.foldl_cons, aways l₂ _ hl₂]
  simp only [upd, hi, hd, hl, hn, NatMap.find?_insert]
  simp

/-! ## One function's sites -/

section site

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.memP (U : FnUnp src low r fn fr fl e me be rs) : (fn.k, fn.f, fr) ∈ secP src r := by
  have := mem_placed (r := r) U.hf
  rw [← U.hfr] at this
  exact this

theorem FnUnp.hR (U : FnUnp src low r fn fr fl e me be rs) : fn.F.R = (secX src r).rangesAt fn.k := by
  rw [U.hF]; rfl
theorem FnUnp.hO (U : FnUnp src low r fn fr fl e me be rs) : fn.F.O = (secX src r).origAt fn.k := by
  rw [U.hF]; rfl
theorem FnUnp.hfpf (U : FnUnp src low r fn fr fl e me be rs) : fn.F.fpf = fpOf (secX src r).fp fn.k := by
  rw [U.hF]; rfl
theorem FnUnp.hD (U : FnUnp src low r fn fr fl e me be rs) : fn.F.D = (secX src r).derived.has fn.k := by
  rw [U.hF]; rfl
theorem FnUnp.ptsLive (U : FnUnp src low r fn fr fl e me be rs) (b : HBlock) (i : Nat) :
    ptsAt (pointsOf fn.f (liveRec fr fn.f)) b.id i = fn.live b i := by
  unfold Fn.live; rw [U.hpts, U.hL]
theorem FnUnp.cSrc (U : FnUnp src low r fn fr fl e me be rs) : fn.c.src = src.module := by
  rw [U.hc]; rfl
theorem FnUnp.cPrec (U : FnUnp src low r fn fr fl e me be rs) : fn.c.prec = r := by
  rw [U.hc]; rfl
theorem FnUnp.cSym (U : FnUnp src low r fn fr fl e me be rs) : fn.c.symbols = src.symbols := by
  rw [U.hc]; rfl

theorem FnUnp.frMem (U : FnUnp src low r fn fr fl e me be rs) (hh : hintsOk src low r = true) :
    fr ∈ r.funcs := by
  simp only [hintsOk, Bool.and_eq_true, beq_iff_eq] at hh
  have hk : fn.k < r.funcs.length := by rw [hh.1.1]; exact (List.getElem?_eq_some_iff.mp U.hf).1
  rw [U.hfr, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

/-- An `alloca`'s range (the record's location and its type's size), the section's rules on it
    (S1, S4, S5, address-0 mode, the footprint), and rule A1 at it. -/
theorem FnUnp.allocaFacts {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {t : Ty} {x : Nat} {tx : Ty}
    (hi : s.inst = .base (.alloca t)) (hd : s.dsts = [(x, tx)]) :
    (∀ loc n, fn.c.frec.allocas.lookup x = some loc → sizeOf fn.c.src.structs sizeFuel t = some n →
      fn.F.R.find? x = some (fn.c.prec.wordAddr loc.word, fn.c.prec.wordAddr loc.word + n)) ∧
    (∀ rg, fn.F.R.find? x = some rg → rg.2 < 2 ^ 32 ∧ (rg.1 = 0 → (secS src r efp).z = true) ∧
      ((secS src r efp).hasHeap = true → rg.2 ≤ (secS src r efp).e ∧ Disj rg (0x40, 0x60)) ∧
      rg ∈ fn.F.fpf) ∧
    (∀ rg, fn.F.R.find? x = some rg → ∀ y ∈ fn.live b (i + 1), y ≠ x →
      ∀ o ∈ origOf fn.F.O (.var y), o ≠ 0 → ∀ r', fn.F.R.find? (o - 1) = some r' → Disj rg r') := by
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have hnd := U.shape'.2.2.2.2.2.2.2.2.1
  refine ⟨fun loc n hl hn => ?_, fun rg hrg => ?_, fun rg hrg => ?_⟩
  · rw [U.hR, rangesAt_eq U.memP, U.cPrec]
    rw [U.frec] at hl
    rw [U.cSrc] at hn
    exact rangesOf_find hnd hb hsm hi hd hl hn
  · have hxs : x ∈ allocaSites fn.f :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_filterMap.mpr ⟨s, hsm, by simp [hi, hd]⟩⟩
    have hown : rg ∈ ownRanges ((secX src r).rangesAt fn.k) fn.f :=
      List.mem_filterMap.mpr ⟨x, hxs, by rw [← U.hR]; exact hrg⟩
    have hrs : rg ∈ secRs src r := List.mem_flatMap.mpr ⟨_, U.memP, hown⟩
    obtain ⟨h4, -, -, h5⟩ := hS.s45'
    refine ⟨h5 rg hrs, fun h0 => ?_, fun hh => ⟨h4 hh rg hrs, ?_⟩, ?_⟩
    · show zeroMode (placed src r) (secRs src r) = true
      unfold zeroMode
      simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl ⟨rg, hrs, h0⟩
    · obtain ⟨_, -, -, hdj⟩ := hS.s1' hh
      exact (hdj rg hrs).symm
    · rw [U.hfpf]; exact (fpOk_get hS.fp U.memP).1 rg hown
  · obtain ⟨mb₀, mblk₀, j, -, hj, hwalk⟩ := U.posWalk hb hp
    have h7 := ruleS7_alloca U.rules.s7 hj (withCallees_get hj) (go_get hwalk hs) hi hd
    rw [U.ptsLive] at h7
    rw [U.hR] at hrg ⊢
    rw [U.hO]
    exact h7 rg hrg

/-- A heap `evm_malloc`'s section: it has a heap, and the bound of the heap bases is below
    `2 ^ 32` and at least the site's minimum base. -/
theorem FnUnp.heapFacts {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {b : HBlock} (hb : b ∈ fn.f.blocks) {s : HStmt}
    (hs : s ∈ b.body) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)]) {minBase : Nat}
    {eb : Option Nat} {u : Bool} (hl : fn.c.frec.mallocs.lookup x = some (.heap minBase eb u)) :
    (secS src r efp).hasHeap = true ∧ (secS src r efp).F0 < 2 ^ 32 ∧
      minBase ≤ (secS src r efp).F0 := by
  rw [U.frec] at hl
  exact ⟨hasHeap_of U.memP hl hb hs hd, hS.F0_lt, minBase_le U.memP (lookup_mem hl)⟩

/-- A call's callee: its `Fn`, its parameters' derived flags and origins from the arguments
    (S8, S3), its footprint within the caller's, and rule A2 at the call. -/
theorem FnUnp.callFacts {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hc : check src low efp r = true) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {gn : String} {args : List Operand}
    (hi : s.inst = .base (.call gn args)) :
    ∀ kg, (calleeOf s cs).1 = some kg → ∃ fg, mkFn src low r kg = some fg ∧
      fn.c.src.funcs[kg]? = some fg.f ∧ fg.k = kg ∧
      (∀ (j : Nat) (a : Operand) (p : Nat × Ty), args[j]? = some a → fg.f.params[j]? = some p →
        ((secS src r efp).z = true → (secX src r).derived.op fn.k a = true → fg.F.D p.1 = true) ∧
        (origOf fn.F.O a ≠ [] → 0 ∈ origOf fg.F.O (.var p.1))) ∧
      (∀ x ∈ fg.F.fpf, x ∈ fn.F.fpf) ∧
      (∀ y, ((y ∈ fn.live b (i + 1) ∧ y ∉ s.defs) ∨ Operand.var y ∈ args) →
        ∀ o ∈ origOf fn.F.O (.var y),
          o = 0 ∨ ∃ rr, fn.F.R.find? (o - 1) = some rr ∧ ∀ x ∈ fg.F.fpf, Disj rr x) := by
  intro kg hkg
  have hS := check_facts hc
  obtain ⟨mb₀, mblk₀, j, -, hj, hwalk⟩ := U.posWalk hb hp
  have hcl : calleeOf s cs = (cs.head?, cs.tail) := by
    rw [calleeOf_eq]; simp [callArgs, hi]
  rw [hcl] at hkg
  have hsi := go_get hwalk hs
  rw [hcl, hkg] at hsi
  have hkcs : kg ∈ cs := by
    cases cs with
    | nil => cases hkg
    | cons c cs' => simp only [List.head?_cons, Option.some.injEq] at hkg; subst hkg; simp
  have hk0 : kg ∈ (fr.calls[j]?).getD [] := (walkTo_cs hwalk).subset hkcs
  obtain ⟨g, hg, hfirst⟩ : ∃ g, src.module.funcs[kg]? = some g ∧
      firstOf (·.name) src.module.funcs kg g.name = true := by
    cases hcj : fr.calls[j]? with
    | none => rw [hcj] at hk0; cases hk0
    | some l =>
      rw [hcj] at hk0
      exact hints_callee hS.hints (U.frMem hS.hints) (List.mem_of_getElem? hcj) hk0
  obtain ⟨fg, hfg, rfl⟩ := mkFn_some hc hg hfirst
  obtain ⟨hfk, frg, flg, eg, meg, beg, rsg, Ug⟩ := fn_unp hc hfg
  have hw := withCallees_get (fr := fr) hj
  have hgo : (s, some kg) ∈ withCallees.go b.body ((fr.calls[j]?).getD []) := by
    have := go_walkTo hwalk hs
    rw [hcl, hkg] at this
    exact this
  have hcs : (kg, args) ∈ callSites fr fn.f := by
    unfold callSites
    exact List.mem_flatMap.mpr ⟨(b, j), mem_zipIdx_of_getElem? hj, go_zip hgo hi⟩
  have hkc : kg ∈ callees fr fn.f := mem_dedupB.mpr (List.mem_map.mpr ⟨(kg, args), hcs, rfl⟩)
  refine ⟨fg, hfg, by rw [U.cSrc]; exact hg, hfk, fun j' a p ha hp' => ⟨fun hz hd => ?_, fun ho => ?_⟩,
    fun x hx => ?_, ?_⟩
  · rw [Ug.hD, hfk]
    have hder := hS.der hz
    have hmem : (fn.k, fn.f, withCallees fr fn.f) ∈ derivedInput (secP src r) :=
      List.mem_map.mpr ⟨_, U.memP, rfl⟩
    have hmg : (kg, fg.f, withCallees frg fg.f) ∈ derivedInput (secP src r) :=
      List.mem_map.mpr ⟨(fg.k, fg.f, frg), Ug.memP, by rw [hfk]⟩
    exact derivedOk_param hder hmg hp'
      (derivedOk_call hder hmem (mem_zip_of hj hw) (List.mem_of_getElem? hsi) hi ha hd)
  · rw [Ug.hO, hfk]
    have hfl := flagsOk_call U.rules.flags hcs ha (by rw [← U.hO]; exact ho)
    have := Ug.rules.orig
    rw [hfk] at this
    exact origOk_param this hp' hfl
  · rw [U.hfpf]; rw [Ug.hfpf, hfk] at hx
    exact (fpOk_get hS.fp U.memP).2 kg hkc x hx
  · have h7 := ruleS7_call U.rules.s7 hj hw hsi hi
    rw [U.ptsLive] at h7
    rw [U.hR, U.hO, Ug.hfpf, hfk]
    exact h7

end site

end Fe.Sonatina.Stage3.Place
