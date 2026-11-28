import Fe.Sonatina.Stage3.Place.Sim

/-!
# What `check` establishes, statically

`check src low efp r = true` unpacked: the section's rules (`SecChecked`) and, for each source
function, its machine function, its translation and the per-function rules (`FnRules`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

theorem orElse_none {α : Type} {x y : Option α} : (x <|> y) = none ↔ x = none ∧ y = none := by
  cases x <;> simp

/-- The liveness certificate of a function's record, or the computed one. -/
def liveRec (fr : FuncRec) (f : HFunc) : Live :=
  match fr.liveCert with
  | some l => NatMap.ofList l
  | none => liveOf f

/-- The per-function rules `funcDiag` checks after the translation. -/
structure FnRules (r : Record) (X : Facts) (z : Bool) (k : Nat) (f : HFunc) (fr : FuncRec)
    (fl : FuncLower) : Prop where
  live : liveOkAt f (liveRec fr f) (pointsOf f (liveRec fr f)) = true
  clob : clobberOk f (liveRec fr f) (pointsOf f (liveRec fr f)) fl = true
  self : selfFree f = true
  orig : origOk fr X.flags k f (X.origAt k) = true
  flags : flagsOk X.flags fr f (X.origAt k) = true
  s3 : s3Uses (X.origAt k) f = true
  s6 : ruleS6 (X.origAt k) fr f = true
  s7 : ruleS7 (X.rangesAt k) fr X.fp (X.origAt k) (pointsOf f (liveRec fr f)) f = true
  s8 : z = true → notObserved X.derived k f = true

theorem funcDiag_none {src : HSection} {low : Module} {r : Record} {X : Facts} {z : Bool}
    {k : Nat} {f : HFunc} {fr : FuncRec} (h : funcDiag src low r X z (k, f, fr) = none) :
    ∃ mf fl, low.funcs[fr.mfunc]? = some mf ∧ funcLower (fctx src r fr f mf) f = some fl ∧
      FnRules r X z k f fr fl := by
  unfold funcDiag at h
  dsimp only at h
  split at h
  · cases h
  · next mf hmf =>
    split at h
    · cases h
    · next fl hfl =>
      refine ⟨mf, fl, hmf, hfl, ?_⟩
      split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
      have t : ∀ {b : Bool}, ¬ (b = false) → b = true := fun {b} h => by cases b <;> simp_all
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true, not_and,
        Bool.not_eq_true] at h1 h2 h3 h4 h5 h6 h7 h8
      have h4' : origOk fr X.flags k f (X.origAt k) = true ∧ flagsOk X.flags fr f (X.origAt k) = true := by
        cases ho : origOk fr X.flags k f (X.origAt k) <;> simp_all
      exact ⟨t h1, t h2, t h3, h4'.1, h4'.2, t h5, t h6, t h7, fun hz => by
        cases hn : notObserved X.derived k f <;> simp_all⟩

/-- The section's facts, as `diagnose` computes them. -/
abbrev secP (src : HSection) (r : Record) : List (Nat × HFunc × FuncRec) := placed src r
abbrev secX (src : HSection) (r : Record) : Facts := facts src r (placed src r)
abbrev secRs (src : HSection) (r : Record) : List Range :=
  (placed src r).flatMap fun (k, f, _) => ownRanges ((secX src r).rangesAt k) f
abbrev secZ (src : HSection) (r : Record) : Bool := zeroMode (placed src r) (secRs src r)

/-- What `check` accepting a section gives. -/
structure SecChecked (src : HSection) (low : Module) (efp : Option Nat) (r : Record) : Prop where
  hints : hintsOk src low r = true
  s1 : ruleS1 (secP src r) (secRs src r) efp = none
  s2 : ruleS2 src r (secP src r) = none
  s45 : ruleS45 (secP src r) (secRs src r) efp = none
  fp : fpOk (fpInput (secP src r) (secX src r).ranges) (secX src r).fp = true
  der : secZ src r = true → derivedOk (derivedInput (secP src r)) (secX src r).derived = true
  fns : ∀ kf ∈ secP src r, funcDiag src low r (secX src r) (secZ src r) kf = none
  entry : ∃ k e, src.module.funcs.findIdx? (·.name == src.entry) = some k ∧
    src.module.funcs[k]? = some e ∧ e.params = []

theorem check_facts {src : HSection} {low : Module} {efp : Option Nat} {r : Record}
    (hc : check src low efp r = true) : SecChecked src low efp r := by
  unfold check diagnose at hc
  simp only [Option.isNone_iff_eq_none] at hc
  split at hc
  · cases hc
  · next hh =>
    simp only [orElse_none] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    split at h4
    · cases h4
    · next h5 =>
      split at h4
      · cases h4
      · next h6 =>
        have t : ∀ {b : Bool}, ¬ (b = false) → b = true := fun {b} h => by cases b <;> simp_all
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true, not_and,
          Bool.not_eq_true] at hh h5 h6
        rw [orElse_none] at h4
        obtain ⟨h7, h8⟩ := h4
        refine ⟨t hh, h1, h2, h3, t h5, fun hz => by
          cases hd : derivedOk (derivedInput (secP src r)) (secX src r).derived <;> simp_all, ?_, ?_⟩
        · intro kf hkf
          exact List.findSome?_eq_none_iff.mp h7 kf hkf
        · split at h8
          · next k hk =>
            split at h8
            · next e he =>
              split at h8
              · next h9 => exact ⟨k, e, hk, he, List.isEmpty_iff.mp h9⟩
              · cases h8
            · cases h8
          · cases h8

/-! ## The checking walk keeps the value map -/

theorem bindV_true {vm vm' : VM} {x : Nat} {o : Operand} (h : bindV true vm x o = some vm') :
    vm' = vm := by
  simp only [bindV, ite_true] at h
  split at h
  · cases h; rfl
  · cases h

theorem foldlM_bindV_true {vm vm' : VM} :
    ∀ {l : List ((Nat × Ty) × Nat)},
      l.foldlM (fun vm (x : (Nat × Ty) × Nat) => bindV true vm x.1.1 (.var x.2)) vm = some vm' → vm' = vm
  | [], h => by simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm
  | p :: l, h => by
    rw [List.foldlM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨vm₁, h1, h2⟩ := h
    have := bindV_true h1
    subst this
    exact foldlM_bindV_true h2

/-- A step's value map, as a property of an optional step. -/
def Keeps (vm : VM) (o : Option Step) : Prop := ∀ x, o = some x → x.1 = vm

theorem keeps_none {vm : VM} : Keeps vm none := fun _ h => by cases h
theorem keeps_some {vm : VM} {mb : Nat} {ms : List Stmt} {ds : List Nat} :
    Keeps vm (some (vm, mb, ms, ds)) := fun _ h => by cases h; rfl
theorem keeps_bind {α : Type} {vm : VM} {a : Option α} {f : α → Option Step}
    (h : ∀ y, Keeps vm (f y)) : Keeps vm (a.bind f) := fun x hx => by
  cases a with
  | none => cases hx
  | some y => exact h y x hx
theorem keeps_bindV {vm : VM} {x : Nat} {o : Operand} {f : VM → Option Step}
    (h : Keeps vm (f vm)) : Keeps vm ((bindV true vm x o).bind f) := fun y hy => by
  cases hb : bindV true vm x o with
  | none => rw [hb] at hy; cases hy
  | some vm₂ => rw [hb] at hy; rw [bindV_true hb] at hy; exact h y hy
theorem keeps_foldlM {vm : VM} {l : List ((Nat × Ty) × Nat)} {f : VM → Option Step}
    (h : Keeps vm (f vm)) :
    Keeps vm ((l.foldlM (fun vm (x : (Nat × Ty) × Nat) => bindV true vm x.1.1 (.var x.2)) vm).bind f) :=
  fun y hy => by
  cases hb : l.foldlM (fun vm (x : (Nat × Ty) × Nat) => bindV true vm x.1.1 (.var x.2)) vm with
  | none => rw [hb] at hy; cases hy
  | some vm₂ => rw [hb] at hy; rw [foldlM_bindV_true hb] at hy; exact h y hy

theorem keeps_none_bind {α : Type} {vm : VM} {f : α → Option Step} :
    Keeps vm ((none : Option α) >>= f) := fun _ h => by cases h

theorem keeps_ite {vm : VM} {p : Prop} [Decidable p] {a b : Option Step} (ha : Keeps vm a)
    (hb : Keeps vm b) : Keeps vm (if p then a else b) := by
  split
  · exact ha
  · exact hb

theorem stmt_keeps (c : FCtx) (vm : VM) (s : HStmt) (mb : Nat) (ms : List Stmt)
    (callee? : Option Nat) : Keeps vm (stmt c true vm s mb ms callee?) := by
  unfold stmt
  split
  case h_18 a l x tx _ _ =>
    apply keeps_ite
    · apply keeps_bind; intro a'
      rcases l with y | ⟨bits, _ | n⟩
      all_goals
        simp only
        repeat
          first
          | exact keeps_none
          | exact keeps_some
          | apply keeps_bindV
          | apply keeps_foldlM
          | (apply keeps_bind; intro _)
          | apply keeps_ite
          | split
    · exact keeps_none_bind
  case h_22 a x tx _ _ =>
    apply keeps_ite
    · apply keeps_bind; intro m
      rcases m with ⟨base, rule⟩ | ⟨minBase, _ | eb, _ | _⟩
      all_goals
        simp only
        repeat
          first
          | exact keeps_none
          | exact keeps_some
          | apply keeps_bindV
          | apply keeps_foldlM
          | (apply keeps_bind; intro _)
          | apply keeps_ite
          | split
    · exact keeps_none_bind
  all_goals
    simp only [Option.bind_eq_bind]
    repeat
      first
      | exact keeps_none
      | exact keeps_some
      | apply keeps_bindV
      | apply keeps_foldlM
      | (apply keeps_bind; intro _)
      | split

theorem stmt_vm {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat}
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) : vm' = vm :=
  stmt_keeps c vm s mb ms callee? _ h

/-! ## The translation of a function -/

theorem mapM_some_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = some bs → List.Forall₂ (fun a b => f a = some b) l bs
  | [], bs, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; exact .nil
  | a :: l, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs', rfl⟩ := h
    exact .cons hb (mapM_some_forall₂ hbs')

theorem funcLower_some {c : FCtx} {f : HFunc} {fl : FuncLower} (h : funcLower c f = some fl) :
    ∃ e me be rs, f.blocks.head? = some e ∧ c.mf.blocks.head? = some me ∧ c.bm.find? e.id = some be ∧
      funcShapeOk c f e me be = true ∧ fl.vm = funcVm c f ∧ paramsOk c f fl.vm = true ∧
      regionsOf c f fl.vm = some rs ∧ distinct (trampOf me be ++ rs.flatMap (·.2.2.2)) = true ∧
      fl.tb = NatMap.ofList (rs.map fun (b, t, _) => (b, t)) ∧
      fl.defs = NatMap.ofList (rs.map fun (b, _, d, _) => (b, d)) ∧
      phisAllOk c f fl.vm fl.tb = true := by
  unfold funcLower at h
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨me, hme, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨be, hbe, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · next hc =>
    split at h
    · next hp =>
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · next hd =>
        split at h
        · next hph =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨e, me, be, rs, he, hme, hbe, hc, rfl, hp, hrs, hd, rfl, rfl, hph⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## The checking walk, position by position -/

theorem walk_cons (c : FCtx) (vm : VM) (s : HStmt) (rest : List HStmt) (mb : Nat) (ms : List Stmt)
    (cs : List Nat) : walk c true vm (s :: rest) mb ms cs =
      match calleeOf s cs with
      | (callee?, cs') => (stmt c true vm s mb ms callee?).bind fun r =>
        (walk c true r.1 rest r.2.1 r.2.2.1 cs').bind fun r' =>
          some (r'.1, r'.2.1, r'.2.2.1, r.2.2.2 :: r'.2.2.2.1, entered c.mf mb r.2.1 ++ r'.2.2.2.2) :=
  rfl

/-- The checking walk is `walkTo`, statement by statement: it keeps the value map, ends where
    `walkTo` does after the last statement, and records each statement's machine values. -/
theorem walk_walkTo {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} {vm' : VM} {tbk : Nat} {ms' : List Stmt} {dss : List (List Nat)}
    {bs : List Nat}, walk c true vm l mb ms cs = some (vm', tbk, ms', dss, bs) →
    vm' = vm ∧ (∃ cs', walkTo c vm l mb ms cs l.length = some (tbk, ms', cs')) ∧
    ∀ (i : Nat) (s : HStmt) (mb₁ : Nat) (ms₁ : List Stmt) (cs₁ : List Nat) (vm₂ : VM) (mb₂ : Nat)
      (ms₂ : List Stmt) (ds : List Nat), l[i]? = some s →
      walkTo c vm l mb ms cs i = some (mb₁, ms₁, cs₁) →
      stmt c true vm s mb₁ ms₁ (calleeOf s cs₁).1 = some (vm₂, mb₂, ms₂, ds) → dss[i]? = some ds
  | [], mb, ms, cs, vm', tbk, ms', dss, bs, h => by
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, ⟨cs, rfl⟩, fun i s _ _ _ _ _ _ _ hs => by simp at hs⟩
  | s :: rest, mb, ms, cs, vm', tbk, ms', dss, bs, h => by
    rw [walk_cons] at h
    rcases hc : calleeOf s cs with ⟨callee?, cs₀⟩
    rw [hc] at h
    dsimp only at h
    obtain ⟨⟨vm₁, mb₁, ms₁, ds₁⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨vm₂, tb₂, ms₂, dss₂, bs₂⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have hv1 : vm₁ = vm := stmt_vm h1
    subst hv1
    obtain ⟨hv2, ⟨cs', hw⟩, hds⟩ := walk_walkTo h2
    refine ⟨hv2, ⟨cs', ?_⟩, ?_⟩
    · simp only [List.length_cons, walkTo, hc, h1]
      exact hw
    · intro i t mb₃ ms₃ cs₃ vm₃ mb₄ ms₄ ds hi hp hst
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [walkTo, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        rw [hc] at hst
        rw [h1] at hst
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        simp [hst.2.2.2]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        simp only [walkTo, hc, h1] at hp
        simpa using hds i t mb₃ ms₃ cs₃ vm₃ mb₄ ms₄ ds hi hp hst

theorem blockLower_some {c : FCtx} {vm : VM} {rets : List Ty} {b : HBlock} {cs : List Nat}
    {vm' : VM} {tbk : Nat} {dss : List (List Nat)} {bs' : List Nat}
    (h : blockLower c true vm rets b cs = some (vm', tbk, dss, bs')) :
    ∃ mb mblk ms bs tblk, c.bm.find? b.id = some mb ∧ c.mf.block? mb = some mblk ∧
      walk c true vm b.body mb mblk.body cs = some (vm', tbk, ms, dss, bs) ∧
      c.mf.block? tbk = some tblk ∧ termOk c vm' rets b.term ms tblk.term = true ∧
      bs' = mb :: bs := by
  unfold blockLower at h
  obtain ⟨mb, hmb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mblk, hmblk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨vm₁, tb₁, ms₁, dss₁, bs₁⟩, hw, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tblk, htblk, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · next ht =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨mb, mblk, ms₁, bs₁, tblk, hmb, hmblk, hw, htblk, ht, rfl⟩
  · cases h

end Fe.Sonatina.Stage3.Place
