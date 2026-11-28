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

end Fe.Sonatina.Stage3.Place
