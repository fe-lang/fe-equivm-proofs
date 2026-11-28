import Fe.Sonatina.Stage3.Place.Inv
import Fe.Sonatina.Stage3.Place.Rules

/-!
# The machine side of a template, and the frame relation across a statement

A source statement other than a call is lowered to machine statements that call nothing
(`Place/Lower.lean`, `stmt`); the simulation runs them by `runPlain`, the machine IR's run of
call-free statements (`runInst` and `bind`, as `runBodyG` runs them under the guard that protects
nothing).  This file gives:

- `mval_eval`: an operand with a word evaluates to it; `runPlain_cons_bin` and the like: the run
  of one statement of the shape `take1` matches;
- `envRel_step`: the frame relation after a statement, from the one before, the statement's
  results related, and the machine values it defines not those of other live values
  (`clobberOk`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The machine run of call-free statements. -/
def runPlain (c : Ctx) : Env → List Stmt → FeM Env
  | env, [] => pure env
  | env, s :: rest => do
    let vals ← runInst c env s.inst
    let env ← Fe.Sonatina.bind env s.dsts vals
    runPlain c env rest

theorem runPlain_append (c : Ctx) (env : Env) (ms ms' : List Stmt) :
    runPlain c env (ms ++ ms') = (runPlain c env ms >>= fun env => runPlain c env ms') := by
  induction ms generalizing env with
  | nil => simp [runPlain]
  | cons s rest ih => simp only [List.cons_append, runPlain, bind_assoc, ih]

/-- An operand with a word evaluates to it, as an `i256`. -/
theorem mval_eval {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalOperand env o = pure (.int 256 m) := by
  cases o with
  | var r =>
    simp only [mval] at h
    split at h
    · next v hv => cases h; simp [evalOperand, hv]
    · cases h
  | imm bits v =>
    simp only [mval] at h
    split at h
    · next hb => cases h; subst hb; rfl
    · cases h

theorem mval_evalInt {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalInt env o = pure (256, m) := by
  simp [evalInt, mval_eval h]

theorem mval_evalWord {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalWord env o = pure (Ethereum.UInt256.ofNat m) := by
  simp [evalWord, mval_evalInt h]

/-- Binding one word result. -/
theorem bind_one (env : Env) (r : Nat) (v : Nat) :
    Fe.Sonatina.bind env [(r, .int 256)] [.int 256 v] = pure (env.insert r (.int 256 (v % W))) := by
  simp [Fe.Sonatina.bind, Val.as, Ty.bits, W]

/-- The run of a binary operation on two words. -/
theorem runPlain_bin (c : Ctx) {env : Env} {op : BinOp} {a b : Operand} {x y r : Nat}
    (ha : mval env a = some x) (hb : mval env b = some y) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .bin op a b⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (op.eval 256 x y % W))) rest := by
  simp [runPlain, runInst, evalPair, mval_evalInt ha, mval_evalInt hb, bind_one]

/-- The run of a comparison of two words. -/
theorem runPlain_cmp (c : Ctx) {env : Env} {op : CmpOp} {a b : Operand} {x y r : Nat}
    (ha : mval env a = some x) (hb : mval env b = some y) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .cmp op a b⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (if op.eval 256 x y then 1 else 0))) rest := by
  simp only [runPlain, runInst, evalPair, mval_evalInt ha, mval_evalInt hb, pure_bind, beq_self_eq_true,
    if_true, Fe.Sonatina.bind, Fe.Sonatina.bool]
  split <;> simp [Val.as, Ty.bits]

/-- The run of `is_zero` of a word. -/
theorem runPlain_isZero (c : Ctx) {env : Env} {a : Operand} {x r : Nat}
    (ha : mval env a = some x) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .isZero a⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (if x = 0 then 1 else 0))) rest := by
  simp only [runPlain, runInst, mval_evalInt ha, pure_bind, Fe.Sonatina.bind, Fe.Sonatina.bool]
  split <;> simp_all [Val.as, Ty.bits]

/-! ## The frame relation across a statement -/

/-- The machine value of each live value of `L` other than `own`'s is kept by an update of the
    machine environment that changes only `ds`, when no machine value in `ds` is one of theirs. -/
theorem mval_keep {vm : VM} {envM envM' : Env} {ds : List Nat}
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {y : Nat}
    (hy : ∀ m ∈ ds, vm.find? y ≠ some (.var m)) :
    (vm.find? y).bind (mval envM') = (vm.find? y).bind (mval envM) := by
  cases h : vm.find? y with
  | none => rfl
  | some o =>
    cases o with
    | var r =>
      have hr : r ∉ ds := fun hm => hy r hm h
      simp only [Option.bind_some, mval, hkeep r hr]
    | imm bits v => rfl

theorem foldl_insert_other {x : Nat} :
    ∀ (l : List ((Nat × Ty) × H.Val)) (env : HEnv), (∀ p ∈ l, p.1.1 ≠ x) →
      (l.foldl (fun env (d, v) => env.insert d.1 v) env)[x]? = env[x]?
  | [], _, _ => rfl
  | p :: l, env, h => by
    rw [List.foldl_cons, foldl_insert_other l _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rw [Std.TreeMap.getElem?_insert]
    have := h p (List.mem_cons_self ..)
    simp [compare_eq_iff_eq, this]

/-- A binding leaves the values it does not bind. -/
theorem bindVals_other {env env' : HEnv} {dsts : List (Nat × Ty)} {vals : List H.Val}
    (h : bindVals env dsts vals = some env') {x : Nat} (hx : x ∉ dsts.map (·.1)) :
    env'[x]? = env[x]? := by
  unfold bindVals at h
  split at h
  · cases h
    apply foldl_insert_other
    intro p hp
    have := (List.of_mem_zip hp).1
    exact fun he => hx (List.mem_map.mpr ⟨p.1, this, he⟩)
  · cases h

theorem bindVals_one {env env' : HEnv} {x : Nat} {t : Ty} {v : H.Val}
    (h : bindVals env [(x, t)] [v] = some env') : v.fits t = true ∧ env' = env.insert x v := by
  unfold bindVals at h
  split at h
  · next hc => cases h; simp at hc; exact ⟨hc, rfl⟩
  · cases h

/-- The frame relation after a statement: the values live after it that it does not define are
    live before it and keep their values on both sides (the machine values the statement defines
    are none of theirs, `clobberOk`); those it defines are related by `hnew`. -/
theorem envRel_step {z : Bool} {F : Frame} {g : Ghost} {hst hst' : H.State} {envH envH' : HEnv}
    {envM envM' : Env} {L L' : List Nat} {dsts : List (Nat × Ty)} {vals : List H.Val}
    {ds : List Nat}
    (hE : EnvRel z F g hst envH envM L)
    (hL : ∀ y ∈ L', y ∉ dsts.map (·.1) → y ∈ L)
    (hb : bindVals envH dsts vals = some envH')
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?)
    (hcl : ∀ y ∈ L', y ∉ dsts.map (·.1) → ∀ m ∈ ds, F.vm.find? y ≠ some (.var m))
    (hold : ∀ v, ValOk hst v → ValOk hst' v)
    (horig : ∀ os v, OrigOk g hst F.R F.fpf os v → OrigOk g hst' F.R F.fpf os v)
    (hnew : ∀ x ∈ dsts.map (·.1), x ∈ L' → ∃ v m, envH'[x]? = some v ∧
      (∃ t, F.decls.find? x = some t ∧ v.fits t = true) ∧ (F.vm.find? x).bind (mval envM') = some m ∧
      VRel g z (F.D x) v m ∧ ValOk hst' v ∧ OrigOk g hst' F.R F.fpf (origOf F.O (.var x)) v) :
    EnvRel z F g hst' envH' envM' L' := by
  intro x hx
  by_cases hd : x ∈ dsts.map (·.1)
  · exact hnew x hd hx
  · obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := hE x (hL x hx hd)
    refine ⟨v, m, ?_, h2, ?_, h4, hold v h5, horig _ v h6⟩
    · rw [bindVals_other hb hd]; exact h1
    · rw [mval_keep hkeep (hcl x hx hd)]; exact h3

end Fe.Sonatina.Stage3.Place
