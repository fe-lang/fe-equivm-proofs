import Fe.Sonatina.Steps.Oracle

/-!
# Calls, step-indexed

The simulation of S14 (`Sim.lean`) runs a function's blocks with calls by a fixed oracle
(`runBlocksO`), so that a block's statements run structurally and each template's statements
run as `runBodyO`.  The oracle of a run with calls `n` deep at most is `runFuncN m c n`.  This
file shows that every run of the machine module that ends is such a run for some `n`
(`runFunc_index`), by fixpoint induction over the module's mutual runner; then the call contract
holds of `runFunc m c` when it holds of every `runFuncN m c n`, which is induction on `n`.

`Def x y`: every run of `x` that ends is a run of `y`, alike.  The runs with an oracle are
monotone in it (`def_runBodyO`, `def_runBlocksO`, `def_runFuncO`), and `runFuncN m c` grows
with `n` (`runFuncN_mono`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.Steps Lean.Order

/-- Every run of `x` that ends is a run of `y` that ends alike. -/
def Def {α : Type} (x y : FeM α) : Prop := ∀ I w r, x.exec I w = some r → y.exec I w = some r

/-- `Def`, call by call. -/
def ODef (o o' : Oracle) : Prop := ∀ name args, Def (o name args) (o' name args)

theorem Def.refl {α : Type} (x : FeM α) : Def x x := fun _ _ _ h => h

theorem Def.trans {α : Type} {x y z : FeM α} (h₁ : Def x y) (h₂ : Def y z) : Def x z :=
  fun I w r h => h₂ I w r (h₁ I w r h)

theorem Def.bind {α β : Type} {x x' : FeM α} {k k' : α → FeM β} (hx : Def x x')
    (hk : ∀ a, Def (k a) (k' a)) : Def (x >>= k) (x' >>= k') := by
  intro I w r h
  simp only [Fe.M.exec_bind] at h ⊢
  cases hx0 : x.exec I w with
  | none => rw [hx0] at h; cases h
  | some r0 =>
    rw [hx0] at h
    rw [hx I w r0 hx0]
    rcases r0 with e | ⟨a, w'⟩
    · exact h
    · exact hk a I w' r h

theorem Def.stuck {α : Type} (y : FeM α) : Def stuck y := fun _ _ _ h => by cases h

/-- That `x` is defined where `y` is is admissible in `x`. -/
theorem admissible_def {α : Type} (y : FeM α) : admissible (fun x : FeM α => Def x y) := by
  have h := Fe.M.admissible_outcome (α := α)
    (fun I w res => ∀ r, res = some r → y.exec I w = some r) (fun _ _ _ h => by cases h)
  have e : (fun x : FeM α => Def x y) =
      fun x => ∀ I w, (fun I w res => ∀ r, res = some r → y.exec I w = some r) I w (x.exec I w) := by
    funext x
    exact propext ⟨fun hx I w r h => hx I w r h, fun hx I w r h => hx I w r h⟩
  rw [e]; exact h

/-- "Every run that ends satisfies `Q`" is admissible. -/
theorem admissible_ends {α : Type} (Q : Fe.EVM.Env → World → Except (Exit World) (α × World) → Prop) :
    admissible (fun x : FeM α => ∀ I w r, x.exec I w = some r → Q I w r) :=
  Fe.M.admissible_outcome (fun I w res => ∀ r, res = some r → Q I w r) fun _ _ _ h => by cases h

/-! ## The runs with an oracle are monotone in it -/

section mono

variable {o o' : Oracle} (ho : ODef o o') (c : Ctx)
include ho

theorem def_runStmtO (env : Env) (s : Stmt) : Def (runStmtO o c env s) (runStmtO o' c env s) := by
  unfold runStmtO
  split
  · exact Def.bind (Def.refl _) fun args => ho _ args
  · exact Def.refl _

theorem def_runBodyO : ∀ (env : Env) (ms : List Stmt), Def (runBodyO o c env ms) (runBodyO o' c env ms)
  | _, [] => Def.refl _
  | env, s :: rest => Def.bind (def_runStmtO ho c env s) fun _ =>
      Def.bind (Def.refl _) fun env' => def_runBodyO env' rest

theorem def_stepBlock (f : Func) (env : Env) (prev : Option Nat) (id : Nat) :
    Def (stepBlock o c f env prev id) (stepBlock o' c f env prev id) := by
  unfold stepBlock
  split
  · exact Def.bind (Def.refl _) fun env₁ => Def.bind (def_runBodyO ho c env₁ _) fun _ => Def.refl _
  · exact Def.refl _

theorem def_runBlocksO (f : Func) :
    ∀ env prev id, Def (runBlocksO o c f env prev id) (runBlocksO o' c f env prev id) := by
  refine runBlocksO.fixpoint_induct o c f
    (fun G => ∀ env prev id, Def (G env prev id) (runBlocksO o' c f env prev id)) ?_ ?_
  · exact Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
        ∀ prev id, Def (G prev id) (runBlocksO o' c f env prev id))
      fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
        ∀ id, Def (G id) (runBlocksO o' c f env prev id))
      fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
        Def x (runBlocksO o' c f env prev id)) fun id => admissible_def _
  · intro G hG env prev id
    rw [runBlocksO]
    refine Def.bind (def_stepBlock ho c f env prev id) fun n => ?_
    cases n with
    | goto env' d => exact hG env' (some id) d
    | done v => exact Def.refl _

theorem def_runFuncO (f : Option Func) (args : List Val) :
    Def (runFuncO o c f args) (runFuncO o' c f args) := by
  unfold runFuncO
  rcases f with _ | f
  · exact Def.refl _
  · dsimp only
    rcases f.blocks.head? with _ | e
    · exact Def.refl _
    · exact Def.bind (Def.refl _) fun env => def_runBlocksO ho c f env none e.id

end mono

/-! ## Step-indexed calls -/

/-- The run of `m`'s functions with calls at most `n` deep: deeper calls diverge. -/
def runFuncN (m : Module) (c : Ctx) : Nat → Oracle
  | 0 => fun _ _ => stuck
  | n + 1 => fun name args => runFuncO (runFuncN m c n) c (m.func? name) args

theorem runFuncN_succ (m : Module) (c : Ctx) : ∀ n, ODef (runFuncN m c n) (runFuncN m c (n + 1))
  | 0 => fun _ _ => Def.stuck _
  | n + 1 => fun _ args => def_runFuncO (runFuncN_succ m c n) c _ args

theorem runFuncN_mono (m : Module) (c : Ctx) {n n' : Nat} (h : n ≤ n') :
    ODef (runFuncN m c n) (runFuncN m c n') := by
  induction h with
  | refl => exact fun _ _ => Def.refl _
  | step _ ih => exact fun name args => (ih name args).trans (runFuncN_succ m c _ name args)

/-- A run of `x >>= k` that ends, from a run of `x` and runs of `k` that each end at some
    index, ends at an index, when both families grow with the index. -/
theorem index_bind {α β : Type} {x : FeM α} {k : α → FeM β} {X : Nat → FeM α}
    {K : Nat → α → FeM β} (hX : ∀ {n n'}, n ≤ n' → Def (X n) (X n'))
    (hK : ∀ {n n'} a, n ≤ n' → Def (K n a) (K n' a)) {I : Fe.EVM.Env} {w : World}
    (hx : ∀ r, x.exec I w = some r → ∃ n, (X n).exec I w = some r)
    (hk : ∀ a w' r, (k a).exec I w' = some r → ∃ n, (K n a).exec I w' = some r)
    {r : Except (Exit World) (β × World)} (h : (x >>= k).exec I w = some r) :
    ∃ n, (X n >>= K n).exec I w = some r := by
  simp only [Fe.M.exec_bind] at h ⊢
  cases hx0 : x.exec I w with
  | none => rw [hx0] at h; cases h
  | some r0 =>
    rw [hx0] at h
    obtain ⟨n₁, h₁⟩ := hx r0 hx0
    rcases r0 with e | ⟨a, w'⟩
    · exact ⟨n₁, by rw [h₁]; exact h⟩
    · obtain ⟨n₂, h₂⟩ := hk a w' r h
      refine ⟨max n₁ n₂, ?_⟩
      rw [hX (le_max_left n₁ n₂) I w _ h₁]
      exact hK a (le_max_right n₁ n₂) I w' r h₂

/-- The terminator's continuation as `runBlocksG` runs it, with block runner `B`. -/
def termK (B : Env → Option Nat → Nat → FeM (List Val)) (id : Nat) (env : Env) :
    Term → FeM (List Val)
  | .jump dest => B env (some id) dest
  | .br cond nz z => do
    let (_, v) ← evalInt env cond
    B env (some id) (if v != 0 then nz else z)
  | .brTable s default cases => do
    let (_, v) ← evalInt env s
    let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
    match (vals.find? (·.1 == v)).map (·.2) <|> default with
    | some dest => B env (some id) dest
    | none => stuck
  | .ret values => values.mapM (evalOperand env)
  | .evmReturn a l => do
    let e ← returnData (← evalWord env a) (← evalWord env l)
    nomatch e
  | .evmRevert a l => do
    let e ← revertData (← evalWord env a) (← evalWord env l)
    nomatch e
  | .evmStop => do
    let e ← stopCall
    nomatch e
  | .evmInvalid => do
    let e ← trap
    nomatch e
  | .evmSelfDestruct a => do
    let e ← Fe.EVM.selfdestruct (← evalWord env a)
    nomatch e
  | .unreachable => do
    let e ← trap
    nomatch e

/-- `termK` is `runTerm` and the block runner. -/
theorem termK_eq (B : Env → Option Nat → Nat → FeM (List Val)) (id : Nat) (env : Env) (t : Term) :
    termK B id env t = (runTerm env t >>= fun
      | .goto env dest => B env (some id) dest
      | .done vals => pure vals) := by
  cases t <;> simp only [termK, runTerm, bind_assoc, pure_bind]
  all_goals first
    | rfl
    | (congr 1; funext x; rcases x; simp only [pure_bind]; done)
    | (simp only [bind_pure]; done)
    | (congr 1; funext x; congr 1; funext vals
       split <;> rename_i h <;> simp only [h, pure_bind] <;> rfl)

/-- The terminator's continuation ends at an index if the block runner does. -/
theorem index_termK {m : Module} {c : Ctx} {G : Env → Option Nat → Nat → FeM (List Val)}
    {f : Func} (hG : ∀ env prev id I w r, (G env prev id).exec I w = some r →
      ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
    (id : Nat) (env : Env) (t : Term) (I : Fe.EVM.Env) (w : World)
    (r : Except (Exit World) (List Val × World)) (h : (termK G id env t).exec I w = some r) :
    ∃ n, (termK (runBlocksO (runFuncN m c n) c f) id env t).exec I w = some r := by
  have hB : ∀ {n n' : Nat} env d, n ≤ n' →
      Def (runBlocksO (runFuncN m c n) c f env (some id) d)
        (runBlocksO (runFuncN m c n') c f env (some id) d) :=
    fun env d hn => def_runBlocksO (runFuncN_mono m c hn) c f env (some id) d
  cases t with
  | jump d => exact hG _ _ _ I w r h
  | br cnd nz z =>
    simp only [termK] at h ⊢
    exact index_bind (X := fun _ => evalInt env cnd) (fun _ => Def.refl _)
      (K := fun n (p : Nat × Nat) => runBlocksO (runFuncN m c n) c f env (some id)
        (if p.2 != 0 then nz else z))
      (fun p hn => hB _ _ hn) (fun r h => ⟨0, h⟩) (fun p w' r h => hG _ _ _ I w' r h) h
  | brTable s d cases =>
    simp only [termK] at h ⊢
    refine index_bind (X := fun _ => evalInt env s) (fun _ => Def.refl _) (fun p hn => ?_)
      (fun r h => ⟨0, h⟩) (fun p w' r h => ?_) h
    · exact Def.bind (Def.refl _) fun vals => by
        split
        · exact hB _ _ hn
        · exact Def.refl _
    · refine index_bind (X := fun _ => _) (fun _ => Def.refl _) (fun vals hn => ?_)
        (fun r h => ⟨0, h⟩) (fun vals w'' r h => ?_) h
      · split
        · exact hB _ _ hn
        · exact Def.refl _
      · split at h
        · next heq =>
          obtain ⟨n, hn⟩ := hG _ _ _ I w'' r h
          exact ⟨n, hn⟩
        · next heq => exact ⟨0, h⟩
  | ret vals => exact ⟨0, h⟩
  | evmReturn a l => exact ⟨0, h⟩
  | evmRevert a l => exact ⟨0, h⟩
  | evmStop => exact ⟨0, h⟩
  | evmInvalid => exact ⟨0, h⟩
  | evmSelfDestruct a => exact ⟨0, h⟩
  | unreachable => exact ⟨0, h⟩

/-- Every run of the machine module's function that ends is a run with calls at some bounded
    depth. -/
theorem runFunc_index (m : Module) (c : Ctx) (name : String) (args : List Val) (I : Fe.EVM.Env)
    (w : World) (r : Except (Exit World) (List Val × World))
    (h : (runFunc m c name args).exec I w = some r) :
    ∃ n, (runFuncN m c n name args).exec I w = some r := by
  rw [← runFuncG_none] at h
  refine runFuncG.fixpoint_induct Guard.none m c
    (fun H => ∀ env stmts I w r, (H [] [] env stmts).exec I w = some r →
      ∃ n, (runBodyO (runFuncN m c n) c env stmts).exec I w = some r)
    (fun F => ∀ name args I w r, (F [] name args).exec I w = some r →
      ∃ n, (runFuncN m c n name args).exec I w = some r)
    (fun G => ∀ f env prev id I w r, (G [] f env prev id).exec I w = some r →
      ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
    ?a1 ?a2 ?a3 ?s1 ?s2 ?s3 name args I w r h
  case a1 =>
    exact admissible_apply (β := fun _ => List (List Nat) → Env → List Stmt → FeM Env)
      (fun _ H => ∀ env stmts I w r, (H [] env stmts).exec I w = some r →
        ∃ n, (runBodyO (runFuncN m c n) c env stmts).exec I w = some r) []
      (admissible_apply (β := fun _ => Env → List Stmt → FeM Env)
        (fun _ H => ∀ env stmts I w r, (H env stmts).exec I w = some r →
          ∃ n, (runBodyO (runFuncN m c n) c env stmts).exec I w = some r) []
        (Fe.M.admissible_arrow (fun env (H : List Stmt → FeM Env) => ∀ stmts I w r,
            (H stmts).exec I w = some r → ∃ n, (runBodyO (runFuncN m c n) c env stmts).exec I w = some r)
          fun env => Fe.M.admissible_arrow (fun stmts (x : FeM Env) => ∀ I w r,
            x.exec I w = some r → ∃ n, (runBodyO (runFuncN m c n) c env stmts).exec I w = some r)
          fun stmts => admissible_ends _))
  case a2 =>
    exact admissible_apply (β := fun _ => String → List Val → FeM (List Val))
      (fun _ F => ∀ name args I w r, (F name args).exec I w = some r →
        ∃ n, (runFuncN m c n name args).exec I w = some r) []
      (Fe.M.admissible_arrow (fun name (F : List Val → FeM (List Val)) => ∀ args I w r,
          (F args).exec I w = some r → ∃ n, (runFuncN m c n name args).exec I w = some r)
        fun name => Fe.M.admissible_arrow (fun args (x : FeM (List Val)) => ∀ I w r,
          x.exec I w = some r → ∃ n, (runFuncN m c n name args).exec I w = some r)
        fun args => admissible_ends _)
  case a3 =>
    exact admissible_apply (β := fun _ => Func → Env → Option Nat → Nat → FeM (List Val))
      (fun _ G => ∀ f env prev id I w r, (G f env prev id).exec I w = some r →
        ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r) []
      (Fe.M.admissible_arrow (fun f (G : Env → Option Nat → Nat → FeM (List Val)) =>
          ∀ env prev id I w r, (G env prev id).exec I w = some r →
            ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
        fun f => Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
          ∀ prev id I w r, (G prev id).exec I w = some r →
            ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
        fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
          ∀ id I w r, (G id).exec I w = some r →
            ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
        fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) => ∀ I w r,
          x.exec I w = some r → ∃ n, (runBlocksO (runFuncN m c n) c f env prev id).exec I w = some r)
        fun id => admissible_ends _)
  case s1 =>
    intro H F hH hF env stmts I w r h
    cases stmts with
    | nil => exact ⟨0, h⟩
    | cons s rest =>
      simp only [List.nil_append, List.headD_nil, List.tail_nil, guarded] at h
      simp only [runBodyO]
      have hK : ∀ {n n' : Nat} (vals : List Val), n ≤ n' →
          Def (bind env s.dsts vals >>= fun env' => runBodyO (runFuncN m c n) c env' rest)
            (bind env s.dsts vals >>= fun env' => runBodyO (runFuncN m c n') c env' rest) :=
        fun vals hn => Def.bind (Def.refl _) fun env' => def_runBodyO (runFuncN_mono m c hn) c env' rest
      refine index_bind (X := fun n => runStmtO (runFuncN m c n) c env s)
        (fun hn => def_runStmtO (runFuncN_mono m c hn) c env s) hK ?_ ?_ h
      · intro r0 h0
        rcases s with ⟨dsts, inst⟩
        cases inst
        case call callee args =>
          simp only [runStmtO]
          refine index_bind (X := fun _ => _) (fun _ => Def.refl _)
            (fun a hn => runFuncN_mono m c hn callee a) (fun r h => ⟨0, h⟩)
            (fun a w' r h => hF callee a I w' r h) h0
        all_goals exact ⟨0, h0⟩
      · intro vals w' r' h'
        exact index_bind (X := fun _ => _) (fun _ => Def.refl _)
          (fun env' hn => def_runBodyO (runFuncN_mono m c hn) c env' rest) (fun r h => ⟨0, h⟩)
          (fun env' w'' r h => hH env' rest I w'' r h) h'
  case s2 =>
    intro G hG name args I w r h
    simp only [guarded] at h
    show ∃ n, (runFuncN m c n name args).exec I w = some r
    cases hf : m.func? name with
    | none => rw [hf] at h; cases h
    | some f =>
      rw [hf] at h
      dsimp only at h
      cases he : f.blocks.head? with
      | none => rw [he] at h; cases h
      | some e =>
        rw [he] at h
        dsimp only at h
        obtain ⟨n, hn⟩ := index_bind (X := fun _ => _) (fun _ => Def.refl _)
          (fun env hn => def_runBlocksO (runFuncN_mono m c hn) c f env none e.id) (fun r h => ⟨0, h⟩)
          (fun env w' r h => hG f env none e.id I w' r h) h
        refine ⟨n + 1, ?_⟩
        simp only [runFuncN, runFuncO, hf, he]
        exact hn
  case s3 =>
    intro H G hH hG f env prev id I w r h
    simp only [Guard.at, Guard.none, List.lookup, Option.bind_none, Option.getD_none] at h
    cases hb : f.block? id with
    | none => simp only [hb] at h; cases h
    | some b =>
      simp only [hb] at h
      have hK : ∀ {n n' : Nat} (env₂ : Env), n ≤ n' →
          Def (termK (runBlocksO (runFuncN m c n) c f) id env₂ b.term)
            (termK (runBlocksO (runFuncN m c n') c f) id env₂ b.term) := by
        intro n n' env₂ hn
        rw [termK_eq, termK_eq]
        exact Def.bind (Def.refl _) fun x => by
          cases x with
          | goto env d => exact def_runBlocksO (runFuncN_mono m c hn) c f env (some id) d
          | done v => exact Def.refl _
      obtain ⟨n, hn⟩ := index_bind (X := fun _ => enter env prev b) (fun _ => Def.refl _)
        (K := fun n env₁ => runBodyO (runFuncN m c n) c env₁ b.body >>= fun env₂ =>
          termK (runBlocksO (runFuncN m c n) c f) id env₂ b.term)
        (fun env₁ hn => Def.bind (def_runBodyO (runFuncN_mono m c hn) c env₁ _) fun env₂ => hK env₂ hn)
        (fun r h => ⟨0, h⟩) (fun env₁ w₁ r₁ h₁ => index_bind
          (X := fun n => runBodyO (runFuncN m c n) c env₁ b.body)
          (fun hn => def_runBodyO (runFuncN_mono m c hn) c env₁ _) (fun env₂ hn => hK env₂ hn)
          (fun r h => hH env₁ b.body I w₁ r h)
          (fun env₂ w₂ r₂ h₂ => index_termK (hG f) id env₂ b.term I w₂ r₂ h₂) h₁) h
      refine ⟨n, ?_⟩
      rw [runBlocksO]
      simp only [stepBlock, hb, bind_assoc]
      simp only [termK_eq] at hn
      exact hn

end Fe.Sonatina.Stage3.Place
