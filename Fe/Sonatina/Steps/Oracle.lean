import Fe.Sonatina.Steps.Prim
import Fe.Partial

/-!
# Runs with an oracle for calls, and composition

`runBlocksO o c f` runs function `f` block by block, each call by the oracle `o`: the iteration
of `stepBlock`, which runs one block's phis, statements and terminator.  The machine IR's own
run is that iteration with the module's semantics as the oracle (`runBlocks_iter`,
`runBlocksO_approx`).

C1 (`modRefines_of_funcs`): if every function of `M'` run with calls by `⟦M⟧` approximates the
same function of `M` with calls by `⟦M⟧`, then `⟦M'⟧ ⊑ ⟦M⟧`.  So each per-function lemma fixes
one oracle, the semantics of the input module.  The proof is fixpoint induction over the mutual
runner of `M'`.

`Sim` is the simulation schema every step kind uses: a relation on block states preserved by
one output block against any number of input blocks.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Lean.Order

/-! ## Oracles -/

/-- How calls run: a function's name and arguments to its results. -/
abbrev Oracle := String → List Val → FeM (List Val)

/-- The oracle approximates itself from related worlds. -/
def Oracle.Mono (o : Oracle) : Prop := ∀ name args, Approx Eq (o name args) (o name args)

/-- `o'` approximates `o`. -/
def Oracle.Le (o' o : Oracle) : Prop := ∀ name args, Approx Eq (o' name args) (o name args)

/-- Run a statement's instruction, a call by the oracle. -/
def runStmtO (o : Oracle) (c : Ctx) (env : Env) (s : Stmt) : FeM (List Val) :=
  match s.inst with
  | .call callee args => args.mapM (evalOperand env) >>= o callee
  | inst => runInst c env inst

/-- Run statements, each call by the oracle. -/
def runBodyO (o : Oracle) (c : Ctx) (env : Env) : List Stmt → FeM Env
  | [] => pure env
  | s :: rest =>
    runStmtO o c env s >>= fun vals => bind env s.dsts vals >>= fun env' => runBodyO o c env' rest

/-- The machine IR's statements run with calls by the module's semantics. -/
theorem runBody_eq_runBodyO (m : Module) (c : Ctx) :
    ∀ (env : Env) (stmts : List Stmt), runBody m c env stmts = runBodyO (runFunc m c) c env stmts
  | env, [] => by rw [runBody_nil_eq]; rfl
  | env, s :: rest => by
    rw [runBody_cons_eq]
    simp only [runBodyO, ← runBody_eq_runBodyO m c _ rest]
    rcases s with ⟨dsts, inst⟩
    cases inst <;> simp only [runStmtO, bind_assoc]

/-- Where a block goes: to `dest` with the environment, or out of the function with values. -/
inductive Next where
  | goto (env : Env) (dest : Nat)
  | done (vals : List Val)

/-- Run a terminator. -/
def runTerm (env : Env) : Term → FeM Next
  | .jump dest => pure (.goto env dest)
  | .br cond nz z => do
    let (_, v) ← evalInt env cond
    pure (.goto env (if v != 0 then nz else z))
  | .brTable s default cases => do
    let (_, v) ← evalInt env s
    let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
    match (vals.find? (·.1 == v)).map (·.2) <|> default with
    | some dest => pure (.goto env dest)
    | none => stuck
  | .ret values => do return .done (← values.mapM (evalOperand env))
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
  | .unreachable => stuck

/-- One block: enter block `id` of `f` from `prev`, run its statements with calls by `o`, and
    its terminator. -/
def stepBlock (o : Oracle) (c : Ctx) (f : Func) (env : Env) (prev : Option Nat) (id : Nat) :
    FeM Next :=
  match f.block? id with
  | some b => enter env prev b >>= fun env => runBodyO o c env b.body >>= fun env => runTerm env b.term
  | none => stuck

/-- Run `f` from block `id`, entered from `prev`, calls by `o`: the iteration of `stepBlock`. -/
def runBlocksO (o : Oracle) (c : Ctx) (f : Func) (env : Env) (prev : Option Nat) (id : Nat) :
    FeM (List Val) :=
  stepBlock o c f env prev id >>= fun
    | .goto env dest => runBlocksO o c f env (some id) dest
    | .done vals => pure vals
partial_fixpoint

/-- Run a function on its arguments from its entry block, calls by `o`. -/
def runFuncO (o : Oracle) (c : Ctx) (f : Option Func) (args : List Val) : FeM (List Val) := do
  let some f := f | stuck
  let some entry := f.blocks.head? | stuck
  let env ← bind {} f.params args
  runBlocksO o c f env none entry.id

/-- Statements run with calls by an oracle that approximates another approximate them run with
    calls by it. -/
theorem Approx.runBodyO {o' o : Oracle} (ho : o'.Le o) (c : Ctx) :
    ∀ (env : Env) (stmts : List Stmt), (∀ s ∈ stmts, s.inst.machine = true) →
      Approx Eq (Steps.runBodyO o' c env stmts) (Steps.runBodyO o c env stmts)
  | env, [], _ => Approx.pure_eq _
  | env, s :: rest, hm => by
    unfold Steps.runBodyO
    have h := EnvSub.refl env
    have hs := hm s (List.mem_cons_self ..)
    refine Approx.bind (R := Eq) ?_ fun vals _ e => e ▸ Approx.bind_eq (Approx.bindVals _ _ _)
      fun env' => Approx.runBodyO ho c env' rest fun s hs => hm s (List.mem_cons_of_mem _ hs)
    unfold runStmtO
    split
    · exact Approx.bind (R := Eq) (Approx.mapM' (Approx.evalOperand h) _) fun _ _ e => e ▸ ho _ _
    · exact Approx.runInst h c _ hs

theorem Approx.runTerm (env : Env) (t : Term) :
    Approx Eq (Steps.runTerm env t) (Steps.runTerm env t) := by
  have h := EnvSub.refl env
  cases t <;> unfold Steps.runTerm <;> approx_auto

theorem Approx.stepBlock {o' o : Oracle} (ho : o'.Le o) (c : Ctx) {f : Func}
    (hf : f.machine = true) (env : Env) (prev : Option Nat) (id : Nat) :
    Approx Eq (Steps.stepBlock o' c f env prev id) (Steps.stepBlock o c f env prev id) := by
  unfold Steps.stepBlock
  cases hb : f.block? id with
  | none => exact Approx.stuck _
  | some b =>
    exact Approx.bind_eq (Approx.enter _ _ _) fun env₁ =>
      Approx.bind (R := Eq) (Approx.runBodyO ho c env₁ b.body (Func.machine_block hf hb))
        fun env₂ _ e => e ▸ Approx.runTerm _ _

/-- The machine IR's run of a block is one `stepBlock` with the module's semantics as the oracle,
    and the run of the block it goes to: `runBlocksG` is the iteration of `stepBlock`. -/
theorem runBlocks_iter (m : Module) (c : Ctx) (f : Func) (env : Env) (prev : Option Nat)
    (id : Nat) : runBlocks m c f env prev id =
      (stepBlock (runFunc m c) c f env prev id >>= fun
        | .goto env dest => runBlocks m c f env (some id) dest
        | .done vals => pure vals) := by
  rw [runBlocks_eq]
  simp only [stepBlock]
  rcases f.block? id with _ | ⟨bid, phis, body, term⟩
  · simp only [stuck, Fe.M.diverge]; rfl
  · simp only [bind_assoc]
    congr 1; funext env₁
    rw [runBody_eq_runBodyO]
    congr 1; funext env₂
    cases term <;> simp only [runTerm, bind_assoc, pure_bind]
    all_goals first
      | rfl
      | (congr 1; funext x; rcases x; simp only [pure_bind]; done)
      | (simp only [bind_pure]; done)
      | (congr 1; funext x; congr 1; funext vals
         split <;> rename_i h <;> simp only [h, pure_bind] <;> rfl)

/-- A function run from its entry block by a block runner. -/
def runFuncT (TB : Func → Env → Option Nat → Nat → FeM (List Val)) (f : Option Func)
    (args : List Val) : FeM (List Val) := do
  let some f := f | stuck
  let some entry := f.blocks.head? | stuck
  let env ← bind {} f.params args
  TB f env none entry.id

theorem runFuncO_eq (o : Oracle) (c : Ctx) : runFuncO o c = runFuncT (runBlocksO o c) := rfl

theorem runFunc_eq_runFuncT (m : Module) (c : Ctx) (name : String) (args : List Val) :
    runFunc m c name args = runFuncT (runBlocks m c) (m.func? name) args := by
  rw [runFunc_eq]; rfl

/-! ## Admissibility -/

/-- Approximating a fixed run, under a condition, is admissible: a diverging run approximates
    anything. -/
theorem admissible_approx {α : Type} (R : α → α → Prop) (t : FeM α) (cond : Prop) :
    admissible (fun x : FeM α => cond → Approx R x t) := by
  have h := Fe.M.admissible_outcome (α := α)
    (fun I w' r => cond → ∀ w, WRel w' w → ResRel R r (t.exec I w)) (fun _ _ _ _ _ => trivial)
  have e : (fun x : FeM α => cond → Approx R x t) =
      fun x => ∀ I w', (fun I w' r => cond → ∀ w, WRel w' w → ResRel R r (t.exec I w)) I w'
        (x.exec I w') := by
    funext x
    apply propext
    exact ⟨fun hx I w' hc w hw => hx hc I w' w hw, fun hx hc I w' w hw => hx I w' hc w hw⟩
  rw [e]; exact h

/-- Approximating each of a family of runs, under conditions, is admissible. -/
theorem admissible_approx_forall {α A : Type} (R : α → α → Prop) (t : A → FeM α)
    (cond : A → Prop) : admissible (fun x : FeM α => ∀ a, cond a → Approx R x (t a)) := by
  have h := Fe.M.admissible_outcome (α := α)
    (fun I w' r => ∀ a, cond a → ∀ w, WRel w' w → ResRel R r ((t a).exec I w))
    (fun _ _ _ _ _ _ => trivial)
  have e : (fun x : FeM α => ∀ a, cond a → Approx R x (t a)) =
      fun x => ∀ I w', (fun I w' r => ∀ a, cond a → ∀ w, WRel w' w → ResRel R r ((t a).exec I w))
        I w' (x.exec I w') := by
    funext x
    apply propext
    exact ⟨fun hx I w' a hc w hw => hx a hc I w' w hw, fun hx a hc I w' w hw => hx I w' a hc w hw⟩
  rw [e]; exact h

theorem admissible_approx' {α : Type} (R : α → α → Prop) (t : FeM α) :
    admissible (fun x : FeM α => Approx R x t) := by
  have h := admissible_approx R t True
  have e : (fun x : FeM α => Approx R x t) = fun x => True → Approx R x t := by
    funext x; exact propext ⟨fun h _ => h, fun h => h trivial⟩
  rw [e]; exact h

/-! ## The machine IR's runs as iterations

`runFunc_approx`: the run of a module approximates an oracle when the iteration of
`stepBlock` from each function's entry does, for any block runner `TB` that is that
iteration.  Its instances are reflexivity (`runFunc_mono`), the run of a function with the
module as its oracle (`runFuncO_approx`), and C1 (`modRefines_of_funcs`). -/

/-- The statements' terminator, as `runBlocksG` runs it, approximates `runTerm` and the
    continuation, given block runners that do. -/
theorem approx_termCont {G TB : Env → Option Nat → Nat → FeM (List Val)}
    (hG : ∀ env prev id, Approx Eq (G env prev id) (TB env prev id)) (id : Nat) (env : Env) :
    ∀ t : Term, Approx Eq (match t with
      | .jump dest => G env (some id) dest
      | .br cond nz z => do
        let (_, v) ← evalInt env cond
        G env (some id) (if v != 0 then nz else z)
      | .brTable s default cases => do
        let (_, v) ← evalInt env s
        let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
        match (vals.find? (·.1 == v)).map (·.2) <|> default with
        | some dest => G env (some id) dest
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
      | .unreachable => stuck)
    (runTerm env t >>= fun
      | .goto env dest => TB env (some id) dest
      | .done vals => pure vals) := by
  have hr := EnvSub.refl env
  intro t
  cases t with
  | jump d => simp only [runTerm, pure_bind]; exact hG _ _ _
  | br cnd nz z =>
    simp only [runTerm, bind_assoc]
    exact Approx.bind (Approx.evalInt hr cnd) fun ⟨_, v⟩ _ e => e ▸ by
      simp only [pure_bind]; exact hG _ _ _
  | brTable s d cases =>
    simp only [runTerm, bind_assoc]
    refine Approx.bind (Approx.evalInt hr s) fun ⟨_, v⟩ _ e => e ▸ ?_
    refine Approx.bind (Approx.mapM (fun _ => ?_) _) fun vals _ e => e ▸ ?_
    · exact Approx.bind_eq (Approx.evalInt hr _) fun _ => Approx.pure_eq _
    · split
      · simp only [pure_bind]; exact hG _ _ _
      · simp only [stuck, Fe.M.diverge]; exact Approx.diverge _
  | ret vals =>
    simp only [runTerm, bind_assoc, pure_bind]
    conv => lhs; rw [← bind_pure (List.mapM _ _)]
    exact Approx.bind (Approx.mapM (Approx.evalOperand hr) _) fun _ _ e => e ▸ Approx.pure_eq _
  | evmReturn a l =>
    simp only [runTerm, bind_assoc]
    exact Approx.bind_eq (Approx.evalWord hr a) fun _ => Approx.bind_eq (Approx.evalWord hr l)
      fun _ => Approx.bind (approx_returnData _ _) fun e _ _ => nomatch e
  | evmRevert a l =>
    simp only [runTerm, bind_assoc]
    exact Approx.bind_eq (Approx.evalWord hr a) fun _ => Approx.bind_eq (Approx.evalWord hr l)
      fun _ => Approx.bind (approx_revertData _ _) fun e _ _ => nomatch e
  | evmStop =>
    simp only [runTerm, bind_assoc]
    exact Approx.bind approx_stopCall fun e _ _ => nomatch e
  | evmInvalid =>
    simp only [runTerm, bind_assoc]
    exact Approx.bind approx_trap fun e _ _ => nomatch e
  | unreachable => simp only [runTerm, stuck, Fe.M.diverge]; exact Approx.diverge _

/-- The run of a module approximates an oracle if the iteration `TB` of `stepBlock` with calls
    by the oracle does, function by function.  By fixpoint induction over the module's mutual
    runner; the oracle is fixed throughout. -/
theorem runFunc_approx {N : Module} (hN : N.machine = true) {c : Ctx} {o : Oracle}
    {TB : Func → Env → Option Nat → Nat → FeM (List Val)}
    (hTB : ∀ f env prev id, TB f env prev id = (stepBlock o c f env prev id >>= fun
      | .goto env d => TB f env (some id) d | .done v => pure v))
    (hF : ∀ name args x, Approx Eq x (runFuncT TB (N.func? name) args) →
      Approx Eq x (o name args)) :
    ∀ name args, Approx Eq (runFunc N c name args) (o name args) := by
  intro name args
  rw [← runFuncG_none]
  refine runFuncG.fixpoint_induct Guard.none N c
    (fun H => ∀ env stmts, (∀ s ∈ stmts, s.inst.machine = true) →
      Approx Eq (H [] [] env stmts) (runBodyO o c env stmts))
    (fun F => ∀ name args, Approx Eq (F [] name args) (o name args))
    (fun G => ∀ f env prev id, f.machine = true →
      Approx Eq (G [] f env prev id) (TB f env prev id))
    ?a1 ?a2 ?a3 ?s1 ?s2 ?s3 name args
  case a1 =>
    exact admissible_apply (β := fun _ => List (List Nat) → Env → List Stmt → FeM Env)
      (fun _ H => ∀ env stmts, (∀ s ∈ stmts, s.inst.machine = true) →
        Approx Eq (H [] env stmts) (runBodyO o c env stmts)) []
      (admissible_apply (β := fun _ => Env → List Stmt → FeM Env)
        (fun _ H => ∀ env stmts, (∀ s ∈ stmts, s.inst.machine = true) →
          Approx Eq (H env stmts) (runBodyO o c env stmts)) []
        (Fe.M.admissible_arrow (fun env (H : List Stmt → FeM Env) => ∀ stmts,
            (∀ s ∈ stmts, s.inst.machine = true) → Approx Eq (H stmts) (runBodyO o c env stmts))
          fun env => Fe.M.admissible_arrow (fun stmts (x : FeM Env) =>
            (∀ s ∈ stmts, s.inst.machine = true) → Approx Eq x (runBodyO o c env stmts))
          fun stmts => admissible_approx _ _ _))
  case a2 =>
    exact admissible_apply (β := fun _ => String → List Val → FeM (List Val))
      (fun _ F => ∀ name args, Approx Eq (F name args) (o name args)) []
      (Fe.M.admissible_arrow (fun name (F : List Val → FeM (List Val)) => ∀ args,
          Approx Eq (F args) (o name args))
        fun name => Fe.M.admissible_arrow (fun args (x : FeM (List Val)) =>
          Approx Eq x (o name args)) fun args => admissible_approx' _ _)
  case a3 =>
    exact admissible_apply (β := fun _ => Func → Env → Option Nat → Nat → FeM (List Val))
      (fun _ G => ∀ f env prev id, f.machine = true →
        Approx Eq (G f env prev id) (TB f env prev id)) []
      (Fe.M.admissible_arrow (fun f (G : Env → Option Nat → Nat → FeM (List Val)) =>
          ∀ env prev id, f.machine = true → Approx Eq (G env prev id) (TB f env prev id))
        fun f => Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
          ∀ prev id, f.machine = true → Approx Eq (G prev id) (TB f env prev id))
        fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
          ∀ id, f.machine = true → Approx Eq (G id) (TB f env prev id))
        fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
          f.machine = true → Approx Eq x (TB f env prev id))
        fun id => admissible_approx _ _ _)
  case s1 =>
    intro H F hH hF env stmts hm
    cases stmts with
    | nil => exact Approx.pure_eq _
    | cons s rest =>
      simp only [List.nil_append, List.headD_nil, List.tail_nil, guarded, runBodyO, runStmtO]
      refine Approx.bind (R := Eq) ?_ fun vals _ e => e ▸ Approx.bind_eq (Approx.bindVals _ _ _)
        fun env' => hH env' rest fun s hs => hm s (List.mem_cons_of_mem _ hs)
      have hs := hm s (List.mem_cons_self ..)
      rcases s with ⟨dsts, inst⟩
      cases inst
      case call callee args =>
        exact Approx.bind (Approx.mapM (Approx.evalOperand (EnvSub.refl env)) _)
          fun _ _ e => e ▸ hF _ _
      all_goals exact Approx.runInst (EnvSub.refl env) c _ hs
  case s2 =>
    intro G hG name args
    simp only [guarded]
    apply hF name args
    unfold runFuncT
    cases hf : N.func? name with
    | none => exact Approx.stuck _
    | some f =>
      dsimp only
      cases f.blocks.head? with
      | none => exact Approx.stuck _
      | some entry =>
        exact Approx.bind_eq (Approx.bindVals _ _ _) fun env =>
          hG f env none entry.id (Module.machine_func hN hf)
  case s3 =>
    intro H G hH hG f env prev id hf
    dsimp only
    rw [hTB]
    unfold stepBlock
    cases hb : f.block? id with
    | none => exact Approx.stuck _
    | some b =>
      dsimp only
      simp only [bind_assoc, Guard.at, Guard.none, List.lookup, Option.bind_none,
        Option.getD_none]
      exact Approx.bind_eq (Approx.enter _ _ _) fun env₁ =>
        Approx.bind (hH env₁ b.body (Func.machine_block hf hb)) fun env₂ _ e => e ▸
          approx_termCont (fun env prev id => hG f env prev id hf) id env₂ b.term

/-- Reflexivity: the run of a machine module approximates itself from related worlds. -/
theorem runFunc_mono {M : Module} (hM : M.machine = true) (c : Ctx) :
    Oracle.Le (runFunc M c) (runFunc M c) :=
  runFunc_approx hM (TB := runBlocks M c) (fun f env prev id => runBlocks_iter M c f env prev id)
    fun name args x hx => by rwa [runFunc_eq_runFuncT]

/-- A function of a machine module, run with calls by the module's semantics, approximates its
    run in the module. -/
theorem runFuncO_approx {M : Module} (hM : M.machine = true) (c : Ctx) (name : String)
    (args : List Val) :
    Approx Eq (runFuncO (runFunc M c) c (M.func? name) args) (runFunc M c name args) := by
  have blocks : ∀ f, f.machine = true → ∀ env prev id,
      Approx Eq (runBlocksO (runFunc M c) c f env prev id) (runBlocks M c f env prev id) := by
    intro f hf
    refine runBlocksO.fixpoint_induct (runFunc M c) c f
      (fun G => ∀ env prev id, Approx Eq (G env prev id) (runBlocks M c f env prev id)) ?_ ?_
    · exact Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
          ∀ prev id, Approx Eq (G prev id) (runBlocks M c f env prev id))
        fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
          ∀ id, Approx Eq (G id) (runBlocks M c f env prev id))
        fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
          Approx Eq x (runBlocks M c f env prev id)) fun id => admissible_approx' _ _
    · intro G hG env prev id
      rw [runBlocks_iter]
      exact Approx.bind (Approx.stepBlock (runFunc_mono hM c) c hf env prev id) fun n _ e => by
        subst e
        cases n with
        | goto env' d => exact hG _ _ _
        | done v => exact Approx.pure_eq _
  rw [runFunc_eq_runFuncT, runFuncO_eq]
  unfold runFuncT
  cases hf : M.func? name with
  | none => exact Approx.stuck _
  | some f =>
    dsimp only
    cases f.blocks.head? with
    | none => exact Approx.stuck _
    | some entry =>
      exact Approx.bind_eq (Approx.bindVals _ _ _) fun env =>
        blocks f (Module.machine_func hM hf) env none entry.id

/-! ## Module refinement and composition -/

/-- `M'` refines `M`: under any context, each function of `M'` approximates the same function
    of `M` from related worlds. -/
def ModRefines (M' M : Module) : Prop :=
  ∀ c name args, Approx Eq (runFunc M' c name args) (runFunc M c name args)

theorem ModRefines.trans {M'' M' M : Module} (h₁ : ModRefines M'' M') (h₂ : ModRefines M' M) :
    ModRefines M'' M := fun c name args => (h₁ c name args).trans_eq (h₂ c name args)

theorem ModRefines.refl {M : Module} (hM : M.machine = true) : ModRefines M M :=
  fun c => runFunc_mono hM c

/-- `f'` approximates `f` when both run with calls by `o`. -/
def FuncRef (o : Oracle) (c : Ctx) (f' f : Option Func) : Prop :=
  ∀ args, Approx Eq (runFuncO o c f' args) (runFuncO o c f args)

theorem FuncRef.trans {o : Oracle} {c : Ctx} {f'' f' f : Option Func} (h₁ : FuncRef o c f'' f')
    (h₂ : FuncRef o c f' f) : FuncRef o c f'' f := fun args => (h₁ args).trans_eq (h₂ args)

/-- C1, compositionality: if every function of `M'`, its calls run by the semantics of `M`,
    approximates the same function of `M` with its calls run so, then `M'` refines `M`.  Every
    per-function lemma therefore fixes one oracle, the semantics of the input module. -/
theorem modRefines_of_funcs {M' M : Module} (hM : M.machine = true) (hM' : M'.machine = true)
    (h : ∀ c name, FuncRef (runFunc M c) c (M'.func? name) (M.func? name)) : ModRefines M' M :=
  fun c => runFunc_approx hM' (TB := runBlocksO (runFunc M c) c)
    (fun f env prev id => by rw [runBlocksO])
    fun name args x hx => (hx.trans_eq (h c name args)).trans_eq (runFuncO_approx hM c name args)

end Fe.Sonatina.Steps
