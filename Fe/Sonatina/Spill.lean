import Fe.Sonatina.Check
import Fe.Sonatina.Plan
import Fe.Sonatina.Interp
import Fe.Sonatina.Refine
import Mathlib.Logic.Relation

/-!
# Memory spills: the machine IR with its spills

Sonatina keeps some values in memory as well as on the stack: it stores such a value at its
word after defining it and reloads it from there later (`FuncHint.spills`, `memory`
locations).  The machine IR says nothing of it.  This file defines the machine IR's run with
its spills, under a spill plan, which is data:

- a `SpillPlan` gives, per function, each spilled value, its word, and the points where the
  bytes may reload it, in the function as `Func.instrument` makes it;
- `Func.instrument` adds the stores the bytes make, as `evm_mstore` statements: after a
  statement defining a spilled value, of each spilled parameter at entry, and at the end of a
  block that jumps to a block with spilled phis, of each such phi (its operand from the block,
  unless it is the phi itself, which its word holds already);
- `Func.reloadLive` finds the spilled values reload-live at each point: a reload of the value
  is reachable from there before the value is defined or stored again.  `Func.liveClosed`
  tests that sets satisfy the equations of that liveness, and `Func.live_mono` is what it
  gives along a path;
- a statement must leave as they were the words of the values reload-live after it that it
  neither defines nor stores (`SpillPlan.guard`), and those its callers protect; the runner
  (`runFuncG`, `Interp.lean`) checks it after each statement and each call, and panics with
  `spillClobbered` where a statement changed one.

`Sidecar.spilledModel s plan` is the contract model this gives.  Under the empty plan it is the
machine IR's (`spilledModel_nil`).  The machine IR never panics (`machine_not_panic`), so a run
of the instrumented model that ends as a run of the machine IR does never panics with
`spillClobbered`.  A guarded run that returns has left the words it protects as they were
(`protected_kept`).  The plan's source does not matter to any of this: a wrong plan makes the
instrumented model differ from the machine IR's, never agree where it should not.
-/

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-! ## Reload-liveness along a path -/

/-- A step of `f` that keeps `v` reload-live backwards: past a statement that does not kill
    `v`, or from a block's terminator to the entry of a successor of which `v` is no phi that
    takes a new value on the edge. -/
inductive Func.LiveStep (f : Func) (p : FuncPlan) (v : Nat) : Nat × Nat → Nat × Nat → Prop
  | stmt {b : Block} {k : Nat} {s : Stmt} : b ∈ f.blocks → b.body[k]? = some s →
      v ∉ s.kills p.words → LiveStep f p v (b.id, k) (b.id, k + 1)
  | edge {b : Block} {S : Nat} {sb : Block} : b ∈ f.blocks → S ∈ b.term.succs →
      f.block? S = some sb → (∀ phi ∈ sb.phis, phi.dst = v → phi.movedFrom b.id = false) →
      LiveStep f p v (b.id, b.body.length) (S, 0)

theorem Func.live_reload {f : Func} {p : FuncPlan} {L : Live} (h : f.liveClosed p L = true)
    {b : Block} (hb : b ∈ f.blocks) {k v : Nat} (hk : k ≤ b.body.length)
    (hv : v ∈ p.reloadsAt b.id k) : v ∈ L.at b.id k := by
  have hb' := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb'
  simpa using hb'.1.1 k (by omega) v hv

theorem Func.live_stmt {f : Func} {p : FuncPlan} {L : Live} (h : f.liveClosed p L = true)
    {b : Block} (hb : b ∈ f.blocks) {k v : Nat} {s : Stmt} (hs : b.body[k]? = some s)
    (hv : v ∈ L.at b.id (k + 1)) (hk : v ∉ s.kills p.words) : v ∈ L.at b.id k := by
  have hb' := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true, List.all_eq_true] at hb'
  have hmem : (s, k) ∈ b.body.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using hs
  have := hb'.1.2 (s, k) hmem v hv
  simp only [Bool.or_eq_true, List.contains_iff_mem] at this
  exact this.resolve_left hk

theorem Func.live_edge {f : Func} {p : FuncPlan} {L : Live} (h : f.liveClosed p L = true)
    {b : Block} (hb : b ∈ f.blocks) {S v : Nat} {sb : Block} (hS : S ∈ b.term.succs)
    (hsb : f.block? S = some sb) (hv : v ∈ L.at S 0)
    (hphi : ∀ phi ∈ sb.phis, phi.dst = v → phi.movedFrom b.id = false) :
    v ∈ L.at b.id b.body.length := by
  have hb' := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true, List.all_eq_true] at hb'
  have := hb'.2 S hS
  rw [hsb] at this
  have := List.all_eq_true.mp this v (by simpa using hv)
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at this
  exact this.resolve_left fun ⟨phi, hp, he, hm⟩ => by rw [hphi phi hp he] at hm; cases hm

/-- Reload-liveness along a path: a value live at the end of steps that keep it live is live
    at their start, given sets that satisfy the equations. -/
theorem Func.live_mono {f : Func} {p : FuncPlan} {L : Live} (h : f.liveClosed p L = true)
    {v : Nat} {q q' : Nat × Nat} (hq : Relation.ReflTransGen (f.LiveStep p v) q q')
    (hv : v ∈ L.at q'.1 q'.2) : v ∈ L.at q.1 q.2 := by
  induction hq with
  | refl => exact hv
  | tail _ hstep ih =>
    apply ih
    cases hstep with
    | stmt hb hs hk => exact Func.live_stmt h hb hs hv hk
    | edge hb hS hsb hphi => exact Func.live_edge h hb hS hsb hv hphi

/-! ## The instrumented model -/

/-- The machine IR with its spills, under the spill plan of each section: the model whose
    runs store the spilled values the plan names at their words and panic with
    `spillClobbered` where a statement changes a word the plan protects. -/
def Sidecar.spilledModel (s : Sidecar) (plan : String → SpillPlan) : ContractModel where
  init _ := s.runSectionWith "init" .machine (plan "init").prepare
  runtime := s.runSectionWith "runtime" .machine (plan "runtime").prepare

theorem SpillPlan.prepare_nil : SpillPlan.prepare [] = fun m => (m, .none) := by
  funext m
  rfl

/-- Under the empty plan the instrumented model is the machine IR's. -/
theorem spilledModel_nil (s : Sidecar) : s.spilledModel (fun _ => []) = s.model .machine := by
  simp only [Sidecar.spilledModel, SpillPlan.prepare_nil, Sidecar.model, Sidecar.runSection]

/-! ## The machine IR never panics -/

/-- The computation never ends in a panic. -/
def NoPanic {α : Type} (x : FeM α) : Prop :=
  ∀ I w code, x.exec I w ≠ some (.error (.panic code))

namespace NoPanic

variable {α β : Type}

theorem pure (a : α) : NoPanic (Pure.pure a : FeM α) := by intro I w c h; simp at h

theorem get : NoPanic (MonadState.get : FeM World) := by intro I w c h; simp at h

theorem read : NoPanic (read : FeM ExecutionEnv) := by intro I w c h; simp at h

theorem set (w' : World) : NoPanic (set w' : FeM PUnit) := by intro I w c h; simp at h

theorem modify (f : World → World) : NoPanic (modify f : FeM PUnit) := by
  intro I w c h; simp at h

theorem fail {f : Exit World} (hf : ∀ c, f ≠ .panic c) : NoPanic (Fe.M.fail f : FeM α) := by
  intro I w c h; simp only [Fe.M.exec_fail, Option.some.injEq, Except.error.injEq] at h
  exact hf c h

theorem diverge : NoPanic (Fe.M.diverge : FeM α) := by intro I w c h; simp at h

theorem bind {x : FeM α} {k : α → FeM β} (hx : NoPanic x) (hk : ∀ a, NoPanic (k a)) :
    NoPanic (x >>= k) := by
  intro I w c h
  rw [Fe.M.exec_bind] at h
  cases hr : x.exec I w with
  | none => rw [hr] at h; cases h
  | some r =>
    cases r with
    | error f =>
      rw [hr] at h
      simp only [Option.some.injEq, Except.error.injEq] at h
      exact hx I w c (h ▸ hr)
    | ok p => rw [hr] at h; exact hk p.1 I p.2 c h

/-- The instance is implicit, so that applying the lemma unifies with the instance a
    conditional carries. -/
theorem ite {c : Prop} {inst : Decidable c} {x y : FeM α} (hx : NoPanic x) (hy : NoPanic y) :
    NoPanic (@_root_.ite _ c inst x y) := by
  split <;> assumption

theorem dite {c : Prop} {inst : Decidable c} {x : c → FeM α} {y : ¬ c → FeM α}
    (hx : ∀ h, NoPanic (x h)) (hy : ∀ h, NoPanic (y h)) :
    NoPanic (@_root_.dite _ c inst x y) := by
  split
  · exact hx _
  · exact hy _

theorem mapM {γ : Type} {f : γ → FeM α} (hf : ∀ a, NoPanic (f a)) :
    ∀ xs : List γ, NoPanic (xs.mapM f)
  | [] => by simpa using NoPanic.pure []
  | a :: xs => by
    rw [List.mapM_cons]
    exact bind (hf a) fun b => bind (mapM hf xs) fun bs => NoPanic.pure _

theorem admissible : Lean.Order.admissible (fun x : FeM α => NoPanic x) :=
  Lean.Order.admissible_pi_apply (β := fun _ => StateT World (ExceptT (Exit World) Option) α)
    (fun _ y => ∀ w code, y w ≠ some (.error (.panic code))) fun _ =>
  Lean.Order.admissible_pi_apply (β := fun _ => ExceptT (Exit World) Option (α × World))
    (fun _ y => ∀ code, y ≠ some (.error (.panic code))) fun _ =>
  Lean.Order.admissible_pi _ fun _ => Lean.Order.admissible_flatOrder _ (fun h => by cases h)

theorem admissible_fun {γ : Type} :
    Lean.Order.admissible (fun F : γ → FeM α => ∀ x, NoPanic (F x)) :=
  Lean.Order.admissible_pi_apply (β := fun _ => FeM α) (fun _ x => NoPanic x) fun _ => admissible

end NoPanic

/-- Prove `NoPanic` of a computation built from binds, conditionals, matches and the core
    operations, its definitions unfolded first. -/
macro "no_panic" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact NoPanic.pure _
    | with_reducible exact NoPanic.get
    | with_reducible exact NoPanic.read
    | with_reducible exact NoPanic.set _
    | with_reducible exact NoPanic.modify _
    | with_reducible exact NoPanic.diverge
    | with_reducible exact NoPanic.fail (by simp)
    | with_reducible assumption
    | with_reducible refine NoPanic.bind ?_ fun _ => ?_
    | with_reducible refine NoPanic.ite ?_ ?_
    | with_reducible refine NoPanic.dite (fun _ => ?_) (fun _ => ?_)
    | with_reducible refine NoPanic.mapM (fun _ => ?_) _
    | contradiction
    | split)

/-! The model library's operations the interpreter runs never panic. -/

theorem noPanic_next : NoPanic Fe.EVM.next := by unfold Fe.EVM.next; no_panic

theorem noPanic_emit (t : Array UInt256) (d : ByteArray) : NoPanic (Fe.EVM.emit t d) := by
  unfold Fe.EVM.emit; no_panic

theorem noPanic_message (g : UInt256) (s r t : AccountAddress) (v v' ap al rp rl : UInt256)
    (perm : Bool) : NoPanic (Fe.EVM.message g s r t v v' ap al rp rl perm) := by
  unfold Fe.EVM.message; no_panic; exact noPanic_next

theorem noPanic_createWith (salt : Option ByteArray) (v p l : UInt256) :
    NoPanic (Fe.EVM.createWith salt v p l) := by
  unfold Fe.EVM.createWith; no_panic; exact noPanic_next


theorem noPanic_evmRun (op : EvmOp) (args : List UInt256) : NoPanic (op.run args) := by
  unfold EvmOp.run
  split <;> simp only [Fe.EVM.selfAddress, Fe.EVM.balance, Fe.EVM.origin, Fe.EVM.caller,
    Fe.EVM.callvalue, Fe.EVM.calldataload, Fe.EVM.calldatasize, Fe.EVM.calldatacopy,
    Fe.EVM.codesize, Fe.EVM.codecopy, Fe.EVM.gasprice, Fe.EVM.extcodesize, Fe.EVM.extcodehash,
    Fe.EVM.extcodecopy, Fe.EVM.returndatasize, Fe.EVM.returndatacopy, Fe.EVM.blockhash,
    Fe.EVM.coinbase, Fe.EVM.timestamp, Fe.EVM.blockNumber, Fe.EVM.prevrandao,
    Fe.EVM.gaslimit, Fe.EVM.chainid, Fe.EVM.selfbalance, Fe.EVM.basefee, Fe.EVM.blobhash,
    Fe.EVM.blobbasefee, Fe.EVM.gas, Fe.EVM.cload, Fe.EVM.mload, Fe.EVM.mstore,
    Fe.EVM.sload, Fe.EVM.sstore, Fe.EVM.tload, Fe.EVM.tstore, Fe.EVM.keccak256, mcopyIR, Fe.EVM.mcopy,
    Fe.EVM.mstore8, Fe.EVM.logData, Fe.EVM.create, Fe.EVM.create2, Fe.EVM.call,
    Fe.EVM.staticcall, Fe.EVM.delegatecall, callcode, stuck] <;> no_panic
  all_goals first
    | with_reducible exact noPanic_next
    | with_reducible exact noPanic_emit _ _
    | with_reducible exact noPanic_message _ _ _ _ _ _ _ _ _ _ _
    | with_reducible exact noPanic_createWith _ _ _ _

theorem noPanic_evalOperand (env : Env) (o : Operand) : NoPanic (evalOperand env o) := by
  unfold evalOperand stuck; no_panic

theorem noPanic_evalInt (env : Env) (o : Operand) : NoPanic (evalInt env o) := by
  unfold evalInt stuck; no_panic; exact noPanic_evalOperand env o

theorem noPanic_evalWord (env : Env) (o : Operand) : NoPanic (evalWord env o) := by
  unfold evalWord; no_panic; exact noPanic_evalInt env o

theorem noPanic_bind (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    NoPanic (Fe.Sonatina.bind env dsts vals) := by
  unfold Fe.Sonatina.bind stuck; no_panic

theorem noPanic_enter (env : Env) (prev : Option Nat) (b : Block) :
    NoPanic (enter env prev b) := by
  unfold enter stuck; no_panic
  all_goals first
    | exact noPanic_evalOperand _ _
    | exact noPanic_bind _ _ _

theorem noPanic_returnData (a l : UInt256) : NoPanic (returnData a l) := by
  unfold returnData Fe.M.stop; no_panic

theorem noPanic_revertData (a l : UInt256) : NoPanic (revertData a l) := by
  unfold revertData Fe.M.revert; no_panic

theorem noPanic_stopCall : NoPanic stopCall := by unfold stopCall Fe.M.stop; no_panic

theorem noPanic_trap : NoPanic trap := by unfold trap; no_panic

theorem noPanic_selfdestruct (a : UInt256) : NoPanic (Fe.EVM.selfdestruct a) := by
  unfold Fe.EVM.selfdestruct Fe.M.stop; no_panic
  all_goals exact noPanic_next

theorem noPanic_runInst (c : Ctx) (env : Env) (inst : Inst) : NoPanic (runInst c env inst) := by
  unfold runInst
  split <;> (try simp only [evalPair, Fe.EVM.mload, Fe.EVM.mstore, Fe.EVM.zeroMem, allocate,
    stuck]) <;> no_panic
  all_goals first
    | with_reducible exact noPanic_evalInt _ _
    | with_reducible exact noPanic_evalWord _ _
    | with_reducible exact noPanic_evalOperand _ _
    | with_reducible exact noPanic_evmRun _ _
    | with_reducible exact noPanic_trap

/-- The guarded run that protects nothing never panics. -/
theorem runFuncG_none_noPanic (m : Module) (c : Ctx) (name : String) (args : List Val) :
    NoPanic (runFuncG .none m c [] name args) := by
  refine runFuncG.fixpoint_induct Guard.none m c
    (fun F => ∀ env stmts, NoPanic (F [] [] env stmts))
    (fun F => ∀ name args, NoPanic (F [] name args))
    (fun F => ∀ f env prev id, NoPanic (F [] f env prev id))
    (Lean.Order.admissible_apply (β := fun _ => List (List Nat) → Env → List Stmt → FeM Env)
      (fun _ G => ∀ env stmts, NoPanic (G [] env stmts)) []
      (Lean.Order.admissible_apply (β := fun _ => Env → List Stmt → FeM Env)
        (fun _ G => ∀ env stmts, NoPanic (G env stmts)) []
        (Lean.Order.admissible_pi_apply (β := fun _ => List Stmt → FeM Env)
          (fun _ G => ∀ stmts, NoPanic (G stmts)) fun _ => NoPanic.admissible_fun)))
    (Lean.Order.admissible_apply (β := fun _ => String → List Val → FeM (List Val))
      (fun _ G => ∀ name args, NoPanic (G name args)) []
      (Lean.Order.admissible_pi_apply (β := fun _ => List Val → FeM (List Val))
        (fun _ G => ∀ args, NoPanic (G args)) fun _ => NoPanic.admissible_fun))
    (Lean.Order.admissible_apply
      (β := fun _ => Func → Env → Option Nat → Nat → FeM (List Val))
      (fun _ G => ∀ f env prev id, NoPanic (G f env prev id)) []
      (Lean.Order.admissible_pi_apply (β := fun _ => Env → Option Nat → Nat → FeM (List Val))
        (fun _ G => ∀ env prev id, NoPanic (G env prev id)) fun _ =>
        Lean.Order.admissible_pi_apply (β := fun _ => Option Nat → Nat → FeM (List Val))
        (fun _ G => ∀ prev id, NoPanic (G prev id)) fun _ =>
        Lean.Order.admissible_pi_apply (β := fun _ => Nat → FeM (List Val))
        (fun _ G => ∀ id, NoPanic (G id)) fun _ => NoPanic.admissible_fun))
    ?_ ?_ ?_ name args
  · intro F G hF hG env stmts
    cases stmts with
    | nil => exact NoPanic.pure _
    | cons s rest =>
      simp only [List.nil_append, List.headD_nil, List.tail_nil, guarded]
      refine NoPanic.bind ?_ fun vals => NoPanic.bind (noPanic_bind _ _ _) fun env' => hF env' rest
      split
      · exact NoPanic.bind (NoPanic.mapM (noPanic_evalOperand env) _) fun _ => hG _ _
      · exact noPanic_runInst _ _ _
  · intro F hF name args
    simp only [guarded, stuck]
    no_panic
    all_goals first
      | exact noPanic_bind _ _ _
      | exact hF _ _ _ _
  · intro F G hF hG f env prev id
    simp only [Guard.none, stuck]
    no_panic
    all_goals first
      | exact noPanic_enter _ _ _
      | exact hF _ _
      | exact hG _ _ _ _
      | exact noPanic_evalInt _ _
      | exact noPanic_evalWord _ _
      | exact noPanic_evalOperand _ _
      | exact noPanic_returnData _ _
      | exact noPanic_revertData _ _
      | exact noPanic_stopCall
      | exact noPanic_trap
      | exact noPanic_selfdestruct _

/-- The run of a section never panics, at any level. -/
theorem runSection_noPanic (s : Sidecar) (name : String) (level : Level) :
    NoPanic (s.runSection name level) := by
  unfold Sidecar.runSection Sidecar.runSectionWith
  simp only [Fe.EVM.mstore, stuck]
  no_panic
  all_goals exact runFuncG_none_noPanic _ _ _ _

/-- The machine IR never panics: its runtime and its constructor never end in `.panic`, so
    neither with `spillClobbered`. -/
theorem machine_not_panic (s : Sidecar) :
    NoPanic (s.model .machine).runtime ∧ ∀ args, NoPanic ((s.model .machine).init args) :=
  ⟨runSection_noPanic s "runtime" .machine, fun _ => runSection_noPanic s "init" .machine⟩

/-! ## Protected words are kept -/

/-- A run of a function under a guard that returns has left the words it was given to protect
    as they were: the words of its callers' reload-live values, across the call. -/
theorem protected_kept {g : Guard} {m : Module} {c : Ctx} {inh : List Nat} {name : String}
    {args : List Val} {I : ExecutionEnv} {w w' : World} {vals : List Val}
    (h : (runFuncG g m c inh name args).exec I w = some (.ok (vals, w'))) :
    ∀ p ∈ inh, w'.memory.readWithPadding p 32 = w.memory.readWithPadding p 32 := by
  rw [runFuncG.eq_1] at h
  exact guarded_kept h

/-- A run of statements under a guard that returns has left the words it was given to protect
    as they were. -/
theorem runBodyG_kept {g : Guard} {m : Module} {c : Ctx} {inh : List Nat} {I : ExecutionEnv} :
    ∀ {ps : List (List Nat)} {env : Env} {stmts : List Stmt} {w w' : World} {env' : Env},
    (runBodyG g m c inh ps env stmts).exec I w = some (.ok (env', w')) →
    ∀ p ∈ inh, w'.memory.readWithPadding p 32 = w.memory.readWithPadding p 32
  | ps, env, [], w, w', env', h => by
    rw [runBodyG.eq_1] at h
    simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; intro _ _; rfl
  | ps, env, s :: rest, w, w', env', h => by
    rw [runBodyG.eq_2] at h
    simp only [Fe.M.exec_bind] at h
    split at h
    · cases h
    · cases h
    · rename_i vals w₁ hs
      have h₁ := guarded_kept hs
      split at h
      · cases h
      · cases h
      · rename_i env₁ w₂ hb
        have hw : w₂ = w₁ := by
          unfold Fe.Sonatina.bind at hb
          split at hb <;> simp_all [stuck]
        subst hw
        intro p hp
        rw [runBodyG_kept h p hp, h₁ p (List.mem_append_left _ hp)]

/-- No memory spills in any function of the sections the checker checks. -/
def Sidecar.noSpills (s : Sidecar) : Bool :=
  (Check.entries s).all fun (name, _) =>
    ((s.section? name).bind (·.lowering)).all (·.funcs.all (·.spills.isEmpty))


end Fe.Sonatina
