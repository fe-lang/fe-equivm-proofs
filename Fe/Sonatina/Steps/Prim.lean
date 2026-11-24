import Fe.Sonatina.Steps.Mem

/-!
# Instructions approximate themselves

Mem0 lifted to the interpreter: an instruction of the machine IR, run in an environment that
binds less (`EnvSub`) and a related world, approximates the same instruction (`Approx.runInst`).
Operands evaluate to `stuck` or a pure value (`lift`).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## Instructions of the machine IR -/

/-- An instruction the machine IR may have: neither `evm_malloc` nor `alloca`, which read the
    size of memory. -/
def _root_.Fe.Sonatina.Inst.machine : Inst → Bool
  | .malloc _ | .alloca _ => false
  | _ => true

/-- Every statement of every block of the function is of the machine IR. -/
def _root_.Fe.Sonatina.Func.machine (f : Func) : Bool := f.blocks.all fun b => b.body.all (·.inst |> Inst.machine)

def _root_.Fe.Sonatina.Module.machine (m : Module) : Bool := m.funcs.all Func.machine

theorem _root_.Fe.Sonatina.Module.machine_func {m : Module} (h : m.machine = true) {name : String} {f : Func}
    (hf : m.func? name = some f) : f.machine = true :=
  List.all_eq_true.mp h f (List.mem_of_find?_eq_some hf)

theorem _root_.Fe.Sonatina.Func.machine_block {f : Func} (h : f.machine = true) {id : Nat} {b : Block}
    (hb : f.block? id = some b) : ∀ s ∈ b.body, s.inst.machine = true := fun s hs =>
  List.all_eq_true.mp (List.all_eq_true.mp h b (List.mem_of_find?_eq_some hb)) s hs

/-! ## Operands as options

An operand's evaluation is `stuck` or pure.  `EnvSub env' env` says `env'` binds nothing `env`
does not bind alike: an instruction run in `env'` approximates the same instruction in `env`. -/

/-- A pure value as a run: stuck on `none`. -/
def lift {α : Type} : Option α → FeM α
  | some a => pure a
  | none => stuck

def opVal (env : Env) : Operand → Option Val
  | .var id => env[id]?
  | .imm bits value => some (.int bits value)
  | .undef ty => some (Val.zero ty)

def intVal (env : Env) (o : Operand) : Option (Nat × Nat) :=
  match opVal env o with
  | some (.int bits value) => some (bits, value)
  | _ => none

theorem evalOperand_eq (env : Env) (o : Operand) : evalOperand env o = lift (opVal env o) := by
  cases o with
  | var id => simp only [evalOperand, opVal]; cases env[id]? <;> rfl
  | imm => rfl
  | undef => rfl

theorem lift_bind {α β : Type} (x : Option α) (k : α → FeM β) :
    lift x >>= k = match x with | some a => k a | none => stuck := by
  cases x
  · simp only [lift, stuck]; rfl
  · simp only [lift, pure_bind]

theorem evalInt_eq (env : Env) (o : Operand) : evalInt env o = lift (intVal env o) := by
  simp only [evalInt, evalOperand_eq, intVal, lift_bind]
  rcases opVal env o with _ | (_ | _) <;> rfl

/-- `env'` binds nothing `env` does not bind alike. -/
def EnvSub (env' env : Env) : Prop := ∀ (id : Nat) (v : Val), env'[id]? = some v → env[id]? = some v

theorem EnvSub.refl (env : Env) : EnvSub env env := fun _ _ h => h

theorem EnvSub.opVal {env' env : Env} (h : EnvSub env' env) {o : Operand} {v : Val}
    (hv : Steps.opVal env' o = some v) : Steps.opVal env o = some v := by
  cases o with
  | var id => exact h id v hv
  | imm | undef => exact hv

theorem EnvSub.intVal {env' env : Env} (h : EnvSub env' env) {o : Operand} {v : Nat × Nat}
    (hv : Steps.intVal env' o = some v) : Steps.intVal env o = some v := by
  unfold Steps.intVal at hv ⊢
  rcases hx : Steps.opVal env' o with _ | x
  · rw [hx] at hv; cases hv
  rw [hx] at hv
  rw [h.opVal hx]
  exact hv

namespace Approx

theorem lift {α : Type} {R : α → α → Prop} {x' x : Option α}
    (h : ∀ a, x' = some a → ∃ b, x = some b ∧ R a b) : Approx R (Steps.lift x') (Steps.lift x) := by
  cases x' with
  | none => exact stuck _
  | some a =>
    obtain ⟨b, rfl, hab⟩ := h a rfl
    exact pure hab

theorem lift_eq {α : Type} {x' x : Option α} (h : ∀ a, x' = some a → x = some a) :
    Approx Eq (Steps.lift x') (Steps.lift x) := lift fun a ha => ⟨a, h a ha, rfl⟩

theorem evalOperand {env' env : Env} (h : EnvSub env' env) (o : Operand) :
    Approx Eq (Fe.Sonatina.evalOperand env' o) (Fe.Sonatina.evalOperand env o) := by
  rw [evalOperand_eq, evalOperand_eq]; exact lift_eq fun _ => h.opVal

theorem evalInt {env' env : Env} (h : EnvSub env' env) (o : Operand) :
    Approx Eq (Fe.Sonatina.evalInt env' o) (Fe.Sonatina.evalInt env o) := by
  rw [evalInt_eq, evalInt_eq]; exact lift_eq fun _ => h.intVal

theorem evalWord {env' env : Env} (h : EnvSub env' env) (o : Operand) :
    Approx Eq (Fe.Sonatina.evalWord env' o) (Fe.Sonatina.evalWord env o) := by
  unfold Fe.Sonatina.evalWord
  exact bind (evalInt h o) fun a' a h => h ▸ pure_eq _

theorem mapM' {α γ : Type} {f' f : γ → FeM α} (hf : ∀ a, Approx Eq (f' a) (f a)) :
    ∀ xs : List γ, Approx Eq (xs.mapM f') (xs.mapM f)
  | [] => by simpa using pure_eq ([] : List α)
  | a :: xs => by
    rw [List.mapM_cons, List.mapM_cons]
    exact bind (hf a) fun b' b hb => hb ▸ bind (mapM' hf xs) fun bs' bs hbs => hbs ▸ pure_eq _

end Approx

theorem pairVal_eq (env : Env) (a b : Operand) :
    evalPair env a b = lift (do
      let (bits, x) ← intVal env a
      let (bits', y) ← intVal env b
      if bits == bits' then some (bits, x, y) else none) := by
  simp only [evalPair, evalInt_eq, lift_bind]
  rcases intVal env a with _ | ⟨bits, x⟩ <;> rcases intVal env b with _ | ⟨bits', y⟩ <;>
    simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some, lift, stuck] <;>
    (try split) <;> rfl

theorem Approx.evalPair {env' env : Env} (h : EnvSub env' env) (a b : Operand) :
    Approx Eq (Fe.Sonatina.evalPair env' a b) (Fe.Sonatina.evalPair env a b) := by
  rw [pairVal_eq, pairVal_eq]
  refine Approx.lift_eq fun v hv => ?_
  rcases ha : intVal env' a with _ | ⟨bits, x⟩
  · rw [ha] at hv; cases hv
  rcases hb : intVal env' b with _ | ⟨bits', y⟩
  · rw [ha, hb] at hv; cases hv
  rw [ha, hb] at hv
  rw [h.intVal ha, h.intVal hb]
  exact hv

set_option maxHeartbeats 4000000 in
/-- The primitives of the model library that approximate themselves. -/
syntax "approx_prim_lib" : tactic
macro_rules
  | `(tactic| approx_prim_lib) => `(tactic| first
    | with_reducible exact approx_selfAddress
    | with_reducible exact approx_balance _
    | with_reducible exact approx_origin
    | with_reducible exact approx_caller
    | with_reducible exact approx_callvalue
    | with_reducible exact approx_calldataload _
    | with_reducible exact approx_calldatasize
    | with_reducible exact approx_calldatacopy _ _ _
    | with_reducible exact approx_codesize
    | with_reducible exact approx_codecopy _ _ _
    | with_reducible exact approx_gasprice
    | with_reducible exact approx_extcodesize _
    | with_reducible exact approx_extcodehash _
    | with_reducible exact approx_extcodecopy _ _ _ _
    | with_reducible exact approx_returndatasize
    | with_reducible exact approx_returndatacopy _ _ _
    | with_reducible exact approx_blockhash _
    | with_reducible exact approx_coinbase
    | with_reducible exact approx_timestamp
    | with_reducible exact approx_blockNumber
    | with_reducible exact approx_prevrandao
    | with_reducible exact approx_gaslimit
    | with_reducible exact approx_chainid
    | with_reducible exact approx_selfbalance
    | with_reducible exact approx_basefee
    | with_reducible exact approx_blobhash _
    | with_reducible exact approx_blobbasefee
    | with_reducible exact approx_gas
    | with_reducible exact approx_cload _
    | with_reducible exact approx_mload _
    | with_reducible exact approx_mstore _ _
    | with_reducible exact approx_sload _
    | with_reducible exact approx_sstore _ _
    | with_reducible exact approx_tload _
    | with_reducible exact approx_tstore _ _
    | with_reducible exact approx_keccak256 _ _
    | with_reducible exact approx_mcopy _ _ _
    | with_reducible exact approx_mstore8 _ _
    | with_reducible exact approx_logData _ _ _
    | with_reducible exact approx_createWith _ _ _ _
    | with_reducible exact approx_create _ _ _
    | with_reducible exact approx_create2 _ _ _ _
    | with_reducible exact approx_call _ _ _ _ _ _ _
    | with_reducible exact approx_staticcall _ _ _ _ _ _
    | with_reducible exact approx_delegatecall _ _ _ _ _ _
    | with_reducible exact approx_zeroMem _ _
    | with_reducible exact approx_returnData _ _
    | with_reducible exact approx_revertData _ _
    | with_reducible exact approx_stopCall
    | with_reducible exact approx_trap)

/-- Prove that a computation approximates its copy, with an environment `EnvSub` in context:
    binds, conditionals and matches piecewise, operands and primitives by their lemmas. -/
syntax "approx_auto" : tactic
macro_rules
  | `(tactic| approx_auto) => `(tactic| repeat' (first
    | with_reducible exact Approx.pure_eq _
    | with_reducible exact Approx.stuck _
    | with_reducible exact Approx.diverge _
    | with_reducible exact Empty.elim ‹Empty›
    | exact Approx.evalOperand ‹EnvSub _ _› _
    | exact Approx.evalInt ‹EnvSub _ _› _
    | exact Approx.evalWord ‹EnvSub _ _› _
    | exact Approx.evalPair ‹EnvSub _ _› _ _
    | exact Approx.mapM' (Approx.evalWord ‹EnvSub _ _›) _
    | exact Approx.mapM' (Approx.evalOperand ‹EnvSub _ _›) _
    | approx_prim_lib
    | with_reducible exact Approx.read
    | with_reducible refine Approx.bind (R := Eq) ?_ fun _ _ e => by subst e; approx_auto
    | with_reducible refine Approx.read_bind fun _ => ?_
    | with_reducible refine Approx.ite ?_ ?_
    | (refine Approx.mapM (fun _ => ?_) _; dsimp only)
    | split))

set_option maxHeartbeats 4000000 in
/-- An EVM instruction approximates itself. -/
theorem Approx.evmRun (op : EvmOp) (args : List UInt256) :
    Approx Eq (op.run args) (op.run args) := by
  have h := EnvSub.refl ({} : Env)
  unfold EvmOp.run
  dsimp only
  split <;> approx_auto

macro_rules
  | `(tactic| approx_prim_lib) => `(tactic| with_reducible exact Approx.evmRun _ _)

/-- An instruction of the machine IR run in an environment that binds less approximates it run
    in the larger one. -/
theorem Approx.runInst {env' env : Env} (h : EnvSub env' env) (c : Ctx) (i : Inst)
    (hi : i.machine = true) :
    Approx Eq (Fe.Sonatina.runInst c env' i) (Fe.Sonatina.runInst c env i) := by
  cases i <;> simp only [Inst.machine, Bool.false_eq_true] at hi <;> simp only [Fe.Sonatina.runInst] <;> approx_auto

theorem Approx.bindVals (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    Approx Eq (Fe.Sonatina.bind env dsts vals) (Fe.Sonatina.bind env dsts vals) := by
  unfold Fe.Sonatina.bind; exact Approx.ite (Approx.pure_eq _) (Approx.stuck _)

theorem Approx.enter (env : Env) (prev : Option Nat) (b : Block) :
    Approx Eq (Fe.Sonatina.enter env prev b) (Fe.Sonatina.enter env prev b) := by
  have h := EnvSub.refl env
  unfold Fe.Sonatina.enter
  refine Approx.bind (R := Eq) (Approx.mapM (fun phi => ?_) _) fun _ _ e => e ▸ bindVals _ _ _
  approx_auto

end Fe.Sonatina.Steps
