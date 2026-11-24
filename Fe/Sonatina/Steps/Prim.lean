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

/-- An operand other than `undef`. -/
def _root_.Fe.Sonatina.Operand.defined : Operand → Bool
  | .undef _ => false
  | _ => true

/-- The operands an instruction reads. -/
def _root_.Fe.Sonatina.Inst.args : Inst → List Operand
  | .bin _ a b | .cmp _ a b | .ovf _ a b | .mstore a b _ | .memzero a b | .extractValue a b =>
    [a, b]
  | .isZero a | .not a | .neg a | .clz a | .ctz a | .cast _ a _ | .mload a _ | .malloc a => [a]
  | .select a b c | .insertValue a b c => [a, b, c]
  | .evm _ args | .keccakWords args | .call _ args => args
  | .alloca _ | .symAddr _ | .symSize _ => []

/-- The operands a terminator reads. -/
def _root_.Fe.Sonatina.Term.args : Term → List Operand
  | .br c _ _ => [c]
  | .brTable s _ cases => s :: cases.map (·.1)
  | .ret vs => vs
  | .evmReturn a l | .evmRevert a l => [a, l]
  | .jump _ | .evmStop | .evmInvalid | .unreachable => []

/-- An instruction the machine IR may have: no `undef` operand, and neither `evm_malloc` nor
    `alloca`, which read the size of memory, nor an aggregate's.  Its values are integers. -/
def _root_.Fe.Sonatina.Inst.machine (i : Inst) : Bool :=
  i.args.all Operand.defined && match i with
    | .malloc _ | .alloca _ | .insertValue .. | .extractValue .. => false
    | _ => true

/-- Every phi, statement and terminator of every block of the function is of the machine IR. -/
def _root_.Fe.Sonatina.Func.machine (f : Func) : Bool := f.blocks.all fun b =>
  b.phis.all (fun phi => phi.incoming.all (·.1.defined)) && b.body.all (·.inst.machine) &&
    b.term.args.all Operand.defined

def _root_.Fe.Sonatina.Module.machine (m : Module) : Bool := m.funcs.all Func.machine

theorem _root_.Fe.Sonatina.Module.machine_func {m : Module} (h : m.machine = true) {name : String} {f : Func}
    (hf : m.func? name = some f) : f.machine = true :=
  List.all_eq_true.mp h f (List.mem_of_find?_eq_some hf)

theorem _root_.Fe.Sonatina.Func.machine_of_mem {f : Func} (h : f.machine = true) {b : Block}
    (hb : b ∈ f.blocks) :
    (∀ phi ∈ b.phis, ∀ p ∈ phi.incoming, p.1.defined = true) ∧
      (∀ s ∈ b.body, s.inst.machine = true) ∧ ∀ o ∈ b.term.args, o.defined = true := by
  have := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem _root_.Fe.Sonatina.Func.machine_block {f : Func} (h : f.machine = true) {id : Nat} {b : Block}
    (hb : f.block? id = some b) :
    (∀ phi ∈ b.phis, ∀ p ∈ phi.incoming, p.1.defined = true) ∧
      (∀ s ∈ b.body, s.inst.machine = true) ∧ ∀ o ∈ b.term.args, o.defined = true :=
  Func.machine_of_mem h (List.mem_of_find?_eq_some hb)

theorem _root_.Fe.Sonatina.Inst.machine_args {i : Inst} (h : i.machine = true) :
    ∀ o ∈ i.args, o.defined = true := by
  unfold Inst.machine at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

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
theorem Approx.runInst {env' env : Env} (h : EnvSub env' env) {c' c : Ctx}
    (hc : c'.symbol = c.symbol) (i : Inst) (hi : i.machine = true) :
    Approx Eq (Fe.Sonatina.runInst c' env' i) (Fe.Sonatina.runInst c env i) := by
  cases i <;> simp only [Inst.machine, Bool.and_false, Bool.false_eq_true] at hi <;>
    simp only [Fe.Sonatina.runInst, hc] <;> approx_auto

theorem Approx.bindVals (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    Approx Eq (Fe.Sonatina.bind env dsts vals) (Fe.Sonatina.bind env dsts vals) := by
  unfold Fe.Sonatina.bind; exact Approx.ite (Approx.pure_eq _) (Approx.stuck _)

theorem Approx.enter (env : Env) (prev : Option Nat) (b : Block) :
    Approx Eq (Fe.Sonatina.enter env prev b) (Fe.Sonatina.enter env prev b) := by
  have h := EnvSub.refl env
  unfold Fe.Sonatina.enter
  refine Approx.bind (R := Eq) (Approx.mapM (fun phi => ?_) _) fun _ _ e => e ▸ bindVals _ _ _
  approx_auto

/-! ## Integer values

A machine function's values are integers: it is called with integers, each instruction gives
integers, and so do its calls when the oracle returns integers on integers.  `Returns P x`:
every value `x` returns satisfies `P`; `Total P x`: `x` returns, leaving the world as it was, a
value satisfying `P`. -/

def _root_.Fe.Sonatina.Val.isInt : Val → Bool
  | .int _ _ => true
  | .agg _ => false

/-- Values that are all integers. -/
def IntVals (vs : List Val) : Prop := vs.all Val.isInt = true

theorem intVals_iff {vs : List Val} : IntVals vs ↔ ∀ v ∈ vs, v.isInt = true := List.all_eq_true

/-- An environment that binds only integers. -/
def EnvInt (env : Env) : Prop := ∀ (k : Nat) (v : Val), env[k]? = some v → v.isInt = true

theorem EnvInt.empty : EnvInt {} := fun _ _ h => by simp at h

/-- Every value a run returns satisfies `P`. -/
def Returns {α : Type} (P : α → Prop) (x : FeM α) : Prop :=
  ∀ I w a w', x.exec I w = some (.ok (a, w')) → P a

/-- A run that returns, leaving the world as it was, a value satisfying `P`. -/
def Total {α : Type} (P : α → Prop) (x : FeM α) : Prop :=
  ∀ I w, ∃ a, x.exec I w = some (.ok (a, w)) ∧ P a

namespace Returns

variable {α β : Type}

theorem pure {P : α → Prop} {a : α} (h : P a) : Returns P (Pure.pure a : FeM α) := by
  intro I w a' w' hx
  simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hx
  exact hx.1 ▸ h

theorem diverge (P : α → Prop) : Returns P (Fe.M.diverge : FeM α) := by
  intro I w a w' hx; simp only [Fe.M.exec_diverge, reduceCtorEq] at hx

theorem stuck (P : α → Prop) : Returns P (Fe.Sonatina.stuck : FeM α) := Returns.diverge P

theorem bind {P : α → Prop} {Q : β → Prop} {x : FeM α} {k : α → FeM β} (hx : Returns P x)
    (hk : ∀ a, P a → Returns Q (k a)) : Returns Q (x >>= k) := by
  intro I w b w' h
  rw [Fe.M.exec_bind] at h
  rcases hx' : x.exec I w with _ | (e | ⟨a, w₁⟩) <;> rw [hx'] at h
  · simp at h
  · simp at h
  · exact hk a (hx I w a w₁ hx') I w₁ b w' h

theorem bind_any {Q : β → Prop} {x : FeM α} {k : α → FeM β} (hk : ∀ a, Returns Q (k a)) :
    Returns Q (x >>= k) := Returns.bind (P := fun _ => True) (fun _ _ _ _ _ => trivial) fun a _ => hk a

theorem mono {P Q : α → Prop} {x : FeM α} (h : Returns P x) (hPQ : ∀ a, P a → Q a) :
    Returns Q x := fun I w a w' hx => hPQ a (h I w a w' hx)

theorem and {P Q : α → Prop} {x : FeM α} (h₁ : Returns P x) (h₂ : Returns Q x) :
    Returns (fun a => P a ∧ Q a) x := fun I w a w' hx => ⟨h₁ I w a w' hx, h₂ I w a w' hx⟩

theorem lift {P : α → Prop} {x : Option α} (h : ∀ a, x = some a → P a) :
    Returns P (Steps.lift x) := by
  cases x with
  | none => exact Returns.stuck P
  | some a => exact Returns.pure (h a rfl)

theorem mapM {γ : Type} {P : α → Prop} {f : γ → FeM α} :
    ∀ {l : List γ}, (∀ a ∈ l, Returns P (f a)) → Returns (fun bs => ∀ b ∈ bs, P b) (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact Returns.pure fun _ h => nomatch h
  | a :: l, h => by
    rw [List.mapM_cons]
    exact Returns.bind (h a (List.mem_cons_self ..)) fun b hb =>
      Returns.bind (Returns.mapM fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs hbs =>
        Returns.pure fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hbs x hx

end Returns

namespace Total

variable {α β : Type}

theorem pure {P : α → Prop} {a : α} (h : P a) : Total P (Pure.pure a : FeM α) :=
  fun _ _ => ⟨a, rfl, h⟩

theorem bind {P : α → Prop} {Q : β → Prop} {x : FeM α} {k : α → FeM β} (hx : Total P x)
    (hk : ∀ a, P a → Total Q (k a)) : Total Q (x >>= k) := by
  intro I w
  obtain ⟨a, hxa, hPa⟩ := hx I w
  obtain ⟨b, hkb, hQb⟩ := hk a hPa I w
  exact ⟨b, by rw [Fe.M.exec_bind, hxa]; exact hkb, hQb⟩

theorem lift {P : α → Prop} {x : Option α} {a : α} (hx : x = some a) (h : P a) :
    Total P (Steps.lift x) := by
  subst hx; exact Total.pure h

theorem mapM {γ : Type} {P : γ → α → Prop} {f : γ → FeM α} :
    ∀ {l : List γ}, (∀ a ∈ l, Total (P a) (f a)) → Total (fun bs => List.Forall₂ P l bs) (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact Total.pure .nil
  | a :: l, h => by
    rw [List.mapM_cons]
    exact Total.bind (h a (List.mem_cons_self ..)) fun b hb =>
      Total.bind (Total.mapM fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs hbs =>
        Total.pure (.cons hb hbs)

end Total

/-- An approximation whose right side returns values satisfying `P` relates them too. -/
theorem Approx.strengthen {α : Type} {S : α → α → Prop} {P : α → Prop} {x' x : FeM α}
    (h : Approx S x' x) (hP : Returns P x) : Approx (fun a' a => S a' a ∧ P a) x' x := by
  intro I w' w hw
  have h1 := h I w' w hw
  have h2 : ∀ a w₁, x.exec I w = some (.ok (a, w₁)) → P a := fun a w₁ => hP I w a w₁
  revert h1 h2
  generalize x'.exec I w' = r'
  generalize x.exec I w = r
  rcases r' with _ | (_ | ⟨a', _⟩) <;> rcases r with _ | (_ | ⟨a, w₁⟩) <;> simp only [ResRel] <;>
    first
      | exact fun h1 _ => h1
      | exact fun h1 h2 => ⟨⟨h1.1, h2 a w₁ rfl⟩, h1.2⟩
      | trivial

/-- A pure value approximates a run that returns a related value and leaves the world. -/
theorem Approx.pure_total {α : Type} {S : α → α → Prop} {a' : α} {x : FeM α}
    (h : Total (S a') x) : Approx S (Pure.pure a') x := by
  intro I w' w hw
  obtain ⟨a, hx, hS⟩ := h I w
  simp only [Fe.M.exec_pure, hx, ResRel]
  exact ⟨hS, hw⟩

/-- The computations of the model library that `returns_auto` proves by lemma. -/
syntax "returns_prim" : tactic
macro_rules
  | `(tactic| returns_prim) => `(tactic| fail "no primitive")

/-- Prove that a computation returns integers: binds piecewise, matches split. -/
syntax "returns_auto" : tactic
macro_rules
  | `(tactic| returns_auto) => `(tactic| repeat' (first
    | exact Returns.pure rfl
    | exact Returns.stuck _
    | exact Returns.diverge _
    | exact Empty.elim ‹Empty›
    | returns_prim
    | refine Returns.bind_any fun _ => ?_
    | split))

theorem Val.as_isInt {v : Val} (h : v.isInt = true) (ty : Ty) : (v.as ty).isInt = true := by
  cases v with
  | agg => cases h
  | int b n => cases ty <;> rfl

theorem opVal_int {env : Env} (h : EnvInt env) {o : Operand} (ho : o.defined = true) {v : Val}
    (hv : opVal env o = some v) : v.isInt = true := by
  cases o with
  | var id => exact h id v hv
  | imm => simp only [opVal, Option.some.injEq] at hv; subst hv; rfl
  | undef => simp [Operand.defined] at ho

theorem returns_evalOperand {env : Env} (h : EnvInt env) {o : Operand} (ho : o.defined = true) :
    Returns (fun v => v.isInt = true) (evalOperand env o) := by
  rw [evalOperand_eq]; exact Returns.lift fun v hv => opVal_int h ho hv

theorem returns_evalOperands {env : Env} (h : EnvInt env) {os : List Operand}
    (ho : ∀ o ∈ os, o.defined = true) : Returns IntVals (os.mapM (evalOperand env)) :=
  Returns.mono (Returns.mapM fun o hm => returns_evalOperand h (ho o hm)) fun _ hb =>
    intVals_iff.mpr hb

set_option maxHeartbeats 4000000 in
theorem returns_evmRun (op : EvmOp) (args : List UInt256) : Returns IntVals (op.run args) := by
  unfold EvmOp.run
  dsimp only
  split <;> returns_auto

macro_rules
  | `(tactic| returns_prim) => `(tactic| exact returns_evmRun _ _)

set_option maxHeartbeats 4000000 in
/-- An instruction of the machine IR returns integers in an environment of integers. -/
theorem returns_runInst {env : Env} (h : EnvInt env) (c : Ctx) (i : Inst) (hi : i.machine = true) :
    Returns IntVals (runInst c env i) := by
  have ha := Inst.machine_args hi
  cases i <;> simp only [Inst.machine, Bool.and_false, Bool.false_eq_true] at hi
  case select cnd a b =>
    have ha' : a.defined = true := ha a (by simp [Inst.args])
    have hb' : b.defined = true := ha b (by simp [Inst.args])
    simp only [runInst]
    refine Returns.bind_any fun x => ?_
    rcases x with ⟨_, n⟩
    dsimp only
    refine Returns.bind (returns_evalOperand h (o := if n != 0 then a else b) ?_) fun v hv =>
      Returns.pure ?_
    · split
      · exact ha'
      · exact hb'
    · simp only [IntVals, List.all_cons, List.all_nil, hv, Bool.and_true]
  all_goals (simp only [runInst]; returns_auto)

/-! ## Binding -/

/-- One binding of `bind`. -/
def bindStep (env : Env) (x : (Nat × Ty) × Val) : Env := env.insert x.1.1 (x.2.as x.1.2)

theorem foldl_bindStep {g : Env → (Nat × Ty) × Val → Env} (hg : ∀ e x, g e x = bindStep e x) :
    ∀ (l : List ((Nat × Ty) × Val)) (env : Env), l.foldl g env = l.foldl bindStep env
  | [], _ => rfl
  | x :: l, env => by rw [List.foldl_cons, List.foldl_cons, hg]; exact foldl_bindStep hg l _

/-- `bind` gives the environment with each value at its id, as its type. -/
theorem returns_bind (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    Returns (fun env' => dsts.length = vals.length ∧ env' = (dsts.zip vals).foldl bindStep env)
      (bind env dsts vals) := by
  unfold bind
  split
  · next hl =>
    exact Returns.pure ⟨by simpa using hl,
      foldl_bindStep (fun e x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl) _ _⟩
  · exact Returns.stuck _

theorem env_insert_get {env : Env} {k id : Nat} {v : Val} :
    (env.insert k v)[id]? = if k = id then some v else env[id]? := by
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : k = id
  · subst h; simp
  · have : ¬compare k id = .eq := by rw [compare_eq_iff_eq]; exact h
    simp [this, h]

/-- A binding keeps every value bound. -/
theorem fold_keep : ∀ (l : List ((Nat × Ty) × Val)) (env : Env) (k : Nat),
    (env[k]?).isSome = true → ((l.foldl bindStep env)[k]?).isSome = true
  | [], _, _, h => h
  | x :: l, env, k, h => by
    rw [List.foldl_cons]
    refine fold_keep l _ k ?_
    unfold bindStep; rw [env_insert_get]; split <;> simp_all

/-- A binding binds each of its ids. -/
theorem fold_binds : ∀ (dsts : List (Nat × Ty)) (vals : List Val) (env : Env),
    dsts.length = vals.length → ∀ d ∈ dsts, (((dsts.zip vals).foldl bindStep env)[d.1]?).isSome = true
  | [], _, _, _, d, hd => nomatch hd
  | _ :: _, [], _, h, _, _ => by simp at h
  | d₀ :: ds, v :: vs, env, h, d, hd => by
    rw [List.zip_cons_cons, List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd
    · exact fold_keep _ _ _ (by unfold bindStep; rw [env_insert_get]; simp)
    · exact fold_binds ds vs _ (by simpa using h) d hd

/-- A binding of integers keeps an environment of integers. -/
theorem fold_int : ∀ (l : List ((Nat × Ty) × Val)) (env : Env), EnvInt env →
    (∀ x ∈ l, x.2.isInt = true) → EnvInt (l.foldl bindStep env)
  | [], _, h, _ => h
  | x :: l, env, h, hl => by
    rw [List.foldl_cons]
    refine fold_int l _ ?_ fun y hy => hl y (List.mem_cons_of_mem _ hy)
    intro k v hv
    unfold bindStep at hv; rw [env_insert_get] at hv
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv
      exact Val.as_isInt (hl x (List.mem_cons_self ..)) _
    · exact h k v hv

theorem returns_bind_int {env : Env} (h : EnvInt env) {dsts : List (Nat × Ty)} {vals : List Val}
    (hv : IntVals vals) : Returns EnvInt (bind env dsts vals) :=
  Returns.mono (returns_bind env dsts vals) fun env' ⟨_, e⟩ => by
    rw [e]; exact fold_int _ _ h fun x hx => intVals_iff.mp hv _ (List.of_mem_zip hx).2

/-- What `enter` binds: a value for each phi, each returned by its operand's evaluation. -/
theorem returns_enter (env : Env) (prev : Option Nat) (b : Block) {P : Val → Prop}
    (hp : ∀ phi ∈ b.phis, ∀ p ∈ phi.incoming, Returns P (evalOperand env p.1)) :
    Returns (fun env' => ∃ vals, (∀ v ∈ vals, P v) ∧
      (b.phis.map fun phi => (phi.dst, phi.ty)).length = vals.length ∧
      env' = ((b.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)
      (enter env prev b) := by
  unfold enter
  refine Returns.bind (Returns.mapM fun phi hphi => ?_) fun vals hvals =>
    Returns.mono (returns_bind _ _ _) fun env' ⟨hl, e⟩ => ⟨vals, hvals, hl, e⟩
  cases prev with
  | none => exact Returns.stuck _
  | some p =>
    dsimp only
    cases hf : phi.incoming.find? (·.2 == p) with
    | none => exact Returns.stuck _
    | some x =>
      obtain ⟨o, q⟩ := x
      exact hp phi hphi (o, q) (List.mem_of_find?_eq_some hf)

theorem returns_enter_int {env : Env} (h : EnvInt env) (prev : Option Nat) (b : Block)
    (hd : ∀ phi ∈ b.phis, ∀ p ∈ phi.incoming, p.1.defined = true) :
    Returns EnvInt (enter env prev b) :=
  Returns.mono (returns_enter env prev b fun phi hphi p hp => returns_evalOperand h (hd phi hphi p hp))
    fun env' ⟨vals, hvals, _, e⟩ => by
      rw [e]; exact fold_int _ _ h fun x hx => hvals _ (List.of_mem_zip hx).2

end Fe.Sonatina.Steps
