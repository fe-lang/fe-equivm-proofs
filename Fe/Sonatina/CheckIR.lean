import Fe.Sonatina.CheckArith
import Fe.Sonatina.Interp

/-!
# The machine IR's run of a block's instructions

The IR side of the checker's soundness proof, instruction by instruction.  `instWord` is the word
a pure instruction computes from its operands' words; `pureWith_eval` and `expand_eval` say the
checker's expression of a value has that word, when the block's values are as `ρ` says
(`Cons`); `pure_run` says the interpreter runs the instruction to it; `evm_run` says an
event's EVM instruction runs as the event's operation on the world (`evRun`).
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

/-- The word of an operand, the value `v` being `ρ v`. -/
def opWord (ρ : Nat → UInt256) : Operand → Option UInt256
  | .var id => some (ρ id)
  | .imm bits v => if bits == 256 && v < UInt256.size then some (.ofNat v) else none
  | .undef _ => none

/-- The word a pure instruction of the class computes, its operands' words given by `ρ`. -/
def instWord (ee : ExecutionEnv) (ρ : Nat → UInt256) (symbols : List (String × Nat × Nat)) :
    Inst → Option UInt256
  | .bin op a b => do opEval ee (← binOpcode op) [← opWord ρ a, ← opWord ρ b]
  | .cmp op a b => do opEval ee (← cmpOpcode op) [← opWord ρ a, ← opWord ρ b]
  | .isZero a => do opEval ee .ISZERO [← opWord ρ a]
  | .not a => do opEval ee .NOT [← opWord ρ a]
  | .evm op args => do opEval ee (← evmPureOpcode op) (← args.mapM (opWord ρ))
  | .symAddr s => do return .ofNat (← symbols.lookup s).1
  | .symSize s => do return .ofNat (← symbols.lookup s).2
  | _ => none

theorem operand_eval {ee : ExecutionEnv} {ρ : Nat → UInt256} {expand : Nat → Option Expr}
    {o : Operand} {e : Expr} (hexp : ∀ id e', o = .var id → expand id = some e' →
      e'.eval ee ρ = some (ρ id))
    (h : operandWith expand o = some e) : e.eval ee ρ = opWord ρ o := by
  cases o with
  | var id => exact (hexp id e rfl h).trans rfl
  | imm bits v =>
    simp only [operandWith] at h
    split_ifs at h with hb
    cases h
    simp [Expr.eval, opWord, hb]
  | undef _ => cases h

theorem operands_eval {ee : ExecutionEnv} {ρ : Nat → UInt256} {expand : Nat → Option Expr}
    {S : List Nat} (hexp : ∀ id e', id ∈ S → expand id = some e' → e'.eval ee ρ = some (ρ id)) :
    ∀ {os : List Operand} {es : List Expr}, reads S os = true →
      os.mapM (operandWith expand) = some es → es.mapM (·.eval ee ρ) = os.mapM (opWord ρ)
  | [], es, _, h => by simp at h; subst h; rfl
  | o :: os, es, hr, h => by
    simp only [reads, List.all_cons, Bool.and_eq_true] at hr
    cases ho : operandWith expand o with
    | none => simp [ho] at h
    | some e =>
      cases hos : os.mapM (operandWith expand) with
      | none => simp [ho, hos] at h
      | some es' =>
        simp only [List.mapM_cons, ho, hos, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [List.mapM_cons, operand_eval (fun id e' h => hexp id e' (by
          subst h; simpa [Operand.var?] using hr.1)) ho, operands_eval hexp hr.2 hos]

theorem bind2 {α β : Type} (x y : Option α) (f : List α → Option β) :
    ((x.bind fun a => (y.bind fun b => some [b]).bind fun l => some (a :: l)).bind f) =
      x.bind fun a => y.bind fun b => f [a, b] := by
  cases x <;> cases y <;> rfl

theorem bind1 {α β : Type} (x : Option α) (f : List α → Option β) :
    ((x.bind fun a => some [a]).bind f) = x.bind fun a => f [a] := by
  cases x <;> rfl

/-- The expression of a pure instruction has the word the instruction computes. -/
theorem pureWith_eval {ee : ExecutionEnv} {ρ : Nat → UInt256} {expand : Nat → Option Expr}
    {symbols : List (String × Nat × Nat)} {inst : Inst} {e : Expr} {S : List Nat}
    (hexp : ∀ id e', id ∈ S → expand id = some e' → e'.eval ee ρ = some (ρ id))
    (hr : reads S inst.operands = true)
    (h : pureWith expand symbols inst = some e) : e.eval ee ρ = instWord ee ρ symbols inst := by
  have hop := fun {o : Operand} {e : Expr} (hs : reads S [o] = true)
      (h : operandWith expand o = some e) =>
    operand_eval (ee := ee) (ρ := ρ) (fun id e' ho => hexp id e' (by
      subst ho; simpa [reads, Operand.var?] using hs)) h
  cases inst with
  | bin op a b =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hr
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : binOpcode op <;> cases ha : operandWith expand a <;>
      cases hb : operandWith expand b <;> simp [hc, ha, hb] at h
    rw [mkOp_eval h]
    simp [instWord, hc, ← hop (by simpa [reads] using hr.1) ha,
      ← hop (by simpa [reads] using hr.2) hb,
      List.mapM_cons]
    exact bind2 _ _ _
  | cmp op a b =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hr
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : cmpOpcode op <;> cases ha : operandWith expand a <;>
      cases hb : operandWith expand b <;> simp [hc, ha, hb] at h
    rw [mkOp_eval h]
    simp [instWord, hc, ← hop (by simpa [reads] using hr.1) ha,
      ← hop (by simpa [reads] using hr.2) hb,
      List.mapM_cons]
    exact bind2 _ _ _
  | isZero a =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true] at hr
    simp only [pureWith, Option.bind_eq_bind] at h
    cases ha : operandWith expand a <;> simp [ha] at h
    rw [mkOp_eval h]
    simp [instWord, ← hop (by simpa [reads] using hr) ha, List.mapM_cons]
    exact bind1 _ _
  | not a =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true] at hr
    simp only [pureWith, Option.bind_eq_bind] at h
    cases ha : operandWith expand a <;> simp [ha] at h
    rw [mkOp_eval h]
    simp [instWord, ← hop (by simpa [reads] using hr) ha, List.mapM_cons]
    exact bind1 _ _
  | evm op args =>
    simp only [Inst.operands] at hr
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hc : evmPureOpcode op <;> cases ha : args.mapM (operandWith expand) <;>
      simp [hc, ha] at h
    rw [mkOp_eval h, operands_eval hexp (by simpa [reads] using hr) ha]
    simp [instWord, hc]
  | symAddr s =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hs : symbols.lookup s <;> simp [hs] at h
    subst h
    simp [Expr.eval, instWord, hs]
  | symSize s =>
    simp only [pureWith, Option.bind_eq_bind] at h
    cases hs : symbols.lookup s <;> simp [hs] at h
    subst h
    simp [Expr.eval, instWord, hs]
  | _ => cases h

/-- The values `D` the block has defined are as `ρ` says: each one the block defines purely
    reads values of `D` and has the word its instruction computes. -/
def Cons (ee : ExecutionEnv) (ρ : Nat → UInt256) (c : Ctx) (D : List Nat) : Prop :=
  ∀ id ∈ D, ∀ inst, c.defs.lookup id = some inst → reads D inst.operands = true ∧
    ∀ d e, pureWith (c.expand d) c.symbols inst = some e →
      instWord ee ρ c.symbols inst = some (ρ id)

/-- The expression of a defined value has the word `ρ` gives it. -/
theorem expand_eval {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D : List Nat}
    (hc : Cons ee ρ c D) : ∀ d id e, id ∈ D → c.expand d id = some e → e.eval ee ρ = some (ρ id)
  | 0, _, _, _, h => by simp [Ctx.expand] at h
  | d + 1, id, e, hid, h => by
    unfold Ctx.expand at h
    split at h
    · next inst hl =>
      obtain ⟨hr, hp⟩ := hc id hid inst hl
      split at h
      · next e' he =>
        cases h
        rw [pureWith_eval (fun id' e'' hid' => expand_eval hc d id' e'' hid') hr he]
        exact hp d _ he
      · split_ifs at h
        cases h
        rfl
    · cases h
      rfl

/-- The run's values `D` are words, `ρ` gives them. -/
def WordsOf (env : Env) (ρ : Nat → UInt256) (D : List Nat) : Prop :=
  ∀ id ∈ D, env[id]? = some (.int 256 (ρ id).toNat)

theorem evalOperand_word {env : Env} {ρ : Nat → UInt256} {D : List Nat} {o : Operand}
    {v : UInt256} (hw : WordsOf env ρ D) (hr : reads D [o] = true) (ho : opWord ρ o = some v) :
    evalOperand env o = pure (.int 256 v.toNat) := by
  cases o with
  | var id =>
    simp only [opWord, Option.some.injEq] at ho
    subst ho
    have hid : id ∈ D := by simpa [reads, Operand.var?] using hr
    simp [evalOperand, hw id hid]
  | imm bits x =>
    simp only [opWord] at ho
    split_ifs at ho with hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    obtain ⟨rfl, hx⟩ := hb
    cases ho
    simp [evalOperand, toNat_ofNat_lt hx]
  | undef _ => cases ho

theorem as_word (n : Nat) {ty : Ty} (hty : ty.bits = 256) :
    (Val.int 256 n).as ty = .int 256 (UInt256.ofNat n).toNat := by
  cases ty <;> simp_all [Val.as, Ty.bits, toNat_ofNat, size_eq]

theorem as_int (b n : Nat) {ty : Ty} (hty : ty.bits = 256) :
    (Val.int b n).as ty = .int 256 (UInt256.ofNat n).toNat := by
  cases ty <;> simp_all [Val.as, Ty.bits, toNat_ofNat, size_eq]

theorem evalWords_word {env : Env} {ρ : Nat → UInt256} {D : List Nat} (hw : WordsOf env ρ D) :
    ∀ {os : List Operand} {ws : List UInt256}, reads D os = true → os.mapM (opWord ρ) = some ws →
      os.mapM (evalWord env) = pure ws
  | [], ws, _, h => by simp at h; subst h; rfl
  | o :: os, ws, hr, h => by
    simp only [reads, List.all_cons, Bool.and_eq_true] at hr
    cases ho : opWord ρ o with
    | none => simp [ho] at h
    | some v =>
      cases hos : os.mapM (opWord ρ) with
      | none => simp [ho, hos] at h
      | some vs =>
        simp only [List.mapM_cons, ho, hos, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        have h1 := evalOperand_word hw (by simpa [reads] using hr.1) ho
        simp [List.mapM_cons, evalWord, evalInt, h1, evalWords_word hw hr.2 hos,
          Reasoning.Theory.u256_ofNat_toNat]

/-- A pure instruction of the class runs to the word `instWord` gives it. -/
theorem pure_run {ee : ExecutionEnv} {ρ : Nat → UInt256} {D : List Nat} {env : Env}
    {expand : Nat → Option Expr} {symbols : List (String × Nat × Nat)} {inst : Inst} {e : Expr}
    {v : UInt256} {ic : Fe.Sonatina.Ctx} (hsym : ic.symbol = (symbols.lookup ·))
    (hw : WordsOf env ρ D) (hr : reads D inst.operands = true)
    (he : pureWith expand symbols inst = some e) (hv : instWord ee ρ symbols inst = some v) :
    ∃ val, (∀ w, (runInst ic env inst).exec ee w = some (.ok ([val], w))) ∧
      ∀ ty : Ty, ty.bits = 256 → val.as ty = .int 256 v.toNat := by
  have hlt : ∀ u : UInt256, u.toNat < UInt256.size := fun u => u.val.isLt
  cases inst with
  | bin op a b =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hr
    simp only [instWord, Option.bind_eq_bind] at hv
    cases hc : binOpcode op <;> cases ha : opWord ρ a <;> cases hb : opWord ρ b <;>
      simp only [hc, ha, hb, Option.bind_none, Option.bind_some, reduceCtorEq] at hv
    next opc va vb =>
    have hea := evalOperand_word hw (by simpa [reads] using hr.1) ha
    have heb := evalOperand_word hw (by simpa [reads] using hr.2) hb
    refine ⟨.int 256 (op.eval 256 va.toNat vb.toNat), fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, evalPair, evalInt, hea, heb]
    · rw [as_word _ hty]
      have := bin_word (ee := ee) hc (hlt va) (hlt vb)
      rw [Reasoning.Theory.u256_ofNat_toNat, Reasoning.Theory.u256_ofNat_toNat, hv] at this
      cases this
      rfl
  | cmp op a b =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hr
    simp only [instWord, Option.bind_eq_bind] at hv
    cases hc : cmpOpcode op <;> cases ha : opWord ρ a <;> cases hb : opWord ρ b <;>
      simp only [hc, ha, hb, Option.bind_none, Option.bind_some, reduceCtorEq] at hv
    next opc va vb =>
    have hea := evalOperand_word hw (by simpa [reads] using hr.1) ha
    have heb := evalOperand_word hw (by simpa [reads] using hr.2) hb
    refine ⟨bool (op.eval 256 va.toNat vb.toNat), fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, evalPair, evalInt, hea, heb]
    · rw [bool, as_int _ _ hty]
      have := cmp_word (ee := ee) hc (hlt va) (hlt vb)
      rw [Reasoning.Theory.u256_ofNat_toNat, Reasoning.Theory.u256_ofNat_toNat, hv] at this
      cases this
      rfl
  | isZero a =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true] at hr
    simp only [instWord, Option.bind_eq_bind] at hv
    cases ha : opWord ρ a <;> simp only [ha, Option.bind_none, Option.bind_some,
      reduceCtorEq] at hv
    next va =>
    have hea := evalOperand_word hw (by simpa [reads] using hr) ha
    refine ⟨bool (va.toNat == 0), fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, evalInt, hea]
    · rw [bool, as_int _ _ hty]
      simp only [opEval, evalOp] at hv
      have := isZero_word (hlt va)
      rw [Reasoning.Theory.u256_ofNat_toNat] at this
      cases hv
      rw [this]
      simp
  | not a =>
    simp only [Inst.operands, reads, List.all_cons, List.all_nil, Bool.and_true] at hr
    simp only [instWord, Option.bind_eq_bind] at hv
    cases ha : opWord ρ a <;> simp only [ha, Option.bind_none, Option.bind_some,
      reduceCtorEq] at hv
    next va =>
    have hea := evalOperand_word hw (by simpa [reads] using hr) ha
    refine ⟨.int 256 (2 ^ 256 - 1 - va.toNat), fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, evalInt, hea]
    · rw [as_word _ hty]
      simp only [opEval, evalOp] at hv
      have := not_word (hlt va)
      rw [Reasoning.Theory.u256_ofNat_toNat] at this
      obtain rfl : UInt256.lnot va = v := Option.some.inj hv
      rw [this]
  | symAddr sym =>
    simp only [instWord, Option.bind_eq_bind] at hv
    cases hs : symbols.lookup sym <;> simp only [hs, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.pure_def, Option.some.injEq] at hv
    next p =>
    refine ⟨.int 256 p.1, fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, hsym, hs]
    · rw [as_word _ hty, ← hv]
  | symSize sym =>
    simp only [instWord, Option.bind_eq_bind] at hv
    cases hs : symbols.lookup sym <;> simp only [hs, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.pure_def, Option.some.injEq] at hv
    next p =>
    refine ⟨.int 256 p.2, fun w => ?_, fun ty hty => ?_⟩
    · simp [runInst, hsym, hs]
    · rw [as_word _ hty, ← hv]
  | evm op args =>
    simp only [Inst.operands] at hr
    simp only [instWord, Option.bind_eq_bind] at hv
    cases hc : evmPureOpcode op <;> cases has : args.mapM (opWord ρ) <;>
      simp only [hc, has, Option.bind_none, Option.bind_some, reduceCtorEq] at hv
    next opc ws =>
    have hws := evalWords_word hw hr has
    refine ⟨.int 256 v.toNat, fun w => ?_, fun ty hty => ?_⟩
    · cases op <;> simp only [evmPureOpcode, reduceCtorEq, Option.some.injEq] at hc <;> subst hc
      all_goals
        rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | _⟩⟩⟩ <;>
          simp [opEval, evalOp, envOp] at hv
        subst hv
        simp [runInst, hws, EvmOp.run, Fe.EVM.selfAddress, Fe.EVM.origin, Fe.EVM.caller,
          Fe.EVM.callvalue, Fe.EVM.calldataload, Fe.EVM.calldatasize, Fe.EVM.codesize,
          Fe.EVM.chainid, Fe.EVM.timestamp, Fe.EVM.blockNumber, Fe.EVM.gaslimit, Fe.EVM.basefee,
          Ethereum.basefee, Fe.EVM.coinbase, Fe.EVM.prevrandao, Fe.EVM.blockhash, word] <;>
          split_ifs <;> simp
    · rw [as_word _ hty, Reasoning.Theory.u256_ofNat_toNat]
  | _ => simp [pureWith] at he

open Fe Fe.EVM in
/-- The IR's run of an EVM instruction is the event's operation on the world: the same failure,
    or the same world with the read word as the value. -/
def RunAs : Option (Except (Fe.Exit World) (List Val × World)) →
    Option (Except (Fe.Exit World) (Option UInt256 × World)) → Prop
  | x, some (.error e) => x = some (.error e)
  | x, some (.ok (r, w')) => x = some (.ok (r.toList.map word, w'))
  | x, none => x = none

open Fe Fe.EVM in
theorem exec_returndatacopy (ee : ExecutionEnv) (w : World) (d o l : UInt256) :
    (returndatacopy d o l).exec ee w =
      if o.toNat + l.toNat > w.returnData.size then some (.error .oob)
      else some (.ok ((), { w with memory := w.returnData.write o.toNat w.memory d.toNat l.toNat })) := by
  unfold returndatacopy
  simp only [Fe.M.exec_bind, Fe.M.exec_get]
  split_ifs <;> simp

open Fe Fe.EVM in
/-- A word the IR's instruction gives is the word the event reads. -/
theorem runAs_one (m : FeM UInt256) (ee : ExecutionEnv) (w : World) :
    RunAs ((do return [word (← m)] : FeM (List Val)).exec ee w) ((some <$> m).exec ee w) := by
  simp only [Fe.M.exec_bind, Fe.M.exec_map, Fe.M.exec_pure]
  rcases m.exec ee w with _ | _ | ⟨x, w'⟩ <;> rfl

open Fe Fe.EVM in
/-- An event's EVM instruction runs as its operation on the world. -/
theorem evm_run {ee : ExecutionEnv} {op : EvmOp} {opc : Operation} {args : List UInt256}
    (h : evmEventOpcode op = some opc) (hk : δ opc = some args.length) (w : World) :
    RunAs ((op.run args).exec ee w) ((evRun opc args).exec ee w) := by
  cases op
  case log n =>
    rcases n with _ | _ | _ | _ | _ | n <;> simp [evmEventOpcode] at h
    all_goals
      subst h
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | _⟩⟩⟩⟩⟩⟩ <;>
        simp [δ] at hk
    all_goals
      by_cases hp : ee.perm = true <;>
        simp [EvmOp.run, evRun, RunAs, Fe.EVM.logData, Fe.EVM.emit, hp]
  case call =>
    simp only [evmEventOpcode, Option.some.injEq] at h
    subst h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [δ] at hk
    exact runAs_one _ ee w
  case staticCall | delegateCall =>
    simp only [evmEventOpcode, Option.some.injEq] at h
    subst h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | _⟩⟩⟩⟩⟩⟩ <;>
      simp [δ] at hk
    exact runAs_one _ ee w
  case create =>
    simp only [evmEventOpcode, Option.some.injEq] at h
    subst h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp [δ] at hk
    exact runAs_one _ ee w
  case create2 =>
    simp only [evmEventOpcode, Option.some.injEq] at h
    subst h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩ <;> simp [δ] at hk
    exact runAs_one _ ee w
  all_goals simp only [evmEventOpcode, reduceCtorEq, Option.some.injEq] at h
  all_goals
    subst h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp [δ] at hk
    all_goals
      by_cases hp : ee.perm = true <;> cases hf : w.feed <;>
      simp [EvmOp.run, evRun, RunAs, Fe.EVM.sstore, Fe.EVM.mload, Fe.EVM.sload,
        Fe.EVM.keccak256, Fe.EVM.mstore, Fe.EVM.mstore8, Fe.EVM.codecopy, Fe.EVM.calldatacopy,
        Fe.EVM.mcopy, Fe.EVM.selfbalance, Fe.EVM.balance, Fe.EVM.extcodesize,
        Fe.EVM.returndatasize, Fe.EVM.gas, Fe.EVM.tload, Fe.EVM.tstore, Fe.EVM.next, exec_returndatacopy, word, hp, hf]
    all_goals split_ifs <;> simp


end Fe.Sonatina.Check
