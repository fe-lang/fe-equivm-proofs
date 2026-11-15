import Fe.Sonatina.CheckArith
import Fe.Sonatina.Interp

/-!
# The machine IR's run of a block's instructions

The IR side of the checker's soundness proof, instruction by instruction.  `instWord` is the word
a pure instruction computes from its operands' words; `pureWith_eval` and `expand_eval` say the
checker's expression of a value has that word, when the block's values are as `ρ` says
(`Cons`), and `Canon.Valid.step` and `expand_new` that value numbering keeps every expression's
word; `pure_run` says the interpreter runs the instruction to it; `evm_run` says an
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

/-- The word the definition of value `id` gives it under `ρ`, if the definition is pure. -/
def Eqn (ee : ExecutionEnv) (ρ : Nat → UInt256) (symbols : List (String × Nat × Nat)) (id : Nat)
    (inst : Inst) : Prop :=
  ∀ (ex : Nat → Option Expr) e, pureWith ex symbols inst = some e →
    instWord ee ρ symbols inst = some (ρ id)

/-- The values `D` the block has defined are as `ρ` says: the block's expressions are numbered
    from its definitions, each value of `D` the block defines purely reads values of `D` and
    has the word its instruction computes, and the expression of each value of `D` has its
    word. -/
def Cons (ee : ExecutionEnv) (ρ : Nat → UInt256) (c : Ctx) (D : List Nat) : Prop :=
  c.canon = Canon.ofDefs c.symbols c.defs ∧
  (∀ id ∈ D, ∀ inst, c.defs.lookup id = some inst → reads D inst.operands = true ∧
    Eqn ee ρ c.symbols id inst) ∧
  ∀ id ∈ D, ∀ e, c.expand id = some e → e.eval ee ρ = some (ρ id)

/-- The expression of a defined value has the word `ρ` gives it. -/
theorem expand_eval {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D : List Nat}
    (hc : Cons ee ρ c D) : ∀ id e, id ∈ D → c.expand id = some e → e.eval ee ρ = some (ρ id) :=
  fun id e hid he => hc.2.2 id hid e he

/-! ## Value numbering -/

theorem lookup_append {α β : Type} [BEq α] {a : α} {b : β} {l₂ : List (α × β)} :
    ∀ {l₁ : List (α × β)}, l₁.lookup a = some b → (l₁ ++ l₂).lookup a = some b
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    cases hk : a == k
    · simp only [List.lookup, hk, List.cons_append] at h ⊢; exact lookup_append h
    · simpa [List.lookup, hk] using h

theorem ne_of_lookup_none {α β : Type} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List (α × β)} {p : α × β}, l.lookup a = none → p ∈ l → p.1 ≠ a
  | [], _, _, hp => by simp at hp
  | (k, v) :: l, p, h, hp => by
    cases hk : a == k
    · simp only [List.lookup, hk] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact fun he => (by simpa using hk : ¬a = k) he.symm
      · exact ne_of_lookup_none h hp
    · simp [List.lookup, hk] at h

theorem lookup_eq_none {β : Type} {o : Option β} (h : ¬o.isSome = true) : o = none := by
  cases o <;> simp_all

theorem reads_self (ops : List Operand) : reads (ops.filterMap Operand.var?) ops = true := by
  simp only [reads, List.all_eq_true]
  intro o ho
  cases hv : o.var? with
  | none => rfl
  | some id => simpa [List.contains_iff_mem] using List.mem_filterMap.mpr ⟨o, ho, hv⟩

/-- Numbering a definition keeps the expressions valid, given its word if it is pure and new. -/
theorem Canon.Valid.step {ee : ExecutionEnv} {ρ : Nat → UInt256} {k : Canon}
    {symbols : List (String × Nat × Nat)} {d : Nat × Inst} (hv : k.Valid ee ρ)
    (he : k.vals.lookup d.1 = none → Eqn ee ρ symbols d.1 d.2) :
    (Canon.step symbols k d).Valid ee ρ := by
  unfold Canon.step
  split
  · exact hv
  · next hn =>
    have he := he (lookup_eq_none hn)
    split
    · refine ⟨fun p hp => ?_, hv.2⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact hv.1 p hp
    · next e hpe =>
      have hev : e.eval ee ρ = some (ρ d.1) := by
        rw [pureWith_eval (S := d.2.operands.filterMap Operand.var?) (fun _ _ _ h => hv.expand h)
          (reads_self _) hpe]
        exact he _ _ hpe
      split
      · next w hw =>
        have hw' := hv.2 _ (mem_of_lookup hw)
        simp only at hw'
        refine ⟨fun p hp => ?_, hv.2⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [Expr.eval]; rw [← hw', hev]
        · exact hv.1 p hp
      · split
        · refine ⟨fun p hp => ?_, fun p hp => ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · rfl
            · exact hv.1 p hp
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact hev
            · exact hv.2 p hp
        · refine ⟨fun p hp => ?_, hv.2⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hev
          · exact hv.1 p hp

/-- Numbering a definition keeps every value numbered before, and every other value but its
    own unnumbered. -/
theorem Canon.step_lookup {symbols : List (String × Nat × Nat)} {k : Canon} {d : Nat × Inst}
    {id : Nat} (h : k.vals.lookup id ≠ none ∨ id ≠ d.1) :
    (Canon.step symbols k d).vals.lookup id = k.vals.lookup id := by
  have hne : k.vals.lookup d.1 = none → id ≠ d.1 := fun hd he => by
    subst he; rcases h with h | h
    · exact h hd
    · exact h rfl
  have hb : ∀ x, k.vals.lookup d.1 = none → ((d.1, x) :: k.vals).lookup id = k.vals.lookup id :=
    fun x hd => by
      simp [List.lookup, beq_false_of_ne (hne hd)]
  unfold Canon.step
  split
  · rfl
  · next hn =>
    have hd : k.vals.lookup d.1 = none := lookup_eq_none hn
    split
    · exact hb _ hd
    · split
      · exact hb _ hd
      · split
        · exact hb _ hd
        · exact hb _ hd

theorem Canon.step_lookup_self {symbols : List (String × Nat × Nat)} {k : Canon}
    {d : Nat × Inst} : (Canon.step symbols k d).vals.lookup d.1 ≠ none := by
  unfold Canon.step
  split
  · next h => simpa using h
  · split
    · simp [List.lookup]
    · split
      · simp [List.lookup]
      · split <;> simp [List.lookup]

theorem Canon.foldl_lookup {symbols : List (String × Nat × Nat)} {id : Nat} :
    ∀ (xs : List (Nat × Inst)) (k : Canon), (k.vals.lookup id ≠ none ∨ ∀ p ∈ xs, p.1 ≠ id) →
      (xs.foldl (Canon.step symbols) k).vals.lookup id = k.vals.lookup id
  | [], _, _ => rfl
  | d :: xs, k, h => by
    rw [List.foldl_cons]
    have h1 : (Canon.step symbols k d).vals.lookup id = k.vals.lookup id :=
      Canon.step_lookup (h.imp (fun h => h) fun h he => h d (by simp) he.symm)
    rw [Canon.foldl_lookup xs _ (by
      rcases h with h | h
      · exact .inl (by rw [h1]; exact h)
      · exact .inr fun p hp => h p (List.mem_cons_of_mem _ hp)), h1]

theorem Canon.Valid.foldl {ee : ExecutionEnv} {ρ : Nat → UInt256}
    {symbols : List (String × Nat × Nat)} :
    ∀ (xs : List (Nat × Inst)) {k : Canon}, k.Valid ee ρ →
      (∀ id inst, k.vals.lookup id = none → xs.lookup id = some inst → Eqn ee ρ symbols id inst) →
      (xs.foldl (Canon.step symbols) k).Valid ee ρ
  | [], _, hv, _ => hv
  | (a, b) :: xs, k, hv, he => by
    rw [List.foldl_cons]
    refine Canon.Valid.foldl xs (hv.step fun hn => he a b hn (by simp [List.lookup])) ?_
    intro id inst hn hl
    have hne : id ≠ a := fun h => by subst h; exact Canon.step_lookup_self (d := (id, b)) hn
    rw [Canon.step_lookup (.inr hne)] at hn
    exact he id inst hn (by unfold List.lookup; simp [beq_false_of_ne hne, hl])

/-- The expressions of a prefix of the definitions are valid when its values have their words. -/
theorem Canon.valid_ofDefs {ee : ExecutionEnv} {ρ : Nat → UInt256}
    {symbols : List (String × Nat × Nat)} {xs : List (Nat × Inst)}
    (he : ∀ id inst, xs.lookup id = some inst → Eqn ee ρ symbols id inst) :
    (Canon.ofDefs symbols xs).Valid ee ρ :=
  Canon.Valid.foldl xs (Canon.valid_empty ee ρ) fun id inst _ hl => he id inst hl

/-- A value no definition defines is itself. -/
theorem expand_atom {c : Ctx} (hk : c.canon = Canon.ofDefs c.symbols c.defs) {id : Nat}
    (h : c.defs.lookup id = none) : c.expand id = some (.atom id) := by
  simp only [Ctx.expand, Canon.expand, hk, Canon.ofDefs]
  rw [Canon.foldl_lookup _ _ (.inr fun p hp => ne_of_lookup_none h hp)]
  rfl

/-- The expression of the value a definition defines first has its word, when the definitions
    before it have theirs and it has its own. -/
theorem expand_new {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    (hk : c.canon = Canon.ofDefs c.symbols c.defs) {xs ys : List (Nat × Inst)} {id : Nat}
    {inst : Inst} (hdefs : c.defs = xs ++ (id, inst) :: ys) (hx : xs.lookup id = none)
    (hv : (Canon.ofDefs c.symbols xs).Valid ee ρ) (he : Eqn ee ρ c.symbols id inst) :
    ∀ e, c.expand id = some e → e.eval ee ρ = some (ρ id) := by
  intro e hce
  set k := Canon.step c.symbols (Canon.ofDefs c.symbols xs) (id, inst)
  have hx' : (Canon.ofDefs c.symbols xs).vals.lookup id = none := by
    simp only [Canon.ofDefs]
    rw [Canon.foldl_lookup _ _ (.inr fun p hp => ne_of_lookup_none hx hp)]
    rfl
  have hvk : k.Valid ee ρ := hv.step fun _ => he
  have hK : c.canon.vals.lookup id = k.vals.lookup id := by
    rw [hk, hdefs, Canon.ofDefs, List.foldl_append, List.foldl_cons]
    exact Canon.foldl_lookup _ _ (.inl (Canon.step_lookup_self (d := (id, inst))))
  apply hvk.expand
  simpa [Ctx.expand, Canon.expand, hK] using hce

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


open Fe Fe.EVM in
/-- `clz` of a word runs as the event `CLZ`: the count of leading zeros from Osaka on, a trap
    before it. -/
theorem clz_run {ee : ExecutionEnv} {ic : Fe.Sonatina.Ctx} {env : Env} {a : Operand}
    {x : UInt256} (h : evalOperand env a = pure (.int 256 x.toNat)) (w : World) :
    RunAs ((runInst ic env (.clz a)).exec ee w) ((evRun .CLZ [x]).exec ee w) := by
  have hi : evalInt env a = pure (256, x.toNat) := by simp [evalInt, h]
  by_cases hf : ee.header.fork = .Osaka
  · have hv : (UInt256.clz x).toNat = if x.toNat = 0 then 256 else 256 - 1 - x.toNat.log2 := by
      simp only [UInt256.clz]
      split_ifs <;> rw [toNat_ofNat_lt (by unfold UInt256.size; omega)]
    simp [runInst, hi, evRun, clzRun, hf, RunAs, Fe.Sonatina.word, hv]
  · simp [runInst, hi, evRun, clzRun, hf, RunAs, trap]

end Fe.Sonatina.Check
