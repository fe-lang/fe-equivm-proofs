import Fe.Sonatina.Check
import Fe.Sonatina.Interp
import Fe.Sonatina.Refine
import Reasoning.EVMWord

/-!
# Towards the soundness of the checker

What `check` implies, and the first lemmas of its proof; `CheckCert.lean` proves it.

`Sound s` is what `check_sound` proves of every sidecar `s` with `check s = true`:
the runtime bytes refine the machine IR's runtime, and the init bytes its constructor, at
profile `P1`: logs and revert payloads too.  The proof steps the bytes by `Xstep` (EVMLean's
`step_*` lemmas, `CheckStep.lean`), whose states hold the substate's logs and the output, so `P1`
costs over `P0` only the logs in the state relation (`step_log0` to `step_log4` against the
IR's `logData`) and the revert payload, read from memory as the return data is.

`Expr.eval` is the meaning of the checker's expressions in a frame: an atom is the word the
environment `env` gives the machine value, a constant itself, an operation what `Xstep`
computes of the operands.  `mkOp_eval` is the soundness of the checker's operand normalization:
constant folding, commuted operands, `GT` as swapped `LT`, three `ISZERO`s as one.
`Exit.next` is where an exit goes on the values of its expressions, and `way_sound` the
soundness of reading a conditional jump against it, the constant-branch rule among it.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The bytes of a section of the sidecar. -/
def _root_.Fe.Sonatina.Sidecar.code (s : Sidecar) (name : String) : ByteArray :=
  ((s.section? name).map (·.bytecode)).getD .empty

/-- What `check s = true` is to imply. -/
def Sound (s : Sidecar) : Prop :=
  RefinesOn .P1 (s.code "runtime") (s.model .machine) CalldataFits
    ∧ RefinesDeploy .P1 (s.code "init") .empty (s.model .machine) (fun _ => True)

/-- A pure opcode `evalOp` does not compute, as `Xstep` pushes it in the frame `ee`: `EXP`, and
    the opcodes of the environment and of the block header. -/
def envOp (ee : ExecutionEnv) : Operation → List UInt256 → Option UInt256
  | .EXP, [a, b] => some (UInt256.exp a b)
  | .CALLVALUE, [] => some ee.weiValue
  | .CALLER, [] => some (.ofNat ee.source.val)
  | .ADDRESS, [] => some (.ofNat ee.codeOwner.val)
  | .ORIGIN, [] => some (.ofNat ee.sender.val)
  | .CALLDATASIZE, [] => some (.ofNat ee.calldata.size)
  | .CODESIZE, [] => some (.ofNat ee.code.size)
  | .CALLDATALOAD, [a] => some (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32))
  | .CHAINID, [] => some (.ofNat Ethereum.chainId)
  | .TIMESTAMP, [] => some (.ofNat ee.header.timestamp)
  | .NUMBER, [] => some (.ofNat ee.header.number)
  | .GASLIMIT, [] => some (.ofNat ee.header.gasLimit)
  | .BASEFEE, [] => some (.ofNat ee.header.baseFeePerGas)
  | .COINBASE, [] => some (.ofNat ee.header.beneficiary.val)
  | .PREVRANDAO, [] => some ee.header.prevRandao
  | .BLOCKHASH, [a] => some (if ee.header.number ≤ a.toNat || a.toNat + 256 < ee.header.number
      then ⟨0⟩ else (ee.blocks.map ProcessedBlock.hash).getD a.toNat ⟨0⟩)
  | _, _ => none

/-- A pure opcode on words in the frame `ee`. -/
def opEval (ee : ExecutionEnv) (op : Operation) (args : List UInt256) : Option UInt256 :=
  evalOp op args <|> envOp ee op args

/-- The word an expression denotes in the frame `ee`, where machine value `id` is `env id`. -/
def Expr.eval (ee : ExecutionEnv) (env : Nat → UInt256) : Expr → Option UInt256
  | .atom id => some (env id)
  | .const v => some (UInt256.ofNat v)
  | .op0 op => opEval ee op []
  | .op1 op a => do opEval ee op [← a.eval ee env]
  | .op2 op a b => do opEval ee op [← a.eval ee env, ← b.eval ee env]
  | .op3 op a b c => do opEval ee op [← a.eval ee env, ← b.eval ee env, ← c.eval ee env]

theorem constWords_eval {ee : ExecutionEnv} {env : Nat → UInt256} :
    ∀ {args : List Expr} {words : List UInt256}, args.mapM constWord = some words →
      args.mapM (·.eval ee env) = some words
  | [], words, h => by simpa using h
  | a :: rest, words, h => by
    cases a with
    | const v =>
      cases hr : rest.mapM constWord with
      | none => simp [constWord, hr] at h
      | some tl =>
        simp only [List.mapM_cons, constWord, hr, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        simp [Expr.eval, constWords_eval hr]
    | _ => simp [constWord] at h

/-- Folding is sound: the constant is what the operation computes of its operands. -/
theorem foldConst_eval {ee : ExecutionEnv} {env : Nat → UInt256} {op : Operation}
    {args : List Expr} {e : Expr} (h : foldConst op args = some e) :
    e.eval ee env = (args.mapM (·.eval ee env)) >>= opEval ee op := by
  unfold foldConst at h
  cases hw : args.mapM constWord with
  | none => simp [hw] at h
  | some words =>
    cases hev : evalOp op words with
    | none => simp [hw, hev] at h
    | some w =>
      simp only [hw, hev, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      simp [constWords_eval hw, Expr.eval, opEval, hev, Reasoning.Theory.u256_ofNat_toNat]

theorem comm_words (a b : UInt256) :
    a + b = b + a ∧ UInt256.mul a b = UInt256.mul b a ∧ UInt256.land a b = UInt256.land b a ∧
      UInt256.lor a b = UInt256.lor b a ∧ UInt256.xor a b = UInt256.xor b a ∧
      UInt256.eq a b = UInt256.eq b a := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show UInt256.mk (a + b) = UInt256.mk (b + a); rw [add_comm]
  · show UInt256.mk (a * b) = UInt256.mk (b * a); rw [mul_comm]
  · simp only [UInt256.land, UInt256.mk.injEq]; ext
    show (a.val &&& b.val) % _ = (b.val &&& a.val) % _; rw [Nat.land_comm]
  · simp only [UInt256.lor, UInt256.mk.injEq]; ext
    show (a.val ||| b.val) % _ = (b.val ||| a.val) % _; rw [Nat.lor_comm]
  · simp only [UInt256.xor, UInt256.mk.injEq]; ext
    show (a.val ^^^ b.val) % _ = (b.val ^^^ a.val) % _; rw [Nat.xor_comm]
  · simp only [UInt256.eq, eq_comm]

/-- The six commutative opcodes commute. -/
theorem opEval_comm {ee : ExecutionEnv} {op : Operation} (h : commutative.contains op = true)
    (a b : UInt256) : opEval ee op [a, b] = opEval ee op [b, a] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := comm_words a b
  simp only [commutative, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [opEval, evalOp, *]

theorem gt_eval {ee : ExecutionEnv} (a b : UInt256) :
    opEval ee .GT [a, b] = opEval ee .LT [b, a] ∧
      opEval ee .SGT [a, b] = opEval ee .SLT [b, a] := by
  refine ⟨rfl, ?_⟩
  simp only [opEval, evalOp, UInt256.sgt, UInt256.slt, UInt256.sgtBool, UInt256.sltBool]
  split_ifs <;> rfl

/-- Normalization keeps the value of an operation on two operands. -/
theorem normalize_eval {ee : ExecutionEnv} {env : Nat → UInt256} (op : Operation) (a b : Expr) :
    (normalize op a b).eval ee env = (do opEval ee op [← a.eval ee env, ← b.eval ee env]) := by
  unfold normalize
  cases ha : a.eval ee env <;> cases hb : b.eval ee env
  all_goals
    by_cases h1 : op = .GT
    · subst h1; simp [Expr.eval, ha, hb, (gt_eval _ _).1]
    by_cases h2 : op = .SGT
    · subst h2; simp [Expr.eval, ha, hb, (gt_eval _ _).2]
    by_cases h3 : commutative.contains op && a.cmp b == .lt
    · rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2), ite_eq_left h3]
      simp only [Bool.and_eq_true] at h3
      simp [Expr.eval, ha, hb, opEval_comm h3.1]
    · rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2), ite_eq_right h3]
      simp [Expr.eval, ha, hb]

theorem isZero_isZero_isZero (a : UInt256) : (a.isZero.isZero).isZero = a.isZero := by
  unfold UInt256.isZero UInt256.eq0
  cases a == { val := 0 } <;> decide

theorem unary_eval {ee : ExecutionEnv} {env : Nat → UInt256} (op : Operation) (a : Expr) :
    (unary op a).eval ee env = (do opEval ee op [← a.eval ee env]) := by
  unfold unary
  split
  next b =>
    cases h : b.eval ee env <;> simp [Expr.eval, opEval, evalOp, h, isZero_isZero_isZero]
  next => rfl

/-- An operation's expression has the value the operation computes of its operands. -/
theorem mkOp_eval {ee : ExecutionEnv} {env : Nat → UInt256} {op : Operation} {args : List Expr}
    {e : Expr} (h : mkOp op args = some e) :
    e.eval ee env = args.mapM (·.eval ee env) >>= opEval ee op := by
  match args, h with
  | [], h => cases h; rfl
  | [a], h =>
    simp only [mkOp, Option.some.injEq] at h; subst h
    cases hf : foldConst op [a] with
    | some f => simpa [hf] using foldConst_eval (ee := ee) (env := env) hf
    | none => cases ha : a.eval ee env <;> simp [unary_eval, ha]
  | [a, b], h =>
    simp only [mkOp, Option.some.injEq] at h; subst h
    cases hf : foldConst op [a, b] with
    | some f => simpa [hf] using foldConst_eval (ee := ee) (env := env) hf
    | none =>
      cases ha : a.eval ee env <;> cases hb : b.eval ee env <;> simp [normalize_eval, ha, hb]
  | [a, b, c], h =>
    simp only [mkOp, Option.some.injEq] at h; subst h
    cases ha : a.eval ee env <;> cases hb : b.eval ee env <;> cases hc : c.eval ee env <;>
      simp [Expr.eval, ha, hb, hc]


/-- The successor an exit goes to, on the values of its expressions; `none` for a halt. -/
def Exit.next (ee : ExecutionEnv) (env : Nat → UInt256) : Exit → Option Nat
  | .goto s => some s
  | .br c nz z => (c.eval ee env).map fun v => if v.toNat != 0 then nz else z
  | .table s d cases _ => (s.eval ee env).map fun v =>
    ((cases.find? (UInt256.ofNat ·.1 == v)).map (·.2)).getD d
  | .halt .. | .ret _ | .unreach => none

/-- What a path knows of its exit: a `br_table`'s cases are words, and those ruled out are not
    the scrutinee's value. -/
def Exit.Valid (ee : ExecutionEnv) (env : Nat → UInt256) : Exit → Prop
  | .table s _ cases ruled => (∀ kd ∈ cases, kd.1 < UInt256.size) ∧
    ∀ v, s.eval ee env = some v → ∀ k ∈ ruled, UInt256.ofNat k ≠ v
  | _ => True

theorem toNat_ofNat (k : Nat) : (UInt256.ofNat k).toNat = k % UInt256.size := rfl

theorem ofNat_injective {a b : Nat} (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have := congrArg UInt256.toNat h
  rwa [toNat_ofNat, toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem fromBool_toNat (b : Bool) : ((UInt256.fromBool b).toNat != 0) = b := by
  cases b <;> rfl

theorem isZero_toNat (a : UInt256) : (a.isZero.toNat != 0) = (a.toNat == 0) := by
  rw [UInt256.isZero, fromBool_toNat]
  obtain ⟨⟨a, ha⟩⟩ := a
  by_cases h : a = 0
  · subst h; rfl
  · have : ((⟨⟨a, ha⟩⟩ : UInt256) == { val := 0 }) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, UInt256.mk.injEq]
      exact fun h' => h (by simpa using h')
    simp only [UInt256.eq0, this, UInt256.toNat]
    simpa using h

theorem eq_toNat (a b : UInt256) : ((UInt256.eq a b).toNat != 0) = decide (a = b) := by
  rw [UInt256.eq, fromBool_toNat]

/-- The first case of a word is the first whose key is the word's, when the keys are words. -/
theorem find_ofNat {cases : List (Nat × Nat)} {k : Nat}
    (hk : k < UInt256.size) (hc : ∀ kd ∈ cases, kd.1 < UInt256.size) :
    (cases.find? (UInt256.ofNat ·.1 == UInt256.ofNat k)).map (·.2) = cases.lookup k := by
  induction cases with
  | nil => rfl
  | cons kd rest ih =>
    obtain ⟨k', d⟩ := kd
    have h1 := hc (k', d) (by simp)
    by_cases he : k = k'
    · subst he; simp [List.lookup]
    · have hne : UInt256.ofNat k' ≠ UInt256.ofNat k := fun h => he (ofNat_injective h1 hk h).symm
      have hb : (k == k') = false := by simpa using he
      simp [List.lookup, hne, hb, ih fun kd h => hc kd (by simp [h])]

/-- No case is the word when every case is ruled out. -/
theorem find_ruled {cases : List (Nat × Nat)} {ruled : List Nat} {v : UInt256}
    (hall : cases.all (ruled.contains ·.1)) (hr : ∀ k ∈ ruled, UInt256.ofNat k ≠ v) :
    cases.find? (UInt256.ofNat ·.1 == v) = none := by
  simp only [List.find?_eq_none, beq_iff_eq]
  intro kd hkd
  simp only [List.all_eq_true, List.contains_iff_mem] at hall
  exact hr _ (hall kd hkd)

/-- A condition comparing the scrutinee with a case is true just when the scrutinee is it. -/
theorem caseOf_sound {ee : ExecutionEnv} {env : Nat → UInt256} {s cond : Expr} {k : Nat}
    (h : s.caseOf cond = some k) {c : UInt256} (hc : cond.eval ee env = some c) :
    ∃ v, s.eval ee env = some v ∧ (c.toNat != 0) = decide (UInt256.ofNat k = v) := by
  unfold Expr.caseOf at h
  split at h
  next k' s' =>
    simp only [beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hs : s'.eval ee env with
    | none => simp [Expr.eval, hs] at hc
    | some v =>
      simp [Expr.eval, hs, opEval, evalOp] at hc
      subst hc
      exact ⟨v, rfl, eq_toNat _ _⟩
  next s' k' _ =>
    simp only [beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hs : s'.eval ee env with
    | none => simp [Expr.eval, hs] at hc
    | some v =>
      simp [Expr.eval, hs, opEval, evalOp] at hc
      subst hc
      refine ⟨v, rfl, ?_⟩
      rw [eq_toNat]
      simp [eq_comm]
  next => cases h

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    unfold List.lookup at h
    split at h
    · next he => cases h; rw [eq_of_beq he]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- What a way says of the exit `e` it is a way of: the successor it goes to, an exit that goes
    where `e` goes, or nothing. -/
def Way.Sound (ee : ExecutionEnv) (env : Nat → UInt256) (e : Exit) : Way → Prop
  | .succ s => e.next ee env = some s
  | .never => False
  | .exit e' => e'.next ee env = e.next ee env ∧ e'.Valid ee env

/-- The constant-branch rule and the reading of a jump's condition are sound: when the
    condition's value says the jump is taken (or not), the way `Exit.way` gives is the exit's. -/
theorem way_sound {ee : ExecutionEnv} {env : Nat → UInt256} {e : Exit} {cond : Expr}
    {taken : Bool} {w : Way} (h : e.way cond taken = some w) {c : UInt256}
    (hc : cond.eval ee env = some c) (ht : (c.toNat != 0) = taken) (hv : e.Valid ee env) :
    w.Sound ee env e := by
  unfold Exit.way at h
  split at h
  next bc nz z =>
    split at h
    next kc k =>
      simp only [Expr.eval, Option.some.injEq] at hc
      subst hc
      rw [toNat_ofNat] at ht
      simp only [ht, BEq.rfl, ite_true, Option.some.injEq] at h
      subst h
      simp [Way.Sound, Exit.next, Expr.eval, toNat_ofNat]
      rfl
    next =>
      by_cases h1 : (cond == bc) = true
      · rw [ite_eq_left h1] at h
        cases h
        simp only [beq_iff_eq] at h1; subst h1
        simp only [Way.Sound, Exit.next, hc, Option.map_some, ht]
      rw [ite_eq_right h1] at h
      by_cases h2 : (cond == .op1 .ISZERO bc) = true
      · rw [ite_eq_left h2] at h
        cases h
        simp only [beq_iff_eq] at h2; subst h2
        cases hc' : bc.eval ee env with
        | none => simp [Expr.eval, hc'] at hc
        | some c' =>
        simp only [Expr.eval, hc', opEval, evalOp] at hc
        cases hc
        rw [isZero_toNat] at ht
        subst ht
        cases hz : c'.toNat == 0 <;> simp_all [Way.Sound, Exit.next]
      · rw [ite_eq_right h2] at h; cases h
  next sc default cases ruled =>
    obtain ⟨hcases, hruled⟩ := hv
    split at h
    next k hk =>
      obtain ⟨v, hv, hcv⟩ := caseOf_sound hk hc
      cases taken
      · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        refine ⟨rfl, hcases, fun v' hv' k' hk' => ?_⟩
        rcases List.mem_cons.mp hk' with rfl | hk'
        · rw [hv] at hv'; cases hv'; rw [ht] at hcv; simpa using hcv.symm
        · exact hruled v' hv' k' hk'
      · simp only [ite_true, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
        obtain ⟨d, ⟨hd, -⟩, rfl⟩ := h
        have hk' : k < UInt256.size := hcases (k, d) (mem_of_lookup hd)
        simp only [Way.Sound, Exit.next, hv, Option.map_some, Option.some.injEq]
        have : UInt256.ofNat k = v := by rw [ht] at hcv; simpa using hcv.symm
        rw [← this, find_ofNat hk' hcases, hd]
        rfl
    next => cases h
  next => simp at h

/-- The successor an exit has selected is where it goes. -/
theorem selected_sound {ee : ExecutionEnv} {env : Nat → UInt256} {e : Exit} {s d : Nat}
    (h : e.selected = some s) (hv : e.Valid ee env) (hn : e.next ee env = some d) : d = s := by
  cases e with
  | goto s' => simp_all [Exit.selected, Exit.next]
  | table sc default cases ruled =>
    simp only [Exit.selected] at h
    split_ifs at h with hall
    cases h
    simp only [Exit.next, Option.map_eq_some_iff] at hn
    obtain ⟨v, hsv, rfl⟩ := hn
    simp [find_ruled hall (hv.2 v hsv)]
  | _ => simp [Exit.selected] at h

/-! ## Value numbering -/

/-- Every expression of `k` has the word, under `ρ`, of the value it is or names. -/
def Canon.Valid (ee : ExecutionEnv) (ρ : Nat → UInt256) (k : Canon) : Prop :=
  (∀ p ∈ k.vals, p.2.eval ee ρ = some (ρ p.1)) ∧ ∀ p ∈ k.nodes, p.1.eval ee ρ = some (ρ p.2)

theorem Canon.valid_empty (ee : ExecutionEnv) (ρ : Nat → UInt256) :
    (⟨[], []⟩ : Canon).Valid ee ρ := ⟨by simp, by simp⟩

theorem Canon.Valid.expand {ee : ExecutionEnv} {ρ : Nat → UInt256} {k : Canon}
    (hv : k.Valid ee ρ) {id : Nat} {e : Expr} (h : k.expand id = some e) :
    e.eval ee ρ = some (ρ id) := by
  simp only [Canon.expand, Option.some.injEq] at h
  subst h
  cases hl : k.vals.lookup id with
  | none => rfl
  | some e' => simpa using hv.1 _ (mem_of_lookup hl)

theorem Canon.Valid.intern {ee : ExecutionEnv} {ρ : Nat → UInt256} {k : Canon}
    (hv : k.Valid ee ρ) {e : Expr} {x : UInt256} (h : e.eval ee ρ = some x) :
    (k.intern e).eval ee ρ = some x := by
  unfold Canon.intern
  cases hl : k.nodes.lookup e with
  | none => simpa using h
  | some w =>
    have := hv.2 _ (mem_of_lookup hl)
    simp only at this
    rw [this] at h
    simpa [Expr.eval] using h

end Fe.Sonatina.Check
