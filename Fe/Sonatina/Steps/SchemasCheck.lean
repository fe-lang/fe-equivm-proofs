import Fe.Sonatina.Steps.SchemasG
import Fe.Sonatina.Steps.SchemasD

/-!
# The checker's entry points

What a checker calls, with hypotheses it can discharge (review 9):

- `Term.norm`: commutative normalization (operands of `add`, `mul`, `and`, `or`, `xor`, `eq`
  sorted, literals reduced modulo `2 ^ 256`), `Term.norm_eval`; `Term.commEq t u` is equality of
  normal forms, `Term.commEq_eval`.  GVN canonicalizes commutative operands by rank and replaces
  `add y x` by a dominating `add x y` (finding 3).  The entry points run each schema on the terms
  as given and on their folded normal forms, so every term comparison inside a schema is up to
  commutativity.
- `FactsOn kb ρ ts`: the facts hold for the atoms of the terms `ts` only (finding 5).  The
  schemas' internal lemmas assume facts for every value (`FactsHold`); the entry points run the
  schemas on the facts restricted to the atoms (`restrict`), for which `FactsOn` gives
  `FactsHold` (`factsHold_restrict`).  `factsOn_env` derives `FactsOn` from the invariant "every
  bound value satisfies its fact" and "every atom is bound to an `i256` word".
- `checkExact`, `checkDemand`, `checkBranchOn`, with `checkExact_sound`, `checkDemand_sound`,
  `checkBranchOn_sound`, `checkBranchOn_target`.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

/-! ## Commutative normalization -/

/-- The commutative operations, as `is_commutative_binary` on machine IR. -/
def Op2.comm : Op2 → Bool
  | .add | .mul | .and | .or | .xor | .eq => true
  | _ => false

theorem Op2.eval_comm {o : Op2} (h : o.comm = true) (x y : Nat) : o.eval x y = o.eval y x := by
  cases o <;> simp only [Op2.comm, reduceCtorEq] at h <;> simp only [Op2.eval]
  · rw [Nat.add_comm]
  · rw [Nat.mul_comm]
  · rw [Nat.and_comm]
  · rw [Nat.or_comm]
  · rw [Nat.xor_comm]
  · by_cases hxy : x = y
    · rw [hxy]
    · have h1 : (x == y) = false := by simpa using hxy
      have h2 : (y == x) = false := by simpa using Ne.symm hxy
      rw [h1, h2]

def Op1.idx : Op1 → Nat
  | .not => 0 | .isZero => 1 | .clz => 2

def Op2.idx : Op2 → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .udiv => 3 | .sdiv => 4 | .umod => 5 | .smod => 6
  | .exp => 7 | .shl => 8 | .shr => 9 | .sar => 10 | .and => 11 | .or => 12 | .xor => 13
  | .byte => 14 | .signextend => 15 | .lt => 16 | .gt => 17 | .slt => 18 | .sgt => 19 | .eq => 20

def Op3.idx : Op3 → Nat
  | .addmod => 0 | .mulmod => 1

/-- The term in prefix order: fixed arities make it a unique code. -/
def Term.code : Term → List Nat
  | .atom v => [0, v]
  | .lit w => [1, w]
  | .op1 o a => [2, o.idx] ++ a.code
  | .op2 o a b => [3, o.idx] ++ a.code ++ b.code
  | .op3 o a b c => [4, o.idx] ++ a.code ++ b.code ++ c.code

/-- Lexicographic order on codes. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLe as bs

namespace Term

/-- Literals reduced modulo `2 ^ 256`, operands of commutative operations in code order. -/
def norm : Term → Term
  | .atom v => .atom v
  | .lit w => .lit (w % W)
  | .op1 o a => .op1 o a.norm
  | .op2 o a b =>
    if o.comm && !lexLe a.norm.code b.norm.code then .op2 o b.norm a.norm
    else .op2 o a.norm b.norm
  | .op3 o a b c => .op3 o a.norm b.norm c.norm

theorem norm_eval (ρ : Nat → Nat) : ∀ t : Term, t.norm.eval ρ = t.eval ρ
  | .atom _ => rfl
  | .lit _ => by simp [norm, eval]
  | .op1 o a => by simp only [norm, eval, norm_eval ρ a]
  | .op2 o a b => by
    simp only [norm]
    split
    · next h =>
      simp only [Bool.and_eq_true] at h
      simp only [eval, norm_eval ρ a, norm_eval ρ b]
      exact Op2.eval_comm h.1 _ _
    · simp only [eval, norm_eval ρ a, norm_eval ρ b]
  | .op3 o a b c => by simp only [norm, eval, norm_eval ρ a, norm_eval ρ b, norm_eval ρ c]

/-- Equality up to commutativity of `add`, `mul`, `and`, `or`, `xor`, `eq`. -/
def commEq (t u : Term) : Bool := t.norm == u.norm

theorem commEq_eval (ρ : Nat → Nat) {t u : Term} (h : commEq t u = true) :
    t.eval ρ = u.eval ρ := by
  simp only [commEq, beq_iff_eq] at h
  rw [← norm_eval ρ t, h, norm_eval]

/-- The folded normal form. -/
def nf (t : Term) : Term := t.fold.norm

theorem nf_eval (ρ : Nat → Nat) (t : Term) : t.nf.eval ρ = t.eval ρ := by
  rw [nf, norm_eval, fold_eval]

/-- The term has atom `v`. -/
def hasAtom (v : Nat) : Term → Bool
  | .atom u => u == v
  | .lit _ => false
  | .op1 _ a => a.hasAtom v
  | .op2 _ a b => a.hasAtom v || b.hasAtom v
  | .op3 _ a b c => a.hasAtom v || b.hasAtom v || c.hasAtom v

/-- The term has `clz`, whose meaning here is Osaka's (review 9, finding 8). -/
def hasClz : Term → Bool
  | .atom _ | .lit _ => false
  | .op1 o a => o == .clz || a.hasClz
  | .op2 _ a b => a.hasClz || b.hasClz
  | .op3 _ a b c => a.hasClz || b.hasClz || c.hasClz

end Term

/-! ## Facts on the atoms only -/

/-- The facts of the atoms of `ts` hold. -/
def FactsOn (kb : Nat → KB) (ρ : Nat → Nat) (ts : List Term) : Prop :=
  ∀ v, ts.any (·.hasAtom v) = true → (kb v).Sat (ρ v % W)

/-- The facts of the atoms of `ts`, unknown elsewhere. -/
def restrict (kb : Nat → KB) (ts : List Term) : Nat → KB :=
  fun v => if ts.any (·.hasAtom v) then kb v else unknown

theorem factsHold_restrict {kb : Nat → KB} {ρ : Nat → Nat} {ts : List Term}
    (h : FactsOn kb ρ ts) : FactsHold (restrict kb ts) ρ := by
  intro v
  unfold restrict
  split
  · next hv => exact h v hv
  · exact sat_unknown _

/-- The word an environment binds a value to (0 if it binds none). -/
def envWord (env : Env) (v : Nat) : Nat :=
  match env[v]? with
  | some (.int _ x) => x
  | _ => 0

/-- From the known-bits invariant (every value bound to an `i256` word satisfies its fact) and
    every atom of `ts` bound to an `i256` word: the facts of the atoms hold in `envWord env`. -/
theorem factsOn_env {env : Env} {kb : Nat → KB} {ts : List Term}
    (hinv : ∀ v x, env[v]? = some (.int 256 x) → (kb v).Sat x)
    (hbound : ∀ v, ts.any (·.hasAtom v) = true → ∃ x, env[v]? = some (.int 256 x) ∧ x < W) :
    FactsOn kb (envWord env) ts := by
  intro v hv
  obtain ⟨x, hx, hlt⟩ := hbound v hv
  have : envWord env v = x := by simp [envWord, hx]
  rw [this, Nat.mod_eq_of_lt hlt]
  exact hinv v x hx

/-- An atom bound to an `i256` word evaluates to it. -/
theorem eval_atom_env {env : Env} {v x : Nat} (hx : env[v]? = some (.int 256 x)) (hlt : x < W) :
    (Term.atom v).eval (envWord env) = x := by
  simp [Term.eval, envWord, hx, Nat.mod_eq_of_lt hlt]

/-! ## Entry points -/

/-- Exact mode: `T_in` and `T_out` have one value.  Folded normal forms equal (F and commutative
    equality), or an identity, `scalar_canonicalize` or GVN schema on the terms or on their
    folded normal forms. -/
def checkExact (kb : Nat → KB) (l r : Term) : Bool :=
  let k := restrict kb [l, r]
  l.nf == r.nf || checkI k l r || checkS k l r || checkG k l r ||
    checkI k l.nf r.nf || checkS k l.nf r.nf || checkG k l.nf r.nf

theorem exact_any {k : Nat → KB} {ρ : Nat → Nat} (hf : FactsHold k ρ) {l r : Term}
    (h : (checkI k l r || checkS k l r || checkG k l r) = true) : l.eval ρ = r.eval ρ := by
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact checkI_sound hf h
  · exact checkS_sound hf h
  · exact checkG_sound hf h

theorem checkExact_sound {kb : Nat → KB} {ρ : Nat → Nat} {l r : Term}
    (h : checkExact kb l r = true) (hf : FactsOn kb ρ [l, r]) : l.eval ρ = r.eval ρ := by
  have hk := factsHold_restrict hf
  unfold checkExact at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · rw [← Term.nf_eval ρ l, h, Term.nf_eval]
  · exact checkI_sound hk h
  · exact checkS_sound hk h
  · exact checkG_sound hk h
  · rw [← Term.nf_eval ρ l, ← Term.nf_eval ρ r]; exact checkI_sound hk h
  · rw [← Term.nf_eval ρ l, ← Term.nf_eval ρ r]; exact checkS_sound hk h
  · rw [← Term.nf_eval ρ l, ← Term.nf_eval ρ r]; exact checkG_sound hk h

/-- Demanded-bits mode (D1–D3): `T_in` and `T_out` agree on the demanded bits `d`. -/
def checkDemand (kb : Nat → KB) (d : Nat) (l r : Term) : Bool :=
  let k := restrict kb [l, r]
  checkD k d l r || checkD k d l.nf r.nf

theorem checkDemand_sound {kb : Nat → KB} {ρ : Nat → Nat} {d : Nat} {l r : Term}
    (h : checkDemand kb d l r = true) (hf : FactsOn kb ρ [l, r]) :
    Agree d (l.eval ρ) (r.eval ρ) := by
  have hk := factsHold_restrict hf
  unfold checkDemand at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact checkD_sound hk h
  · have := checkD_sound hk h
    rwa [Term.nf_eval, Term.nf_eval] at this

/-- A branch on `c'` stands for a branch on `c`, the targets swapped if `swap` (B1–B3). -/
def checkBranchOn (kb : Nat → KB) (c c' : Term) (swap : Bool) : Bool :=
  let k := restrict kb [c, c']
  checkBranch k c c' swap || checkBranch k c.nf c'.nf swap

theorem checkBranchOn_sound {kb : Nat → KB} {ρ : Nat → Nat} {c c' : Term} {swap : Bool}
    (h : checkBranchOn kb c c' swap = true) (hf : FactsOn kb ρ [c, c']) :
    truthy (c'.eval ρ) = (truthy (c.eval ρ) ^^ swap) := by
  have hk := factsHold_restrict hf
  unfold checkBranchOn at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact checkBranch_sound hk h
  · have := checkBranch_sound hk h
    rwa [Term.nf_eval, Term.nf_eval] at this

theorem checkBranchOn_target {kb : Nat → KB} {ρ : Nat → Nat} {c c' : Term} {swap : Bool}
    (h : checkBranchOn kb c c' swap = true) (hf : FactsOn kb ρ [c, c']) (nz z : Nat) :
    branchTarget (c.eval ρ) nz z =
      if swap then branchTarget (c'.eval ρ) z nz else branchTarget (c'.eval ρ) nz z := by
  have := checkBranchOn_sound h hf
  unfold branchTarget
  simp only [truthy] at this
  cases swap <;> cases h1 : (c.eval ρ != 0) <;> cases h2 : (c'.eval ρ != 0) <;>
    simp_all

end Fe.Sonatina.Steps.Schemas
