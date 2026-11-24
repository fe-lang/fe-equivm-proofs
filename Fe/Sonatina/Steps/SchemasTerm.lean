import Fe.Sonatina.Steps.EvalConst
import Fe.Sonatina.Steps.KnownBits

/-!
# Small terms over words

The term check of design §4.2 (E3) unfolds an instruction's definition to a small term and
compares it with the output's.  `Term` is that term (design §4.1: `atom v | lit w | op1 | op2 |
op3`, fixed arities so evaluation is structural).

- `Term.eval ρ`: its value, with `ρ v` the value of atom `v` (each reduced modulo `2 ^ 256`, so
  every value is a word without side conditions; the interpreter's `i256` values are words
  already, `Val.as`);
- `Term.fact kb`: its known bits, from the facts `kb v` of the atoms and the transfer functions,
  and `Term.fact_sat`: if every atom satisfies its fact (`FactsHold kb ρ`), the term satisfies
  its fact;
- `Term.const? kb`: the word the term's fact fixes, if any (`isC`);
- `Term.constEval`, `Term.fold`: constant evaluation (design "F") and constant folding, both
  sound for every environment.

A term with `clz` has the Osaka meaning of `clz`: a checker uses terms with `clz` only on Osaka
(review H-2).
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

inductive Term where
  | atom (v : Nat)
  | lit (w : Nat)
  | op1 (o : Op1) (a : Term)
  | op2 (o : Op2) (a b : Term)
  | op3 (o : Op3) (a b c : Term)
  deriving DecidableEq, Repr, Inhabited

namespace Term

def eval (ρ : Nat → Nat) : Term → Nat
  | .atom v => ρ v % W
  | .lit w => w % W
  | .op1 o a => o.eval (a.eval ρ)
  | .op2 o a b => o.eval (a.eval ρ) (b.eval ρ)
  | .op3 o a b c => o.eval (a.eval ρ) (b.eval ρ) (c.eval ρ)

theorem eval_lt (ρ : Nat → Nat) : ∀ t : Term, t.eval ρ < W
  | .atom _ => Nat.mod_lt _ (by decide)
  | .lit _ => Nat.mod_lt _ (by decide)
  | .op1 o a => Op1.eval_lt o (eval_lt ρ a)
  | .op2 o a b => Op2.eval_lt o (eval_lt ρ a) (eval_lt ρ b)
  | .op3 o _ _ c => Op3.eval_lt o (eval_lt ρ c)

theorem eval_mod (ρ : Nat → Nat) (t : Term) : t.eval ρ % W = t.eval ρ :=
  Nat.mod_eq_of_lt (eval_lt ρ t)

/-- The known bits of the term, from those of its atoms; a literal's are exact. -/
def fact (kb : Nat → KB) : Term → KB
  | .atom v => kb v
  | .lit w => exact (w % W)
  | .op1 o a => transfer1 o (a.fact kb)
  | .op2 o a b => transfer2 o (a.fact kb) (b.fact kb)
  | .op3 o a b c => transfer3 o (a.fact kb) (b.fact kb) (c.fact kb)

end Term

/-- Every atom's value satisfies its fact. -/
def FactsHold (kb : Nat → KB) (ρ : Nat → Nat) : Prop := ∀ v, (kb v).Sat (ρ v % W)

/-- The facts that know nothing hold everywhere. -/
theorem factsHold_unknown (ρ : Nat → Nat) : FactsHold (fun _ => unknown) ρ :=
  fun _ => sat_unknown _

namespace Term

theorem fact_sat {kb : Nat → KB} {ρ : Nat → Nat} (hf : FactsHold kb ρ) :
    ∀ t : Term, (t.fact kb).Sat (t.eval ρ)
  | .atom v => hf v
  | .lit _ => sat_exact (Nat.mod_lt _ (by decide))
  | .op1 o a => transfer1_sound o (eval_lt ρ a) (fact_sat hf a)
  | .op2 o a b => transfer2_sound o (eval_lt ρ a) (eval_lt ρ b) (fact_sat hf a) (fact_sat hf b)
  | .op3 o _ _ _ => transfer3_sound o _ _ _ _ _ _

/-- The word the term's known bits fix. -/
def const? (kb : Nat → KB) (t : Term) : Option Nat := (t.fact kb).exactVal?

theorem const?_eval {kb : Nat → KB} {ρ : Nat → Nat} (hf : FactsHold kb ρ) {t : Term} {n : Nat}
    (h : t.const? kb = some n) : t.eval ρ = n :=
  exactVal?_sat h (fact_sat hf t) (eval_lt ρ t)

/-- The term's value, if it has no atom. -/
def constEval : Term → Option Nat
  | .atom _ => none
  | .lit w => some (w % W)
  | .op1 o a => a.constEval.bind fun x => evalConst (.op1 o) [x]
  | .op2 o a b => a.constEval.bind fun x => b.constEval.bind fun y => evalConst (.op2 o) [x, y]
  | .op3 o a b c => a.constEval.bind fun x => b.constEval.bind fun y =>
      c.constEval.bind fun z => evalConst (.op3 o) [x, y, z]

theorem constEval_eval (ρ : Nat → Nat) : ∀ {t : Term} {n : Nat}, t.constEval = some n →
    t.eval ρ = n
  | .atom _, _, h => by cases h
  | .lit _, _, h => by simp only [constEval, Option.some.injEq] at h; exact h
  | .op1 o a, n, h => by
    simp only [constEval, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [evalConst] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp [eval, constEval_eval ρ hx]
    · cases h
  | .op2 o a b, n, h => by
    simp only [constEval, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    simp only [evalConst] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      simp [eval, constEval_eval ρ hx, constEval_eval ρ hy]
    · cases h
  | .op3 o a b c, n, h => by
    simp only [constEval, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, h⟩ := h
    simp only [evalConst] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      simp [eval, constEval_eval ρ hx, constEval_eval ρ hy, constEval_eval ρ hz]
    · cases h

/-- Constant folding: every subterm without an atom becomes the literal of its value. -/
def fold : Term → Term
  | .atom v => .atom v
  | .lit w => .lit (w % W)
  | .op1 o a =>
    match a.fold with
    | .lit x => .lit (o.eval (x % W))
    | a' => .op1 o a'
  | .op2 o a b =>
    match a.fold, b.fold with
    | .lit x, .lit y => .lit (o.eval (x % W) (y % W))
    | a', b' => .op2 o a' b'
  | .op3 o a b c =>
    match a.fold, b.fold, c.fold with
    | .lit x, .lit y, .lit z => .lit (o.eval (x % W) (y % W) (z % W))
    | a', b', c' => .op3 o a' b' c'

theorem fold_eval (ρ : Nat → Nat) : ∀ t : Term, t.fold.eval ρ = t.eval ρ
  | .atom _ => rfl
  | .lit _ => by simp [fold, eval]
  | .op1 o a => by
    have ha := fold_eval ρ a
    simp only [fold]
    split
    · next x hx =>
      rw [hx] at ha
      simp only [eval] at ha ⊢
      rw [ha]; exact Nat.mod_eq_of_lt (Op1.eval_lt o (eval_lt ρ a))
    · simp only [eval, ha]
  | .op2 o a b => by
    have ha := fold_eval ρ a
    have hb := fold_eval ρ b
    simp only [fold]
    split
    · next x y hx hy =>
      rw [hx] at ha; rw [hy] at hb
      simp only [eval] at ha hb ⊢
      rw [ha, hb]; exact Nat.mod_eq_of_lt (Op2.eval_lt o (eval_lt ρ a) (eval_lt ρ b))
    · simp only [eval, ha, hb]
  | .op3 o a b c => by
    have ha := fold_eval ρ a
    have hb := fold_eval ρ b
    have hc := fold_eval ρ c
    simp only [fold]
    split
    · next x y z hx hy hz =>
      rw [hx] at ha; rw [hy] at hb; rw [hz] at hc
      simp only [eval] at ha hb hc ⊢
      rw [ha, hb, hc]; exact Nat.mod_eq_of_lt (Op3.eval_lt o (eval_lt ρ c))
    · simp only [eval, ha, hb, hc]

end Term

/-! ## Tests the schemas use -/

/-- The term is known to be the word `n`: a literal, or a term whose known bits fix it. -/
def isC (kb : Nat → KB) (t : Term) (n : Nat) : Bool := t.const? kb == some n

theorem isC_eval {kb : Nat → KB} {ρ : Nat → Nat} (hf : FactsHold kb ρ) {t : Term} {n : Nat}
    (h : isC kb t n = true) : t.eval ρ = n :=
  Term.const?_eval hf (by simpa [isC] using h)

/-- The shift of a nontrivial power of two below `2 ^ 256`: `k` with `v = 2 ^ k`, `1 ≤ k < 256`
    (`nontrivial_pow2_shift`). -/
def pow2Shift? (v : Nat) : Option Nat :=
  if v = 2 ^ v.log2 ∧ 1 ≤ v.log2 ∧ v.log2 < 256 then some v.log2 else none

theorem pow2Shift?_eq {v k : Nat} (h : pow2Shift? v = some k) : v = 2 ^ k ∧ 1 ≤ k ∧ k < 256 := by
  unfold pow2Shift? at h
  split at h
  · next hc => simp only [Option.some.injEq] at h; subst h; exact hc
  · cases h

end Fe.Sonatina.Steps.Schemas
