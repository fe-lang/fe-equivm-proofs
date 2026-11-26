import Fe.Sonatina.Steps.KnownBitsDemand

/-!
# Demanded-bits schemas (design §4.13, D1–D3)

`simplify_binary_with_demanded_bits` in `optim/known_bits_simplify.rs`: the result of
`and a b` (`or`, `xor`) becomes `a` when `b` changes only bits of the result no use reads, in
both operand orders (review H-7).  The conclusion is agreement on the demanded bits `d` of the
result, not equality (`Agree`): a `known_bits_simplify` round of these rewrites is checked in the
demanded-bits mode only (review C-2).

- D1: `and a b → a` when every demanded bit is known one in `b` (`d &&& (M ^^^ ko b) = 0`);
- D2, D3: `or a b → a`, `xor a b → a` when every demanded bit is known zero in `b`.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

variable {kb : Nat → KB} {ρ : Nat → Nat}

/-- No demanded bit is one `t` can clear (`changed` for `and`: `type_mask & !known_one`). -/
def dAnd (kb : Nat → KB) (d : Nat) (t : Term) : Bool := d &&& (M ^^^ ((t.fact kb).ko &&& M)) == 0

/-- No demanded bit is one `t` can set or flip (`type_mask & !known_zero`). -/
def dOr (kb : Nat → KB) (d : Nat) (t : Term) : Bool := d &&& (M ^^^ ((t.fact kb).kz &&& M)) == 0

/-- D1–D3, both operand orders. -/
def checkD (kb : Nat → KB) (d : Nat) : Term → Term → Bool
  | .op2 .and a b, r => (r == a && dAnd kb d b) || (r == b && dAnd kb d a)
  | .op2 .or a b, r | .op2 .xor a b, r => (r == a && dOr kb d b) || (r == b && dOr kb d a)
  | _, _ => false

theorem demanded_bit {d m i : Nat} (h : d &&& (M ^^^ (m &&& M)) = 0) (hd : d.testBit i = true)
    (hi : i < 256) : m.testBit i = true := by
  have := congrArg (·.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_xor, testBit_M, hi, decide_true, hd, Bool.true_and,
    Bool.and_true, Nat.zero_testBit] at this
  cases hm : m.testBit i <;> simp_all

theorem dAnd_sound (hf : FactsHold kb ρ) {d : Nat} {a b : Term} (h : dAnd kb d b = true) :
    Agree d (Op2.eval .and (a.eval ρ) (b.eval ρ)) (a.eval ρ) := by
  simp only [dAnd, beq_iff_eq] at h
  have hb := Term.fact_sat hf b
  have ha := Term.eval_lt ρ a
  apply agree_iff.mpr; intro i hi
  simp only [Op2.eval, Nat.testBit_and]
  by_cases hi' : i < 256
  · rw [hb.one (demanded_bit h hi hi'), Bool.and_true]
  · simp [testBit_hi (i := i) ha (by omega)]

theorem dOr_sound (hf : FactsHold kb ρ) {d : Nat} {a b : Term} (h : dOr kb d b = true) :
    Agree d (Op2.eval .or (a.eval ρ) (b.eval ρ)) (a.eval ρ) ∧
      Agree d (Op2.eval .xor (a.eval ρ) (b.eval ρ)) (a.eval ρ) := by
  simp only [dOr, beq_iff_eq] at h
  have hb := Term.fact_sat hf b
  have ha := Term.eval_lt ρ a
  have hbw := Term.eval_lt ρ b
  constructor
  · apply agree_iff.mpr; intro i hi
    simp only [Op2.eval, Nat.testBit_or]
    by_cases hi' : i < 256
    · rw [hb.zero (demanded_bit h hi hi'), Bool.or_false]
    · simp [testBit_hi (i := i) ha (by omega), testBit_hi (i := i) hbw (by omega)]
  · apply agree_iff.mpr; intro i hi
    simp only [Op2.eval, Nat.testBit_xor]
    by_cases hi' : i < 256
    · rw [hb.zero (demanded_bit h hi hi'), Bool.xor_false]
    · simp [testBit_hi (i := i) ha (by omega), testBit_hi (i := i) hbw (by omega)]

/-- Soundness of D1–D3: if the check passes and the atoms satisfy their known bits, the input
    and the output agree on the demanded bits `d`. -/
theorem checkD_sound (hf : FactsHold kb ρ) {d : Nat} {l r : Term} (h : checkD kb d l r = true) :
    Agree d (l.eval ρ) (r.eval ρ) := by
  unfold checkD at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hr, h⟩ | ⟨hr, h⟩ <;> rw [hr]
    · exact dAnd_sound hf h
    · have := dAnd_sound hf (a := b) (b := a) h
      simp only [Term.eval]; rw [Op2.eval, Nat.and_comm]; exact this
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hr, h⟩ | ⟨hr, h⟩ <;> rw [hr]
    · exact (dOr_sound hf h).1
    · have := (dOr_sound hf (a := b) (b := a) h).1
      simp only [Term.eval]; rw [Op2.eval, Nat.or_comm]; exact this
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hr, h⟩ | ⟨hr, h⟩ <;> rw [hr]
    · exact (dOr_sound hf h).2
    · have := (dOr_sound hf (a := b) (b := a) h).2
      simp only [Term.eval]; rw [Op2.eval, Nat.xor_comm]; exact this
  · cases h

end Fe.Sonatina.Steps.Schemas
