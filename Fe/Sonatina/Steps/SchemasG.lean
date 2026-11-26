import Fe.Sonatina.Steps.SchemasS

/-!
# GVN schemas (G2–G6) and branch truthiness (B1–B3)

**GVN** (`optim/gvn.rs`, `perform_simplification` and the simplifications after it):
- G2 `simplify_sub_add_cancellation`: `sub (add a b) c → a` when `c` is `b`, `→ b` when `c` is
  `a` (`subAdd`);
- G3 `simplify_add_sub_cancellation`: `add (sub a b) c`, `add c (sub a b) → a` when `c` is `b`
  (`addSub`);
- G4 `eq x 0`, `eq 0 x ≅ is_zero x` (`eqZero`, as S9);
- G6 `mul (2 ^ k) x`, `mul x (2 ^ k) ≅ shl k x`, `1 ≤ k < 256` (`mulPow2`, as S11).
GVN compares through congruence classes: a checker gives the terms with each class member
replaced by its representative, so "`c` is `b`" is equality of terms.  G5 (`neg`) is not
machine IR; G7 (a phi whose incoming values are all one value) is not a word identity.

**Branches** (`optim/branch_canonicalize.rs`, `machine/branch.rs`): a branch goes to its first
target if its condition is not zero (`Term.br` in `Interp.lean`).  `checkBranch c c' swap`
accepts the output condition `c'` for the input condition `c`, swapping the targets if `swap`:
`c = is_zero^k c₀` (B1) and either `c' = c₀`, swapping iff `k` is odd, or `c' = is_zero x` with
`c₀` one of `eq x 0`, `eq 0 x` (B2, swapping iff `k` is odd) or `gt x 0`, `lt 0 x` (B3,
swapping iff `k` is even), as review M-3 corrects design §4.4.  In machine IR every value is an
`i256`, so the Rust peels `is_zero` only (it peels `not` of an `i1`, which machine IR does not
have), and it never inverts a comparison (`lt`, `gt`, `slt`, `sgt`, `eq` cost 0).
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

variable {kb : Nat → KB} {ρ : Nat → Nat}

/-- `sub (add a b) c → a` if `c = b`; `→ b` if `c = a` (G2). -/
def subAdd : Term → Term → Bool
  | .op2 .sub (.op2 .add a b) c, r => (c == b && r == a) || (c == a && r == b)
  | _, _ => false

def addSubHalf : Term → Term → Term → Bool
  | .op2 .sub a b, c, r => c == b && r == a
  | _, _, _ => false

/-- `add (sub a b) c`, `add c (sub a b) → a` if `c = b` (G3). -/
def addSub : Term → Term → Bool
  | .op2 .add x y, r => addSubHalf x y r || addSubHalf y x r
  | _, _ => false

/-- All the GVN schemas.  G4 and G6 put both forms in one class, and GVN replaces whichever
    comes later by whichever dominates, so both directions (review 9, finding 3). -/
def checkG (kb : Nat → KB) (l r : Term) : Bool :=
  subAdd l r || addSub l r || eqZero kb l r || eqZero kb r l || mulPow2 kb l r ||
    mulPow2 kb r l

theorem add_sub_words {a b : Nat} (ha : a < W) (hb : b < W) :
    Op2.eval .add (Op2.eval .sub a b) b = a ∧ Op2.eval .add b (Op2.eval .sub a b) = a ∧
      Op2.eval .sub (Op2.eval .add a b) b = a ∧ Op2.eval .sub (Op2.eval .add a b) a = b := by
  simp only [Op2.eval]; simp only [W] at *; omega

theorem subAdd_sound {l r : Term} (h : subAdd l r = true) : l.eval ρ = r.eval ρ := by
  unfold subAdd at h
  split at h
  · next a b c =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (add_sub_words (Term.eval_lt ρ _) (Term.eval_lt ρ _)).2.2.1
    · exact (add_sub_words (Term.eval_lt ρ _) (Term.eval_lt ρ _)).2.2.2
  · cases h

theorem addSubHalf_sound {x y r : Term} (h : addSubHalf x y r = true) :
    Op2.eval .add (x.eval ρ) (y.eval ρ) = r.eval ρ ∧
      Op2.eval .add (y.eval ρ) (x.eval ρ) = r.eval ρ := by
  unfold addSubHalf at h
  split at h
  · next a b c =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := add_sub_words (Term.eval_lt ρ r) (Term.eval_lt ρ y)
    exact ⟨this.1, this.2.1⟩
  · cases h

theorem addSub_sound {l r : Term} (h : addSub l r = true) : l.eval ρ = r.eval ρ := by
  unfold addSub at h
  split at h
  · next x y =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact (addSubHalf_sound h).1
    · exact (addSubHalf_sound h).2
  · cases h

theorem checkG_sound (hf : FactsHold kb ρ) {l r : Term} (h : checkG kb l r = true) :
    l.eval ρ = r.eval ρ := by
  simp only [checkG, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact subAdd_sound h
  · exact addSub_sound h
  · exact eqZero_sound hf h
  · exact (eqZero_sound hf h).symm
  · exact mulPow2_sound hf h
  · exact (mulPow2_sound hf h).symm

/-! ## Branches -/

/-- A condition sends a branch to its first target. -/
def truthy (w : Nat) : Bool := w != 0

/-- `c = is_zero^k c₀`: the number of `is_zero`s and `c₀`. -/
def peelIsZero : Term → Nat × Term
  | .op1 .isZero t => ((peelIsZero t).1 + 1, (peelIsZero t).2)
  | t => (0, t)

/-- `zero_compare_branch_rewrite`: `c₀` is `eq x 0` or `eq 0 x` (`is_zero x`, no swap) or
    `gt x 0` or `lt 0 x` (its negation, a swap). -/
def zeroCmp (kb : Nat → KB) (c₀ x : Term) : Option Bool :=
  match c₀ with
  | .op2 .eq a b => if (isC kb b 0 && a == x) || (isC kb a 0 && b == x) then some false else none
  | .op2 .gt a b => if isC kb b 0 && a == x then some true else none
  | .op2 .lt a b => if isC kb a 0 && b == x then some true else none
  | _ => none

/-- The output condition `c'` stands for the input condition `c`, with the targets swapped if
    `swap` (B1–B3, as review M-3 states them). -/
def checkBranch1 (kb : Nat → KB) (c c' : Term) (swap : Bool) : Bool :=
  let odd := (peelIsZero c).1 % 2 == 1
  (c' == (peelIsZero c).2 && swap == odd) ||
    match c' with
    | .op1 .isZero x =>
      match zeroCmp kb (peelIsZero c).2 x with
      | some s => swap == (odd ^^ s)
      | none => false
    | _ => false

/-- B1–B3 with `is_zero` peeled from both conditions: `branch_conditions` strips one `is_zero`
    (`br (is_zero a) nz z → br a z nz`), which leaves `c'` an `is_zero` when `c` had two, and
    composed forms (review 9, finding 6). -/
def checkBranch2 (kb : Nat → KB) (c c' : Term) (swap : Bool) : Bool :=
  let odd := ((peelIsZero c).1 + (peelIsZero c').1) % 2 == 1
  ((peelIsZero c').2 == (peelIsZero c).2 && swap == odd) ||
    match zeroCmp kb (peelIsZero c).2 (peelIsZero c').2 with
    | some s => swap == (odd ^^ !s)
    | none => false

def checkBranch (kb : Nat → KB) (c c' : Term) (swap : Bool) : Bool :=
  checkBranch1 kb c c' swap || checkBranch2 kb c c' swap

theorem odd_add (k k' : Nat) : ((k + k') % 2 == 1) = ((k % 2 == 1) ^^ (k' % 2 == 1)) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one k' with h' | h' <;>
    simp [h, h', Nat.add_mod]

theorem truthy_isZero (x : Nat) : truthy (Op1.eval .isZero x) = !truthy x := by
  by_cases h : x = 0 <;> simp [truthy, Op1.eval, ofBool, h]

theorem peelIsZero_sound (ρ : Nat → Nat) : ∀ c : Term,
    truthy (c.eval ρ) = (truthy ((peelIsZero c).2.eval ρ) ^^ ((peelIsZero c).1 % 2 == 1))
  | .op1 .isZero t => by
    have ih := peelIsZero_sound ρ t
    simp only [peelIsZero, Term.eval]
    rw [truthy_isZero, ih]
    rcases Nat.mod_two_eq_zero_or_one (peelIsZero t).1 with h | h
    · have h' : ((peelIsZero t).1 + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : ((peelIsZero t).1 + 1) % 2 = 0 := by omega
      simp [h, h']
  | .atom _ | .lit _ | .op1 .not _ | .op1 .clz _ | .op2 _ _ _ | .op3 _ _ _ _ => by
    simp [peelIsZero]

theorem zeroCmp_sound (hf : FactsHold kb ρ) {c₀ x : Term} {s : Bool}
    (h : zeroCmp kb c₀ x = some s) : truthy (c₀.eval ρ) = (truthy ((Term.op1 .isZero x).eval ρ) ^^ s) := by
  unfold zeroCmp at h
  split at h
  · next a b =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Term.eval, Bool.xor_false]
      rcases hc with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · rw [isC_eval hf h1]; rfl
      · rw [isC_eval hf h1]
        by_cases h0 : b.eval ρ = 0
        · rw [h0]; rfl
        · have e1 : (0 == b.eval ρ) = false := by simpa using Ne.symm h0
          have e2 : (b.eval ρ == 0) = false := by simpa using h0
          simp only [Op2.eval, Op1.eval, e1, e2]
    · cases h
  · next a b =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨h1, rfl⟩ := hc
      simp only [Term.eval, isC_eval hf h1]
      by_cases h0 : a.eval ρ = 0 <;> simp [truthy, Op2.eval, Op1.eval, ofBool, h0] <;> omega
    · cases h
  · next a b =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨h1, rfl⟩ := hc
      simp only [Term.eval, isC_eval hf h1]
      by_cases h0 : b.eval ρ = 0 <;> simp [truthy, Op2.eval, Op1.eval, ofBool, h0] <;> omega
    · cases h
  · cases h

/-- Soundness of the branch check: the output condition is truthy exactly when the input one
    is, unless the targets are swapped. -/
theorem checkBranch1_sound (hf : FactsHold kb ρ) {c c' : Term} {swap : Bool}
    (h : checkBranch1 kb c c' swap = true) :
    truthy (c'.eval ρ) = (truthy (c.eval ρ) ^^ swap) := by
  have hp := peelIsZero_sound ρ c
  unfold checkBranch1 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | h
  · rw [hp, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · split at h
    · next x =>
      split at h
      · next s hs =>
        simp only [beq_iff_eq] at h; subst h
        rw [hp, zeroCmp_sound hf hs]
        cases truthy ((Term.op1 .isZero x).eval ρ) <;> cases s <;>
          cases ((peelIsZero c).1 % 2 == 1) <;> rfl
      · cases h
    · cases h

theorem checkBranch2_sound (hf : FactsHold kb ρ) {c c' : Term} {swap : Bool}
    (h : checkBranch2 kb c c' swap = true) :
    truthy (c'.eval ρ) = (truthy (c.eval ρ) ^^ swap) := by
  have hp := peelIsZero_sound ρ c
  have hp' := peelIsZero_sound ρ c'
  unfold checkBranch2 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rw [hp, hp']
  rcases h with ⟨he, rfl⟩ | h
  · rw [he, odd_add]
    cases truthy ((peelIsZero c).2.eval ρ) <;> cases ((peelIsZero c).1 % 2 == 1) <;>
      cases ((peelIsZero c').1 % 2 == 1) <;> rfl
  · split at h
    · next s hs =>
      simp only [beq_iff_eq] at h; subst h
      have hz := zeroCmp_sound hf hs
      simp only [Term.eval, truthy_isZero] at hz
      rw [hz, odd_add]
      cases truthy ((peelIsZero c').2.eval ρ) <;> cases s <;>
        cases ((peelIsZero c).1 % 2 == 1) <;> cases ((peelIsZero c').1 % 2 == 1) <;> rfl
    · cases h

theorem checkBranch_sound (hf : FactsHold kb ρ) {c c' : Term} {swap : Bool}
    (h : checkBranch kb c c' swap = true) :
    truthy (c'.eval ρ) = (truthy (c.eval ρ) ^^ swap) := by
  simp only [checkBranch, Bool.or_eq_true] at h
  rcases h with h | h
  · exact checkBranch1_sound hf h
  · exact checkBranch2_sound hf h

/-- The block a branch goes to, as `runBlocks` picks it. -/
def branchTarget (w nz z : Nat) : Nat := if w != 0 then nz else z

/-- A branch on `c` to `nz`, `z` goes where the branch on `c'` goes, to the targets swapped if
    `swap`. -/
theorem checkBranch_target (hf : FactsHold kb ρ) {c c' : Term} {swap : Bool}
    (h : checkBranch kb c c' swap = true) (nz z : Nat) :
    branchTarget (c.eval ρ) nz z =
      if swap then branchTarget (c'.eval ρ) z nz else branchTarget (c'.eval ρ) nz z := by
  have := checkBranch_sound hf h
  unfold branchTarget
  simp only [truthy] at this
  cases swap <;> cases h1 : (c.eval ρ != 0) <;> cases h2 : (c'.eval ρ != 0) <;>
    simp_all

end Fe.Sonatina.Steps.Schemas
