import Fe.Sonatina.Steps.SchemasTerm

/-!
# Identities (design §4.13, I1–I21)

The identities of `optim/simplify_expr.rs` that apply to machine IR: `simplify_binary_with_facts`
(with `undo_inverse_shift`, `simplify_and_copy_with_facts`, `simplify_or_copy_with_facts`,
`simplify_evm_signextend_copy_with_facts`), the partial folds `simplify_evm_exp_known`,
`simplify_evm_byte_known`, `simplify_evm_signextend_known`, `simplify_evm_modop_known`, and
`simplify_unary_with_same_inner`.  `sccp_fold`, `known_bits_simplify` and GVN use them.

Each schema is a check `kb → T_in → T_out → Bool` with its soundness lemma: if the check
passes and the atoms satisfy their known bits (`FactsHold kb ρ`), the two terms have one value.
Where the Rust asks for an immediate (`known_imm`), the check asks that the term be known to be
that word (`isC`: a literal, or a term whose known bits fix it), which accepts at least what the
Rust rewrites.  Where the Rust compares value ids (`lhs == rhs`), the check compares terms.

I6 (`simplify_low_mask_copy_with_range`) needs range facts and is not here.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

variable {kb : Nat → KB} {ρ : Nat → Nat}

/-! ## Word lemmas -/

section Words

variable {x y : Nat}

theorem and_M (hx : x < W) : x &&& M = x := by
  rw [show M = 2 ^ 256 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem M_and (hx : x < W) : M &&& x = x := by rw [Nat.and_comm, and_M hx]

theorem or_M (hx : x < W) : x ||| M = M := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, testBit_M]
  by_cases hi : i < 256
  · simp [hi]
  · simp [hi, testBit_hi (i := i) hx (by omega)]

theorem M_or (hx : x < W) : M ||| x = M := by rw [Nat.or_comm, or_M hx]

theorem wrap_signed (hx : x < W) : wrap 256 (signed 256 x) = x := by
  by_cases h : x < 2 ^ 255
  · rw [signed_of_lt h, wrap_natCast, Nat.mod_eq_of_lt hx]
  · rw [signed_of_ge h]; unfold wrap; simp only [W] at hx; omega

theorem signed_one : signed 256 1 = 1 := by rw [signed_of_lt (by decide)]; rfl

theorem not_lt_signed_self (x : Nat) : ¬ signed 256 x < signed 256 x := Int.lt_irrefl _

theorem shlW_zero_left (hy : y < W) : shlW 0 y = y := by
  simp [shlW, Nat.mod_eq_of_lt hy]

theorem shrW_zero_left : shrW 0 y = y := by simp [shrW]

theorem sarW_zero_left (hy : y < W) : sarW 0 y = y := by
  unfold sarW; split
  · exact shrW_zero_left
  · rw [shrW_zero_left]; simp only [M, W] at *; omega

theorem shlW_zero_right (s : Nat) : shlW s 0 = 0 := by simp [shlW]

theorem shrW_zero_right (s : Nat) : shrW s 0 = 0 := by simp [shrW]

theorem sarW_zero_right (s : Nat) : sarW s 0 = 0 := by
  simp [sarW, shrW_zero_right]

theorem testBit_shlW' {s y i : Nat} (hi : i < 256) :
    (shlW s y).testBit i = (decide (s ≤ i) && y.testBit (i - s)) := by
  by_cases hs : s < 256
  · exact testBit_shlW hs hi
  · rw [shlW, if_pos (by omega)]; simp; omega

theorem testBit_shrW' {s y i : Nat} (hy : y < W) :
    (shrW s y).testBit i = (decide (s < 256) && y.testBit (s + i)) := by
  by_cases hs : s < 256
  · rw [testBit_shrW hs]; simp [hs]
  · rw [shrW, if_pos (by omega)]; simp [hs]

theorem shrW_lt {s y : Nat} (hy : y < W) : shrW s y < W := lt_of_le_of_lt (shrW_le _ _) hy

theorem shlW_lt (s y : Nat) : shlW s y < W := by
  unfold shlW; split
  · decide
  · exact Nat.mod_lt _ (by decide)

end Words

/-! ## The schemas -/

/-- `add 0 x → x`, `add x 0 → x` (I1). -/
def schemaAdd (kb : Nat → KB) : Term → Term → Bool
  | .op2 .add a b, r => (isC kb a 0 && r == b) || (isC kb b 0 && r == a)
  | _, _ => false

/-- `sub x x → 0`, `sub x 0 → x` (I2). -/
def schemaSub (kb : Nat → KB) : Term → Term → Bool
  | .op2 .sub a b, r => (a == b && isC kb r 0) || (isC kb b 0 && r == a)
  | _, _ => false

/-- `mul 0 _ → 0`, `mul _ 0 → 0`, `mul 1 x → x`, `mul x 1 → x` (I3). -/
def schemaMul (kb : Nat → KB) : Term → Term → Bool
  | .op2 .mul a b, r =>
    ((isC kb a 0 || isC kb b 0) && isC kb r 0) || (isC kb a 1 && r == b) || (isC kb b 1 && r == a)
  | _, _ => false

/-- `simplify_and_copy_with_facts value mask`: `and value mask → value` when `value` is known
    zero at every bit `mask` clears (I5). -/
def andCopy (kb : Nat → KB) (value mask : Term) : Bool :=
  match mask.const? kb with
  | some m => (value.fact kb).allZero (M ^^^ m)
  | none => false

/-- `simplify_or_copy_with_facts value mask`: `or value mask → value` when `value` is known one
    at every bit `mask` sets (I8). -/
def orCopy (kb : Nat → KB) (value mask : Term) : Bool :=
  match mask.const? kb with
  | some m => (value.fact kb).allOne m
  | none => false

/-- `and 0 _ → 0`, `and _ 0 → 0`, `and -1 x → x`, `and x -1 → x`, `and x x → x` (I4), and
    I5 in both operand orders. -/
def schemaAnd (kb : Nat → KB) : Term → Term → Bool
  | .op2 .and a b, r =>
    ((isC kb a 0 || isC kb b 0) && isC kb r 0) || (isC kb a M && r == b) || (isC kb b M && r == a)
      || (r == a && andCopy kb a b) || (r == b && andCopy kb b a) || (a == b && r == a)
  | _, _ => false

/-- `or -1 _ → -1`, `or _ -1 → -1`, `or 0 x → x`, `or x 0 → x`, `or x x → x` (I7), and I8 in
    both operand orders. -/
def schemaOr (kb : Nat → KB) : Term → Term → Bool
  | .op2 .or a b, r =>
    ((isC kb a M || isC kb b M) && isC kb r M) || (isC kb a 0 && r == b) || (isC kb b 0 && r == a)
      || (r == a && orCopy kb a b) || (r == b && orCopy kb b a) || (a == b && r == a)
  | _, _ => false

/-- `xor 0 x → x`, `xor x 0 → x`, `xor x x → 0` (I9). -/
def schemaXor (kb : Nat → KB) : Term → Term → Bool
  | .op2 .xor a b, r => (isC kb a 0 && r == b) || (isC kb b 0 && r == a) || (a == b && isC kb r 0)
  | _, _ => false

/-- `evm_udiv x 1 → x`, `evm_sdiv x 1 → x` (I10); `evm_umod x 1 → 0`, `evm_smod x 1 → 0`
    (I11). -/
def schemaDiv (kb : Nat → KB) : Term → Term → Bool
  | .op2 .udiv a b, r | .op2 .sdiv a b, r => isC kb b 1 && r == a
  | .op2 .umod _ b, r | .op2 .smod _ b, r => isC kb b 1 && isC kb r 0
  | _, _ => false

/-- `eq x x → 1`; `eq x y → 0` when the known bits of `x` and `y` conflict (I12). -/
def schemaEq (kb : Nat → KB) : Term → Term → Bool
  | .op2 .eq a b, r => (a == b && isC kb r 1) || (conflict (a.fact kb) (b.fact kb) && isC kb r 0)
  | _, _ => false

/-- `lt x x`, `gt x x`, `slt x x`, `sgt x x → 0`; `gt 0 x → 0`; `lt x 0 → 0` (I13). -/
def schemaCmp (kb : Nat → KB) : Term → Term → Bool
  | .op2 .lt a b, r => (a == b || isC kb b 0) && isC kb r 0
  | .op2 .gt a b, r => (a == b || isC kb a 0) && isC kb r 0
  | .op2 .slt a b, r | .op2 .sgt a b, r => a == b && isC kb r 0
  | _, _ => false

/-- The shift amount is known to be at least 256. -/
def countGe256 (kb : Nat → KB) (c : Term) : Bool :=
  match c.const? kb with
  | some n => decide (256 ≤ n)
  | none => false

/-- `undo_inverse_shift`: `shr c (shl c x) → x` when the top `c` bits of `x` are known zero, and
    `shl c (shr c x) → x` when its low `c` bits are, for `c < 256` (I15, review H-7). -/
def undoShift (kb : Nat → KB) : Term → Term → Bool
  | .op2 .shr c (.op2 .shl c' x), r =>
    r == x && match c.const? kb, c'.const? kb with
      | some n, some n' => n == n' && decide (n < 256) && (x.fact kb).allZero (M ^^^ (M >>> n))
      | _, _ => false
  | .op2 .shl c (.op2 .shr c' x), r =>
    r == x && match c.const? kb, c'.const? kb with
      | some n, some n' => n == n' && decide (n < 256) && (x.fact kb).allZero (lowMask n)
      | _, _ => false
  | _, _ => false

/-- `shl`/`shr`/`sar` of a zero value `→ 0`, by a zero amount `→` the value; `shl`/`shr` by 256
    or more `→ 0` (I14); and `undo_inverse_shift` (I15). -/
def schemaShift (kb : Nat → KB) : Term → Term → Bool
  | l@(.op2 o a b), r =>
    (o == .shl || o == .shr || o == .sar) &&
      ((isC kb b 0 && isC kb r 0) || (isC kb a 0 && r == b)
        || (o != .sar && countGe256 kb a && isC kb r 0) || undoShift kb l r)
  | _, _ => false

/-- `simplify_evm_signextend_copy_with_facts byte value`: `signextend byte value → value` for a
    byte of 31 or more, or when the sign bit and every bit above it are known alike (I17). -/
def signextendCopy (kb : Nat → KB) (byte value : Term) : Bool :=
  match byte.const? kb with
  | some n =>
    if 32 ≤ n then true
    else if 256 ≤ (n + 1) * 8 then true
    else
      let f := value.fact kb
      let sign := 2 ^ ((n + 1) * 8 - 1)
      let high := M ^^^ lowMask ((n + 1) * 8)
      (f.allZero sign && f.allZero high) || (f.allOne sign && f.allOne high)
  | none => false

/-- `signextend _ 0 → 0` (I16), I17; `exp _ 0 → 1`, `exp 1 _ → 1`, `exp 0 e → 0` for `e ≠ 0`
    (I18); `byte _ 0 → 0` (I19). -/
def schemaEvm (kb : Nat → KB) : Term → Term → Bool
  | .op2 .signextend b v, r => (isC kb v 0 && isC kb r 0) || (r == v && signextendCopy kb b v)
  | .op2 .exp b e, r =>
    ((isC kb e 0 || isC kb b 1) && isC kb r 1) ||
      (isC kb b 0 && (match e.const? kb with | some n => n != 0 | none => false) && isC kb r 0)
  | .op2 .byte _ v, r => isC kb v 0 && isC kb r 0
  | _, _ => false

/-- `evm_add_mod _ _ 0 → 0`, `evm_mul_mod _ _ 0 → 0` (`simplify_evm_modop_known`, review H-7). -/
def schemaModop (kb : Nat → KB) : Term → Term → Bool
  | .op3 _ _ _ m, r => isC kb m 0 && isC kb r 0
  | _, _ => false

/-- `not (not x) → x` (`simplify_unary_with_same_inner`, I20). -/
def schemaNotNot : Term → Term → Bool
  | .op1 .not (.op1 .not x), r => r == x
  | _, _ => false

/-- All the identities. -/
def checkI (kb : Nat → KB) (l r : Term) : Bool :=
  schemaAdd kb l r || schemaSub kb l r || schemaMul kb l r || schemaAnd kb l r ||
    schemaOr kb l r || schemaXor kb l r || schemaDiv kb l r || schemaEq kb l r ||
    schemaCmp kb l r || schemaShift kb l r || schemaEvm kb l r || schemaModop kb l r ||
    schemaNotNot l r

theorem conflict_ne {a b : KB} {x y : Nat} (ha : a.Sat x) (hb : b.Sat y)
    (h : conflict a b = true) : x ≠ y := by
  intro hxy; subst hxy
  simp only [conflict, bne_iff_ne, ne_eq] at h
  apply h
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit]
  cases h1 : a.kz.testBit i <;> cases h2 : b.ko.testBit i <;>
    cases h3 : a.ko.testBit i <;> cases h4 : b.kz.testBit i <;> simp
  all_goals first
    | (have := ha.zero h1; have := hb.one h2; simp_all)
    | (have := ha.one h3; have := hb.zero h4; simp_all)


theorem testBit_signextendW_high_zero {n y : Nat} (hy : y < W) (hn : n ≤ 31) {i : Nat}
    (hi : i < 256) (hsign : y.testBit (8 * n + 7) = false)
    (hhigh : ∀ j, 8 * n + 7 < j → j < 256 → y.testBit j = false) :
    (signextendW n y).testBit i = y.testBit i := by
  rw [testBit_signextendW hy hn hi]
  split
  · rfl
  · rw [hsign, hhigh i (by omega) hi]


theorem signextendW_zero (b : Nat) : signextendW b 0 = 0 := by
  unfold signextendW; split
  · split
    · next h => simp at h
    · simp
  · rfl


theorem byteW_zero (i : Nat) : byteW i 0 = 0 := by
  unfold byteW; split <;> simp


/-! ## Soundness -/

section Sound

variable (hf : FactsHold kb ρ)
include hf

local macro "eq_of" h:ident : term => `(beq_iff_eq.mp $h)

theorem schemaAdd_sound {l r : Term} (h : schemaAdd kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaAdd at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.zero_add, Term.eval_mod]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.add_zero, Term.eval_mod]
  · cases h

theorem schemaSub_sound {l r : Term} (h : schemaSub kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaSub at h
  split at h
  · next a b =>
    have := Term.eval_lt ρ a
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h1⟩ | ⟨h1, rfl⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1]
      simp only [W] at this ⊢; omega
    · simp only [Term.eval, Op2.eval, isC_eval hf h1]
      simp only [W] at this ⊢; omega
  · cases h

theorem schemaMul_sound {l r : Term} (h : schemaMul kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaMul at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (⟨h1 | h1, h2⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, Term.eval_mod]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, Term.eval_mod]
  · cases h

theorem andCopy_sound {a m : Term} (h : andCopy kb a m = true) :
    a.eval ρ &&& m.eval ρ = a.eval ρ := by
  unfold andCopy at h
  split at h
  · next mv hm =>
    rw [Term.const?_eval hf hm]
    have hs := Term.fact_sat hf a
    have ha := Term.eval_lt ρ a
    simp only [allZero, beq_iff_eq] at h
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    cases hb : (a.eval ρ).testBit i
    · rfl
    · simp only [Bool.true_and]
      by_contra hc
      have hi : i < 256 := by
        by_contra hi; rw [testBit_hi ha (by omega)] at hb; cases hb
      have h1 : (M ^^^ mv).testBit i = true := by
        simp [Nat.testBit_xor, testBit_M, hi]; simpa using hc
      have : (a.fact kb).kz.testBit i = true := by
        have := congrArg (·.testBit i) h; simp only [Nat.testBit_and, h1, Bool.and_true] at this
        exact this
      rw [hs.zero this] at hb; cases hb
  · cases h

theorem orCopy_sound {a m : Term} (h : orCopy kb a m = true) :
    a.eval ρ ||| m.eval ρ = a.eval ρ := by
  unfold orCopy at h
  split at h
  · next mv hm =>
    rw [Term.const?_eval hf hm]
    have hs := Term.fact_sat hf a
    simp only [allOne, beq_iff_eq] at h
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or]
    cases hb : mv.testBit i
    · simp
    · have : (a.fact kb).ko.testBit i = true := by
        have := congrArg (·.testBit i) h; simp only [Nat.testBit_and, hb, Bool.and_true] at this
        exact this
      simp [hs.one this]
  · cases h

theorem schemaAnd_sound {l r : Term} (h : schemaAnd kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaAnd at h
  split at h
  · next a b =>
    have ha := Term.eval_lt ρ a
    have hb := Term.eval_lt ρ b
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (((((⟨h1 | h1, h2⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩) | ⟨rfl, h1⟩) | ⟨rfl, h1⟩) | ⟨rfl, rfl⟩)
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, M_and hb]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, and_M ha]
    · exact andCopy_sound hf h1
    · simp only [Term.eval, Op2.eval]; rw [Nat.and_comm]; exact andCopy_sound hf h1
    · simp only [Term.eval, Op2.eval, Nat.and_self]
  · cases h

theorem schemaOr_sound {l r : Term} (h : schemaOr kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaOr at h
  split at h
  · next a b =>
    have ha := Term.eval_lt ρ a
    have hb := Term.eval_lt ρ b
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (((((⟨h1 | h1, h2⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩) | ⟨rfl, h1⟩) | ⟨rfl, h1⟩) | ⟨rfl, rfl⟩)
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, M_or hb]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, or_M ha]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.zero_or]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.or_zero]
    · exact orCopy_sound hf h1
    · simp only [Term.eval, Op2.eval]; rw [Nat.or_comm]; exact orCopy_sound hf h1
    · simp only [Term.eval, Op2.eval, Nat.or_self]
  · cases h

theorem schemaXor_sound {l r : Term} (h : schemaXor kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaXor at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (⟨h1, rfl⟩ | ⟨h1, rfl⟩) | ⟨rfl, h1⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.zero_xor]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.xor_zero]
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, Nat.xor_self]
  · cases h

theorem schemaDiv_sound {l r : Term} (h : schemaDiv kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaDiv at h
  split at h
  · next a b =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    simp [Term.eval, Op2.eval, isC_eval hf h1]
  · next a b =>
    have ha := Term.eval_lt ρ a
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [Term.eval, Op2.eval, sdivW, isC_eval hf h1, Nat.one_ne_zero, ite_false, signed_one,
      Int.tdiv_one]
    exact wrap_signed ha
  · next a b =>
    simp only [Bool.and_eq_true] at h
    simp [Term.eval, Op2.eval, isC_eval hf h.1, isC_eval hf h.2, Nat.mod_one]
  · next a b =>
    simp only [Bool.and_eq_true] at h
    simp only [Term.eval, Op2.eval, smodW, isC_eval hf h.1, isC_eval hf h.2, Nat.one_ne_zero,
      ite_false, signed_one, Int.tmod_one]
    rfl
  · cases h

theorem schemaEq_sound {l r : Term} (h : schemaEq kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaEq at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h1⟩ | ⟨h1, h2⟩
    · simp [Term.eval, Op2.eval, isC_eval hf h1, ofBool]
    · have := conflict_ne (Term.fact_sat hf a) (Term.fact_sat hf b) h1
      simp [Term.eval, Op2.eval, isC_eval hf h2, ofBool, this]
  · cases h

theorem schemaCmp_sound {l r : Term} (h : schemaCmp kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaCmp at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl | h1, h2⟩
    · simp [Term.eval, Op2.eval, isC_eval hf h2, ofBool]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, ofBool]
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl | h1, h2⟩
    · simp [Term.eval, Op2.eval, isC_eval hf h2, ofBool]
    · simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, ofBool]
  · next a b =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [Term.eval, Op2.eval, isC_eval hf h2, ofBool, not_lt_signed_self]
  · next a b =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [Term.eval, Op2.eval, isC_eval hf h2, ofBool, not_lt_signed_self]
  · cases h

theorem undoShift_sound {l r : Term} (h : undoShift kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold undoShift at h
  split at h
  · next c c' x =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next n n' hn hn' =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hlt⟩, hz⟩ := h
      have hx := Term.eval_lt ρ r
      have hs := Term.fact_sat hf r
      simp only [allZero, beq_iff_eq] at hz
      simp only [Term.eval, Op2.eval, Term.const?_eval hf hn, Term.const?_eval hf hn']
      apply Nat.eq_of_testBit_eq; intro i
      rw [testBit_shrW hlt]
      by_cases hni : n + i < 256
      · rw [testBit_shlW hlt hni]; simp [show n + i - n = i by omega]
      · rw [testBit_hi (shlW_lt _ _) (by omega)]
        by_cases hi : i < 256
        · symm; apply hs.zero
          have hm : (M ^^^ (M >>> n)).testBit i = true := by
            simp [Nat.testBit_xor, testBit_M, Nat.testBit_shiftRight, hi, hni]
          have := congrArg (·.testBit i) hz
          simp only [Nat.testBit_and, hm, Bool.and_true] at this
          exact this
        · rw [testBit_hi hx (by omega)]
    · cases h
  · next c c' x =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next n n' hn hn' =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hlt⟩, hz⟩ := h
      have hx := Term.eval_lt ρ r
      have hs := Term.fact_sat hf r
      simp only [allZero, beq_iff_eq] at hz
      simp only [Term.eval, Op2.eval, Term.const?_eval hf hn, Term.const?_eval hf hn']
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 256
      · rw [testBit_shlW hlt hi]
        by_cases hni : n ≤ i
        · rw [testBit_shrW hlt]; simp [hni, show n + (i - n) = i by omega]
        · simp only [hni, decide_false, Bool.false_and]
          symm; apply hs.zero
          have hm : (lowMask n).testBit i = true := by simp [testBit_lowMask]; omega
          have := congrArg (·.testBit i) hz
          simp only [Nat.testBit_and, hm, Bool.and_true] at this
          exact this
      · rw [testBit_hi (shlW_lt _ _) (by omega), testBit_hi hx (by omega)]
    · cases h
  · cases h

theorem schemaShift_sound {l r : Term} (h : schemaShift kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaShift at h
  split at h
  · next o a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨ho, h⟩ := h
    have hb := Term.eval_lt ρ b
    rcases h with ((⟨h1, h2⟩ | ⟨h1, rfl⟩) | ⟨⟨hs, h1⟩, h2⟩) | h1
    · rcases ho with (rfl | rfl) | rfl <;>
        simp [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, shlW_zero_right,
          shrW_zero_right, sarW_zero_right]
    · rcases ho with (rfl | rfl) | rfl <;>
        simp only [Term.eval, Op2.eval, isC_eval hf h1, shlW_zero_left hb, shrW_zero_left,
          sarW_zero_left hb]
    · unfold countGe256 at h1
      split at h1
      · next n hn =>
        simp only [decide_eq_true_eq] at h1
        rcases ho with (rfl | rfl) | rfl
        · simp [Term.eval, Op2.eval, isC_eval hf h2, Term.const?_eval hf hn, shlW, h1]
        · simp [Term.eval, Op2.eval, isC_eval hf h2, Term.const?_eval hf hn, shrW, h1]
        · exact absurd rfl hs
      · cases h1
    · exact undoShift_sound hf h1
  · cases h

theorem signextendCopy_sound {b v : Term} (h : signextendCopy kb b v = true) :
    signextendW (b.eval ρ) (v.eval ρ) = v.eval ρ := by
  unfold signextendCopy at h
  split at h
  · next n hn =>
    rw [Term.const?_eval hf hn]
    have hv := Term.eval_lt ρ v
    have hs := Term.fact_sat hf v
    split at h
    · next h32 => exact signextendW_of_ge (by omega)
    · split at h
      · next _ h256 => rw [show n = 31 by omega]; exact signextendW_31 hv
      · next h32 h256 =>
        have hsw : (n + 1) * 8 - 1 = 8 * n + 7 := by omega
        simp only [hsw, Bool.or_eq_true, Bool.and_eq_true, allZero, allOne, beq_iff_eq] at h
        apply Nat.eq_of_testBit_eq; intro i
        by_cases hi : i < 256
        · rw [testBit_signextendW hv (by omega) hi]
          split
          · rfl
          · next hle =>
            have hhi : (M ^^^ lowMask ((n + 1) * 8)).testBit i = true := by
              simp [Nat.testBit_xor, testBit_M, testBit_lowMask, hi]; omega
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have e1 := congrArg (·.testBit (8 * n + 7)) h1
              have e2 := congrArg (·.testBit i) h2
              simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, hhi] at e1 e2
              rw [hs.zero e1, hs.zero e2]
            · have e1 := congrArg (·.testBit (8 * n + 7)) h1
              have e2 := congrArg (·.testBit i) h2
              simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, hhi] at e1 e2
              rw [hs.one e1, hs.one e2]
        · have := Op2.eval_lt .signextend (Term.eval_lt ρ b) hv
          simp only [Op2.eval] at this
          rw [Term.const?_eval hf hn] at this
          rw [testBit_hi this (by omega), testBit_hi hv (by omega)]
  · cases h

theorem schemaEvm_sound {l r : Term} (h : schemaEvm kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaEvm at h
  split at h
  · next b v =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨rfl, h1⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, signextendW_zero]
    · exact signextendCopy_sound hf h1
  · next b e =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    have he := Term.eval_lt ρ e
    rcases h with ⟨h1 | h1, h2⟩ | ⟨⟨h1, h3⟩, h2⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, expW_eq (e := 0) (by decide),
        Nat.pow_zero]; rfl
    · simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, expW_eq he, Nat.one_pow]
      rfl
    · split at h3
      · next n hn =>
        have := Term.const?_eval hf hn
        simp only [bne_iff_ne, ne_eq] at h3
        simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
        rw [expW_eq he, this, Nat.zero_pow (Nat.pos_of_ne_zero h3)]
        rfl
      · cases h3
  · next i v =>
    simp only [Bool.and_eq_true] at h
    simp only [Term.eval, Op2.eval, isC_eval hf h.1, isC_eval hf h.2, byteW_zero]
  · cases h

theorem schemaModop_sound {l r : Term} (h : schemaModop kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaModop at h
  split at h
  · next o a b m =>
    simp only [Bool.and_eq_true] at h
    cases o <;> simp [Term.eval, Op3.eval, addmodW, mulmodW, isC_eval hf h.1, isC_eval hf h.2]
  · cases h

omit hf in
theorem schemaNotNot_sound {l r : Term} (h : schemaNotNot l r = true) : l.eval ρ = r.eval ρ := by
  unfold schemaNotNot at h
  split at h
  · next x =>
    simp only [beq_iff_eq] at h; subst h
    have := Term.eval_lt ρ r
    simp only [Term.eval, Op1.eval]; simp only [M, W] at this ⊢; omega
  · cases h

theorem checkI_sound {l r : Term} (h : checkI kb l r = true) : l.eval ρ = r.eval ρ := by
  simp only [checkI, Bool.or_eq_true] at h
  rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact schemaAdd_sound hf h
  · exact schemaSub_sound hf h
  · exact schemaMul_sound hf h
  · exact schemaAnd_sound hf h
  · exact schemaOr_sound hf h
  · exact schemaXor_sound hf h
  · exact schemaDiv_sound hf h
  · exact schemaEq_sound hf h
  · exact schemaCmp_sound hf h
  · exact schemaShift_sound hf h
  · exact schemaEvm_sound hf h
  · exact schemaModop_sound hf h
  · exact schemaNotNot_sound h

end Sound

end Fe.Sonatina.Steps.Schemas
