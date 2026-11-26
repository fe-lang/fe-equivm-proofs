import Fe.Sonatina.Steps.SchemasI

/-!
# `scalar_canonicalize` schemas (design §4.13, S1–S15)

The rewrites of `optim/scalar_canonicalize.rs` that apply to machine IR, each a check on
`T_in`, `T_out` with its soundness lemma (equal values when the atoms satisfy their facts).
The Rust also asks that the matched producers be single-use and in the same block, and prices
constants; those conditions keep the rewrite profitable and are not needed for soundness, so the
checks do not ask them.  Every condition on values the Rust has is asked.

- S1 `fold_bitwise_pair` (`foldBitwisePair`);
- S2, S3 `canonicalize_evm_byte` (`canonByte`), S4 `canonicalize_evm_signextend`
  (`canonSignextend`), with `0 < c ≤ 248`, `c % 8 = 0` (review H-7);
- S5–S8 `fold_constant_comparison` (`foldConstCmp`), for `eq` with the bound on either side and
  for `is_zero`, telling `sub x c` from `sub c x` (review H-7);
- S9 `eq x 0`, `eq 0 x → is_zero x` (`eqZero`);
- S11 `mul_pow2_rewrite` (`mulPow2`), `1 ≤ k < 256`;
- S12 `merge_shifts` (`mergeShifts`);
- S13 `merge_unsigned_divisions` (`mergeDivs`);
- S14, S15 the power-of-two divisor rewrites of `canonicalize_binary_inst` (`divPow2`),
  `1 ≤ k < 256` (review H-7).

The Rust's `neg` and `zext` rewrites are not machine IR.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

variable {kb : Nat → KB} {ρ : Nat → Nat}

/-! ## S1: pairs of bitwise operations -/

inductive BitOp where
  | and | or | xor
  deriving DecidableEq, Repr

def Op2.bit? : Op2 → Option BitOp
  | .and => some .and
  | .or => some .or
  | .xor => some .xor
  | _ => none

def BitOp.f : BitOp → Bool → Bool → Bool
  | .and, p, q => p && q
  | .or, p, q => p || q
  | .xor, p, q => p ^^ q

/-- The table of `fold_bitwise_pair`: `outer (a x y) (b x y)` is `result x y`. -/
def bitPair : BitOp → BitOp → BitOp → Option BitOp
  | .and, .and, .or | .and, .or, .and => some .and
  | .and, .or, .xor | .and, .xor, .or => some .xor
  | .or, .and, .or | .or, .and, .xor | .or, .or, .and | .or, .xor, .and | .or, .or, .xor
  | .or, .xor, .or => some .or
  | .xor, .and, .or | .xor, .or, .and => some .xor
  | .xor, .and, .xor | .xor, .xor, .and => some .or
  | .xor, .or, .xor | .xor, .xor, .or => some .and
  | _, _, _ => none

theorem bitPair_sound {o a b h : BitOp} (hh : bitPair o a b = some h) (p q : Bool) :
    h.f p q = o.f (a.f p q) (b.f p q) := by
  cases o <;> cases a <;> cases b <;> simp only [bitPair, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> cases p <;> cases q <;> rfl

theorem BitOp.f_comm (o : BitOp) (p q : Bool) : o.f p q = o.f q p := by
  cases o <;> cases p <;> cases q <;> rfl

theorem testBit_bit {o : Op2} {b : BitOp} (h : o.bit? = some b) (x y i : Nat) :
    (o.eval x y).testBit i = b.f (x.testBit i) (y.testBit i) := by
  cases o <;> simp only [Op2.bit?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [Op2.eval, BitOp.f]

/-- `fold_bitwise_pair`: `outer (a x y) (b u v) → result x y` for `{u, v} = {x, y}` and an entry
    of the table, with the output's operands in either order (S1). -/
def foldBitwisePair : Term → Term → Bool
  | .op2 outer (.op2 a x y) (.op2 b u v), .op2 h x' y' =>
    match outer.bit?, a.bit?, b.bit?, h.bit? with
    | some fo, some fa, some fb, some fh =>
      bitPair fo fa fb == some fh && ((u == x && v == y) || (u == y && v == x)) &&
        ((x' == x && y' == y) || (x' == y && y' == x))
    | _, _, _, _ => false
  | _, _ => false

theorem foldBitwisePair_sound {l r : Term} (h : foldBitwisePair l r = true) :
    l.eval ρ = r.eval ρ := by
  unfold foldBitwisePair at h
  split at h
  · next outer a x y b u v hop x' y' =>
    split at h
    · next fo fa fb fh ho ha hb hh =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨htab, huv⟩, hxy⟩ := h
      simp only [Term.eval]
      apply Nat.eq_of_testBit_eq; intro i
      rw [testBit_bit ho, testBit_bit ha, testBit_bit hb, testBit_bit hh]
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [bitPair_sound htab]
      · rw [BitOp.f_comm fh, bitPair_sound htab]
      · rw [BitOp.f_comm fb, bitPair_sound htab]
      · rw [BitOp.f_comm fb, BitOp.f_comm fh, bitPair_sound htab]
    · cases h
  · cases h

/-! ## S2–S4: `evm_byte` and `evm_signextend` -/

/-- `and s m` with `s = shr c x`, `m = 255`, as `evm_byte i x'`. -/
def byteOfShift (kb : Nat → KB) (s m i x' : Term) : Bool :=
  match s with
  | .op2 .shr c x =>
    isC kb m 255 && x' == x && match c.const? kb with
      | some n => decide (0 < n ∧ n ≤ 248 ∧ n % 8 = 0) && isC kb i (31 - n / 8)
      | none => false
  | _ => false

/-- `canonicalize_evm_byte`: `shr 248 x → evm_byte 0 x` (S2), and `and (shr c x) 255` in either
    order `→ evm_byte (31 - c / 8) x` for `0 < c ≤ 248`, `c % 8 = 0` (S3). -/
def canonByte (kb : Nat → KB) : Term → Term → Bool
  | .op2 .shr c x, .op2 .byte i x' => isC kb c 248 && isC kb i 0 && x' == x
  | .op2 .and a b, .op2 .byte i x' => byteOfShift kb a b i x' || byteOfShift kb b a i x'
  | _, _ => false

/-- `canonicalize_evm_signextend`: `sar c (shl c x) → evm_signextend (31 - c / 8) x` for
    `0 < c ≤ 248`, `c % 8 = 0` (S4). -/
def canonSignextend (kb : Nat → KB) : Term → Term → Bool
  | .op2 .sar c (.op2 .shl c' x), .op2 .signextend b x' =>
    x' == x && match c.const? kb, c'.const? kb with
      | some n, some n' =>
        n == n' && decide (0 < n ∧ n ≤ 248 ∧ n % 8 = 0) && isC kb b (31 - n / 8)
      | _, _ => false
  | _, _ => false

/-! ## S5–S9: equalities -/

/-- The bound of `eq x k'` for `eq (o x c) k` (`fold_constant_comparison`, constant on the
    right): `k - c`, `k + c`, `k ^ c`. -/
def newBoundR : Op2 → Nat → Nat → Option Nat
  | .add, k, c => some ((k + (W - c)) % W)
  | .sub, k, c => some ((k + c) % W)
  | .xor, k, c => some (k ^^^ c)
  | _, _, _ => none

/-- The bound of `eq x k'` for `eq (o c x) k` (constant on the left): `k - c`, `c - k`, `k ^ c`. -/
def newBoundL : Op2 → Nat → Nat → Option Nat
  | .add, k, c => some ((k + (W - c)) % W)
  | .sub, k, c => some ((c + (W - k)) % W)
  | .xor, k, c => some (k ^^^ c)
  | _, _, _ => none

/-- `eq value k ↔ eq x' k'` by moving `value`'s constant into the bound. -/
def moveConst (kb : Nat → KB) (value : Term) (k : Nat) (x' k' : Term) : Bool :=
  match value with
  | .op2 o p q =>
    (match q.const? kb with
      | some c => x' == p && match newBoundR o k c with
        | some b => isC kb k' b
        | none => false
      | none => false) ||
    (match p.const? kb with
      | some c => x' == q && match newBoundL o k c with
        | some b => isC kb k' b
        | none => false
      | none => false)
  | _ => false

/-- `fold_constant_comparison`: `eq (add/sub/xor …) k`, the bound on either side, and
    `is_zero (add/sub/xor …)`, `→ eq x k'` (S5–S8). -/
def foldConstCmp (kb : Nat → KB) : Term → Term → Bool
  | .op2 .eq a b, .op2 .eq x' k' =>
    (match b.const? kb with
      | some k => moveConst kb a k x' k' || moveConst kb a k k' x'
      | none => false) ||
    (match a.const? kb with
      | some k => moveConst kb b k x' k' || moveConst kb b k k' x'
      | none => false)
  | .op1 .isZero v, .op2 .eq x' k' => moveConst kb v 0 x' k' || moveConst kb v 0 k' x'
  | _, _ => false

/-- `eq x 0`, `eq 0 x → is_zero x` (S9, and GVN's G4). -/
def eqZero (kb : Nat → KB) : Term → Term → Bool
  | .op2 .eq a b, .op1 .isZero x => (isC kb a 0 && x == b) || (isC kb b 0 && x == a)
  | _, _ => false

/-! ## S11–S15: shifts and divisions -/

/-- `a` is known to be `2 ^ n` and `k` known to be `n`, `1 ≤ n < 256`. -/
def pow2C (kb : Nat → KB) (a k : Term) : Bool :=
  match a.const? kb, k.const? kb with
  | some v, some n => pow2Shift? v == some n
  | _, _ => false

/-- `mul_pow2_rewrite`: `mul (2 ^ k) x`, `mul x (2 ^ k) → shl k x` for `1 ≤ k < 256` (S11, and
    GVN's G6). -/
def mulPow2 (kb : Nat → KB) : Term → Term → Bool
  | .op2 .mul a b, .op2 .shl k x => (pow2C kb a k && x == b) || (pow2C kb b k && x == a)
  | _, _ => false

/-- `merge_shifts`: `o a (o b x) → o (min (min a 256 + min b 256) L) x` for `o` one of `shl`,
    `shr`, `sar`, with `L = 256`, or 255 for `sar` (S12). -/
def mergeShifts (kb : Nat → KB) : Term → Term → Bool
  | .op2 o a (.op2 o' b x), .op2 o'' t x' =>
    (o == .shl || o == .shr || o == .sar) && o' == o && o'' == o && x' == x &&
      match a.const? kb, b.const? kb, t.const? kb with
      | some na, some nb, some nt =>
        nt == min (min na 256 + min nb 256) (if o == .sar then 255 else 256)
      | _, _, _ => false
  | _, _ => false

/-- `merge_unsigned_divisions`: `evm_udiv (evm_udiv x a) b → evm_udiv x (a b)` for `a`, `b`
    nonzero and not nontrivial powers of two, `a b < 2 ^ 256` (S13). -/
def mergeDivs (kb : Nat → KB) : Term → Term → Bool
  | .op2 .udiv (.op2 .udiv x a) b, .op2 .udiv x' p =>
    x' == x && match a.const? kb, b.const? kb, p.const? kb with
      | some na, some nb, some np =>
        na != 0 && nb != 0 && (pow2Shift? na).isNone && (pow2Shift? nb).isNone &&
          decide (na * nb < W) && np == na * nb
      | _, _, _ => false
  | _, _ => false

/-- `evm_udiv x (2 ^ k) → shr k x` (S14) and `evm_umod x (2 ^ k) → and x (2 ^ k - 1)`, the mask
    on either side (S15), for `1 ≤ k < 256`. -/
def divPow2 (kb : Nat → KB) : Term → Term → Bool
  | .op2 .udiv x d, .op2 .shr k x' => x' == x && pow2C kb d k
  | .op2 .umod x d, .op2 .and a b =>
    match d.const? kb with
    | some nd => (pow2Shift? nd).isSome &&
        ((a == x && isC kb b (nd - 1)) || (b == x && isC kb a (nd - 1)))
    | none => false
  | _, _ => false

/-- All the `scalar_canonicalize` schemas. -/
def checkS (kb : Nat → KB) (l r : Term) : Bool :=
  foldBitwisePair l r || canonByte kb l r || canonSignextend kb l r || foldConstCmp kb l r ||
    eqZero kb l r || mulPow2 kb l r || mergeShifts kb l r || mergeDivs kb l r || divPow2 kb l r

/-! ## Soundness -/

theorem testBit_sarW' {s y i : Nat} (hy : y < W) (hi : i < 256) :
    (sarW s y).testBit i = if s + i < 256 then y.testBit (s + i) else y.testBit 255 := by
  by_cases hs : s < 256
  · exact testBit_sarW hy hs hi
  · rw [if_neg (by omega)]
    unfold sarW
    split
    · next hneg => rw [shrW, if_pos (by omega), Nat.zero_testBit, Nat.testBit_lt_two_pow hneg]
    · next hneg =>
      rw [shrW, if_pos (by omega), Nat.sub_zero, testBit_M]
      simp only [hi, decide_true]
      symm; rw [← Bool.not_eq_false]; intro h
      exact hneg ((lt_sign_iff hy).mpr h)

theorem sarW_lt {s y : Nat} (hy : y < W) : sarW s y < W := by
  unfold sarW; split
  · exact shrW_lt hy
  · simp only [M, W] at *; omega

theorem byteW_zero_eq {y : Nat} (hy : y < W) : byteW 0 y = shrW 248 y := by
  unfold byteW shrW
  rw [if_neg (by decide), if_neg (by decide), show (31 - 0) * 8 = 248 from rfl,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_lt_of_lt_mul; simp only [W] at hy; omega

theorem pow2C_eq (hf : FactsHold kb ρ) {a k : Term} (h : pow2C kb a k = true) :
    ∃ n, a.eval ρ = 2 ^ n ∧ k.eval ρ = n ∧ 1 ≤ n ∧ n < 256 := by
  unfold pow2C at h
  split at h
  · next v n hv hn =>
    simp only [beq_iff_eq] at h
    obtain ⟨rfl, h1, h2⟩ := pow2Shift?_eq h
    exact ⟨n, Term.const?_eval hf hv, Term.const?_eval hf hn, h1, h2⟩
  · cases h

theorem ofBool_beq_congr {a b c d : Nat} (h : a = b ↔ c = d) :
    ofBool (a == b) = ofBool (c == d) := by
  by_cases h1 : a = b
  · have := h.mp h1; simp [ofBool, h1, this]
  · have : ¬ c = d := fun h2 => h1 (h.mpr h2)
    simp [ofBool, h1, this]

theorem xor_xor_cancel (a b : Nat) : a ^^^ b ^^^ b = a := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem newBoundR_iff {o : Op2} {k c b p : Nat} (h : newBoundR o k c = some b) (hp : p < W)
    (hc : c < W) (hk : k < W) : o.eval p c = k ↔ p = b := by
  cases o <;> simp only [newBoundR, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · simp only [Op2.eval]; simp only [W] at *; omega
  · simp only [Op2.eval]; simp only [W] at *; omega
  · simp only [Op2.eval]
    constructor
    · rintro rfl; exact (xor_xor_cancel p c).symm
    · rintro rfl; exact xor_xor_cancel k c

theorem newBoundL_iff {o : Op2} {k c b q : Nat} (h : newBoundL o k c = some b) (hq : q < W)
    (hc : c < W) (hk : k < W) : o.eval c q = k ↔ q = b := by
  cases o <;> simp only [newBoundL, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · simp only [Op2.eval]; simp only [W] at *; omega
  · simp only [Op2.eval]; simp only [W] at *; omega
  · simp only [Op2.eval]
    constructor
    · rintro rfl; rw [Nat.xor_comm c q, xor_xor_cancel]
    · rintro rfl; rw [Nat.xor_comm, xor_xor_cancel]

section Sound

variable (hf : FactsHold kb ρ)
include hf

theorem canonByte_sound {l r : Term} (h : canonByte kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold canonByte at h
  split at h
  · next c x i x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    exact (byteW_zero_eq (Term.eval_lt ρ _)).symm
  · next a b i x' =>
    have key : ∀ s m, byteOfShift kb s m i x' = true →
        s.eval ρ &&& m.eval ρ = byteW (i.eval ρ) (x'.eval ρ) := by
      intro s m hs
      unfold byteOfShift at hs
      split at hs
      · next c x =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨⟨h1, rfl⟩, hs⟩ := hs
        split at hs
        · next n hn =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
          obtain ⟨⟨h0, h248, h8⟩, h2⟩ := hs
          simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, Term.const?_eval hf hn,
            shrW, byteW, if_neg (show ¬ 256 ≤ n by omega),
            if_neg (show ¬ 31 < 31 - n / 8 by omega)]
          rw [show (31 - (31 - n / 8)) * 8 = n by omega]
        · cases hs
      · cases hs
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact key a b h
    · simp only [Term.eval, Op2.eval]; rw [Nat.and_comm]; exact key b a h
  · cases h

theorem canonSignextend_sound {l r : Term} (h : canonSignextend kb l r = true) :
    l.eval ρ = r.eval ρ := by
  unfold canonSignextend at h
  split at h
  · next c c' x b x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next n n' hn hn' =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, h0, h248, h8⟩, hb⟩ := h
      have hx := Term.eval_lt ρ x'
      simp only [Term.eval, Op2.eval, isC_eval hf hb, Term.const?_eval hf hn,
        Term.const?_eval hf hn']
      have hsl := shlW_lt n (Term.eval ρ x')
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 256
      · rw [testBit_sarW hsl (by omega) hi, testBit_signextendW hx (by omega) hi]
        have h7 : 8 * (31 - n / 8) + 7 = 255 - n := by omega
        rw [h7]
        split
        · next hni =>
          rw [testBit_shlW (by omega) hni, if_pos (by omega)]
          simp [show n + i - n = i by omega]
        · next hni =>
          rw [testBit_shlW (by omega) (by decide), if_neg (by omega)]
          have : n ≤ 255 := by omega
          simp [this]
      · have h2 := Op2.eval_lt .signextend (x := 31 - n / 8) (by simp only [W]; omega) hx
        simp only [Op2.eval] at h2
        rw [testBit_hi (sarW_lt hsl) (by omega), testBit_hi h2 (by omega)]
    · cases h
  · cases h

theorem moveConst_iff {v x' k' : Term} {k : Nat} (hk : k < W)
    (h : moveConst kb v k x' k' = true) : v.eval ρ = k ↔ x'.eval ρ = k'.eval ρ := by
  unfold moveConst at h
  split at h
  · next o p q =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · next c hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        split at h
        · next b hb =>
          rw [isC_eval hf h]
          simp only [Term.eval, Term.const?_eval hf hc]
          exact newBoundR_iff hb (Term.eval_lt ρ _) (exactVal?_lt hc) hk
        · cases h
      · cases h
    · split at h
      · next c hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        split at h
        · next b hb =>
          rw [isC_eval hf h]
          simp only [Term.eval, Term.const?_eval hf hc]
          exact newBoundL_iff hb (Term.eval_lt ρ _) (exactVal?_lt hc) hk
        · cases h
      · cases h
  · cases h

theorem foldConstCmp_sound {l r : Term} (h : foldConstCmp kb l r = true) :
    l.eval ρ = r.eval ρ := by
  unfold foldConstCmp at h
  split at h
  · next a b x' k' =>
    simp only [Bool.or_eq_true] at h
    simp only [Term.eval, Op2.eval]
    rcases h with h | h
    · split at h
      · next k hk =>
        rw [Term.const?_eval hf hk]
        try simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact ofBool_beq_congr (moveConst_iff hf (exactVal?_lt hk) h)
        · apply ofBool_beq_congr
          rw [moveConst_iff hf (exactVal?_lt hk) h]; exact eq_comm
      · cases h
    · split at h
      · next k hk =>
        rw [Term.const?_eval hf hk]
        try simp only [Bool.or_eq_true] at h
        apply ofBool_beq_congr
        rw [eq_comm]
        rcases h with h | h
        · exact moveConst_iff hf (exactVal?_lt hk) h
        · rw [moveConst_iff hf (exactVal?_lt hk) h]; exact eq_comm
      · cases h
  · next v x' k' =>
    simp only [Term.eval, Op2.eval, Op1.eval]
    try simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact ofBool_beq_congr (moveConst_iff hf (by decide) h)
    · apply ofBool_beq_congr
      rw [moveConst_iff hf (by decide) h]; exact eq_comm
  · cases h

theorem eqZero_sound {l r : Term} (h : eqZero kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold eqZero at h
  split at h
  · next a b x =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h2
      simp only [Term.eval, Op2.eval, Op1.eval, isC_eval hf h1]
      apply ofBool_beq_congr; exact eq_comm
    · subst h2
      simp only [Term.eval, Op2.eval, Op1.eval, isC_eval hf h1]
  · cases h

theorem mulPow2_sound {l r : Term} (h : mulPow2 kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold mulPow2 at h
  split at h
  · next a b k x =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h2
      obtain ⟨n, ha, hk, h1, h2⟩ := pow2C_eq hf h1
      simp only [Term.eval, Op2.eval, ha, hk, shlW, if_neg (show ¬ 256 ≤ n by omega),
        Nat.shiftLeft_eq]
      rw [Nat.mul_comm]
    · subst h2
      obtain ⟨n, ha, hk, h1, h2⟩ := pow2C_eq hf h1
      simp only [Term.eval, Op2.eval, ha, hk, shlW, if_neg (show ¬ 256 ≤ n by omega),
        Nat.shiftLeft_eq]
  · cases h

theorem mergeShifts_sound {l r : Term} (h : mergeShifts kb l r = true) :
    l.eval ρ = r.eval ρ := by
  unfold mergeShifts at h
  split at h
  · next o a o' b x o'' t x' =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨ho, rfl⟩, rfl⟩, h3⟩, h⟩ := h
    subst h3
    split at h
    · next na nb nt hna hnb hnt =>
      simp only [beq_iff_eq] at h
      have hx := Term.eval_lt ρ x'
      have hna' := exactVal?_lt hna
      have hnb' := exactVal?_lt hnb
      have hnt' := exactVal?_lt hnt
      simp only [Term.eval, Term.const?_eval hf hna, Term.const?_eval hf hnb,
        Term.const?_eval hf hnt]
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 256
      · rcases ho with (rfl | rfl) | rfl
        · rw [if_neg (by decide)] at h
          subst h
          simp only [Op2.eval]
          rw [testBit_shlW' hi, testBit_shlW' hi]
          by_cases h1 : na ≤ i
          · rw [testBit_shlW' (by omega)]
            by_cases h2 : nb ≤ i - na
            · have h3 : min (min na 256 + min nb 256) 256 ≤ i := by omega
              simp only [h1, h2, h3, decide_true, Bool.true_and]; congr 1; omega
            · have h3 : ¬ min (min na 256 + min nb 256) 256 ≤ i := by omega
              simp [h1, h2, h3]
          · have h3 : ¬ min (min na 256 + min nb 256) 256 ≤ i := by omega
            simp [h1, h3]
        · rw [if_neg (by decide)] at h
          subst h
          simp only [Op2.eval]
          rw [testBit_shrW' (shrW_lt hx), testBit_shrW' hx, testBit_shrW' hx]
          by_cases h1 : na < 256 <;> by_cases h2 : nb < 256
          · by_cases h3 : na + nb < 256
            · have : min (min na 256 + min nb 256) 256 = na + nb := by omega
              simp only [h1, h2, this, h3, decide_true, Bool.true_and]; congr 1; omega
            · have : min (min na 256 + min nb 256) 256 = 256 := by omega
              simp only [h1, h2, this, decide_true, Bool.true_and,
                show ¬ ((256 : Nat) < 256) by decide, decide_false, Bool.false_and]
              exact testBit_hi hx (by omega)
          all_goals
            have : min (min na 256 + min nb 256) 256 = 256 := by omega
            simp [h1, h2, this]
        · rw [if_pos rfl] at h
          subst h
          simp only [Op2.eval]
          rw [testBit_sarW' (sarW_lt hx) hi, testBit_sarW' hx hi]
          split
          · next h1 =>
            rw [testBit_sarW' hx h1]
            split_ifs <;> first | (exfalso; omega) | (congr 1; omega) | rfl
          · next h1 =>
            rw [testBit_sarW' hx (by decide)]
            split_ifs <;> first | (exfalso; omega) | (congr 1; omega) | rfl
      · subst h
        rw [testBit_hi (i := i) (Op2.eval_lt _ hna' (Op2.eval_lt _ hnb' hx)) (by omega),
          testBit_hi (i := i) (Op2.eval_lt _ hnt' hx) (by omega)]
    · cases h
  · cases h

theorem mergeDivs_sound {l r : Term} (h : mergeDivs kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold mergeDivs at h
  split at h
  · next x a b x' p =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next na nb np hna hnb hnp =>
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, rfl⟩ := h
      simp only [Term.eval, Op2.eval, Term.const?_eval hf hna, Term.const?_eval hf hnb,
        Term.const?_eval hf hnp, h1, h2, Nat.mul_eq_zero, or_self, ite_false,
        Nat.div_div_eq_div_mul]
    · cases h
  · cases h

theorem divPow2_sound {l r : Term} (h : divPow2 kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold divPow2 at h
  split at h
  · next x d k x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨n, hd, hk, h1, h2⟩ := pow2C_eq hf h
    have hp : (2 : Nat) ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)
    simp only [Term.eval, Op2.eval, hd, hk, shrW, if_neg (show ¬ 256 ≤ n by omega),
      Nat.shiftRight_eq_div_pow, hp, ite_false]
  · next x d a b =>
    split at h
    · next nd hnd =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨n, hn⟩, h⟩ := h
      obtain ⟨rfl, h1, h2⟩ := pow2Shift?_eq hn
      have hd := Term.const?_eval hf hnd
      have hp : (2 : Nat) ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)
      rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · subst h3
        simp only [Term.eval, Op2.eval, hd, isC_eval hf h4, hp, ite_false,
          Nat.and_two_pow_sub_one_eq_mod]
      · subst h3
        simp only [Term.eval, Op2.eval, hd, isC_eval hf h4, hp, ite_false]
        rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    · cases h
  · cases h

theorem checkS_sound {l r : Term} (h : checkS kb l r = true) : l.eval ρ = r.eval ρ := by
  simp only [checkS, Bool.or_eq_true] at h
  rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · exact foldBitwisePair_sound h
  · exact canonByte_sound hf h
  · exact canonSignextend_sound hf h
  · exact foldConstCmp_sound hf h
  · exact eqZero_sound hf h
  · exact mulPow2_sound hf h
  · exact mergeShifts_sound hf h
  · exact mergeDivs_sound hf h
  · exact divPow2_sound hf h

end Sound

end Fe.Sonatina.Steps.Schemas
