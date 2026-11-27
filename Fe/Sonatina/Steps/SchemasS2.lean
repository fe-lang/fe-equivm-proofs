import Fe.Sonatina.Steps.SchemasS
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring

/-!
# `scalar_canonicalize` schemas added since the design (S16–S24)

The rewrites Sonatina `main` added to `optim/scalar_canonicalize.rs` after design §4.13 was
written, each as it fires on machine IR (every type `i256`, the target the EVM), a check on
`T_in`, `T_out` with its soundness lemma.  As in `SchemasS.lean`, the Rust's single-use,
same-block and cost conditions are not asked (they keep a rewrite profitable); every condition
on values is.

- S16 `cancel_common_operand` (`cancelCommon`): `eq (o k x) (o k y) → eq x y` for `o` one of
  `add`, `sub`, `xor`, `mul`, the shared operand in the same place on both sides, or, `o`
  commutative, in opposite places; for `mul` the shared operand an odd constant (`Ne` is not
  machine IR);
- S17 the quotient zero tests of `fold_constant_comparison` (`quotientZero`): `eq (evm_udiv x c)
  0`, `eq 0 (evm_udiv x c)`, `is_zero (evm_udiv x c) → lt x c` for a constant `c ≠ 0`;
- S18 `fold_complemented_arithmetic` and the `sub` of two `not`s (`complShl`, `complSub1`,
  `complAdd`, `complSub`, `subNots`): `not (sub (shl n 1) 1) → shl n (-1)`, `not (sub x 1) →
  sub 0 x`, `not (add (not x) y)`, `not (add y (not x)) → sub x y`, `not (sub (not x) y) → add x
  y`, `sub (not x) (not y) → sub y x`;
- S19 `canonicalize_signed_top_field` (`signedTop`): `evm_signextend b (shr (248 - 8 b) x) → sar
  (248 - 8 b) x` for `b < 31`, and `evm_signextend 0 (evm_byte 0 x) → sar 248 x`;
- S20 `fold_shifted_byte` (`shiftedByte`): `evm_byte i (shl c x) → evm_byte (i + c / 8) x` for
  `i + c / 8 < 32`, `evm_byte i (shr c x) → evm_byte (i - c / 8) x` for `c / 8 ≤ i`, `i < 32`,
  `c < 256`, `c % 8 = 0`;
- S21 `fold_dynamic_pow2_division` (`dynPow2Div`): `evm_udiv x (shl n 1) → shr n x`, any `n`;
- S22 `fold_shifted_sign_test` (`signTest`): `slt (sar c x) 0 → slt x 0`, `sgt (sar c x) (-1) →
  sgt x (-1)`, and with the bound on the left, `sgt 0 (sar c x) → slt x 0`, `slt (-1) (sar c x)
  → sgt x (-1)`, any `c` (`sle`, `sge` are not machine IR);
- S23 the powers of two of `canonicalize_binary_inst` (`expTwo`): `evm_exp 2 e → shl e 1`,
  `evm_exp b 2 → mul b b`;
- S24 the neutral operand of `evm_add_mod`/`evm_mul_mod` (`modopUmod`): `evm_add_mod x 0 m`,
  `evm_add_mod 0 x m`, `evm_mul_mod x 1 m`, `evm_mul_mod 1 x m → evm_umod x m`.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

variable {kb : Nat → KB} {ρ : Nat → Nat}

/-! ## The checks -/

/-- `o` cancels the shared operand `key`: `add`, `sub`, `xor`, and `mul` by an odd constant. -/
def keyOk (kb : Nat → KB) (o : Op2) (key : Term) : Bool :=
  match o with
  | .add | .sub | .xor => true
  | .mul => match key.const? kb with
    | some k => k % 2 == 1
    | none => false
  | _ => false

/-- The operand pairs left when `o a b` and `o c d` share an operand (`cancel_common_operand`):
    first in both, second in both, or, `o` other than `sub`, first in one and second in the
    other; `add`, `sub`, `xor`, and `mul` by an odd constant. -/
def cancelPairs (kb : Nat → KB) (o : Op2) (a b c d : Term) : List (Term × Term) :=
  (if a == c && keyOk kb o a then [(b, d)] else []) ++
    (if b == d && keyOk kb o b then [(a, c)] else []) ++
    (if o != .sub && a == d && keyOk kb o a then [(b, c)] else []) ++
    (if o != .sub && b == c && keyOk kb o b then [(a, d)] else [])

/-- `cancel_common_operand`: `eq (o a b) (o c d) → eq x y` for a pair `cancelPairs` gives, in
    either order (S16). -/
def cancelCommon (kb : Nat → KB) : Term → Term → Bool
  | .op2 .eq (.op2 o a b) (.op2 o' c d), .op2 .eq x y =>
    o == o' && (cancelPairs kb o a b c d).any fun p =>
      (x == p.1 && y == p.2) || (x == p.2 && y == p.1)
  | _, _ => false

/-- `q` is `evm_udiv x c` for a constant `c ≠ 0`, and `r` is `lt x c`. -/
def udivZero (kb : Nat → KB) (q r : Term) : Bool :=
  match q, r with
  | .op2 .udiv x c, .op2 .lt x' c' => x' == x && match c.const? kb with
    | some n => n != 0 && isC kb c' n
    | none => false
  | _, _ => false

/-- The quotient zero tests (S17). -/
def quotientZero (kb : Nat → KB) (l r : Term) : Bool :=
  match l with
  | .op2 .eq a b => (isC kb b 0 && udivZero kb a r) || (isC kb a 0 && udivZero kb b r)
  | .op1 .isZero a => udivZero kb a r
  | _ => false

/-- `not (sub (shl n 1) 1) → shl n (-1)` (S18). -/
def complShl (kb : Nat → KB) : Term → Term → Bool
  | .op1 .not (.op2 .sub (.op2 .shl n one) one'), .op2 .shl n' m =>
    isC kb one 1 && isC kb one' 1 && n' == n && isC kb m M
  | _, _ => false

/-- `not (sub x 1) → sub 0 x` (S18). -/
def complSub1 (kb : Nat → KB) : Term → Term → Bool
  | .op1 .not (.op2 .sub x one), .op2 .sub z x' => isC kb one 1 && isC kb z 0 && x' == x
  | _, _ => false

/-- `t` is `not x`. -/
def notOf (t x : Term) : Bool :=
  match t with
  | .op1 .not y => y == x
  | _ => false

/-- `not (add (not x) y)`, `not (add y (not x)) → sub x y` (S18). -/
def complAdd : Term → Term → Bool
  | .op1 .not (.op2 .add a b), .op2 .sub x y => (notOf a x && b == y) || (notOf b x && a == y)
  | _, _ => false

/-- `not (sub (not x) y) → add x y`, the output's operands in either order (S18). -/
def complSub : Term → Term → Bool
  | .op1 .not (.op2 .sub a y), .op2 .add x y' =>
    (notOf a x && y' == y) || (notOf a y' && x == y)
  | _, _ => false

/-- `sub (not x) (not y) → sub y x` (S18). -/
def subNots : Term → Term → Bool
  | .op2 .sub a b, .op2 .sub y x => notOf a x && notOf b y
  | _, _ => false

/-- `canonicalize_signed_top_field` (S19). -/
def signedTop (kb : Nat → KB) : Term → Term → Bool
  | .op2 .signextend b v, .op2 .sar c' x' =>
    match b.const? kb with
    | some nb => decide (nb < 31) && isC kb c' (248 - 8 * nb) && match v with
      | .op2 .shr c x => isC kb c (248 - 8 * nb) && x' == x
      | .op2 .byte i x => nb == 0 && isC kb i 0 && x' == x
      | _ => false
    | none => false
  | _, _ => false

/-- `fold_shifted_byte` (S20). -/
def shiftedByte (kb : Nat → KB) : Term → Term → Bool
  | .op2 .byte i (.op2 o c x), .op2 .byte j x' =>
    x' == x && match i.const? kb, c.const? kb, j.const? kb with
    | some ni, some nc, some nj => decide (ni < 32 ∧ nc < 256 ∧ nc % 8 = 0) &&
        ((o == .shl && decide (ni + nc / 8 < 32) && nj == ni + nc / 8) ||
          (o == .shr && decide (nc / 8 ≤ ni) && nj == ni - nc / 8))
    | _, _, _ => false
  | _, _ => false

/-- `fold_dynamic_pow2_division` (S21). -/
def dynPow2Div (kb : Nat → KB) : Term → Term → Bool
  | .op2 .udiv x (.op2 .shl n one), .op2 .shr n' x' => isC kb one 1 && n' == n && x' == x
  | _, _ => false

/-- `t` is `sar _ x`. -/
def sarOf (t x : Term) : Bool :=
  match t with
  | .op2 .sar _ y => y == x
  | _ => false

/-- `fold_shifted_sign_test` (S22). -/
def signTest (kb : Nat → KB) (l r : Term) : Bool :=
  match l, r with
  | .op2 o a b, .op2 o' x z =>
    (o == .slt && o' == .slt && isC kb z 0 && isC kb b 0 && sarOf a x) ||
    (o == .sgt && o' == .sgt && isC kb z M && isC kb b M && sarOf a x) ||
    (o == .sgt && o' == .slt && isC kb z 0 && isC kb a 0 && sarOf b x) ||
    (o == .slt && o' == .sgt && isC kb z M && isC kb a M && sarOf b x)
  | _, _ => false

/-- `evm_exp 2 e → shl e 1`, `evm_exp b 2 → mul b b` (S23). -/
def expTwo (kb : Nat → KB) : Term → Term → Bool
  | .op2 .exp b e, .op2 .shl e' one => isC kb b 2 && isC kb one 1 && e' == e
  | .op2 .exp b e, .op2 .mul b' b'' => isC kb e 2 && b' == b && b'' == b
  | _, _ => false

/-- `evm_add_mod x 0 m`, `evm_add_mod 0 x m`, `evm_mul_mod x 1 m`, `evm_mul_mod 1 x m → evm_umod
    x m` (S24). -/
def modopUmod (kb : Nat → KB) : Term → Term → Bool
  | .op3 .addmod a b m, .op2 .umod x m' =>
    m' == m && ((isC kb b 0 && x == a) || (isC kb a 0 && x == b))
  | .op3 .mulmod a b m, .op2 .umod x m' =>
    m' == m && ((isC kb b 1 && x == a) || (isC kb a 1 && x == b))
  | _, _ => false

/-- The schemas of this file. -/
def checkS2 (kb : Nat → KB) (l r : Term) : Bool :=
  cancelCommon kb l r || quotientZero kb l r || complShl kb l r || complSub1 kb l r ||
    complAdd l r || complSub l r || subNots l r || signedTop kb l r || shiftedByte kb l r ||
    dynPow2Div kb l r || signTest kb l r || expTwo kb l r || modopUmod kb l r

/-! ## Word lemmas -/

theorem mul_cancel_odd {k x y : Nat} (hk : k % 2 = 1) (hx : x < W) (hy : y < W)
    (h : k * x % W = k * y % W) : x = y := by
  have h2 : Nat.Coprime 2 k := by
    show Nat.gcd 2 k = 1
    rw [Nat.gcd_rec, hk]; rfl
  have hc : Nat.Coprime (2 ^ 256) k := Nat.Coprime.pow_left 256 h2
  have := Nat.ModEq.cancel_left_of_coprime (m := 2 ^ 256) (c := k) hc h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem mul_pred_mod {w q : Nat} (hq : q + 1 ≤ w) : (w - 1) * (q + 1) % w = w - (q + 1) := by
  have : (w - 1) * (q + 1) = (w - (q + 1)) + w * q := by
    zify [hq, (by omega : 1 ≤ w)]; ring
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem xor_inj_left {k x y : Nat} (h : k ^^^ x = k ^^^ y) : x = y := by simpa using h

theorem shlW_one {n : Nat} (hn : n < 256) : shlW n 1 = 2 ^ n := by
  unfold shlW
  rw [if_neg (by omega), Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)

theorem shrW_eq_div {n x : Nat} (hn : n < 256) : shrW n x = x / 2 ^ n := by
  unfold shrW; rw [if_neg (by omega), Nat.shiftRight_eq_div_pow]

theorem sarW_sign {c x : Nat} (hx : x < W) : sarW c x < 2 ^ 255 ↔ x < 2 ^ 255 := by
  unfold sarW
  split
  · next h => exact ⟨fun _ => h, fun _ => lt_of_le_of_lt (shrW_le _ _) h⟩
  · next h =>
    have h1 := shrW_le c (M - x)
    simp only [M, W] at *
    constructor <;> intro h2 <;> omega

theorem signed_neg {x : Nat} (hx : x < W) : signed 256 x < 0 ↔ ¬ x < 2 ^ 255 := by
  by_cases h : x < 2 ^ 255
  · rw [signed_of_lt h]; constructor <;> intro <;> omega
  · rw [signed_of_ge h]; simp only [W] at hx; constructor <;> intro <;> omega

theorem signed_M : signed 256 M = -1 := by
  rw [signed_of_ge (by decide)]; decide

theorem signextend_shr {nb x : Nat} (hb : nb < 31) (hx : x < W) :
    signextendW nb (shrW (248 - 8 * nb) x) = sarW (248 - 8 * nb) x := by
  have hs : 248 - 8 * nb < 256 := by omega
  have hl : shrW (248 - 8 * nb) x < W := shrW_lt hx
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 256
  · rw [testBit_signextendW hl (by omega) hi, testBit_sarW hx hs hi]
    split
    · next hle => rw [testBit_shrW hs, if_pos (by omega)]
    · next hle => rw [testBit_shrW hs, if_neg (by omega)]; congr 1; omega
  · have h1 := Op2.eval_lt .signextend (x := nb) (by simp only [W]; omega) hl
    simp only [Op2.eval] at h1
    rw [testBit_hi h1 (by omega), testBit_hi (sarW_lt hx) (by omega)]

theorem testBit_byteW {i y t : Nat} (hi : i < 32) :
    (byteW i y).testBit t = (decide (t < 8) && y.testBit ((31 - i) * 8 + t)) := by
  unfold byteW
  rw [if_neg (by omega), show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem byte_shl {ni k x : Nat} (h : ni + k < 32) :
    byteW ni (shlW (8 * k) x) = byteW (ni + k) x := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [testBit_byteW (by omega), testBit_byteW h]
  by_cases ht : t < 8
  · rw [testBit_shlW (by omega) (by omega)]
    simp only [ht, decide_true, Bool.true_and, show 8 * k ≤ (31 - ni) * 8 + t by omega]
    congr 1; omega
  · simp [ht]

theorem byte_shr {ni k x : Nat} (hk : k ≤ ni) (hn : ni < 32) :
    byteW ni (shrW (8 * k) x) = byteW (ni - k) x := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [testBit_byteW hn, testBit_byteW (by omega), testBit_shrW (by omega)]
  congr 2; omega

/-! ## Soundness -/

section Sound

variable (hf : FactsHold kb ρ)
include hf

theorem cancelPairs_iff {o : Op2} {a b c d : Term} {p : Term × Term}
    (hp : p ∈ cancelPairs kb o a b c d) :
    o.eval (a.eval ρ) (b.eval ρ) = o.eval (c.eval ρ) (d.eval ρ) ↔ p.1.eval ρ = p.2.eval ρ := by
  -- the operation is injective in each argument, the other fixed
  have inj : ∀ (key : Term) (x y : Nat), x < W → y < W →
      keyOk kb o key = true →
      (o.eval (key.eval ρ) x = o.eval (key.eval ρ) y ↔ x = y) ∧
        (o.eval x (key.eval ρ) = o.eval y (key.eval ρ) ↔ x = y) := by
    intro key x y hx hy hok
    have hk := Term.eval_lt ρ key
    unfold keyOk at hok
    refine ⟨⟨fun h => ?_, fun h => h ▸ rfl⟩, ⟨fun h => ?_, fun h => h ▸ rfl⟩⟩ <;>
      cases o <;> simp only [Bool.false_eq_true] at hok <;> simp only [Op2.eval] at h
    · simp only [W] at *; omega
    · simp only [W] at *; omega
    · split at hok
      · next k hkc =>
        simp only [beq_iff_eq] at hok
        rw [Term.const?_eval hf hkc] at h
        exact mul_cancel_odd hok hx hy h
      · cases hok
    · exact xor_inj_left h
    · simp only [W] at *; omega
    · simp only [W] at *; omega
    · split at hok
      · next k hkc =>
        simp only [beq_iff_eq] at hok
        rw [Term.const?_eval hf hkc, Nat.mul_comm x, Nat.mul_comm y] at h
        exact mul_cancel_odd hok hx hy h
      · cases hok
    · exact xor_inj_left (by rw [Nat.xor_comm, h, Nat.xor_comm])
  have hcomm : ∀ x y, o != .sub → keyOk kb o a = true → o.eval x y = o.eval y x := by
    intro x y hs hok
    unfold keyOk at hok
    cases o <;> simp_all [Op2.eval, Nat.add_comm, Nat.mul_comm, Nat.xor_comm]
  have hcomm' : ∀ x y, o != .sub → keyOk kb o b = true → o.eval x y = o.eval y x := by
    intro x y hs hok
    unfold keyOk at hok
    cases o <;> simp_all [Op2.eval, Nat.add_comm, Nat.mul_comm, Nat.xor_comm]
  unfold cancelPairs at hp
  simp only [List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp <;> split at hp <;>
    simp only [List.mem_singleton, List.not_mem_nil] at hp <;> subst hp
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hok⟩ := h
    exact (inj a _ _ (Term.eval_lt ρ _) (Term.eval_lt ρ _) hok).1
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hok⟩ := h
    exact (inj b _ _ (Term.eval_lt ρ _) (Term.eval_lt ρ _) hok).2
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, rfl⟩, hok⟩ := h
    rw [hcomm (c.eval ρ) (a.eval ρ) hs hok]
    exact (inj a _ _ (Term.eval_lt ρ _) (Term.eval_lt ρ _) hok).1
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, rfl⟩, hok⟩ := h
    rw [hcomm' (b.eval ρ) (d.eval ρ) hs hok]
    exact (inj b _ _ (Term.eval_lt ρ _) (Term.eval_lt ρ _) hok).2

theorem cancelCommon_sound {l r : Term} (h : cancelCommon kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold cancelCommon at h
  split at h
  · next o a b o' c d x y =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, Bool.or_eq_true] at h
    obtain ⟨rfl, p, hp, hxy⟩ := h
    have hi := cancelPairs_iff hf hp
    simp only [Term.eval, Op2.eval]
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ofBool_beq_congr hi
    · exact ofBool_beq_congr (hi.trans eq_comm)
  · cases h

theorem udivZero_sound {q r : Term} (h : udivZero kb q r = true) :
    ofBool (q.eval ρ == 0) = r.eval ρ := by
  unfold udivZero at h
  split at h
  · next x c x' c' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next n hn =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨h0, h1⟩ := h
      simp only [Term.eval, Op2.eval, Term.const?_eval hf hn, isC_eval hf h1, h0, ite_false]
      have : x'.eval ρ / n = 0 ↔ x'.eval ρ < n := by
        rw [Nat.div_eq_zero_iff]; constructor
        · rintro (h | h)
          · exact absurd h h0
          · exact h
        · exact Or.inr
      by_cases hl : x'.eval ρ < n
      · simp [ofBool, this.mpr hl, hl]
      · have : ¬ x'.eval ρ / n = 0 := fun h' => hl (this.mp h')
        simp [ofBool, this, hl]
    · cases h
  · cases h

theorem quotientZero_sound {l r : Term} (h : quotientZero kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold quotientZero at h
  split at h
  · next a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Term.eval, Op2.eval, isC_eval hf h1]; exact udivZero_sound hf h2
    · simp only [Term.eval, Op2.eval, isC_eval hf h1]
      rw [← udivZero_sound hf h2]
      by_cases hb : b.eval ρ = 0
      · simp [hb]
      · have hb' : (0 == b.eval ρ) = false := by simpa using Ne.symm hb
        have hb'' : (b.eval ρ == 0) = false := by simpa using hb
        rw [hb', hb'']
  · next a => simp only [Term.eval, Op1.eval]; exact udivZero_sound hf h
  · cases h

theorem complShl_sound {l r : Term} (h : complShl kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold complShl at h
  split at h
  · next n one one' n' m =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, rfl⟩, h3⟩ := h
    simp only [Term.eval, Op2.eval, Op1.eval, isC_eval hf h1, isC_eval hf h2, isC_eval hf h3]
    by_cases hn : n'.eval ρ < 256
    · have hP1 : 1 ≤ 2 ^ n'.eval ρ := Nat.one_le_two_pow
      have hPW : 2 ^ n'.eval ρ < W := Nat.pow_lt_pow_right (by decide) hn
      unfold shlW
      rw [if_neg (by omega), if_neg (by omega), Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.mod_eq_of_lt hPW]
      generalize 2 ^ n'.eval ρ = P at hP1 hPW
      obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
      rw [show M = W - 1 from rfl, mul_pred_mod hPW.le]
      simp only [W] at *
      omega
    · simp only [shlW, if_pos (show 256 ≤ n'.eval ρ by omega)]
      simp [M, W]
  · cases h

theorem complSub1_sound {l r : Term} (h : complSub1 kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold complSub1 at h
  split at h
  · next x one z x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    have hx := Term.eval_lt ρ x'
    simp only [Term.eval, Op2.eval, Op1.eval, isC_eval hf h1, isC_eval hf h2]
    simp only [M, W] at *; omega
  · cases h

omit hf in
theorem notOf_eval {t x : Term} (h : notOf t x = true) : t.eval ρ = M - x.eval ρ := by
  unfold notOf at h
  split at h
  · next y => simp only [beq_iff_eq] at h; subst h; rfl
  · cases h

omit hf in
theorem complAdd_sound {l r : Term} (h : complAdd l r = true) : l.eval ρ = r.eval ρ := by
  unfold complAdd at h
  split at h
  · next a b x y =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    have hx := Term.eval_lt ρ x
    have hy := Term.eval_lt ρ y
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · simp only [Term.eval, Op2.eval, Op1.eval, notOf_eval h1]
      simp only [M, W] at *; omega
    · simp only [Term.eval, Op2.eval, Op1.eval, notOf_eval h1]
      simp only [M, W] at *; omega
  · cases h

omit hf in
theorem complSub_sound {l r : Term} (h : complSub l r = true) : l.eval ρ = r.eval ρ := by
  unfold complSub at h
  split at h
  · next a y x y' =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · have hx := Term.eval_lt ρ x
      have hy := Term.eval_lt ρ y'
      simp only [Term.eval, Op2.eval, Op1.eval, notOf_eval h1]
      simp only [M, W] at *; omega
    · have hx := Term.eval_lt ρ x
      have hy := Term.eval_lt ρ y'
      simp only [Term.eval, Op2.eval, Op1.eval, notOf_eval h1]
      simp only [M, W] at *; omega
  · cases h

omit hf in
theorem subNots_sound {l r : Term} (h : subNots l r = true) : l.eval ρ = r.eval ρ := by
  unfold subNots at h
  split at h
  · next a b y x =>
    simp only [Bool.and_eq_true] at h
    have hx := Term.eval_lt ρ x
    have hy := Term.eval_lt ρ y
    simp only [Term.eval, Op2.eval, notOf_eval h.1, notOf_eval h.2]
    simp only [M, W] at *; omega
  · cases h

theorem signedTop_sound {l r : Term} (h : signedTop kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold signedTop at h
  split at h
  · next b v c' x' =>
    split at h
    · next nb hnb =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hb, hc'⟩, h⟩ := h
      simp only [Term.eval, Op2.eval, Term.const?_eval hf hnb, isC_eval hf hc']
      split at h
      · next c x =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hc, rfl⟩ := h
        simp only [Term.eval, Op2.eval, isC_eval hf hc]
        exact signextend_shr hb (Term.eval_lt ρ _)
      · next i x =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hi⟩, rfl⟩ := h
        simp only [Term.eval, Op2.eval, isC_eval hf hi, byteW_zero_eq (Term.eval_lt ρ _)]
        exact signextend_shr hb (Term.eval_lt ρ _)
      · cases h
    · cases h
  · cases h

theorem shiftedByte_sound {l r : Term} (h : shiftedByte kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold shiftedByte at h
  split at h
  · next i o c x j x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next ni nc nj hi hc hj =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨hni, hnc, h8⟩, h⟩ := h
      have hk : nc = 8 * (nc / 8) := by omega
      simp only [Term.eval, Term.const?_eval hf hi, Term.const?_eval hf hc, Term.const?_eval hf hj]
      rcases h with ⟨⟨rfl, hlt⟩, rfl⟩ | ⟨⟨rfl, hle⟩, rfl⟩
      · have e := byte_shl (x := x'.eval ρ) hlt
        rw [← hk] at e
        simpa only [Op2.eval] using e
      · have e := byte_shr (x := x'.eval ρ) hle hni
        rw [← hk] at e
        simpa only [Op2.eval] using e
    · cases h
  · cases h

theorem dynPow2Div_sound {l r : Term} (h : dynPow2Div kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold dynPow2Div at h
  split at h
  · next x n one n' x' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, rfl⟩, rfl⟩ := h
    simp only [Term.eval, Op2.eval, isC_eval hf h1]
    by_cases hn : n'.eval ρ < 256
    · rw [shlW_one hn, shrW_eq_div hn, if_neg (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))]
    · simp [shlW, shrW, show 256 ≤ n'.eval ρ by omega]
  · cases h

omit hf in
theorem sarOf_sign {t x : Term} (h : sarOf t x = true) :
    t.eval ρ < 2 ^ 255 ↔ x.eval ρ < 2 ^ 255 := by
  unfold sarOf at h
  split at h
  · next c y =>
    simp only [beq_iff_eq] at h; subst h
    exact sarW_sign (Term.eval_lt ρ _)
  · cases h

theorem signTest_sound {l r : Term} (h : signTest kb l r = true) : l.eval ρ = r.eval ρ := by
  have neg : ∀ {t x : Term}, sarOf t x = true →
      (signed 256 (t.eval ρ) < 0 ↔ signed 256 (x.eval ρ) < 0) := fun hs => by
    rw [signed_neg (Term.eval_lt ρ _), signed_neg (Term.eval_lt ρ _), sarOf_sign hs]
  have nonneg : ∀ {t x : Term}, sarOf t x = true →
      (-1 < signed 256 (t.eval ρ) ↔ -1 < signed 256 (x.eval ρ)) := fun hs => by
    have := neg hs
    constructor <;> intro h' <;> omega
  unfold signTest at h
  split at h
  · next o a b o' x z =>
    have h0 : signed 256 0 = 0 := by decide
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (((⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩) |
      ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩) | ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩) <;>
      simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2, signed_M, h0]
    · simp only [neg h3]
    · simp only [nonneg h3]
    · simp only [neg h3]
    · simp only [nonneg h3]
  · cases h

theorem expTwo_sound {l r : Term} (h : expTwo kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold expTwo at h
  split at h
  · next b e e' one =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    simp only [Term.eval, Op2.eval, isC_eval hf h1, isC_eval hf h2]
    rw [expW_eq (Term.eval_lt ρ _)]
    by_cases hn : e'.eval ρ < 256
    · rw [shlW_one hn]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)
    · rw [show shlW (e'.eval ρ) 1 = 0 by simp [shlW, show 256 ≤ e'.eval ρ by omega]]
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.pow_dvd_pow 2 (by omega)
  · next b e b' b'' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, rfl⟩, rfl⟩ := h
    simp only [Term.eval, Op2.eval, isC_eval hf h1]
    rw [expW_eq (by decide), Nat.pow_two]
  · cases h

theorem modopUmod_sound {l r : Term} (h : modopUmod kb l r = true) : l.eval ρ = r.eval ρ := by
  unfold modopUmod at h
  split at h
  · next a b m x m' =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Term.eval, Op3.eval, Op2.eval, addmodW]
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp only [isC_eval hf h1, Nat.add_zero, Nat.zero_add]
  · next a b m x m' =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Term.eval, Op3.eval, Op2.eval, mulmodW]
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp only [isC_eval hf h1, Nat.mul_one, Nat.one_mul]
  · cases h

theorem checkS2_sound {l r : Term} (h : checkS2 kb l r = true) : l.eval ρ = r.eval ρ := by
  simp only [checkS2, Bool.or_eq_true, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact cancelCommon_sound hf h
  · exact quotientZero_sound hf h
  · exact complShl_sound hf h
  · exact complSub1_sound hf h
  · exact complAdd_sound h
  · exact complSub_sound h
  · exact subNots_sound h
  · exact signedTop_sound hf h
  · exact shiftedByte_sound hf h
  · exact dynPow2Div_sound hf h
  · exact signTest_sound hf h
  · exact expTwo_sound hf h
  · exact modopUmod_sound hf h

end Sound

end Fe.Sonatina.Steps.Schemas
