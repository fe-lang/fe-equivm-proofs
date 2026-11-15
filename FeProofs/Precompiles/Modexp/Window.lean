import FeProofs.Precompiles.Modexp.Ops
import FeProofs.Precompiles.Field.Checked

/-!
# Modexp: the exponent walk

`modexp.fe` raises to the exponent `e` left to right over sliding windows.  The walk starts at the
top set bit of `e`; from bit `i` (counted from the most significant end) a zero bit squares
once, and a window `[i, j)` ending in a set bit squares `j - i` times and multiplies by the odd
power `x ^ d` of the window's digit `d`, from a table of `x, x³, x⁵, …`.

- `ww`, `window_width_eq`: the window width `window_width` picks, between 1 and 7.
- `prefixOf`, `window_step`, `pow_window`: the walk's invariant, stated once for any monoid, so
  that the register (`small_power`), memory (`large_power`) and bit-by-bit (`low_power`) walks
  share it: after the steps up to bit `j` the accumulator is `x ^ prefixOf e total j`, the number
  the exponent's first `j` bits denote.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Modexp

/-! ## The window width -/

/-- One candidate width: `2 ^ (w - 1)` table products against `bits / (w + 1)` window
    products, kept when cheaper. -/
def wwStep (bits : ℕ) (st : ℕ × ℕ) (w : ℕ) : ℕ × ℕ :=
  if 2 ^ (w - 1) + bits / (w + 1) < st.2 then (w, 2 ^ (w - 1) + bits / (w + 1)) else st

/-- `window_width`: the cheapest width from 1 to 7. -/
def ww (bits : ℕ) : ℕ := ([2, 3, 4, 5, 6, 7].foldl (wwStep bits) (1, bits / 2)).1

theorem wwStep_bounds (bits : ℕ) (st : ℕ × ℕ) (w : ℕ) (h : 1 ≤ st.1 ∧ st.1 ≤ 7)
    (hw : 1 ≤ w ∧ w ≤ 7) : 1 ≤ (wwStep bits st w).1 ∧ (wwStep bits st w).1 ≤ 7 := by
  unfold wwStep; split_ifs <;> simp [h, hw]

theorem fold_bounds (bits : ℕ) : ∀ (l : List ℕ) (st : ℕ × ℕ), (∀ w ∈ l, 1 ≤ w ∧ w ≤ 7) →
    1 ≤ st.1 ∧ st.1 ≤ 7 → 1 ≤ (l.foldl (wwStep bits) st).1 ∧ (l.foldl (wwStep bits) st).1 ≤ 7
  | [], _, _, h => h
  | w :: l, st, hl, h =>
    fold_bounds bits l _ (fun v hv => hl v (List.mem_cons_of_mem _ hv))
      (wwStep_bounds bits st w h (hl w List.mem_cons_self))

theorem ww_bounds (bits : ℕ) : 1 ≤ ww bits ∧ ww bits ≤ 7 :=
  fold_bounds bits _ _ (by decide) (by simp)

theorem pow_lt256 {k : ℕ} (hk : k < 256) : 2 ^ k < 2 ^ 256 :=
  Nat.pow_lt_pow_right (by norm_num) hk

theorem shl_one_lit {k : ℕ} (hk : k < 255) :
    UInt256.ofNat 1 <<< UInt256.ofNat k = UInt256.ofNat (2 ^ k) := by
  apply word_eq_of_toNat
  have h1 : (UInt256.ofNat 1).toNat = 1 := toNat_lit (by norm_num)
  rw [shiftLeft_toNat _ (by omega) (by rw [h1, Nat.one_mul]; exact pow_lt256 (by omega)), h1,
    Nat.mul_one, toNat_lit (pow_lt256 (by omega))]

theorem checkedSub_lit {a b : ℕ} (ha : a < 2 ^ 256) (h : b ≤ a) :
    checkedSub (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a - b)) := by
  unfold checkedSub
  rw [toNat_lit ha, toNat_lit (by omega), ite_eq_right (by omega)]
  congr 1
  apply word_eq_of_toNat
  rw [usub_toNat (by rw [toNat_lit ha, toNat_lit (by omega)]; exact h), toNat_lit ha,
    toNat_lit (by omega), toNat_lit (by omega)]

/-- One pass of `window_width`'s loop. -/
theorem ww_b1_step (bits best cost w : ℕ) (hb : bits < 2 ^ 64) (hcost : cost < 2 ^ 64) (hw : 2 ≤ w ∧ w ≤ 7) :
    window_width.b1 (UInt256.ofNat bits) (UInt256.ofNat best) (UInt256.ofNat cost)
        (UInt256.ofNat w) =
      window_width.b1 (UInt256.ofNat bits) (UInt256.ofNat (wwStep bits (best, cost) w).1)
        (UInt256.ofNat (wwStep bits (best, cost) w).2) (UInt256.ofNat (w + 1)) := by
  have hp : 2 ^ (w - 1) ≤ 64 := by
    rcases hw with ⟨h1, h2⟩; interval_cases w <;> norm_num
  have hdiv : bits / (w + 1) < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hb
  rw [window_width.b1.eq_1]
  simp only [toNat_lit (show w < 2 ^ 256 by omega), toNat_lit (show 7 < 2 ^ 256 by norm_num),
    show w ≤ 7 from hw.2, decide_true, ite_true,
    checkedSub_lit (show w < 2 ^ 256 by omega) (show 1 ≤ w by omega),
    pure_bind, shl_one_lit (show w - 1 < 255 by omega),
    checkedAdd_small (show w + 1 < 2 ^ 256 by omega),
    checkedDiv_lit (show bits < 2 ^ 256 by omega) (show w + 1 < 2 ^ 256 by omega) (by omega),
    checkedAdd_small (show 2 ^ (w - 1) + bits / (w + 1) < 2 ^ 256 by omega),
    toNat_lit (show 2 ^ (w - 1) + bits / (w + 1) < 2 ^ 256 by omega),
    toNat_lit (show cost < 2 ^ 256 by omega), wwStep, decide_eq_true_eq]
  split_ifs <;> rfl

theorem wwStep_snd_le (bits : ℕ) (st : ℕ × ℕ) (w : ℕ) : (wwStep bits st w).2 ≤ st.2 := by
  unfold wwStep; split_ifs <;> simp; omega

/-- The loop from width `w` on, over the widths of `l`. -/
theorem ww_b1_fold (bits : ℕ) (hb : bits < 2 ^ 64) :
    ∀ (l : List ℕ) (st : ℕ × ℕ) (w : ℕ), l = List.range' w (8 - w) → 2 ≤ w → w ≤ 8 →
      st.2 < 2 ^ 64 →
      window_width.b1 (UInt256.ofNat bits) (UInt256.ofNat st.1) (UInt256.ofNat st.2)
          (UInt256.ofNat w) =
        pure (UInt256.ofNat (l.foldl (wwStep bits) st).1)
  | [], st, w, hl, hw2, hw8, hst => by
    have : w = 8 := by
      by_contra h; have : 8 - w ≠ 0 := by omega
      have := congrArg List.length hl; simp at this; omega
    subst this
    rw [window_width.b1.eq_1]
    simp [toNat_lit (show 8 < 2 ^ 256 by norm_num), toNat_lit (show 7 < 2 ^ 256 by norm_num)]
  | v :: l, st, w, hl, hw2, hw8, hst => by
    have hw8' : w < 8 := by
      by_contra h; have : 8 - w = 0 := by omega
      rw [this] at hl; simp at hl
    have hv : v = w := by
      rw [show 8 - w = (8 - (w + 1)) + 1 by omega, List.range'_succ] at hl
      exact (List.cons.inj hl).1
    have hl' : l = List.range' (w + 1) (8 - (w + 1)) := by
      rw [show 8 - w = (8 - (w + 1)) + 1 by omega, List.range'_succ] at hl
      exact (List.cons.inj hl).2
    subst hv
    rw [ww_b1_step bits st.1 st.2 v hb hst ⟨hw2, by omega⟩, Prod.mk.eta, List.foldl_cons]
    exact ww_b1_fold bits hb l _ (v + 1) hl' (by omega) (by omega)
      (lt_of_le_of_lt (wwStep_snd_le bits st v) hst)

/-- **`window_width`** of a bit count below `2 ^ 64` is `ww`. -/
theorem window_width_eq (bits : ℕ) (hb : bits < 2 ^ 64) :
    window_width (UInt256.ofNat bits) = pure (UInt256.ofNat (ww bits)) := by
  unfold window_width
  simp only [checkedDiv_lit (show bits < 2 ^ 256 by omega) (show 2 < 2 ^ 256 by norm_num)
    (by norm_num), pure_bind]
  exact ww_b1_fold bits hb _ (1, bits / 2) 2 rfl le_rfl (by norm_num) (by simp; omega)

/-! ## The walk -/

/-- The number the first `j` of the `total` bits of `e` denote, most significant first. -/
def prefixOf (e total j : ℕ) : ℕ := e / 2 ^ (total - j)

/-- The digit of the bits `[i, j)`, most significant first. -/
def digitOf (e total i j : ℕ) : ℕ := e / 2 ^ (total - j) % 2 ^ (j - i)

/-- Bit `i` from the most significant end. -/
def bitOf (e total i : ℕ) : ℕ := e / 2 ^ (total - 1 - i) % 2

theorem prefixOf_total (e total : ℕ) : prefixOf e total total = e := by simp [prefixOf]

/-- Before the top set bit the prefix is zero. -/
theorem prefixOf_zero {e total j : ℕ} (h : e < 2 ^ (total - j)) : prefixOf e total j = 0 :=
  Nat.div_eq_of_lt h

/-- **A window step**: the prefix up to `j` is the prefix up to `i`, shifted, and the digit. -/
theorem window_step (e total i j : ℕ) (hij : i ≤ j) (hj : j ≤ total) :
    prefixOf e total j = prefixOf e total i * 2 ^ (j - i) + digitOf e total i j := by
  unfold prefixOf digitOf
  have h : total - i = (total - j) + (j - i) := by omega
  rw [h, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ _).symm

/-- A one-bit step. -/
theorem bit_step (e total i : ℕ) (hi : i < total) :
    prefixOf e total (i + 1) = 2 * prefixOf e total i + bitOf e total i := by
  have := window_step e total i (i + 1) (by omega) (by omega)
  rw [this, show i + 1 - i = 1 by omega, pow_one, Nat.mul_comm]
  unfold digitOf bitOf
  rw [show total - (i + 1) = total - 1 - i by omega, show i + 1 - i = 1 by omega, pow_one]

/-- **The walk's invariant, in any monoid**: squaring `j - i` times the power of the prefix up to
    `i`, then multiplying by the digit's power, gives the power of the prefix up to `j`. -/
theorem pow_window {M : Type*} [Monoid M] (x : M) (e total i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ total) :
    x ^ prefixOf e total j = (x ^ prefixOf e total i) ^ (2 ^ (j - i)) * x ^ digitOf e total i j := by
  rw [window_step e total i j hij hj, pow_add, pow_mul]

/-- Squaring `n` times is raising to `2 ^ n`. -/
theorem iterate_sq {M : Type*} [Monoid M] (y : M) (n : ℕ) :
    (fun z => z * z)^[n] y = y ^ (2 ^ n) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← pow_two, ← pow_mul, pow_succ]

end FeProofs.Modexp
