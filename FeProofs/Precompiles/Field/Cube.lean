import Mathlib.FieldTheory.Finite.Basic
import Ethereum.Weierstrass.Curve

/-!
# Precompiles: `x ^ 3 + c` without a root

A short Weierstrass curve `y² = x³ + c` has a point with `y = 0` exactly when `x ^ 3 + c` has a
root, and the curve code of fevm doubles such a point to infinity without dividing by `y`.  For a
prime `q ≡ 1 (mod 3)`, `x ^ 3 = -c` gives `(-c) ^ ((q - 1) / 3) = x ^ (q - 1) = 1`; a modular
power that a decision procedure evaluates (`powMod`, square-and-multiply) shows it is not one, so
there is no root (`cube_add_ne_zero`).
-/

namespace FeProofs.Precompiles

/-- `b ^ e mod m` by square-and-multiply over `f` bits, times `acc`. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, e, acc => powMod m f (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

theorem powMod_eq (m : ℕ) :
    ∀ f b e acc, e < 2 ^ f → (powMod m f b e acc : ZMod m) = acc * (b : ZMod m) ^ e
  | 0, b, e, acc, he => by
    obtain rfl : e = 0 := by simpa using he
    simp [powMod]
  | f + 1, b, e, acc, he => by
    rw [powMod, powMod_eq m f _ _ _ (by rw [pow_succ] at he; omega)]
    have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [if_neg (by omega)]
      conv_rhs => rw [hsplit, h]
      push_cast [ZMod.natCast_mod]
      ring
    · rw [if_pos h]
      conv_rhs => rw [hsplit, h]
      push_cast [ZMod.natCast_mod]
      ring

/-- `x ^ 3 + c` has no root modulo a prime `q ≡ 1 (mod 3)` when `(-c) ^ ((q - 1) / 3)` is not
one. -/
theorem cube_add_ne_zero {q : ℕ} [Fact q.Prime] {c : ℕ} (hc0 : 0 < c) (hcq : c < q)
    (h3 : 3 * ((q - 1) / 3) = q - 1) (hq : (q - 1) / 3 < 2 ^ 256)
    (h : powMod q 256 (q - c) ((q - 1) / 3) 1 % q ≠ 1) (x : ZMod q) : x ^ 3 + c ≠ 0 := by
  intro hx3
  have hx : x ≠ 0 := by
    rintro rfl
    exact Ethereum.Weierstrass.natCast_ne_zero hc0 hcq (by simpa using hx3)
  have hc : x ^ 3 = ((q - c : ℕ) : ZMod q) := by
    rw [Nat.cast_sub hcq.le, ZMod.natCast_self, zero_sub]
    linear_combination hx3
  apply h
  have hm := powMod_eq q 256 (q - c) ((q - 1) / 3) 1 hq
  rw [← hc, ← pow_mul, h3, ZMod.pow_card_sub_one_eq_one hx, Nat.cast_one, mul_one] at hm
  have h1 : ((powMod q 256 (q - c) ((q - 1) / 3) 1 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [hm, Nat.cast_one]
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h1).trans
    (Nat.mod_eq_of_lt (Fact.out : q.Prime).one_lt)

end FeProofs.Precompiles
