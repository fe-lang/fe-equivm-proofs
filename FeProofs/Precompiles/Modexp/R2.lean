import FeProofs.Precompiles.Modexp.SmallRep
import Mathlib.Data.Nat.Prime.Basic

/-!
# Modexp: `R² mod m` in registers

`Small::r2` starts from `2 ^ (64 (L - 1) + s)`, the top bit of the modulus `m` (`s` the position
of the top bit of its limb `L - 1`), doubles it `64 - s + L` times modulo `m` to `2 ^ L R mod m`,
and squares that six times in Montgomery form: `2 ^ L R` stands for `2 ^ L`, and `(2 ^ L) ^ 64` is
`R`, which stands as `R R mod m`.  `r2` is that computation on limbs and `r2_spec` its value, for
an odd `m > 1` of `L` limbs whose top limb is not zero.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- Limb `L - 1` of the modulus. -/
def topLimb (L : ℕ) (m : L4) : Limb :=
  if L = 1 then m.l0 else if L = 2 then m.l1 else if L = 3 then m.l2 else m.l3

theorem log2_lt64 (x : Limb) : x.val.log2 < 64 := by
  rcases Nat.eq_zero_or_pos x.val with h | h
  · rw [h]; decide
  · exact (Nat.log2_lt (by omega)).mpr x.isLt

/-- The limb `2 ^ s`. -/
def bitL (s : ℕ) (hs : s < 64) : Limb := ⟨2 ^ s, Nat.pow_lt_pow_right (by norm_num) hs⟩

/-- `2 ^ (64 (L - 1) + s)`: the top bit of the modulus, at its place. -/
def r2start (L : ℕ) (m : L4) : L4 :=
  let b := bitL _ (log2_lt64 (topLimb L m))
  ⟨if L = 1 then b else 0, if L = 2 then b else 0, if L = 3 then b else 0, if L = 4 then b else 0⟩

/-- Montgomery squaring. -/
def ssq (L : ℕ) (m : L4) (inv : Limb) (x : L4) : L4 := smul L m inv x x

/-- `Small::r2`. -/
def r2 (L : ℕ) (m : L4) (inv : Limb) : L4 :=
  (ssq L m inv)^[6] ((sdouble m)^[64 - (topLimb L m).val.log2 + L] (r2start L m))

theorem nat4_r2start (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) :
    nat4 (r2start L m) = 2 ^ (64 * (L - 1)) * 2 ^ (topLimb L m).val.log2 := by
  obtain ⟨h1, h4⟩ := hL
  interval_cases L <;> simp [r2start, nat4, bitL]

theorem top_le (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) :
    2 ^ (64 * (L - 1)) * (topLimb L m).val ≤ nat4 m := by
  obtain ⟨h1, h4⟩ := hL
  interval_cases L <;> simp only [topLimb, nat4] <;> norm_num <;> omega

/-- The start is below the modulus. -/
theorem r2start_lt (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) (hodd : nat4 m % 2 = 1)
    (hm1 : 1 < nat4 m) (htop : 0 < (topLimb L m).val) : nat4 (r2start L m) < nat4 m := by
  have hle : nat4 (r2start L m) ≤ nat4 m := by
    rw [nat4_r2start L hL]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.log2_self_le (by omega))) (top_le L hL m)
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  exfalso
  rw [nat4_r2start L hL, ← pow_add] at h
  rcases Nat.eq_zero_or_pos (64 * (L - 1) + (topLimb L m).val.log2) with h0 | h0
  · rw [h0] at h; omega
  · rw [← h, show 64 * (L - 1) + (topLimb L m).val.log2 =
      (64 * (L - 1) + (topLimb L m).val.log2 - 1) + 1 by omega, pow_succ] at hodd
    omega

/-- Doubling `n` times. -/
theorem sdouble_iter (m x : L4) (hx : nat4 x < nat4 m) :
    ∀ n, nat4 ((sdouble m)^[n] x) = 2 ^ n * nat4 x % nat4 m
  | 0 => by simp [Nat.mod_eq_of_lt hx]
  | n + 1 => by
    have ih := sdouble_iter m x hx n
    have hpos : 0 < nat4 m := by omega
    rw [Function.iterate_succ_apply', (sdouble_spec m _ (by rw [ih]; exact Nat.mod_lt _ hpos)).1,
      ih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
    ring_nf

/-- Squaring `n` times in Montgomery form. -/
theorem ssq_iter (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hm : nat4 m < 2 ^ (64 * L)) (hcop : Nat.Coprime (2 ^ (64 * L)) (nat4 m)) :
    ∀ n (x : L4) (a : ℕ), MRep (2 ^ (64 * L)) m x a →
      MRep (2 ^ (64 * L)) m ((ssq L m inv)^[n] x) (a ^ 2 ^ n)
  | 0, x, a, h => by simpa using h
  | n + 1, x, a, h => by
    rw [Function.iterate_succ_apply, show a ^ 2 ^ (n + 1) = (a * a) ^ 2 ^ n by
      rw [pow_succ, pow_mul, sq, mul_pow]]
    exact ssq_iter L hL m inv hinv hm hcop n _ _ (mrep_mul L hL m x x inv a a hinv hm hcop h h)

/-- An odd modulus is coprime to `R`. -/
theorem coprime_R (L : ℕ) (m : L4) (hodd : nat4 m % 2 = 1) :
    Nat.Coprime (2 ^ (64 * L)) (nat4 m) :=
  Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr hodd))

/-- **`Small::r2` is `R² mod m`** for an odd `m > 1` of `L` limbs with a nonzero top limb. -/
theorem r2_spec (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hm : nat4 m < 2 ^ (64 * L)) (hodd : nat4 m % 2 = 1) (hm1 : 1 < nat4 m)
    (htop : 0 < (topLimb L m).val) :
    nat4 (r2 L m inv) = 2 ^ (64 * L) * 2 ^ (64 * L) % nat4 m := by
  have hcop := coprime_R L m hodd
  have hs := log2_lt64 (topLimb L m)
  have hx0 := r2start_lt L hL m hodd hm1 htop
  have hd := sdouble_iter m _ hx0 (64 - (topLimb L m).val.log2 + L)
  rw [nat4_r2start L hL, ← pow_add, ← pow_add,
    show 64 - (topLimb L m).val.log2 + L + (64 * (L - 1) + (topLimb L m).val.log2) =
      L + 64 * L by omega, pow_add] at hd
  have hrep : MRep (2 ^ (64 * L)) m ((sdouble m)^[64 - (topLimb L m).val.log2 + L] (r2start L m))
      (2 ^ L) := ⟨by rw [hd]; exact Nat.mod_lt _ (by omega), by rw [hd]; exact Nat.mod_modEq _ _⟩
  obtain ⟨hlt, heq⟩ := ssq_iter L hL m inv hinv hm hcop 6 _ _ hrep
  rw [← pow_mul, show L * 2 ^ 6 = 64 * L by ring] at heq
  rw [r2, ← Nat.mod_eq_of_lt hlt]
  exact heq

end FeProofs.Modexp
