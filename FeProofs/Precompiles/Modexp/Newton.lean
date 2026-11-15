import FeProofs.Precompiles.Modexp.SmallRows
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Modexp: the Montgomery inverse by Newton's iteration

`small_power` (as `Montgomery::new`) computes `-m⁻¹ mod 2 ^ 64` from the low limb `a` of the odd
modulus: `x := a`, then five times `x := x (2 - a x)`, all modulo `2 ^ 64`, and negates.  Each
step squares the error, `1 - a x' = (1 - a x) ^ 2`, and `1 - a ^ 2` is a multiple of 8 for an odd
`a`, so after five steps the error is a multiple of `8 ^ 32 = 2 ^ 96`: `newton_inv` proves the
result is `InvOk`, the hypothesis of the Montgomery products.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- One Newton step towards `a⁻¹ mod 2 ^ 64`. -/
def newton (a x : Limb) : Limb := mulLo x (subMod ⟨2, by norm_num⟩ (mulLo a x))

/-- `small_power`'s inverse: five steps from `a`, negated. -/
def minv (a : Limb) : Limb := subMod 0 ((newton a)^[5] a)

/-- A limb in `ZMod (2 ^ 64)`. -/
def zl (x : Limb) : ZMod (2 ^ 64) := (x.val : ZMod (2 ^ 64))

theorem zl_mulLo (a b : Limb) : zl (mulLo a b) = zl a * zl b := by
  simp only [zl, mulLo, ZMod.natCast_mod, Nat.cast_mul]

theorem zl_subMod (a b : Limb) : zl (subMod a b) = zl a - zl b := by
  have hb := b.isLt
  simp only [zl, subMod, ZMod.natCast_mod]
  rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]
  ring

theorem newton_err (a x : Limb) : 1 - zl a * zl (newton a x) = (1 - zl a * zl x) ^ 2 := by
  simp only [newton, zl_mulLo, zl_subMod]
  have : zl ⟨2, by norm_num⟩ = 2 := by simp [zl]
  rw [this]
  ring

theorem newton_iter (a : Limb) : ∀ n x, 1 - zl a * zl ((newton a)^[n] x) = (1 - zl a * zl x) ^ 2 ^ n
  | 0, x => by simp
  | n + 1, x => by
    rw [Function.iterate_succ_apply', newton_err, newton_iter a n x, ← pow_mul, ← pow_succ]

/-- **The inverse is right**: for an odd low limb `a`, `a · minv a ≡ -1 (mod 2 ^ 64)`. -/
theorem newton_inv (a : Limb) (ha : a.val % 2 = 1) : InvOk a (minv a) := by
  obtain ⟨t, ht⟩ : ∃ t, a.val * a.val = 8 * t + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, a.val = 2 * k + 1 := ⟨a.val / 2, by omega⟩
    rw [hk]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩ <;> subst hj
    · exact ⟨j * (2 * j + 1), by ring⟩
    · exact ⟨(2 * j + 1) * (j + 1), by ring⟩
  have h8 : 1 - zl a * zl a = -(8 * (t : ZMod (2 ^ 64))) := by
    have : zl a * zl a = 8 * (t : ZMod (2 ^ 64)) + 1 := by
      simp only [zl]; rw [← Nat.cast_mul, ht]; push_cast; ring
    rw [this]; ring
  have hzero : (2 : ZMod (2 ^ 64)) ^ 64 = 0 := by
    rw [show (2 : ZMod (2 ^ 64)) ^ 64 = ((2 ^ 64 : ℕ) : ZMod (2 ^ 64)) by push_cast; rfl,
      ZMod.natCast_self]
  have he : 1 - zl a * zl ((newton a)^[5] a) = 0 := by
    rw [newton_iter, h8, show (2 : ℕ) ^ 5 = 32 from rfl, neg_pow, mul_pow,
      show (8 : ZMod (2 ^ 64)) ^ 32 = 2 ^ 64 * 2 ^ 32 by norm_num, hzero]
    ring
  have hz : zl a * zl (minv a) = -1 := by
    rw [minv, zl_subMod, show zl 0 = 0 by simp [zl]]
    linear_combination he
  unfold InvOk
  have hc : ((a.val * (minv a).val : ℕ) : ZMod (2 ^ 64)) = ((2 ^ 64 - 1 : ℕ) : ZMod (2 ^ 64)) := by
    rw [Nat.cast_mul]
    change zl a * zl (minv a) = _
    rw [hz, Nat.cast_sub (by norm_num), ZMod.natCast_self]
    simp
  rw [ZMod.natCast_eq_natCast_iff'] at hc
  rw [hc]
  norm_num

end FeProofs.Modexp
