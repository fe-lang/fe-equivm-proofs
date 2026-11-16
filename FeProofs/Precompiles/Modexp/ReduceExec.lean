import FeProofs.Precompiles.Modexp.ReduceMain

/-!
# Modexp: `Modulus::reduce`

Pieces for the function-level statement of `md.reduce(work, count)` (not yet proved): with
`count, n < ws.length`, the first `max count n + 1` limbs of the work array become those of
`X mod M`, `X` the number of its first `count` limbs, and nothing else in memory changes.

- `putLimbs_prefix`: the final memory, from the loops' `putLimbs Mem wp (lf g L)` form;
- `lf_getD`: the initial memory in that form;
- `ModAt.ge`: the modulus has `n` limbs; `limbAt_high`, `take_limbAt`: limbs of the dividend.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- **A write over a prefix**: memory holding `ls` at `p`, with all its limbs rewritten by `g`,
    which keeps them from `K'` on and agrees with `rs` below, is memory with `rs` written. -/
theorem putLimbs_prefix {Mem : ByteArray} {p : ℕ} {ls rs : List Limb} (hL : LimbsAt Mem p ls)
    (hKL : rs.length ≤ ls.length) (g : ℕ → Limb)
    (hlo : ∀ k (hk : k < rs.length), g k = rs[k])
    (hhi : ∀ k (hk : k < ls.length), rs.length ≤ k → g k = ls[k]) :
    putLimbs Mem p (lf g ls.length) = putLimbs Mem p rs := by
  have hb := hL.1
  have hb' : p + 8 * (lf g ls.length).length ≤ Mem.size := by simpa using hb
  have hG := limbsAt_putLimbs hb'
  apply eq_putLimbs (putLimbs_size hb') ⟨by rw [putLimbs_size hb']; omega, fun i hi => by
    rw [hG.2 i (by simp; omega), lf_get _ (by omega), hlo i hi]⟩
  intro j hj
  by_cases hj' : j < p ∨ p + 8 * ls.length ≤ j
  · exact byteAt_putLimbs_out hb' (by simpa using hj')
  · obtain ⟨i, r, hi, hr, rfl⟩ : ∃ i r, i < ls.length ∧ r < 8 ∧ j = p + 8 * i + r :=
      ⟨(j - p) / 8, (j - p) % 8, by omega, by omega, by omega⟩
    rw [byte_of_limbsAt hG (by simpa using hi) hr, byte_of_limbsAt hL hi hr, lf_get _ hi,
      hhi i hi (by omega)]

/-- The limbs of a list, as a function. -/
theorem lf_getD (ws : List Limb) : lf (fun k => ws.getD k 0) ws.length = ws := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [lf_length] at h1
  rw [lf_get _ h1, List.getD_eq_getElem _ _ h1]

/-- The modulus of a `ModAt` has `n` limbs. -/
theorem ModAt.ge {md : Exported.Modexp.Modulus} {M n s : ℕ} {mem : ByteArray} (h : ModAt md M n s mem) :
    2 ^ (64 * (n - 1)) ≤ M := by
  have h1 := h.top
  have h2 : M * 2 ^ s ≤ M * 2 ^ 63 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by
    have := h.s_lt; omega))
  have h3 : 2 ^ (64 * n - 1) = 2 ^ (64 * (n - 1)) * 2 ^ 63 := by
    rw [← pow_add]; congr 1; have := h.pos; omega
  rw [h3] at h1
  exact Nat.le_of_mul_le_mul_right (h1.trans h2) (by positivity)

/-- A limb of a number below `2 ^ (64 k)`, at `k` or above, is zero. -/
theorem limbAt_high {N k i : ℕ} (hN : N < 2 ^ (64 * k)) (hi : k ≤ i) : limbAt N i = 0 :=
  Fin.ext (by
    simp only [limbAt]
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl)

/-- The limbs a list's prefix holds are those of its number. -/
theorem take_limbAt (ws : List Limb) {c k : ℕ} (hk : k < c) (hc : c ≤ ws.length) :
    ws.getD k 0 = limbAt (val (ws.take c)) k := by
  rw [List.getD_eq_getElem _ _ (by omega), ← getElem_limbAt (ws.take c) (k := k) (by simp; omega),
    List.getElem_take]

end FeProofs.Modexp
