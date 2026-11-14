import FeProofs.Precompiles.Secp256k1.Purify
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.ClearExcept

/-!
# Ecrecover: what the Montgomery arithmetic computes

For a modulus `K` whose limbs make a `p` with `INV · p ≡ -1 (mod 2 ^ 64)` (`Modulus.Valid`,
which makes `p` odd), the functions of `MontPure.lean` compute Montgomery arithmetic modulo
`p`.  Four limbs `a` represent `x : ZMod p` (`Rep K a x`) when their value is below `p` and is
`x R` modulo `p`, for `R = 2 ^ 256`.  Under it `mul`, `add`, `sub`, `new` and the rest compute
the field operations (`mul_rep` and the rest).  The proofs are on natural numbers: each carry
chain is an integer identity (`shiftReduced_spec`, `row_spec`), from which the bounds and the
congruences follow.

The last sections check the constants of the two moduli by `decide` (`KB_valid`, `KB_R2`, …)
and state the result for each exported method (`Mont_mul_Base_rep` and the rest).
-/

set_option exponentiation.threshold 512

namespace FeProofs.Ecrecover

/-- The modulus the limbs `P0 … P3` denote. -/
def Modulus.p (K : Modulus) : ℕ :=
  K.P0.val + 2 ^ 64 * K.P1.val + 2 ^ 128 * K.P2.val + 2 ^ 192 * K.P3.val

/-- What the Montgomery arithmetic needs of its constants: `INV = -p⁻¹ mod 2 ^ 64`. -/
def Modulus.Valid (K : Modulus) : Prop := (K.P0.val * K.INV.val + 1) % 2 ^ 64 = 0

theorem Modulus.p_lt (K : Modulus) : K.p < 2 ^ 256 := by
  have := K.P0.isLt; have := K.P1.isLt; have := K.P2.isLt; have := K.P3.isLt
  unfold Modulus.p; omega

namespace Mont

/-- The number four limbs denote. -/
def val (a : L4) : ℕ := a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val + 2 ^ 192 * a.l3.val

theorem val_lt (a : L4) : val a < 2 ^ 256 := by
  have := a.l0.isLt; have := a.l1.isLt; have := a.l2.isLt; have := a.l3.isLt
  unfold val; omega

variable {K : Modulus}

/-- The multiplier `m = s₀ · INV mod 2 ^ 64` clears the low limb of `s + m p`. -/
theorem low_cleared (hK : K.Valid) (s0 : Limb) :
    (s0.val + (mulLo (mulLo s0 K.INV) K.P0).val) % 2 ^ 64 = 0 := by
  unfold Modulus.Valid at hK
  simp only [mulLo]
  have h1 : s0.val * K.INV.val % 2 ^ 64 * K.P0.val % 2 ^ 64 ≡
      s0.val * K.INV.val * K.P0.val [MOD 2 ^ 64] :=
    (Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul_right _)
  have e : s0.val + s0.val * K.INV.val % 2 ^ 64 * K.P0.val % 2 ^ 64 ≡
      s0.val * (K.P0.val * K.INV.val + 1) [MOD 2 ^ 64] := by
    refine (h1.add_left _).trans ?_
    rw [show s0.val + s0.val * K.INV.val * K.P0.val = s0.val * (K.P0.val * K.INV.val + 1) by
      ring]
  unfold Nat.ModEq at e
  rw [e, Nat.mul_mod, hK, Nat.mul_zero, Nat.zero_mod]

/-- `shift_reduced` is the integer `(s + m p) / 2 ^ 64` for the `m` that makes it exact, when
`s + m p` has fewer than 384 bits. -/
theorem shiftReduced_spec (hK : K.Valid) (s0 s1 s2 s3 s4 s5 : Limb)
    (hS : s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val + 2 ^ 256 * s4.val +
      2 ^ 320 * s5.val + 2 ^ 64 * K.p < 2 ^ 384) :
    ∃ m < 2 ^ 64, 2 ^ 64 * (val (shiftReduced K s0 s1 s2 s3 s4 s5).1 +
        2 ^ 256 * (shiftReduced K s0 s1 s2 s3 s4 s5).2.val) =
      s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val + 2 ^ 256 * s4.val +
        2 ^ 320 * s5.val + m * K.p := by
  refine ⟨(mulLo s0 K.INV).val, (mulLo s0 K.INV).isLt, ?_⟩
  have hlow := low_cleared hK s0
  unfold shiftReduced
  extract_lets m k0 j0 ca0 u1 cb1 k1 j1 u1' ca1 u2 cb2 k2 j2 u2' ca2 u3 cb3 k3 j3 u3' ca3 u4 cb4
    u4' ca4 u5
  change _ = _ + m.val * K.p
  have e0 : k0.val + 2 ^ 64 * j0.val = m.val * K.P0.val := mulLo_add_mulHi m K.P0
  have e1 : k1.val + 2 ^ 64 * j1.val = m.val * K.P1.val := mulLo_add_mulHi m K.P1
  have e2 : k2.val + 2 ^ 64 * j2.val = m.val * K.P2.val := mulLo_add_mulHi m K.P2
  have e3 : k3.val + 2 ^ 64 * j3.val = m.val * K.P3.val := mulLo_add_mulHi m K.P3
  have a0 : (adcLo s0 k0 0).val + 2 ^ 64 * ca0.val = s0.val + k0.val + 0 :=
    adcLo_add_adcHi s0 k0 0
  have a1 : u1.val + 2 ^ 64 * cb1.val = s1.val + j0.val + 0 := adcLo_add_adcHi s1 j0 0
  have a2 : u1'.val + 2 ^ 64 * ca1.val = u1.val + k1.val + ca0.val := adcLo_add_adcHi u1 k1 ca0
  have a3 : u2.val + 2 ^ 64 * cb2.val = s2.val + j1.val + cb1.val := adcLo_add_adcHi s2 j1 cb1
  have a4 : u2'.val + 2 ^ 64 * ca2.val = u2.val + k2.val + ca1.val := adcLo_add_adcHi u2 k2 ca1
  have a5 : u3.val + 2 ^ 64 * cb3.val = s3.val + j2.val + cb2.val := adcLo_add_adcHi s3 j2 cb2
  have a6 : u3'.val + 2 ^ 64 * ca3.val = u3.val + k3.val + ca2.val := adcLo_add_adcHi u3 k3 ca2
  have a7 : u4.val + 2 ^ 64 * cb4.val = s4.val + j3.val + cb3.val := adcLo_add_adcHi s4 j3 cb3
  have a8 : u4'.val + 2 ^ 64 * ca4.val = u4.val + 0 + ca3.val := adcLo_add_adcHi u4 0 ca3
  have a9 : u5.val + 2 ^ 64 * (adcHi s5 cb4 ca4).val = s5.val + cb4.val + ca4.val :=
    adcLo_add_adcHi s5 cb4 ca4
  have hlo : (adcLo s0 k0 0).val = 0 := by
    simp only [adcLo, Fin.val_zero, Nat.add_zero]; exact hlow
  generalize adcLo s0 k0 0 = lo0 at a0 hlo
  generalize adcHi s5 cb4 ca4 = c5 at a9 ⊢
  clear_value m k0 j0 ca0 u1 cb1 k1 j1 u1' ca1 u2 cb2 k2 j2 u2' ca2 u3 cb3 k3 j3 u3' ca3 u4 cb4
    u4' ca4 u5
  have hp : m.val * K.p = m.val * K.P0.val + 2 ^ 64 * (m.val * K.P1.val) +
      2 ^ 128 * (m.val * K.P2.val) + 2 ^ 192 * (m.val * K.P3.val) := by
    unfold Modulus.p; ring
  -- The chain is the integer identity, with `c5` the carry the code drops.
  have key : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val + 2 ^ 320 * s5.val + m.val * K.p : ℤ) =
      2 ^ 64 * u1'.val + 2 ^ 128 * u2'.val + 2 ^ 192 * u3'.val + 2 ^ 256 * u4'.val +
        2 ^ 320 * u5.val + 2 ^ 384 * c5.val := by
    zify at e0 e1 e2 e3 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 hlo hp
    rw [hp]
    linear_combination -a0 - 2 ^ 64 * a1 - 2 ^ 64 * a2 - 2 ^ 128 * a3 - 2 ^ 128 * a4 -
      2 ^ 192 * a5 - 2 ^ 192 * a6 - 2 ^ 256 * a7 - 2 ^ 256 * a8 - 2 ^ 320 * a9 - e0 -
      2 ^ 64 * e1 - 2 ^ 128 * e2 - 2 ^ 192 * e3 + hlo
  have hmp : m.val * K.p ≤ 2 ^ 64 * K.p := Nat.mul_le_mul_right _ m.isLt.le
  have hc : c5.val = 0 := by
    by_contra hne
    have h1 : 1 ≤ c5.val := Nat.one_le_iff_ne_zero.mpr hne
    have : (1 : ℤ) ≤ c5.val := by exact_mod_cast h1
    have : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val + 2 ^ 320 * s5.val + m.val * K.p : ℤ) < 2 ^ 384 := by
      have : (m.val * K.p : ℤ) ≤ 2 ^ 64 * K.p := by exact_mod_cast hmp
      have : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val + 2 ^ 256 * s4.val +
        2 ^ 320 * s5.val + 2 ^ 64 * K.p : ℤ) < 2 ^ 384 := by exact_mod_cast hS
      linarith
    have : (0 : ℤ) ≤ 2 ^ 64 * u1'.val + 2 ^ 128 * u2'.val + 2 ^ 192 * u3'.val +
        2 ^ 256 * u4'.val + 2 ^ 320 * u5.val := by positivity
    linarith
  simp only [val]
  zify
  rw [hc] at key
  push_cast at key ⊢
  linear_combination -key

theorem mul_val_lt (b : Limb) (a : L4) : b.val * val a < 2 ^ 320 := by
  have := Nat.mul_lt_mul'' b.isLt (val_lt a)
  simpa using this

/-- `first_row`: `(b a + m p) / 2 ^ 64` for the `m` that makes it exact. -/
theorem firstRow_spec (hK : K.Valid) (a : L4) (b : Limb) :
    ∃ m < 2 ^ 64, 2 ^ 64 * (val (firstRow K a b).1 + 2 ^ 256 * (firstRow K a b).2.val) =
      b.val * val a + m * K.p := by
  unfold firstRow
  extract_lets s0 h0 l1 h1 s1 c1 l2 h2 s2 c2 l3 h3 s3 c3 s4
  have m0 : s0.val + 2 ^ 64 * h0.val = b.val * a.l0.val := mulLo_add_mulHi b a.l0
  have m1 : l1.val + 2 ^ 64 * h1.val = b.val * a.l1.val := mulLo_add_mulHi b a.l1
  have m2 : l2.val + 2 ^ 64 * h2.val = b.val * a.l2.val := mulLo_add_mulHi b a.l2
  have m3 : l3.val + 2 ^ 64 * h3.val = b.val * a.l3.val := mulLo_add_mulHi b a.l3
  have x1 : s1.val + 2 ^ 64 * c1.val = h0.val + l1.val + 0 := adcLo_add_adcHi h0 l1 0
  have x2 : s2.val + 2 ^ 64 * c2.val = h1.val + l2.val + c1.val := adcLo_add_adcHi h1 l2 c1
  have x3 : s3.val + 2 ^ 64 * c3.val = h2.val + l3.val + c2.val := adcLo_add_adcHi h2 l3 c2
  have x4 : s4.val + 2 ^ 64 * (adcHi h3 0 c3).val = h3.val + 0 + c3.val :=
    adcLo_add_adcHi h3 0 c3
  generalize adcHi h3 0 c3 = c4 at x4
  have hba := mul_val_lt b a
  clear_value s0 h0 l1 h1 s1 c1 l2 h2 s2 c2 l3 h3 s3 c3 s4
  have hS : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val + 2 ^ 320 * c4.val : ℤ) = b.val * val a := by
    simp only [val]
    zify at m0 m1 m2 m3 x1 x2 x3 x4
    push_cast
    linear_combination m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 + 2 ^ 64 * x1 +
      2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4
  have hc4 : c4.val = 0 := by
    by_contra hne
    have : (1 : ℤ) ≤ c4.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have : (b.val * val a : ℤ) < 2 ^ 320 := by exact_mod_cast hba
    have : (0 : ℤ) ≤ s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val := by positivity
    linarith
  have hpl := K.p_lt
  obtain ⟨m, hm, hr⟩ := shiftReduced_spec hK s0 s1 s2 s3 s4 0 (by
    rw [hc4, Nat.cast_zero, mul_zero, add_zero] at hS
    have : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val : ℤ) = b.val * val a := by linarith
    have : s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
      2 ^ 256 * s4.val = b.val * val a := by exact_mod_cast this
    simp only [Fin.val_zero]
    omega)
  refine ⟨m, hm, ?_⟩
  rw [hr]
  rw [hc4, Nat.cast_zero, mul_zero, add_zero] at hS
  have : (s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
    2 ^ 256 * s4.val : ℤ) = b.val * val a := by linarith
  have : s0.val + 2 ^ 64 * s1.val + 2 ^ 128 * s2.val + 2 ^ 192 * s3.val +
    2 ^ 256 * s4.val = b.val * val a := by exact_mod_cast this
  simp only [Fin.val_zero]
  omega

/-- `row`: `(t + 2 ^ 256 top + b a + m p) / 2 ^ 64` for the `m` that makes it exact. -/
theorem row_spec (hK : K.Valid) (a : L4) (b : Limb) (t : L4) (top : Limb) :
    ∃ m < 2 ^ 64, 2 ^ 64 * (val (row K a b t top).1 + 2 ^ 256 * (row K a b t top).2.val) =
      val t + 2 ^ 256 * top.val + b.val * val a + m * K.p := by
  unfold row
  extract_lets l0 h0 s0 ca0 s1 cb1 l1 h1 s1' ca1 s2 cb2 l2 h2 s2' ca2 s3 cb3 l3 h3 s3' ca3 s4
    cb4 s4' ca4 s5
  have m0 : l0.val + 2 ^ 64 * h0.val = b.val * a.l0.val := mulLo_add_mulHi b a.l0
  have m1 : l1.val + 2 ^ 64 * h1.val = b.val * a.l1.val := mulLo_add_mulHi b a.l1
  have m2 : l2.val + 2 ^ 64 * h2.val = b.val * a.l2.val := mulLo_add_mulHi b a.l2
  have m3 : l3.val + 2 ^ 64 * h3.val = b.val * a.l3.val := mulLo_add_mulHi b a.l3
  have y0 : s0.val + 2 ^ 64 * ca0.val = t.l0.val + l0.val + 0 := adcLo_add_adcHi t.l0 l0 0
  have y1 : s1.val + 2 ^ 64 * cb1.val = t.l1.val + h0.val + 0 := adcLo_add_adcHi t.l1 h0 0
  have y2 : s1'.val + 2 ^ 64 * ca1.val = s1.val + l1.val + ca0.val := adcLo_add_adcHi s1 l1 ca0
  have y3 : s2.val + 2 ^ 64 * cb2.val = t.l2.val + h1.val + cb1.val :=
    adcLo_add_adcHi t.l2 h1 cb1
  have y4 : s2'.val + 2 ^ 64 * ca2.val = s2.val + l2.val + ca1.val := adcLo_add_adcHi s2 l2 ca1
  have y5 : s3.val + 2 ^ 64 * cb3.val = t.l3.val + h2.val + cb2.val :=
    adcLo_add_adcHi t.l3 h2 cb2
  have y6 : s3'.val + 2 ^ 64 * ca3.val = s3.val + l3.val + ca2.val := adcLo_add_adcHi s3 l3 ca2
  have y7 : s4.val + 2 ^ 64 * cb4.val = top.val + h3.val + cb3.val := adcLo_add_adcHi top h3 cb3
  have y8 : s4'.val + 2 ^ 64 * ca4.val = s4.val + 0 + ca3.val := adcLo_add_adcHi s4 0 ca3
  have y9 : s5.val + 2 ^ 64 * (adcHi cb4 0 ca4).val = cb4.val + 0 + ca4.val :=
    adcLo_add_adcHi cb4 0 ca4
  generalize adcHi cb4 0 ca4 = c6 at y9
  have hba := mul_val_lt b a
  have ht := val_lt t
  have htop := top.isLt
  clear_value l0 h0 s0 ca0 s1 cb1 l1 h1 s1' ca1 s2 cb2 l2 h2 s2' ca2 s3 cb3 l3 h3 s3' ca3 s4
    cb4 s4' ca4 s5
  have hS : (s0.val + 2 ^ 64 * s1'.val + 2 ^ 128 * s2'.val + 2 ^ 192 * s3'.val +
      2 ^ 256 * s4'.val + 2 ^ 320 * s5.val + 2 ^ 384 * c6.val : ℤ) =
      val t + 2 ^ 256 * top.val + b.val * val a := by
    simp only [val]
    zify at m0 m1 m2 m3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
    push_cast
    linear_combination m0 + y0 + 2 ^ 64 * y1 + 2 ^ 64 * m1 + 2 ^ 64 * y2 + 2 ^ 128 * y3 +
      2 ^ 128 * m2 + 2 ^ 128 * y4 + 2 ^ 192 * y5 + 2 ^ 192 * m3 + 2 ^ 192 * y6 +
      2 ^ 256 * y7 + 2 ^ 256 * y8 + 2 ^ 320 * y9
  have hc6 : c6.val = 0 := by
    by_contra hne
    have : (1 : ℤ) ≤ c6.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have : (b.val * val a : ℤ) < 2 ^ 320 := by exact_mod_cast hba
    have : (val t : ℤ) < 2 ^ 256 := by exact_mod_cast ht
    have : (top.val : ℤ) < 2 ^ 64 := by exact_mod_cast htop
    have : (0 : ℤ) ≤ s0.val + 2 ^ 64 * s1'.val + 2 ^ 128 * s2'.val + 2 ^ 192 * s3'.val +
      2 ^ 256 * s4'.val + 2 ^ 320 * s5.val := by positivity
    linarith
  rw [hc6, Nat.cast_zero, mul_zero, add_zero] at hS
  have hS' : s0.val + 2 ^ 64 * s1'.val + 2 ^ 128 * s2'.val + 2 ^ 192 * s3'.val +
      2 ^ 256 * s4'.val + 2 ^ 320 * s5.val = val t + 2 ^ 256 * top.val + b.val * val a := by
    exact_mod_cast hS
  clear m0 m1 m2 m3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 hS
  have hpl := K.p_lt
  obtain ⟨m, hm, hr⟩ := shiftReduced_spec hK s0 s1' s2' s3' s4' s5 (by
    rw [hS']; clear hS'; omega)
  exact ⟨m, hm, by rw [hr, hS']⟩

theorem val_raw {v : ℕ} (hv : v < 2 ^ 256) : val (raw v) = v := by
  simp only [val, raw]; omega

theorem val_zero : val zero = 0 := rfl

/-- `reduce` of a value below `2 p` is its remainder. -/
theorem reduce_spec (a : L4) (top : Limb) (hV : val a + 2 ^ 256 * top.val < 2 * K.p) :
    val (reduce K a top) = (val a + 2 ^ 256 * top.val) % K.p := by
  unfold reduce
  extract_lets d0 b0 d1 b1 d2 b2 d3 b3 b4
  have e0 : d0.val + K.P0.val + 0 = a.l0.val + 2 ^ 64 * b0.val :=
    sbbLo_sbbHi a.l0 K.P0 0 (by decide)
  have e1 : d1.val + K.P1.val + b0.val = a.l1.val + 2 ^ 64 * b1.val :=
    sbbLo_sbbHi a.l1 K.P1 b0 (sbbHi_val_le _ _ _)
  have e2 : d2.val + K.P2.val + b1.val = a.l2.val + 2 ^ 64 * b2.val :=
    sbbLo_sbbHi a.l2 K.P2 b1 (sbbHi_val_le _ _ _)
  have e3 : d3.val + K.P3.val + b2.val = a.l3.val + 2 ^ 64 * b3.val :=
    sbbLo_sbbHi a.l3 K.P3 b2 (sbbHi_val_le _ _ _)
  have hb3 : b3.val ≤ 1 := sbbHi_val_le _ _ _
  have hb4 : b4 = if top.val < 0 + b3.val then 1 else 0 := rfl
  clear_value d0 b0 d1 b1 d2 b2 d3 b3 b4
  have key : (val ⟨d0, d1, d2, d3⟩ + K.p : ℤ) = val a + 2 ^ 256 * b3.val := by
    simp only [val, Modulus.p]
    zify at e0 e1 e2 e3
    push_cast
    linear_combination e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3
  have key' : val ⟨d0, d1, d2, d3⟩ + K.p = val a + 2 ^ 256 * b3.val := by exact_mod_cast key
  have hd := val_lt ⟨d0, d1, d2, d3⟩
  have hpl := K.p_lt
  clear e0 e1 e2 e3 key
  by_cases h : top.val < b3.val
  · rw [hb4, if_pos (show top.val < 0 + b3.val by omega), if_pos rfl,
      Nat.mod_eq_of_lt (show val a + 2 ^ 256 * top.val < K.p by omega)]
    omega
  · rw [hb4, if_neg (show ¬ top.val < 0 + b3.val by omega),
      if_neg (show ¬ (0 : Limb) = 1 by decide),
      Nat.mod_eq_sub_mod (show K.p ≤ val a + 2 ^ 256 * top.val by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- `mul`, for `a < p`: below `p`, and `a b 2 ^ -256` modulo `p`. -/
theorem mul_spec (hK : K.Valid) (a b : L4) (ha : val a < K.p) :
    val (mul K a b) < K.p ∧
      (val (mul K a b) : ZMod K.p) * 2 ^ 256 = (val a : ZMod K.p) * val b := by
  unfold mul
  obtain ⟨m0, hm0, h0⟩ := firstRow_spec hK a b.l0
  generalize firstRow K a b.l0 = r1 at h0 ⊢
  obtain ⟨t1, c1⟩ := r1
  obtain ⟨m1, hm1, h1⟩ := row_spec hK a b.l1 t1 c1
  dsimp only at h0 h1 ⊢
  generalize row K a b.l1 t1 c1 = r2 at h1 ⊢
  obtain ⟨t2, c2⟩ := r2
  obtain ⟨m2, hm2, h2⟩ := row_spec hK a b.l2 t2 c2
  dsimp only at h1 h2 ⊢
  generalize row K a b.l2 t2 c2 = r3 at h2 ⊢
  obtain ⟨t3, c3⟩ := r3
  obtain ⟨m3, hm3, h3⟩ := row_spec hK a b.l3 t3 c3
  dsimp only at h2 h3 ⊢
  generalize row K a b.l3 t3 c3 = r4 at h3 ⊢
  obtain ⟨t4, c4⟩ := r4
  dsimp only at h3 ⊢
  -- Each row keeps the running value below `a + p`.
  have le {x : ℕ} (hx : x < 2 ^ 64) (y : ℕ) : x * y ≤ (2 ^ 64 - 1) * y :=
    Nat.mul_le_mul_right y (by omega)
  have hp0 := le hm0 K.p
  have hb0 := le b.l0.isLt (val a)
  have hp1 := le hm1 K.p
  have hb1 := le b.l1.isLt (val a)
  have hp2 := le hm2 K.p
  have hb2 := le b.l2.isLt (val a)
  have hp3 := le hm3 K.p
  have hb3 := le b.l3.isLt (val a)
  generalize val t1 + 2 ^ 256 * c1.val = T1 at h0 h1
  generalize val t2 + 2 ^ 256 * c2.val = T2 at h1 h2
  generalize val t3 + 2 ^ 256 * c3.val = T3 at h2 h3
  have hT1 : T1 < val a + K.p := by omega
  have hT2 : T2 < val a + K.p := by omega
  have hT3 : T3 < val a + K.p := by omega
  have hT4 : val t4 + 2 ^ 256 * c4.val < 2 * K.p := by omega
  rw [reduce_spec t4 c4 hT4]
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  rw [ZMod.natCast_mod]
  have z0 := congrArg (Nat.cast : ℕ → ZMod K.p) h0
  have z1 := congrArg (Nat.cast : ℕ → ZMod K.p) h1
  have z2 := congrArg (Nat.cast : ℕ → ZMod K.p) h2
  have z3 := congrArg (Nat.cast : ℕ → ZMod K.p) h3
  push_cast [ZMod.natCast_self] at z0 z1 z2 z3 ⊢
  simp only [val] at z0 z1 z2 z3 ⊢
  push_cast at z0 z1 z2 z3 ⊢
  linear_combination 2 ^ 192 * z3 + 2 ^ 128 * z2 + 2 ^ 64 * z1 + z0

/-- `add`, for `a, b < p`: their sum modulo `p`. -/
theorem add_spec (a b : L4) (ha : val a < K.p) (hb : val b < K.p) :
    val (add K a b) = (val a + val b) % K.p := by
  unfold add
  extract_lets s0 c0 s1 c1 s2 c2 s3 c3
  have e0 : s0.val + 2 ^ 64 * c0.val = a.l0.val + b.l0.val + 0 := adcLo_add_adcHi _ _ _
  have e1 : s1.val + 2 ^ 64 * c1.val = a.l1.val + b.l1.val + c0.val := adcLo_add_adcHi _ _ _
  have e2 : s2.val + 2 ^ 64 * c2.val = a.l2.val + b.l2.val + c1.val := adcLo_add_adcHi _ _ _
  have e3 : s3.val + 2 ^ 64 * c3.val = a.l3.val + b.l3.val + c2.val := adcLo_add_adcHi _ _ _
  clear_value s0 c0 s1 c1 s2 c2 s3 c3
  have key : (val ⟨s0, s1, s2, s3⟩ + 2 ^ 256 * c3.val : ℤ) = val a + val b := by
    simp only [val]
    zify at e0 e1 e2 e3
    push_cast
    linear_combination e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3
  have key' : val ⟨s0, s1, s2, s3⟩ + 2 ^ 256 * c3.val = val a + val b := by exact_mod_cast key
  rw [reduce_spec _ _ (by omega), key']

/-- `sub`, for `a, b < p`: their difference, with `p` added when `a < b`. -/
theorem sub_spec (a b : L4) (ha : val a < K.p) (hb : val b < K.p) :
    val (sub K a b) = if val b ≤ val a then val a - val b else val a + K.p - val b := by
  unfold sub
  extract_lets d0 w0 d1 w1 d2 w2 d3 w3 s0 c0 s1 c1 s2 c2 s3
  have f0 : d0.val + b.l0.val + 0 = a.l0.val + 2 ^ 64 * w0.val :=
    sbbLo_sbbHi a.l0 b.l0 0 (by decide)
  have f1 : d1.val + b.l1.val + w0.val = a.l1.val + 2 ^ 64 * w1.val :=
    sbbLo_sbbHi a.l1 b.l1 w0 (sbbHi_val_le _ _ _)
  have f2 : d2.val + b.l2.val + w1.val = a.l2.val + 2 ^ 64 * w2.val :=
    sbbLo_sbbHi a.l2 b.l2 w1 (sbbHi_val_le _ _ _)
  have f3 : d3.val + b.l3.val + w2.val = a.l3.val + 2 ^ 64 * w3.val :=
    sbbLo_sbbHi a.l3 b.l3 w2 (sbbHi_val_le _ _ _)
  have hw3 : w3.val ≤ 1 := sbbHi_val_le _ _ _
  have g0 : s0.val + 2 ^ 64 * c0.val = d0.val + K.P0.val + 0 := adcLo_add_adcHi _ _ _
  have g1 : s1.val + 2 ^ 64 * c1.val = d1.val + K.P1.val + c0.val := adcLo_add_adcHi _ _ _
  have g2 : s2.val + 2 ^ 64 * c2.val = d2.val + K.P2.val + c1.val := adcLo_add_adcHi _ _ _
  have g3 : s3.val + 2 ^ 64 * (adcHi d3 K.P3 c2).val = d3.val + K.P3.val + c2.val :=
    adcLo_add_adcHi _ _ _
  generalize adcHi d3 K.P3 c2 = c3 at g3
  clear_value d0 w0 d1 w1 d2 w2 d3 w3 s0 c0 s1 c1 s2 c2 s3
  have kd : (val ⟨d0, d1, d2, d3⟩ + val b : ℤ) = val a + 2 ^ 256 * w3.val := by
    simp only [val]
    zify at f0 f1 f2 f3
    push_cast
    linear_combination f0 + 2 ^ 64 * f1 + 2 ^ 128 * f2 + 2 ^ 192 * f3
  have ks : (val ⟨s0, s1, s2, s3⟩ + 2 ^ 256 * c3.val : ℤ) = val ⟨d0, d1, d2, d3⟩ + K.p := by
    simp only [val, Modulus.p]
    zify at g0 g1 g2 g3
    push_cast
    linear_combination g0 + 2 ^ 64 * g1 + 2 ^ 128 * g2 + 2 ^ 192 * g3
  have kd' : val ⟨d0, d1, d2, d3⟩ + val b = val a + 2 ^ 256 * w3.val := by exact_mod_cast kd
  have ks' : val ⟨s0, s1, s2, s3⟩ + 2 ^ 256 * c3.val = val ⟨d0, d1, d2, d3⟩ + K.p := by
    exact_mod_cast ks
  have hd := val_lt ⟨d0, d1, d2, d3⟩
  have hs := val_lt ⟨s0, s1, s2, s3⟩
  have hpl := K.p_lt
  clear f0 f1 f2 f3 g0 g1 g2 g3 kd ks
  by_cases hw : w3 = 1
  · have h1 : w3.val = 1 := by rw [hw]; rfl
    rw [if_pos hw, if_neg (by omega)]
    omega
  · have h0 : w3.val = 0 := by
      have : w3.val ≠ 1 := fun h => hw (Fin.ext h)
      omega
    rw [if_neg hw, if_pos (by omega)]
    omega

/-! ## The representation -/

theorem _root_.FeProofs.Ecrecover.Modulus.p_odd (hK : K.Valid) : K.p % 2 = 1 := by
  unfold Modulus.Valid at hK
  have h2 : (K.P0.val * K.INV.val + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by norm_num), hK]
  have h3 : K.P0.val % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one K.P0.val with h | h
    · rw [Nat.add_mod, Nat.mul_mod, h] at h2; simp at h2
    · exact h
  unfold Modulus.p; omega

/-- `R = 2 ^ 256` is a unit modulo an odd `p`. -/
theorem R_isUnit (hK : K.Valid) : IsUnit (2 ^ 256 : ZMod K.p) := by
  have h : IsUnit ((2 : ℕ) : ZMod K.p) :=
    (ZMod.isUnit_iff_coprime 2 K.p).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (K.p_odd hK)))
  rw [Nat.cast_ofNat] at h
  exact h.pow _

/-- `a` represents `x` modulo `p`: four limbs whose value is below `p` and is `x R`, for the
Montgomery radix `R = 2 ^ 256`; that is, `x = a R⁻¹`. -/
def Rep (K : Modulus) (a : L4) (x : ZMod K.p) : Prop :=
  val a < K.p ∧ (val a : ZMod K.p) = x * 2 ^ 256

/-- Two representations are of the same element exactly when their values are equal. -/
theorem Rep.val_eq_iff (hK : K.Valid) {a b : L4} {x y : ZMod K.p} (ha : Rep K a x)
    (hb : Rep K b y) : val a = val b ↔ x = y := by
  constructor
  · intro h
    exact (R_isUnit hK).mul_right_cancel (by rw [← ha.2, ← hb.2, h])
  · rintro rfl
    have := (ZMod.natCast_eq_natCast_iff' (val a) (val b) K.p).mp (by rw [ha.2, hb.2])
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this

theorem val_inj {a b : L4} : val a = val b ↔ a = b := by
  constructor
  · intro h
    obtain ⟨a0, a1, a2, a3⟩ := a
    obtain ⟨b0, b1, b2, b3⟩ := b
    simp only [val] at h
    have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    have e0 : a0 = b0 := Fin.ext (by omega)
    have e1 : a1 = b1 := Fin.ext (by omega)
    have e2 : a2 = b2 := Fin.ext (by omega)
    have e3 : a3 = b3 := Fin.ext (by omega)
    rw [e0, e1, e2, e3]
  · rintro rfl; rfl

theorem zero_rep (hK : K.Valid) : Rep K zero 0 := by
  have := K.p_odd hK
  exact ⟨by rw [val_zero]; omega, by rw [val_zero]; simp⟩

theorem mul_rep (hK : K.Valid) {a b : L4} {x y : ZMod K.p} (ha : Rep K a x) (hb : Rep K b y) :
    Rep K (mul K a b) (x * y) := by
  obtain ⟨hlt, hm⟩ := mul_spec hK a b ha.1
  refine ⟨hlt, (R_isUnit hK).mul_right_cancel ?_⟩
  rw [hm, ha.2, hb.2]; ring

theorem add_rep {a b : L4} {x y : ZMod K.p} (ha : Rep K a x) (hb : Rep K b y) :
    Rep K (add K a b) (x + y) := by
  rw [Rep, add_spec a b ha.1 hb.1, ZMod.natCast_mod]
  exact ⟨Nat.mod_lt _ (by have := ha.1; omega), by push_cast; rw [ha.2, hb.2]; ring⟩

theorem sub_rep {a b : L4} {x y : ZMod K.p} (ha : Rep K a x) (hb : Rep K b y) :
    Rep K (sub K a b) (x - y) := by
  have h1 := ha.1; have h2 := hb.1
  rw [Rep, sub_spec a b ha.1 hb.1]
  split_ifs with h
  · refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub h, ha.2, hb.2]; ring
  · refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ha.2, hb.2]; ring

theorem neg_rep (hK : K.Valid) {a : L4} {x : ZMod K.p} (ha : Rep K a x) :
    Rep K (sub K zero a) (-x) := by
  simpa using sub_rep (zero_rep hK) ha

theorem double_rep {a : L4} {x : ZMod K.p} (ha : Rep K a x) : Rep K (add K a a) (2 * x) := by
  simpa [two_mul] using add_rep ha ha

theorem square_rep (hK : K.Valid) {a : L4} {x : ZMod K.p} (ha : Rep K a x) :
    Rep K (mul K a a) (x ^ 2) := by
  simpa [sq] using mul_rep hK ha ha

/-- `new v` represents `v`, for `v < p`, given `R2 = R ^ 2 mod p`. -/
theorem new_rep (hK : K.Valid) (hR : K.R2 = 2 ^ 512 % K.p) {v : ℕ} (hv : v < K.p) :
    Rep K (new K v) v := by
  have hpl := K.p_lt
  have hv' : val (raw v) = v := val_raw (by omega)
  have hp0 := K.p_odd hK
  have hR' : val (raw K.R2) = K.R2 :=
    val_raw (by rw [hR]; exact lt_trans (Nat.mod_lt _ (by omega)) hpl)
  obtain ⟨hlt, hm⟩ := mul_spec hK (raw v) (raw K.R2) (by rw [hv']; exact hv)
  refine ⟨hlt, (R_isUnit hK).mul_right_cancel ?_⟩
  rw [new, hm, hv', hR', hR, ZMod.natCast_mod]
  push_cast; ring

theorem one_rep (hK : K.Valid) (hR : K.R2 = 2 ^ 512 % K.p) (h1 : 1 < K.p) :
    Rep K (new K 1) 1 := by
  simpa using new_rep hK hR h1

/-- `value` is the canonical integer of the element represented. -/
theorem value_rep (hK : K.Valid) {a : L4} {x : ZMod K.p} (ha : Rep K a x) :
    value K a < K.p ∧ (value K a : ZMod K.p) = x := by
  have hpl := K.p_lt
  obtain ⟨hlt, hm⟩ := mul_spec hK a (raw 1) ha.1
  refine ⟨hlt, (R_isUnit hK).mul_right_cancel ?_⟩
  change (val (mul K a (raw 1)) : ZMod K.p) * 2 ^ 256 = _
  rw [hm, val_raw (by decide), ha.2]; push_cast; ring

theorem isZero_rep (hK : K.Valid) {a : L4} {x : ZMod K.p} (ha : Rep K a x) :
    isZero a = true ↔ x = 0 := by
  rw [← (Rep.val_eq_iff hK ha (zero_rep hK)), val_inj]
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp [isZero, zero, L4.mk.injEq, and_assoc]

theorem equals_rep (hK : K.Valid) {a b : L4} {x y : ZMod K.p} (ha : Rep K a x)
    (hb : Rep K b y) : equals a b = true ↔ x = y := by
  rw [← (Rep.val_eq_iff hK ha hb), val_inj]
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp [equals, L4.mk.injEq, and_assoc]

end Mont

/-! ## The two moduli -/

theorem KB_p : KB.p = Ethereum.Secp256k1.p := by decide
theorem KO_p : KO.p = Ethereum.Secp256k1.n := by decide
theorem KB_valid : KB.Valid := by unfold Modulus.Valid; decide
theorem KO_valid : KO.Valid := by unfold Modulus.Valid; decide
theorem KB_R2 : KB.R2 = 2 ^ 512 % KB.p := by decide
theorem KO_R2 : KO.R2 = 2 ^ 512 % KO.p := by decide
theorem Base_value_eq : Base.value = KB.p := by decide
theorem Order_value_eq : Order.value = KO.p := by decide

/-! ## The exported methods

Each exported method on representations returns a representation of the result. -/

open Ethereum Precompiles.Exported.Shared Precompiles.Exported.Ecrecover Mont

section
variable {a b : L4} {x y : ZMod KB.p}

theorem Mont_new_Base_rep (v : UInt256) (hv : v.toNat < KB.p) :
    ∃ c, Mont_new_Base v = pure (toB c) ∧ Rep KB c v.toNat :=
  ⟨_, new_Base v (by rw [Base_value_eq]; exact hv), new_rep KB_valid KB_R2 hv⟩

theorem Mont_one_Base_rep : ∃ c, Mont_one_Base = pure (toB c) ∧ Rep KB c 1 :=
  ⟨_, one_Base, one_rep KB_valid KB_R2 (by decide)⟩

theorem Mont_zero_Base_rep : Mont_zero_Base = pure (toB zero) ∧ Rep KB zero 0 :=
  ⟨zero_Base, zero_rep KB_valid⟩

theorem Mont_value_Base_rep (ha : Rep KB a x) :
    ∃ v < KB.p, Mont_value_Base (toB a) = pure (UInt256.ofNat v) ∧ (v : ZMod KB.p) = x :=
  ⟨_, (value_rep KB_valid ha).1, value_Base a, (value_rep KB_valid ha).2⟩

theorem Mont_mul_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_mul_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x * y) :=
  ⟨_, mul_Base a b, mul_rep KB_valid ha hb⟩

theorem Mont_square_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_square_Base (toB a) = pure (toB c) ∧ Rep KB c (x ^ 2) :=
  ⟨_, square_Base a, square_rep KB_valid ha⟩

theorem Mont_add_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_add_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x + y) :=
  ⟨_, add_Base a b, add_rep ha hb⟩

theorem Mont_double_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_double_Base (toB a) = pure (toB c) ∧ Rep KB c (2 * x) :=
  ⟨_, double_Base a, double_rep ha⟩

theorem Mont_sub_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    ∃ c, Mont_sub_Base (toB a) (toB b) = pure (toB c) ∧ Rep KB c (x - y) :=
  ⟨_, sub_Base a b, sub_rep ha hb⟩

theorem Mont_neg_Base_rep (ha : Rep KB a x) :
    ∃ c, Mont_neg_Base (toB a) = pure (toB c) ∧ Rep KB c (-x) :=
  ⟨_, neg_Base a, neg_rep KB_valid ha⟩

theorem Mont_is_zero_Base_rep (ha : Rep KB a x) :
    Mont_is_zero_Base (toB a) = pure (decide (x = 0)) := by
  rw [is_zero_Base]
  congr 1
  exact Bool.eq_iff_iff.mpr ((isZero_rep KB_valid ha).trans decide_eq_true_iff.symm)

theorem Mont_equals_Base_rep (ha : Rep KB a x) (hb : Rep KB b y) :
    Mont_equals_Base (toB a) (toB b) = pure (decide (x = y)) := by
  rw [equals_Base]
  congr 1
  exact Bool.eq_iff_iff.mpr ((equals_rep KB_valid ha hb).trans decide_eq_true_iff.symm)

end

section
variable {a b : L4} {x y : ZMod KO.p}

theorem Mont_new_Order_rep (v : UInt256) (hv : v.toNat < KO.p) :
    ∃ c, Mont_new_Order v = pure (toO c) ∧ Rep KO c v.toNat :=
  ⟨_, new_Order v (by rw [Order_value_eq]; exact hv), new_rep KO_valid KO_R2 hv⟩

theorem Mont_zero_Order_rep : Mont_zero_Order = pure (toO zero) ∧ Rep KO zero 0 :=
  ⟨zero_Order, zero_rep KO_valid⟩

theorem Mont_value_Order_rep (ha : Rep KO a x) :
    ∃ v < KO.p, Mont_value_Order (toO a) = pure (UInt256.ofNat v) ∧ (v : ZMod KO.p) = x :=
  ⟨_, (value_rep KO_valid ha).1, value_Order a, (value_rep KO_valid ha).2⟩

theorem Mont_mul_Order_rep (ha : Rep KO a x) (hb : Rep KO b y) :
    ∃ c, Mont_mul_Order (toO a) (toO b) = pure (toO c) ∧ Rep KO c (x * y) :=
  ⟨_, mul_Order a b, mul_rep KO_valid ha hb⟩

theorem Mont_sub_Order_rep (ha : Rep KO a x) (hb : Rep KO b y) :
    ∃ c, Mont_sub_Order (toO a) (toO b) = pure (toO c) ∧ Rep KO c (x - y) :=
  ⟨_, sub_Order a b, sub_rep ha hb⟩

theorem Mont_neg_Order_rep (ha : Rep KO a x) :
    ∃ c, Mont_neg_Order (toO a) = pure (toO c) ∧ Rep KO c (-x) :=
  ⟨_, neg_Order a, neg_rep KO_valid ha⟩

end

end FeProofs.Ecrecover
