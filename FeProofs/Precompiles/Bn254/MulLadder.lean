import FeProofs.Precompiles.Bn254.MulPoint
import Mathlib.Data.List.TakeWhile

/-!
# Bn254Mul: the joint ladder

`multiply_g1` runs one double-and-add over the bits of both half-scalars `n₁`, `n₂`, from bit
`256 − clz(n₁ | n₂)` down, adding the affine `P₁`, `P₂` or their precomputed sum by the pair
of bits.  From the point `(n₁ / 2 ^ m) • P₁ + (n₂ / 2 ^ m) • P₂` with `m` bits to go the loop
returns `n₁ • P₁ + n₂ • P₂` (`ladder`); it starts at infinity with `m` bits such that both
half-scalars are below `2 ^ m` (`leadingZeros_bound`).  The loop is pure.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory WeierstrassCurve WeierstrassCurve.Jacobian

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul Mont

/-- `256 − clz(v)` bits hold `v`. -/
theorem leadingZeros_bound (v : UInt256) :
    (IntTy.leadingZeros (.u 256) v).toNat ≤ 256 ∧
      v.toNat < 2 ^ (256 - (IntTy.leadingZeros (.u 256) v).toNat) := by
  unfold IntTy.leadingZeros
  simp only [IntTy.bits, IntTy.pattern]
  set L := (List.range 256).takeWhile fun n => !(v.toNat % 2 ^ 256).testBit (256 - 1 - n)
  have hL : L.length ≤ 256 := by
    have := List.IsPrefix.length_le (List.takeWhile_prefix
      (p := fun n => !(v.toNat % 2 ^ 256).testBit (256 - 1 - n)) (l := List.range 256))
    simpa using this
  have hv : v.toNat < 2 ^ 256 := v.val.isLt
  rw [toNat_lit (by omega)]
  refine ⟨hL, Nat.lt_pow_two_of_testBit _ fun i hi => ?_⟩
  by_cases h256 : 256 ≤ i
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h256))
  · have he : L = List.range (min L.length 256) := by
      rw [← List.take_range]
      exact List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
    have hmem : 255 - i ∈ List.range (min L.length 256) := List.mem_range.mpr (by omega)
    rw [← he] at hmem
    have := List.mem_takeWhile_imp hmem
    rw [Nat.mod_eq_of_lt hv, show 256 - 1 - (255 - i) = i by omega] at this
    simpa using this

theorem sub_one_u64 {m : ℕ} (hm : m + 1 < 2 ^ 64) :
    IntTy.sub (.u 64) (UInt256.ofNat (m + 1)) (UInt256.ofNat 1) = pure (UInt256.ofNat m) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show m + 1 < 2 ^ 256 by omega), toNat_lit (show 1 < 2 ^ 256 by decide)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

/-- One bit of the ladder: the point with `m + 1` bits to go, doubled, plus the bits `m`. -/
theorem ladder_split (n1 n2 m : ℕ) (P1 P2 : BN254.Spec.Point) :
    (n1 / 2 ^ m) • P1 + (n2 / 2 ^ m) • P2 =
      ((n1 / 2 ^ (m + 1)) • P1 + (n2 / 2 ^ (m + 1)) • P2 +
        ((n1 / 2 ^ (m + 1)) • P1 + (n2 / 2 ^ (m + 1)) • P2)) +
        ((n1 / 2 ^ m % 2) • P1 + (n2 / 2 ^ m % 2) • P2) := by
  have e1 : n1 / 2 ^ m = 2 * (n1 / 2 ^ (m + 1)) + n1 / 2 ^ m % 2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
  have e2 : n2 / 2 ^ m = 2 * (n2 / 2 ^ (m + 1)) + n2 / 2 ^ m % 2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
  conv_lhs => rw [e1, e2]
  simp only [add_nsmul, mul_nsmul', two_nsmul]
  abel

/-- **The ladder**: from `(n₁ / 2 ^ m) • P₁ + (n₂ / 2 ^ m) • P₂` with `m` bits to go, the loop
returns `n₁ • P₁ + n₂ • P₂`, whatever the scratch registers hold. -/
theorem ladder (n1 n2 : ℕ) (h1 : n1 < 2 ^ 256) (h2 : n2 < 2 ^ 256) {P1 P2 : BN254.Spec.Point}
    {a0 b0 a1 b1 a2 b2 : L4} (hP1 : AffB a0 b0 P1) (hP2 : AffB a1 b1 P2)
    (hS : AffB a2 b2 (P1 + P2)) :
    ∀ m ≤ 256, ∀ cur : Point_Mont_Bn254Base,
      GoodB cur ((n1 / 2 ^ m) • P1 + (n2 / 2 ^ m) • P2) →
      ∃ R, GoodB R (n1 • P1 + n2 • P2) ∧ ∀ r8 r9 r10 r11 r12 r13 r14 r15 r16 r17,
        multiply_g1_k1.loop (UInt256.ofNat n1) (UInt256.ofNat n2) (toBn a0) (toBn b0) (toBn a1)
          (toBn b1) (toBn a2) (toBn b2) cur (UInt256.ofNat m) r8 r9 r10 r11 r12 r13 r14 r15 r16
          r17 = pure R
  | 0, _, cur, hc => by
    refine ⟨cur, by simpa using hc, fun r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 => ?_⟩
    rw [multiply_g1_k1.loop.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, if_false]
  | m + 1, hm, cur, hc => by
    obtain ⟨D, eD, hD⟩ := hc.double
    have t1 := bit_test (UInt256.ofNat n1) (show m < 256 by omega)
    have t2 := bit_test (UInt256.ofNat n2) (show m < 256 by omega)
    rw [toNat_lit h1] at t1
    rw [toNat_lit h2] at t2
    have hs := ladder_split n1 n2 m P1 P2
    have IH := ladder n1 n2 h1 h2 hP1 hP2 hS m (by omega)
    rcases Nat.mod_two_eq_zero_or_one (n1 / 2 ^ m) with d1 | d1 <;>
      rcases Nat.mod_two_eq_zero_or_one (n2 / 2 ^ m) with d2 | d2 <;>
      simp only [d1, d2, zero_nsmul, one_nsmul, _root_.add_zero, zero_add] at hs
    · obtain ⟨R, hR, eR⟩ := IH D (hs ▸ hD)
      refine ⟨R, hR, fun _ _ _ _ _ _ _ _ _ _ => ?_⟩
      rw [multiply_g1_k1.loop.eq_1]
      simp only [toNat_lit (show 0 < 2 ^ 256 by decide),
        toNat_lit (show m + 1 < 2 ^ 256 by omega), show 0 < m + 1 by omega, decide_true,
        if_true, sub_one_u64 (show m + 1 < 2 ^ 64 by omega), pure_bind, eD, t1, t2, d1, d2,
        zero_ne_one, decide_false, Bool.false_eq_true, if_false, eR]
    · obtain ⟨E, eE, hE⟩ := hD.add_affine hP2
      obtain ⟨R, hR, eR⟩ := IH E (hs ▸ hE)
      refine ⟨R, hR, fun _ _ _ _ _ _ _ _ _ _ => ?_⟩
      rw [multiply_g1_k1.loop.eq_1]
      simp only [toNat_lit (show 0 < 2 ^ 256 by decide),
        toNat_lit (show m + 1 < 2 ^ 256 by omega), show 0 < m + 1 by omega, decide_true,
        if_true, sub_one_u64 (show m + 1 < 2 ^ 64 by omega), pure_bind, eD, t1, t2, d1, d2,
        zero_ne_one, decide_false, Bool.false_eq_true, if_false, eE, eR]
    · obtain ⟨E, eE, hE⟩ := hD.add_affine hP1
      obtain ⟨R, hR, eR⟩ := IH E (hs ▸ hE)
      refine ⟨R, hR, fun _ _ _ _ _ _ _ _ _ _ => ?_⟩
      rw [multiply_g1_k1.loop.eq_1]
      simp only [toNat_lit (show 0 < 2 ^ 256 by decide),
        toNat_lit (show m + 1 < 2 ^ 256 by omega), show 0 < m + 1 by omega, decide_true,
        if_true, sub_one_u64 (show m + 1 < 2 ^ 64 by omega), pure_bind, eD, t1, t2, d1, d2,
        zero_ne_one, decide_false, Bool.false_eq_true, if_false, eE, eR]
    · obtain ⟨E, eE, hE⟩ := hD.add_affine hS
      obtain ⟨R, hR, eR⟩ := IH E (hs ▸ hE)
      refine ⟨R, hR, fun _ _ _ _ _ _ _ _ _ _ => ?_⟩
      rw [multiply_g1_k1.loop.eq_1]
      simp only [toNat_lit (show 0 < 2 ^ 256 by decide),
        toNat_lit (show m + 1 < 2 ^ 256 by omega), show 0 < m + 1 by omega, decide_true,
        if_true, sub_one_u64 (show m + 1 < 2 ^ 64 by omega), pure_bind, eD, t1, t2, d1, d2,
        eE, eR]

end FeProofs.Bn254Mul
