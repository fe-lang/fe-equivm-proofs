import FeProofs.Precompiles.Modexp.R2
import FeProofs.Precompiles.Modexp.Small
import FeProofs.Precompiles.Modexp.Clz
import FeProofs.Precompiles.LimbArray

/-!
# Modexp: the exported `Small<L>::r2` is `r2`

Each copy `Small_r2_1` … `Small_r2_4` is `pure` of `r2` at its `L`, for a modulus whose top limb is
not zero: the top bit by `leading_zeros` (`clz`), the doubling loop (`Small_r2_L.b22`), the six
squarings (`Small_r2_L.b22.b26`).  The loop lemmas are stated and proved once per copy by the
same text.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

theorem has0_eq (N : ℕ) (hN : N < 2 ^ 256) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_0 ⟨(), UInt256.ofNat N⟩ (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < N)) := by
  simp only [Lib.Range_has_0, range_has_eq (lo := 0) hk (by norm_num) hN, bind_pure]

theorem has06_eq (r : Lib.Range_Known_0_Known_6) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_0_6 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 6)) := by
  simp only [Lib.Range_has_0_6, range_has_eq (lo := 0) (hi := 6) hk (by norm_num) (by norm_num),
    bind_pure]

/-- The position of the top bit of a nonzero limb, as `Small::r2` computes it. -/
theorem shift_eq (x : Limb) (hx : 0 < x.val) :
    UInt256.ofNat 255 - IntTy.leadingZeros (.u 256) x.w = UInt256.ofNat x.val.log2 := by
  have hl := log2_lt64 x
  rw [leadingZeros_eq_clz, UInt256.clz, Limb.toNat_w, if_neg (by omega)]
  apply word_eq_of_toNat
  rw [show UInt256.ofNat 255 - UInt256.ofNat (255 - x.val.log2) = UInt256.sub _ _ from rfl,
    usub_toNat (by rw [toNat_lit (by omega), toNat_lit (by omega)]; omega),
    toNat_lit (by omega), toNat_lit (by omega), toNat_lit (by omega)]
  omega

theorem shl64_bit {s : ℕ} (hs : s < 64) :
    IntTy.shl (.u 64) (UInt256.ofNat 1) (UInt256.ofNat s) = (bitL s hs).w := by
  simp only [IntTy.shl, val_u, toNat_lit (show 1 < 2 ^ 256 by norm_num),
    toNat_lit (show s < 2 ^ 256 by omega), show (256 ≤ s) = False by simp; omega, if_false]
  rw [show ((1 : ℕ) : ℤ) * 2 ^ s = ((2 ^ s : ℕ) : ℤ) by push_cast; ring, wrap_u_nat]
  simp only [bitL, Limb.w]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hs)]

theorem sub64_eq {s : ℕ} (hs : s < 64) :
    IntTy.subW (.u 64) (UInt256.ofNat 64) (UInt256.ofNat s) = UInt256.ofNat (64 - s) := by
  have := subW64_eq ⟨64, by norm_num⟩ ⟨s, by omega⟩
  simp only [Limb.w, subMod] at this
  rw [this, show (64 + 2 ^ 64 - s) % 2 ^ 64 = 64 - s by omega]

/-- Reduces the exporter's `if L == k` branches at a constant `L`. -/
macro "lbranch" : tactic => `(tactic| (
  simp only [ne12, ne13, ne14, ne21, ne23, ne24, ne31, ne32, ne34, ne41, ne42, ne43,
    decide_false, decide_true, Bool.false_eq_true, if_false, if_true]))

theorem r2_sq1 (m : L4) (inv : Limb) (r1 : Lib.Range_Known_0_Unknown) (r2 : Wide)
    (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r4 r5 : Wide), i + n = 6 →
      Small_r2_1.b22.b26 ⟨toW m, inv.w⟩ (toW x) r1 r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 1 m inv)^[n] x))
  | 0, i, x, r4, r5, h => by
    rw [Small_r2_1.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = False from eq_false (by omega),
      decide_false]
    rfl
  | n + 1, i, x, r4, r5, h => by
    rw [Small_r2_1.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0_6, Lib.Range_next_0_6, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, smul1_eq]
    rw [Function.iterate_succ_apply]
    exact r2_sq1 m inv r1 r2 r3 n (i + 1) _ _ _ (by omega)

theorem r2_dbl1 (m : L4) (inv : Limb) (N : ℕ) (hN : N < 2 ^ 256) (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r2 r4 r5 : Wide), i + n = N →
      Small_r2_1.b22 ⟨toW m, inv.w⟩ (toW x) ⟨(), UInt256.ofNat N⟩ r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 1 m inv)^[6] ((sdouble m)^[n] x)))
  | 0, i, x, r2, r4, r5, h => by
    rw [Small_r2_1.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, if_false, Lib.Range_start_0_6, pure_bind]
    exact r2_sq1 m inv _ _ _ 6 0 x _ _ rfl
  | n + 1, i, x, r2, r4, r5, h => by
    rw [Small_r2_1.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0, Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, sdouble1_eq]
    rw [Function.iterate_succ_apply (sdouble m)]
    exact r2_dbl1 m inv N hN r3 n (i + 1) _ _ _ _ (by omega)

/-- **`Small<1>::r2`** for a nonzero top limb. -/
theorem r2_1_eq (m : L4) (inv : Limb) (htop : 0 < (topLimb 1 m).val) :
    Small_r2_1 ⟨toW m, inv.w⟩ = pure (toW (r2 1 m inv)) := by
  have hs := log2_lt64 (topLimb 1 m)
  have ht : topLimb 1 m = m.l0 := by simp [topLimb]
  rw [ht] at htop hs
  simp only [Small_r2_1]
  lbranch
  simp only [toW, shift_eq _ htop,
    downcast_truncate_u256_u64_eq, toNat_lit (show m.l0.val.log2 < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show m.l0.val.log2 < 2 ^ 64 by omega), pure_bind, shl64_bit hs,
    sub64_eq hs, downcast_u64_usize, Fe.EVM.ofNat_add_ofNat (show 64 - m.l0.val.log2 + 1 <
      UInt256.size by unfold UInt256.size; omega), Lib.Range_start_0]
  have e : (Wide.mk (bitL _ hs).w (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0)) = toW (r2start 1 m) := by simp [toW, r2start, topLimb, zero_w]
  rw [e]
  have := r2_dbl1 m inv (64 - m.l0.val.log2 + 1) (by omega) default (64 - m.l0.val.log2 + 1) 0
    (r2start 1 m) default default default (by omega)
  have hr : r2 1 m inv = (ssq 1 m inv)^[6] ((sdouble m)^[64 - m.l0.val.log2 + 1] (r2start 1 m)) := by
    rw [r2, ht]
  simp only [toW] at this ⊢
  rw [this, hr]

theorem r2_sq2 (m : L4) (inv : Limb) (r1 : Lib.Range_Known_0_Unknown) (r2 : Wide)
    (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r4 r5 : Wide), i + n = 6 →
      Small_r2_2.b22.b26 ⟨toW m, inv.w⟩ (toW x) r1 r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 2 m inv)^[n] x))
  | 0, i, x, r4, r5, h => by
    rw [Small_r2_2.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = False from eq_false (by omega),
      decide_false]
    rfl
  | n + 1, i, x, r4, r5, h => by
    rw [Small_r2_2.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0_6, Lib.Range_next_0_6, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, smul2_eq]
    rw [Function.iterate_succ_apply]
    exact r2_sq2 m inv r1 r2 r3 n (i + 1) _ _ _ (by omega)

theorem r2_dbl2 (m : L4) (inv : Limb) (N : ℕ) (hN : N < 2 ^ 256) (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r2 r4 r5 : Wide), i + n = N →
      Small_r2_2.b22 ⟨toW m, inv.w⟩ (toW x) ⟨(), UInt256.ofNat N⟩ r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 2 m inv)^[6] ((sdouble m)^[n] x)))
  | 0, i, x, r2, r4, r5, h => by
    rw [Small_r2_2.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, if_false, Lib.Range_start_0_6, pure_bind]
    exact r2_sq2 m inv _ _ _ 6 0 x _ _ rfl
  | n + 1, i, x, r2, r4, r5, h => by
    rw [Small_r2_2.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0, Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, sdouble2_eq]
    rw [Function.iterate_succ_apply (sdouble m)]
    exact r2_dbl2 m inv N hN r3 n (i + 1) _ _ _ _ (by omega)

/-- **`Small<2>::r2`** for a nonzero top limb. -/
theorem r2_2_eq (m : L4) (inv : Limb) (htop : 0 < (topLimb 2 m).val) :
    Small_r2_2 ⟨toW m, inv.w⟩ = pure (toW (r2 2 m inv)) := by
  have hs := log2_lt64 (topLimb 2 m)
  have ht : topLimb 2 m = m.l1 := by simp [topLimb]
  rw [ht] at htop hs
  simp only [Small_r2_2]
  lbranch
  simp only [toW, shift_eq _ htop,
    downcast_truncate_u256_u64_eq, toNat_lit (show m.l1.val.log2 < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show m.l1.val.log2 < 2 ^ 64 by omega), pure_bind, shl64_bit hs,
    sub64_eq hs, downcast_u64_usize, Fe.EVM.ofNat_add_ofNat (show 64 - m.l1.val.log2 + 2 <
      UInt256.size by unfold UInt256.size; omega), Lib.Range_start_0]
  have e : (Wide.mk (UInt256.ofNat 0) (bitL _ hs).w (UInt256.ofNat 0) (UInt256.ofNat 0)) = toW (r2start 2 m) := by simp [toW, r2start, topLimb, zero_w]
  rw [e]
  have := r2_dbl2 m inv (64 - m.l1.val.log2 + 2) (by omega) default (64 - m.l1.val.log2 + 2) 0
    (r2start 2 m) default default default (by omega)
  have hr : r2 2 m inv = (ssq 2 m inv)^[6] ((sdouble m)^[64 - m.l1.val.log2 + 2] (r2start 2 m)) := by
    rw [r2, ht]
  simp only [toW] at this ⊢
  rw [this, hr]

theorem r2_sq3 (m : L4) (inv : Limb) (r1 : Lib.Range_Known_0_Unknown) (r2 : Wide)
    (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r4 r5 : Wide), i + n = 6 →
      Small_r2_3.b22.b26 ⟨toW m, inv.w⟩ (toW x) r1 r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 3 m inv)^[n] x))
  | 0, i, x, r4, r5, h => by
    rw [Small_r2_3.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = False from eq_false (by omega),
      decide_false]
    rfl
  | n + 1, i, x, r4, r5, h => by
    rw [Small_r2_3.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0_6, Lib.Range_next_0_6, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, smul3_eq]
    rw [Function.iterate_succ_apply]
    exact r2_sq3 m inv r1 r2 r3 n (i + 1) _ _ _ (by omega)

theorem r2_dbl3 (m : L4) (inv : Limb) (N : ℕ) (hN : N < 2 ^ 256) (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r2 r4 r5 : Wide), i + n = N →
      Small_r2_3.b22 ⟨toW m, inv.w⟩ (toW x) ⟨(), UInt256.ofNat N⟩ r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 3 m inv)^[6] ((sdouble m)^[n] x)))
  | 0, i, x, r2, r4, r5, h => by
    rw [Small_r2_3.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, if_false, Lib.Range_start_0_6, pure_bind]
    exact r2_sq3 m inv _ _ _ 6 0 x _ _ rfl
  | n + 1, i, x, r2, r4, r5, h => by
    rw [Small_r2_3.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0, Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, sdouble3_eq]
    rw [Function.iterate_succ_apply (sdouble m)]
    exact r2_dbl3 m inv N hN r3 n (i + 1) _ _ _ _ (by omega)

/-- **`Small<3>::r2`** for a nonzero top limb. -/
theorem r2_3_eq (m : L4) (inv : Limb) (htop : 0 < (topLimb 3 m).val) :
    Small_r2_3 ⟨toW m, inv.w⟩ = pure (toW (r2 3 m inv)) := by
  have hs := log2_lt64 (topLimb 3 m)
  have ht : topLimb 3 m = m.l2 := by simp [topLimb]
  rw [ht] at htop hs
  simp only [Small_r2_3]
  lbranch
  simp only [toW, shift_eq _ htop,
    downcast_truncate_u256_u64_eq, toNat_lit (show m.l2.val.log2 < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show m.l2.val.log2 < 2 ^ 64 by omega), pure_bind, shl64_bit hs,
    sub64_eq hs, downcast_u64_usize, Fe.EVM.ofNat_add_ofNat (show 64 - m.l2.val.log2 + 3 <
      UInt256.size by unfold UInt256.size; omega), Lib.Range_start_0]
  have e : (Wide.mk (UInt256.ofNat 0) (UInt256.ofNat 0) (bitL _ hs).w (UInt256.ofNat 0)) = toW (r2start 3 m) := by simp [toW, r2start, topLimb, zero_w]
  rw [e]
  have := r2_dbl3 m inv (64 - m.l2.val.log2 + 3) (by omega) default (64 - m.l2.val.log2 + 3) 0
    (r2start 3 m) default default default (by omega)
  have hr : r2 3 m inv = (ssq 3 m inv)^[6] ((sdouble m)^[64 - m.l2.val.log2 + 3] (r2start 3 m)) := by
    rw [r2, ht]
  simp only [toW] at this ⊢
  rw [this, hr]

theorem r2_sq4 (m : L4) (inv : Limb) (r1 : Lib.Range_Known_0_Unknown) (r2 : Wide)
    (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r4 r5 : Wide), i + n = 6 →
      Small_r2_4.b22.b26 ⟨toW m, inv.w⟩ (toW x) r1 r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 4 m inv)^[n] x))
  | 0, i, x, r4, r5, h => by
    rw [Small_r2_4.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = False from eq_false (by omega),
      decide_false]
    rfl
  | n + 1, i, x, r4, r5, h => by
    rw [Small_r2_4.b22.b26.eq_1]
    simp only [has06_eq r3 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 6) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0_6, Lib.Range_next_0_6, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, smul4_eq]
    rw [Function.iterate_succ_apply]
    exact r2_sq4 m inv r1 r2 r3 n (i + 1) _ _ _ (by omega)

theorem r2_dbl4 (m : L4) (inv : Limb) (N : ℕ) (hN : N < 2 ^ 256) (r3 : Lib.Range_Known_0_Known_6) :
    ∀ n i (x : L4) (r2 r4 r5 : Wide), i + n = N →
      Small_r2_4.b22 ⟨toW m, inv.w⟩ (toW x) ⟨(), UInt256.ofNat N⟩ r2 r3 r4 r5 (UInt256.ofNat i) =
        pure (toW ((ssq 4 m inv)^[6] ((sdouble m)^[n] x)))
  | 0, i, x, r2, r4, r5, h => by
    rw [Small_r2_4.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, if_false, Lib.Range_start_0_6, pure_bind]
    exact r2_sq4 m inv _ _ _ 6 0 x _ _ rfl
  | n + 1, i, x, r2, r4, r5, h => by
    rw [Small_r2_4.b22.eq_1]
    simp only [has0_eq N hN (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < N) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_at_0, Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega),
      pure_bind, sdouble4_eq]
    rw [Function.iterate_succ_apply (sdouble m)]
    exact r2_dbl4 m inv N hN r3 n (i + 1) _ _ _ _ (by omega)

/-- **`Small<4>::r2`** for a nonzero top limb. -/
theorem r2_4_eq (m : L4) (inv : Limb) (htop : 0 < (topLimb 4 m).val) :
    Small_r2_4 ⟨toW m, inv.w⟩ = pure (toW (r2 4 m inv)) := by
  have hs := log2_lt64 (topLimb 4 m)
  have ht : topLimb 4 m = m.l3 := by simp [topLimb]
  rw [ht] at htop hs
  simp only [Small_r2_4]
  lbranch
  simp only [toW, shift_eq _ htop,
    downcast_truncate_u256_u64_eq, toNat_lit (show m.l3.val.log2 < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show m.l3.val.log2 < 2 ^ 64 by omega), pure_bind, shl64_bit hs,
    sub64_eq hs, downcast_u64_usize, Fe.EVM.ofNat_add_ofNat (show 64 - m.l3.val.log2 + 4 <
      UInt256.size by unfold UInt256.size; omega), Lib.Range_start_0]
  have e : (Wide.mk (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (bitL _ hs).w) = toW (r2start 4 m) := by simp [toW, r2start, topLimb, zero_w]
  rw [e]
  have := r2_dbl4 m inv (64 - m.l3.val.log2 + 4) (by omega) default (64 - m.l3.val.log2 + 4) 0
    (r2start 4 m) default default default (by omega)
  have hr : r2 4 m inv = (ssq 4 m inv)^[6] ((sdouble m)^[64 - m.l3.val.log2 + 4] (r2start 4 m)) := by
    rw [r2, ht]
  simp only [toW] at this ⊢
  rw [this, hr]

end FeProofs.Modexp
