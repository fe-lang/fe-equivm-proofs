import FeProofs.Precompiles.Modexp.SmallRows
import Mathlib.Tactic.LinearCombination

/-!
# Modexp: what `Small<L>::mul` computes

`smul_spec`: for an odd modulus `M` of `L ≤ 4` limbs with `inv = -M⁻¹ mod β`, and `a`, `b` of `L`
limbs with `a b < R M` (`R = β^L`; it holds when either is below `M`), `smul L` returns the
Montgomery product: below `M`, and `≡ a b R⁻¹ (mod M)`, stated as `c R ≡ a b`.  The rows give
`R T = a b + Q M` with `Q < R`, so `T < 2 M`, and `ssub` subtracts `M` once if `T ≥ M`
(`ssub_spec`).
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- The number four limbs denote. -/
def nat4 (a : L4) : ℕ := a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val + 2 ^ 192 * a.l3.val

theorem nat4_lt (a : L4) : nat4 a < 2 ^ 256 := by
  have := a.l0.isLt; have := a.l1.isLt; have := a.l2.isLt; have := a.l3.isLt
  unfold nat4; omega

theorem sbb_step (a b c : Limb) (hc : c.val ≤ 1) :
    (sbbLo a b c).val + b.val + c.val = a.val + 2 ^ 64 * (sbbHi a b c).val :=
  sbbLo_sbbHi a b c hc

theorem fin_mod {T M v : ℕ} (h2 : T < 2 * M)
    (hv : (T < M ∧ v = T) ∨ (M ≤ T ∧ v = T - M)) : v = T % M ∧ v < M := by
  rcases hv with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact ⟨(Nat.mod_eq_of_lt h).symm, h⟩
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; exact ⟨rfl, by omega⟩

/-- The subtraction borrowed: `T < M`, and the result is `t`, which is `T`. -/
theorem ssub_borrow {T M R v top D lo : ℕ} (hE : D + R * lo + M = T + R * 2 ^ 64)
    (hD : D < R) (hlo : lo < 2 ^ 64) (hM : M < R) (hT : T = v + R * top) (h2 : T < 2 * M) :
    v = T % M ∧ v < M := by
  have : R * lo ≤ R * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have : R * (2 ^ 64 - 1) + R = R * 2 ^ 64 := by
    rw [← Nat.mul_succ]; congr 1
  have hTM : T < M := by omega
  have htop : top = 0 := by
    by_contra h
    have : R ≤ R * top := Nat.le_mul_of_pos_right _ (by omega)
    omega
  subst htop
  exact fin_mod h2 (Or.inl ⟨hTM, by omega⟩)

/-- The subtraction did not borrow: the result is `T - M`. -/
theorem ssub_noborrow {T M R v D lo : ℕ} (hE : D + R * lo + M = T) (hM : M < R)
    (h2 : T < 2 * M) (hv : v = D) : v = T % M ∧ v < M := by
  have hlo : lo = 0 := by
    by_contra h
    have : R ≤ R * lo := Nat.le_mul_of_pos_right _ (by omega)
    omega
  subst hlo
  exact fin_mod h2 (Or.inr ⟨by omega, by omega⟩)

theorem chain2 {d0 d1 lo m0 m1 t0 t1 top c0 c1 bf : ℕ}
    (e0 : d0 + m0 + 0 = t0 + 2 ^ 64 * c0) (e1 : d1 + m1 + c0 = t1 + 2 ^ 64 * c1)
    (f : lo + 0 + c1 = top + 2 ^ 64 * bf) :
    (d0 + 2 ^ 64 * d1) + 2 ^ 128 * lo + (m0 + 2 ^ 64 * m1) =
      (t0 + 2 ^ 64 * t1 + 2 ^ 128 * top) + 2 ^ 128 * 2 ^ 64 * bf := by omega

theorem chain3 {d0 d1 d2 lo m0 m1 m2 t0 t1 t2 top c0 c1 c2 bf : ℕ}
    (e0 : d0 + m0 + 0 = t0 + 2 ^ 64 * c0) (e1 : d1 + m1 + c0 = t1 + 2 ^ 64 * c1)
    (e2 : d2 + m2 + c1 = t2 + 2 ^ 64 * c2) (f : lo + 0 + c2 = top + 2 ^ 64 * bf) :
    (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2) + 2 ^ 192 * lo + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2) =
      (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * top) + 2 ^ 192 * 2 ^ 64 * bf := by omega

theorem chain4 {d0 d1 d2 d3 lo m0 m1 m2 m3 t0 t1 t2 t3 top c0 c1 c2 c3 bf : ℕ}
    (e0 : d0 + m0 + 0 = t0 + 2 ^ 64 * c0) (e1 : d1 + m1 + c0 = t1 + 2 ^ 64 * c1)
    (e2 : d2 + m2 + c1 = t2 + 2 ^ 64 * c2) (e3 : d3 + m3 + c2 = t3 + 2 ^ 64 * c3)
    (f : lo + 0 + c3 = top + 2 ^ 64 * bf) :
    (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3) + 2 ^ 256 * lo +
        (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) =
      (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * top) +
        2 ^ 256 * 2 ^ 64 * bf := by omega

theorem limb0 : ((0 : Limb).val) = 0 := rfl
theorem limb1 : ((1 : Limb).val) = 1 := rfl

theorem lt128 {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a + 2 ^ 64 * b < 2 ^ 128 := by
  calc a + 2 ^ 64 * b < 2 ^ 64 + 2 ^ 64 * b := by omega
    _ = 2 ^ 64 * (b + 1) := by ring
    _ ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_left _ hb
    _ = 2 ^ 128 := by norm_num

theorem bf_cases {bf : ℕ} (h : bf ≤ 1) : bf = 0 ∨ bf = 1 := by omega

theorem high_zero2 {a : L4} (h : nat4 a < 2 ^ 128) : a.l2.val = 0 ∧ a.l3.val = 0 := by
  have := a.l0.isLt; have := a.l1.isLt; unfold nat4 at h; omega

theorem high_zero3 {a : L4} (h : nat4 a < 2 ^ 192) : a.l3.val = 0 := by
  have := a.l0.isLt; have := a.l1.isLt; have := a.l2.isLt; unfold nat4 at h; omega

/-- `ssub` at two limbs. -/
theorem ssub2_spec (m t : L4) (top : Limb) (hm : nat4 m < 2 ^ 128) (ht : nat4 t < 2 ^ 128)
    (hT : nat4 t + 2 ^ 128 * top.val < 2 * nat4 m) :
    nat4 (ssub 2 m t top) = (nat4 t + 2 ^ 128 * top.val) % nat4 m ∧
      nat4 (ssub 2 m t top) < nat4 m := by
  obtain ⟨hm2, hm3⟩ := high_zero2 hm
  obtain ⟨ht2, ht3⟩ := high_zero2 ht
  have e0 := sbb_step t.l0 m.l0 0 zero_val_le
  have b0 := sbbHi_val_le t.l0 m.l0 0
  have e1 := sbb_step t.l1 m.l1 _ b0
  have b1 := sbbHi_val_le t.l1 m.l1 (sbbHi t.l0 m.l0 0)
  have f := sbb_step top 0 _ b1
  have hf := sbbHi_val_le top 0 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))
  have hE := chain2 e0 e1 f
  have hd0 := (sbbLo t.l0 m.l0 0).isLt
  have hd1 := (sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0)).isLt
  have hlo := (sbbLo top 0 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))).isLt
  have hT' : t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * top.val < 2 * (m.l0.val + 2 ^ 64 * m.l1.val) := by
    unfold nat4 at hT; rw [hm2, hm3, ht2, ht3] at hT; simpa using hT
  have hm' : m.l0.val + 2 ^ 64 * m.l1.val < 2 ^ 128 := by
    unfold nat4 at hm; rw [hm2, hm3] at hm; simpa using hm
  have eT : nat4 t = t.l0.val + 2 ^ 64 * t.l1.val := by unfold nat4; rw [ht2, ht3]; simp
  have eM : nat4 m = m.l0.val + 2 ^ 64 * m.l1.val := by unfold nat4; rw [hm2, hm3]; simp
  rw [eT, eM]
  simp only [ssub, if_true]
  generalize sbbHi top 0 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)) = bf at *
  generalize sbbLo t.l0 m.l0 0 = d0 at *
  generalize sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0) = d1 at *
  generalize sbbLo top 0 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)) = lo at *
  by_cases h : bf = 1
  · rw [if_pos h, eT]
    rw [h, limb1, Nat.mul_one] at hE
    exact ssub_borrow (R := 2 ^ 128) (v := t.l0.val + 2 ^ 64 * t.l1.val) (top := top.val) hE
      (lt128 hd0 hd1) hlo hm' rfl hT'
  · have h0 : bf.val = 0 := by
      rcases bf_cases hf with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') h
    rw [if_neg h, show nat4 ⟨d0, d1, 0, 0⟩ = d0.val + 2 ^ 64 * d1.val by unfold nat4; simp]
    rw [h0, Nat.mul_zero, Nat.add_zero] at hE
    exact ssub_noborrow (R := 2 ^ 128) hE hm' hT' rfl

theorem lt192 {a b c : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    a + 2 ^ 64 * b + 2 ^ 128 * c < 2 ^ 192 := by
  have := lt128 ha hb
  calc a + 2 ^ 64 * b + 2 ^ 128 * c < 2 ^ 128 + 2 ^ 128 * c := by omega
    _ = 2 ^ 128 * (c + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ 64 := Nat.mul_le_mul_left _ hc
    _ = 2 ^ 192 := by norm_num

theorem lt256 {a b c d : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64) :
    a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d < 2 ^ 256 := by
  have := lt192 ha hb hc
  calc a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d < 2 ^ 192 + 2 ^ 192 * d := by omega
    _ = 2 ^ 192 * (d + 1) := by ring
    _ ≤ 2 ^ 192 * 2 ^ 64 := Nat.mul_le_mul_left _ hd
    _ = 2 ^ 256 := by norm_num

/-- `ssub` at three limbs. -/
theorem ssub3_spec (m t : L4) (top : Limb) (hm : nat4 m < 2 ^ 192) (ht : nat4 t < 2 ^ 192)
    (hT : nat4 t + 2 ^ 192 * top.val < 2 * nat4 m) :
    nat4 (ssub 3 m t top) = (nat4 t + 2 ^ 192 * top.val) % nat4 m ∧
      nat4 (ssub 3 m t top) < nat4 m := by
  have hm3 := high_zero3 hm
  have ht3 := high_zero3 ht
  have e0 := sbb_step t.l0 m.l0 0 zero_val_le
  have b0 := sbbHi_val_le t.l0 m.l0 0
  have e1 := sbb_step t.l1 m.l1 _ b0
  have b1 := sbbHi_val_le t.l1 m.l1 (sbbHi t.l0 m.l0 0)
  have e2 := sbb_step t.l2 m.l2 _ b1
  have b2 := sbbHi_val_le t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))
  have f := sbb_step top 0 _ b2
  have hf := sbbHi_val_le top 0 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))
  have hE := chain3 e0 e1 e2 f
  have hd0 := (sbbLo t.l0 m.l0 0).isLt
  have hd1 := (sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0)).isLt
  have hd2 := (sbbLo t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))).isLt
  have hlo := (sbbLo top 0 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))).isLt
  have eT : nat4 t = t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * t.l2.val := by
    unfold nat4; rw [ht3]; simp
  have eM : nat4 m = m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val := by
    unfold nat4; rw [hm3]; simp
  rw [eT] at hT; rw [eM] at hT hm
  rw [eT, eM]
  simp only [ssub, show (3 = 2) = False by decide, if_false, if_true]
  generalize sbbHi top 0 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))) = bf at *
  generalize sbbLo t.l0 m.l0 0 = d0 at *
  generalize sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0) = d1 at *
  generalize sbbLo t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)) = d2 at *
  generalize sbbLo top 0 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))) = lo at *
  by_cases h : bf = 1
  · rw [if_pos h, eT]
    rw [h, limb1, Nat.mul_one] at hE
    exact ssub_borrow (R := 2 ^ 192) (v := t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * t.l2.val)
      (top := top.val) hE (lt192 hd0 hd1 hd2) hlo hm rfl hT
  · have h0 : bf.val = 0 := by
      rcases bf_cases hf with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') h
    rw [if_neg h, show nat4 ⟨d0, d1, d2, 0⟩ = d0.val + 2 ^ 64 * d1.val + 2 ^ 128 * d2.val by
      unfold nat4; simp]
    rw [h0, Nat.mul_zero, Nat.add_zero] at hE
    exact ssub_noborrow (R := 2 ^ 192) hE hm hT rfl

/-- `ssub` at four limbs. -/
theorem ssub4_spec (m t : L4) (top : Limb) (hT : nat4 t + 2 ^ 256 * top.val < 2 * nat4 m) :
    nat4 (ssub 4 m t top) = (nat4 t + 2 ^ 256 * top.val) % nat4 m ∧
      nat4 (ssub 4 m t top) < nat4 m := by
  have hm := nat4_lt m
  have e0 := sbb_step t.l0 m.l0 0 zero_val_le
  have b0 := sbbHi_val_le t.l0 m.l0 0
  have e1 := sbb_step t.l1 m.l1 _ b0
  have b1 := sbbHi_val_le t.l1 m.l1 (sbbHi t.l0 m.l0 0)
  have e2 := sbb_step t.l2 m.l2 _ b1
  have b2 := sbbHi_val_le t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))
  have e3 := sbb_step t.l3 m.l3 _ b2
  have b3 := sbbHi_val_le t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))
  have f := sbb_step top 0 _ b3
  have hf := sbbHi_val_le top 0
    (sbbHi t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))))
  have hE := chain4 e0 e1 e2 e3 f
  have hd0 := (sbbLo t.l0 m.l0 0).isLt
  have hd1 := (sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0)).isLt
  have hd2 := (sbbLo t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))).isLt
  have hd3 := (sbbLo t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))).isLt
  have hlo := (sbbLo top 0
    (sbbHi t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))))).isLt
  unfold nat4 at hT hm ⊢
  simp only [ssub, show (4 = 2) = False by decide, show (4 = 3) = False by decide, if_false]
  generalize sbbHi top 0
    (sbbHi t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))) = bf at *
  generalize sbbLo t.l0 m.l0 0 = d0 at *
  generalize sbbLo t.l1 m.l1 (sbbHi t.l0 m.l0 0) = d1 at *
  generalize sbbLo t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)) = d2 at *
  generalize sbbLo t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0))) = d3 at *
  generalize sbbLo top 0
    (sbbHi t.l3 m.l3 (sbbHi t.l2 m.l2 (sbbHi t.l1 m.l1 (sbbHi t.l0 m.l0 0)))) = lo at *
  by_cases h : bf = 1
  · rw [if_pos h]
    rw [h, limb1, Nat.mul_one] at hE
    exact ssub_borrow (R := 2 ^ 256) (top := top.val) hE (lt256 hd0 hd1 hd2 hd3) hlo hm rfl hT
  · have h0 : bf.val = 0 := by
      rcases bf_cases hf with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') h
    rw [if_neg h]
    rw [h0, Nat.mul_zero, Nat.add_zero] at hE
    exact ssub_noborrow (R := 2 ^ 256) hE hm hT rfl

end FeProofs.Modexp

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- From `R T = A B + Q M` with `Q < R`, `A B < R M` and the reduction `r = T mod M`, the
    Montgomery product's two facts. -/
theorem mont_close {R T A B Q M r : ℕ} (hR : 0 < R) (hT : R * T = A * B + Q * M) (hQ : Q < R)
    (hAB : A * B < R * M) (hr : r = T % M) : T < 2 * M ∧ r * R % M = A * B % M := by
  have hQM : Q * M ≤ (R - 1) * M := Nat.mul_le_mul_right _ (by omega)
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, Nat.mul_zero] at hAB; omega
    · exact h
  refine ⟨?_, ?_⟩
  · by_contra h
    have : R * (2 * M) ≤ R * T := Nat.mul_le_mul_left _ (by omega)
    have : (R - 1) * M + M = R * M := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hR]
    nlinarith
  · rw [hr, Nat.mod_mul_mod, Nat.mul_comm, hT, Nat.add_mul_mod_self_right]

theorem nat4_two {a : L4} (h : nat4 a < 2 ^ 128) : nat4 a = a.l0.val + 2 ^ 64 * a.l1.val := by
  obtain ⟨h2, h3⟩ := high_zero2 h; unfold nat4; rw [h2, h3]; simp

/-- **`Small<2>::mul`.** -/
theorem smul2_spec (m a b : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ 128)
    (ha : nat4 a < 2 ^ 128) (hb : nat4 b < 2 ^ 128) (hab : nat4 a * nat4 b < 2 ^ 128 * nat4 m) :
    nat4 (smul 2 m inv a b) < nat4 m ∧
      nat4 (smul 2 m inv a b) * 2 ^ 128 % nat4 m = nat4 a * nat4 b % nat4 m := by
  simp only [smul, show (2 = 1) = False by decide, if_false, if_true]
  obtain ⟨z12, z13, e1⟩ := row2_spec m a Z4 inv b.l0 0 hinv
  generalize row2 m inv a b.l0 Z4 0 = x1 at z12 z13 e1
  obtain ⟨z22, z23, e2⟩ := row2_spec m a x1.1 inv b.l1 x1.2 hinv
  generalize row2 m inv a b.l1 x1.1 x1.2 = x2 at z22 z23 e2
  have hx2 : nat4 x2.1 < 2 ^ 128 := by
    have := lt128 x2.1.l0.isLt x2.1.l1.isLt; unfold nat4; rw [z22, z23]; simpa using this
  have ex2 := nat4_two hx2
  have em := nat4_two hm
  have hm2 : m.l0.val + 2 ^ 64 * m.l1.val < 2 ^ 128 := em ▸ hm
  rw [nat4_two ha, em, nat4_two hb] at hab
  rw [em]
  simp only [Z4, limb0, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e1
  generalize mulLo (macLo a.l0 b.l0 0 0) inv = q1 at e1
  generalize mulLo (macLo a.l0 b.l1 x1.1.l0 0) inv = q2 at e2
  have hq1 := q1.isLt; have hq2 := q2.isLt
  have hT : 2 ^ 128 * (nat4 x2.1 + 2 ^ 128 * x2.2.val) =
      (a.l0.val + 2 ^ 64 * a.l1.val) * (b.l0.val + 2 ^ 64 * b.l1.val) +
        (q1.val + 2 ^ 64 * q2.val) * (m.l0.val + 2 ^ 64 * m.l1.val) := by
    rw [ex2]; zify at e1 e2 ⊢; linear_combination 2 ^ 64 * e2 + e1
  obtain ⟨hT2, hc⟩ := mont_close (by norm_num) hT (lt128 hq1 hq2) hab rfl
  obtain ⟨r1, r2⟩ := ssub2_spec m x2.1 x2.2 hm hx2 (by rw [em]; exact hT2)
  rw [em] at r1 r2
  rw [nat4_two ha, nat4_two hb]
  exact ⟨r2, by rw [r1]; exact hc⟩

theorem nat4_three {a : L4} (h : nat4 a < 2 ^ 192) :
    nat4 a = a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val := by
  have h3 := high_zero3 h; unfold nat4; rw [h3]; simp

/-- **`Small<3>::mul`.** -/
theorem smul3_spec (m a b : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ 192)
    (ha : nat4 a < 2 ^ 192) (hb : nat4 b < 2 ^ 192) (hab : nat4 a * nat4 b < 2 ^ 192 * nat4 m) :
    nat4 (smul 3 m inv a b) < nat4 m ∧
      nat4 (smul 3 m inv a b) * 2 ^ 192 % nat4 m = nat4 a * nat4 b % nat4 m := by
  simp only [smul, show (3 = 1) = False by decide, show (3 = 2) = False by decide, if_false,
    if_true]
  obtain ⟨z13, e1⟩ := row3_spec m a Z4 inv b.l0 0 hinv
  generalize row3 m inv a b.l0 Z4 0 = x1 at z13 e1
  obtain ⟨z23, e2⟩ := row3_spec m a x1.1 inv b.l1 x1.2 hinv
  generalize row3 m inv a b.l1 x1.1 x1.2 = x2 at z23 e2
  obtain ⟨z33, e3⟩ := row3_spec m a x2.1 inv b.l2 x2.2 hinv
  generalize row3 m inv a b.l2 x2.1 x2.2 = x3 at z33 e3
  have hx3 : nat4 x3.1 < 2 ^ 192 := by
    have := lt192 x3.1.l0.isLt x3.1.l1.isLt x3.1.l2.isLt; unfold nat4; rw [z33]; simpa using this
  have ex3 := nat4_three hx3
  have em := nat4_three hm
  rw [nat4_three ha, em, nat4_three hb] at hab
  rw [em]
  simp only [Z4, limb0, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e1
  generalize mulLo (macLo a.l0 b.l0 0 0) inv = q1 at e1
  generalize mulLo (macLo a.l0 b.l1 x1.1.l0 0) inv = q2 at e2
  generalize mulLo (macLo a.l0 b.l2 x2.1.l0 0) inv = q3 at e3
  have hq1 := q1.isLt; have hq2 := q2.isLt; have hq3 := q3.isLt
  have hT : 2 ^ 192 * (nat4 x3.1 + 2 ^ 192 * x3.2.val) =
      (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val) *
        (b.l0.val + 2 ^ 64 * b.l1.val + 2 ^ 128 * b.l2.val) +
        (q1.val + 2 ^ 64 * q2.val + 2 ^ 128 * q3.val) *
          (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val) := by
    rw [ex3]; zify at e1 e2 e3 ⊢; linear_combination 2 ^ 128 * e3 + 2 ^ 64 * e2 + e1
  obtain ⟨hT2, hc⟩ := mont_close (by norm_num) hT (lt192 hq1 hq2 hq3) hab rfl
  obtain ⟨r1, r2⟩ := ssub3_spec m x3.1 x3.2 hm hx3 (by rw [em]; exact hT2)
  rw [em] at r1 r2
  rw [nat4_three ha, nat4_three hb]
  exact ⟨r2, by rw [r1]; exact hc⟩

/-- **`Small<4>::mul`.** -/
theorem smul4_spec (m a b : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hab : nat4 a * nat4 b < 2 ^ 256 * nat4 m) :
    nat4 (smul 4 m inv a b) < nat4 m ∧
      nat4 (smul 4 m inv a b) * 2 ^ 256 % nat4 m = nat4 a * nat4 b % nat4 m := by
  simp only [smul, show (4 = 1) = False by decide, show (4 = 2) = False by decide,
    show (4 = 3) = False by decide, if_false]
  have e1 := row4_spec m a Z4 inv b.l0 0 hinv
  generalize row4 m inv a b.l0 Z4 0 = x1 at e1
  have e2 := row4_spec m a x1.1 inv b.l1 x1.2 hinv
  generalize row4 m inv a b.l1 x1.1 x1.2 = x2 at e2
  have e3 := row4_spec m a x2.1 inv b.l2 x2.2 hinv
  generalize row4 m inv a b.l2 x2.1 x2.2 = x3 at e3
  have e4 := row4_spec m a x3.1 inv b.l3 x3.2 hinv
  generalize row4 m inv a b.l3 x3.1 x3.2 = x4 at e4
  unfold nat4 at hab ⊢
  simp only [Z4, limb0, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e1
  generalize mulLo (macLo a.l0 b.l0 0 0) inv = q1 at e1
  generalize mulLo (macLo a.l0 b.l1 x1.1.l0 0) inv = q2 at e2
  generalize mulLo (macLo a.l0 b.l2 x2.1.l0 0) inv = q3 at e3
  generalize mulLo (macLo a.l0 b.l3 x3.1.l0 0) inv = q4 at e4
  have hq1 := q1.isLt; have hq2 := q2.isLt; have hq3 := q3.isLt; have hq4 := q4.isLt
  have hT : 2 ^ 256 * (nat4 x4.1 + 2 ^ 256 * x4.2.val) =
      (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val + 2 ^ 192 * a.l3.val) *
        (b.l0.val + 2 ^ 64 * b.l1.val + 2 ^ 128 * b.l2.val + 2 ^ 192 * b.l3.val) +
        (q1.val + 2 ^ 64 * q2.val + 2 ^ 128 * q3.val + 2 ^ 192 * q4.val) *
          (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val + 2 ^ 192 * m.l3.val) := by
    unfold nat4; zify at e1 e2 e3 e4 ⊢
    linear_combination 2 ^ 192 * e4 + 2 ^ 128 * e3 + 2 ^ 64 * e2 + e1
  obtain ⟨hT2, hc⟩ := mont_close (by norm_num) hT (lt256 hq1 hq2 hq3 hq4) hab rfl
  obtain ⟨r1, r2⟩ := ssub4_spec m x4.1 x4.2 (by unfold nat4; exact hT2)
  unfold nat4 at r1 r2
  exact ⟨r2, by rw [r1]; exact hc⟩

theorem nat4_one {a : L4} (h : nat4 a < 2 ^ 64) : nat4 a = a.l0.val := by
  have := a.l0.isLt; have := a.l1.isLt; have := a.l2.isLt; have := a.l3.isLt
  unfold nat4 at *; omega

/-- **`Small<1>::mul`**, in `u128` arithmetic. -/
theorem smul1_spec (m a b : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ 64)
    (ha : nat4 a < 2 ^ 64) (hb : nat4 b < 2 ^ 64) (hab : nat4 a * nat4 b < 2 ^ 64 * nat4 m) :
    nat4 (smul 1 m inv a b) < nat4 m ∧
      nat4 (smul 1 m inv a b) * 2 ^ 64 % nat4 m = nat4 a * nat4 b % nat4 m := by
  rw [nat4_one ha, nat4_one hb, nat4_one hm] at *
  simp only [smul, if_true, smul1]
  have hc := macLo_cancel m.l0 inv (loD (mulD a.l0 b.l0)) hinv
  generalize hq : mulLo (loD (mulD a.l0 b.l0)) inv = q at hc
  have hP := mul_limbs_lt q m.l0
  have hm0 := m.l0.isLt
  generalize htd : mulD a.l0 b.l0 = tD at hc hq
  have htv : tD.val = a.l0.val * b.l0.val := by rw [← htd]; rfl
  generalize hpd : mulD q m.l0 = pD
  have hpv : pD.val = q.val * m.l0.val := by rw [← hpd]; rfl
  simp only [macLo, loD, limb0, Nat.add_zero] at hc
  -- `s = (t + p) / β` exactly, as `t mod β + p mod β` is `0` or `β`.
  generalize hsd : addD (addD (L2D (hiD tD)) (L2D (hiD pD)))
    (L2D (if loD tD = 0 then 0 else 1)) = s
  have hs : s.val * 2 ^ 64 = a.l0.val * b.l0.val + q.val * m.l0.val := by
    rw [← hsd, ← htv, ← hpv]
    simp only [addD, L2D, hiD, loD]
    have h1 := tD.isLt; have h2 := pD.isLt
    rw [hpv] at h2
    split_ifs with h
    · have h0 : tD.val % 2 ^ 64 = 0 := by simpa using congrArg Fin.val h
      simp only [limb0]; rw [← hpv] at hc; omega
    · have h0 : tD.val % 2 ^ 64 ≠ 0 := fun e => h (Fin.ext e)
      simp only [limb1]; rw [← hpv] at hc; omega
  -- The reduction.
  have hsm : s.val < 2 * m.l0.val := by
    have : q.val * m.l0.val < 2 ^ 64 * m.l0.val := Nat.mul_lt_mul_of_pos_right q.isLt (by
      rcases Nat.eq_zero_or_pos m.l0.val with h | h
      · rw [h, Nat.mul_zero] at hab; omega
      · exact h)
    nlinarith
  obtain ⟨hT2, hcm⟩ := mont_close (R := 2 ^ 64) (T := s.val) (Q := q.val) (by norm_num)
    (by rw [Nat.mul_comm]; exact hs) q.isLt hab rfl
  have hval : (loD (if m.l0.val ≤ s.val then subD s (L2D m.l0) else s)).val = s.val % m.l0.val := by
    have := s.isLt
    split_ifs with h
    · simp only [loD, subD, L2D]
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show s.val - m.l0.val < m.l0.val by omega)]
      omega
    · simp only [loD]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hz : nat4 ⟨loD (if m.l0.val ≤ s.val then subD s (L2D m.l0) else s), 0, 0, 0⟩ =
      s.val % m.l0.val := by
    unfold nat4; rw [hval]; simp
  rw [hz]
  exact ⟨Nat.mod_lt _ (by omega), hcm⟩

/-- **`Small<L>::mul`**, for `L = 1 … 4` and `R = 2 ^ (64 L)`: the product is below `M` and
    `c R ≡ a b (mod M)`. -/
theorem smul_spec (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m a b : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hm : nat4 m < 2 ^ (64 * L)) (ha : nat4 a < 2 ^ (64 * L)) (hb : nat4 b < 2 ^ (64 * L))
    (hab : nat4 a * nat4 b < 2 ^ (64 * L) * nat4 m) :
    nat4 (smul L m inv a b) < nat4 m ∧
      nat4 (smul L m inv a b) * 2 ^ (64 * L) % nat4 m = nat4 a * nat4 b % nat4 m := by
  obtain ⟨h1, h4⟩ := hL
  interval_cases L
  · exact smul1_spec m a b inv hinv hm ha hb hab
  · exact smul2_spec m a b inv hinv hm ha hb hab
  · exact smul3_spec m a b inv hinv hm ha hb hab
  · exact smul4_spec m a b inv hinv hab

end FeProofs.Modexp
