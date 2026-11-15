import FeProofs.Precompiles.Inverse.Divsteps
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Precompiles: what `divsteps` returns

For an odd `f0`, `divsteps eta f0 g0` returns a matrix `[u v; q r]` with `|u| + |v| ≤ 2 ^ 62`,
`|q| + |r| ≤ 2 ^ 62`, determinant `2 ^ 62`, and `u f0 + v g0 ≡ q f0 + r g0 ≡ 0 (mod 2 ^ 62)`
(`divsteps_spec`).  These are what the outer loop of `invert` needs: the matrix maps `(f, g)`
to integers, keeps them bounded, and does not change their odd common divisors.

The proof follows the loop: at each entry, with `i = 62 - left` divsteps done, the first row
is bounded by `2 ^ i`, the second by `2 ^ (i + c)` where `2 ^ c` divides `g` (`DS.Inv`), and the
rows map `(f0, g0)` to `2 ^ i (f, g)` modulo `2 ^ 64`.  Each pass removes at least one more bit
than the last left pending, so the loop ends.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

/-! ## Trailing zeros -/

theorem takeWhile_range (p : ℕ → Bool) (N : ℕ) :
    ((List.range N).takeWhile p).length ≤ N ∧
      (∀ j < ((List.range N).takeWhile p).length, p j = true) ∧
      (((List.range N).takeWhile p).length < N → p ((List.range N).takeWhile p).length = false) := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.range_succ, List.takeWhile_append]
    split
    · rename_i hl
      simp only [List.length_range] at hl
      rw [List.length_append, List.takeWhile_cons]
      split
      · rename_i hp
        simp only [List.takeWhile_nil, List.length_cons, List.length_nil, List.length_range]
        refine ⟨by omega, fun j hj => ?_, by omega⟩
        rcases Nat.lt_or_ge j N with h | h
        · exact h2 j (by omega)
        · obtain rfl : j = N := by omega
          exact hp
      · rename_i hp
        simp only [List.length_nil, List.length_range, Nat.add_zero]
        refine ⟨by omega, fun j hj => h2 j (by omega), fun _ => by simpa using hp⟩
    · rename_i hl
      simp only [List.length_range] at hl
      exact ⟨by omega, h2, fun _ => h3 (by omega)⟩

theorem tz_spec (a : Limb) :
    a.tz.val ≤ 64 ∧ (∀ j < a.tz.val, a.val.testBit j = false) ∧
      (a.tz.val < 64 → a.val.testBit a.tz.val = true) := by
  obtain ⟨h1, h2, h3⟩ := takeWhile_range (fun n => !a.val.testBit n) 64
  refine ⟨h1, fun j hj => by simpa using h2 j hj, fun h => by simpa using h3 h⟩

theorem sentinel_testBit (left j : ℕ) (hl : left ≤ 64) :
    (Limb.shl 18446744073709551615 left).val.testBit j = (decide (left ≤ j) && decide (j < 64)) := by
  have hv : (Limb.shl 18446744073709551615 left).val = 2 ^ left * (2 ^ (64 - left) - 1) := by
    simp only [Limb.shl]
    show 18446744073709551615 * 2 ^ left % 2 ^ 64 = _
    have h64 : (2 : ℕ) ^ 64 = 2 ^ left * 2 ^ (64 - left) := by rw [← pow_add]; congr 1; omega
    rw [show (18446744073709551615 : ℕ) = 2 ^ 64 - 1 by rfl, h64]
    generalize hA : 2 ^ left = A
    generalize hB : 2 ^ (64 - left) = B
    have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_two_pow
    have hB1 : 1 ≤ B := by rw [← hB]; exact Nat.one_le_two_pow
    have hAB : 1 ≤ A * B := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e : (A * B - 1) * A = A * (B - 1) + (A - 1) * (A * B) := by
      zify [hA1, hB1, hAB]; ring
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  rw [hv, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases h : left ≤ j <;> simp [h]
  omega

/-- What `shift` removes: `z ≤ left` zeros, all zeros of `g`, and all of its trailing zeros
when `z < left`; at least any `c ≤ left` with `2 ^ c ∣ g`. -/
theorem zeros_spec (s : DS) (hl : s.left.val ≤ 62) :
    s.zeros.val ≤ s.left.val ∧ s.g.val = 2 ^ s.zeros.val * (s.g.val / 2 ^ s.zeros.val) ∧
      (s.zeros.val < s.left.val → s.g.val / 2 ^ s.zeros.val % 2 = 1) ∧
      (∀ c ≤ s.left.val, 2 ^ c ∣ s.g.val → c ≤ s.zeros.val) := by
  obtain ⟨h1, h2, h3⟩ := tz_spec (s.g ||| Limb.shl 18446744073709551615 s.left.val)
  have hbit : ∀ j, (s.g ||| Limb.shl 18446744073709551615 s.left.val).val.testBit j =
      (s.g.val.testBit j || (decide (s.left.val ≤ j) && decide (j < 64))) := by
    intro j
    rw [show (s.g ||| Limb.shl 18446744073709551615 s.left.val).val =
      s.g.val ||| (Limb.shl 18446744073709551615 s.left.val).val from
        Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 64) s.g.isLt (Limb.shl _ _).isLt),
      Nat.testBit_or, sentinel_testBit _ _ (by omega)]
  rw [show s.zeros = (s.g ||| Limb.shl 18446744073709551615 s.left.val).tz from rfl]
  generalize hz : (s.g ||| Limb.shl 18446744073709551615 s.left.val).tz.val = z at h1 h2 h3
  have hzl : z ≤ s.left.val := by
    by_contra h
    have := h2 s.left.val (by omega)
    rw [hbit] at this
    simp at this
    omega
  have hlow : ∀ j < z, s.g.val.testBit j = false := by
    intro j hj
    have := h2 j hj
    rw [hbit] at this
    simp only [Bool.or_eq_false_iff] at this
    exact this.1
  have hmod : s.g.val % 2 ^ z = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < z
    · simp [hi, hlow i hi]
    · simp [hi]
  have hset : z < s.left.val → s.g.val.testBit z = true := by
    intro h
    have := h3 (by omega)
    rw [hbit] at this
    simpa [show ¬ s.left.val ≤ z by omega] using this
  refine ⟨hzl, ?_, ?_, ?_⟩
  · have := Nat.div_add_mod s.g.val (2 ^ z)
    omega
  · intro h
    have := hset h
    rw [Nat.testBit_eq_decide_div_mod_eq] at this
    simpa using this
  · intro c hc hdvd
    by_contra h
    have := hset (by omega)
    have h0 : s.g.val % 2 ^ c = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h4 := Nat.testBit_mod_two_pow s.g.val c z
    rw [h0, Nat.zero_testBit, this] at h4
    simp at h4
    omega

/-! ## Signed readings of limbs -/

theorem sgn_modEq (x : Limb) : x.sgn ≡ x.val [ZMOD 2 ^ 64] := by
  have := Int.bmod_emod (x := (x.val : ℤ)) (m := 2 ^ 64)
  push_cast at this
  exact this

theorem sgn_range (x : Limb) : -2 ^ 63 ≤ x.sgn ∧ x.sgn < 2 ^ 63 := by
  have h1 := Int.le_bmod (x := (x.val : ℤ)) (m := 2 ^ 64) (by decide)
  have h2 := Int.bmod_lt (x := (x.val : ℤ)) (m := 2 ^ 64) (by decide)
  unfold Limb.sgn
  simp only [Nat.reducePow, Nat.cast_ofNat] at h1 h2 ⊢
  constructor <;> omega

/-- A limb whose value is `n` modulo `2 ^ 64`, for `n` in the signed range, reads as `n`. -/
theorem sgn_eq {x : Limb} {n : ℤ} (h : (x.val : ℤ) ≡ n [ZMOD 2 ^ 64]) (h1 : -2 ^ 63 ≤ n)
    (h2 : n < 2 ^ 63) : x.sgn = n := by
  unfold Limb.sgn
  unfold Int.ModEq at h
  have e1 := Int.emod_bmod (x.val : ℤ) (2 ^ 64)
  have e2 := Int.emod_bmod n (2 ^ 64)
  rw [Nat.cast_pow, Nat.cast_ofNat] at e1 e2
  rw [← e1, h, e2]
  apply Int.bmod_eq_of_le <;> norm_num <;> omega

theorem val_add (a b : Limb) : ((a + b).val : ℤ) ≡ a.val + b.val [ZMOD 2 ^ 64] := by
  rw [Fin.val_add]; unfold Int.ModEq; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)

theorem val_mul (a b : Limb) : ((a * b).val : ℤ) ≡ a.val * b.val [ZMOD 2 ^ 64] := by
  rw [Fin.val_mul]; unfold Int.ModEq; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)

theorem val_sub (a b : Limb) : ((a - b).val : ℤ) ≡ a.val - b.val [ZMOD 2 ^ 64] := by
  rw [Fin.sub_def]
  unfold Int.ModEq
  simp only
  have := b.isLt
  push_cast
  omega

theorem val_shl (a : Limb) (k : ℕ) : ((a.shl k).val : ℤ) ≡ a.val * 2 ^ k [ZMOD 2 ^ 64] := by
  simp only [Limb.shl]; unfold Int.ModEq; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)

theorem sgn_cong (x : Limb) : (x.val : ℤ) ≡ x.sgn [ZMOD 2 ^ 64] := (sgn_modEq x).symm

theorem sgn_shl {x : Limb} {k : ℕ} (h : |x.sgn| * 2 ^ k ≤ 2 ^ 62) :
    (x.shl k).sgn = x.sgn * 2 ^ k := by
  apply sgn_eq ((val_shl x k).trans ((sgn_cong x).mul_right _))
  · have := neg_abs_le x.sgn
    have : (0 : ℤ) < 2 ^ k := by positivity
    nlinarith
  · have := le_abs_self x.sgn
    have : (0 : ℤ) < 2 ^ k := by positivity
    nlinarith

theorem sgn_neg {x : Limb} (h : |x.sgn| ≤ 2 ^ 62) : (0 - x).sgn = -x.sgn := by
  apply sgn_eq ((val_sub 0 x).trans ?_)
  · have := le_abs_self x.sgn; linarith
  · have := neg_abs_le x.sgn; linarith
  · simpa using (sgn_cong x).neg

theorem sgn_add_mul {q u w : Limb} (h : |q.sgn| + |u.sgn| * (w.val : ℤ) ≤ 2 ^ 62) :
    (q + u * w).sgn = q.sgn + u.sgn * (w.val : ℤ) := by
  have hw : (0 : ℤ) ≤ w.val := by positivity
  apply sgn_eq ((val_add q (u * w)).trans
    ((sgn_cong q).add ((val_mul u w).trans ((sgn_cong u).mul_right _))))
  · have := neg_abs_le q.sgn; have := neg_abs_le u.sgn
    nlinarith [abs_nonneg u.sgn]
  · have := le_abs_self q.sgn; have := le_abs_self u.sgn
    nlinarith [abs_nonneg u.sgn]

/-! ## The mask and the multiple -/

theorem Limb.val_land (x y : Limb) : (x &&& y).val = x.val &&& y.val := by
  obtain ⟨x, hx⟩ := x; obtain ⟨y, hy⟩ := y
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hx)

theorem land_four (x : ℕ) : x &&& 4 = x % 8 &&& 4 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, show (8 : ℕ) = 2 ^ 3 by rfl, Nat.testBit_mod_two_pow,
    show (4 : ℕ) = 2 ^ 2 by rfl, Nat.testBit_two_pow]
  by_cases hi : i = 2
  · subst hi; simp
  · simp [show (2 = i) = False from propext ⟨fun h => hi h.symm, False.elim⟩]

/-- The inverse of an odd `f` modulo `16` that `cancel` uses for `eta ≥ 0`. -/
theorem inv16 (f : ℕ) (hf : f % 2 = 1) :
    16 ∣ ((f * (f + 2 * ((f + 1) % 2 ^ 64 &&& 4)) : ℕ) : ℤ) - 1 := by
  have ht : (f + 1) % 2 ^ 64 &&& 4 = ((f % 16 + 1) % 8) &&& 4 := by
    rw [land_four, Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 2 ^ 64)]
    congr 1; omega
  have key : ∀ j < 16, j % 2 = 1 → (j * (j + 2 * ((j + 1) % 8 &&& 4))) % 16 = 1 := by decide
  have h1 := key (f % 16) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [ht]
  generalize (f % 16 + 1) % 8 &&& 4 = t at h1
  have hm : f * (f + 2 * t) ≡ f % 16 * (f % 16 + 2 * t) [MOD 16] :=
    (Nat.mod_modEq f 16).symm.mul ((Nat.mod_modEq f 16).symm.add_right _)
  have h2 : (1 : ℤ) ≡ ((f * (f + 2 * t) : ℕ) : ℤ) [ZMOD 16] := by
    have : f * (f + 2 * t) % 16 = 1 := by unfold Nat.ModEq at hm; rw [hm]; exact h1
    unfold Int.ModEq
    exact_mod_cast this.symm
  exact h2.dvd

/-- For odd `f`, `(f ^ 2 - 1) ^ 2` is a multiple of `64`, so `f (f ^ 2 - 2)` is minus an inverse
of `f` modulo `64`: what `cancel` uses for `eta < 0`. -/
theorem inv64 (f g : ℤ) (hf : f % 2 = 1) : 64 ∣ g + f * (f * g * (f * f - 2)) := by
  have h8 : 8 ∣ f * f - 1 := by
    have : f % 8 = 1 ∨ f % 8 = 3 ∨ f % 8 = 5 ∨ f % 8 = 7 := by omega
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.mul_emod]
    rcases this with h | h | h | h <;> rw [h] <;> norm_num
  obtain ⟨k, hk⟩ := h8
  exact ⟨g * k * k, by linear_combination g * (f * f - 1 + 8 * k) * hk⟩

/-- The mask of `cancel`, for `left ≥ 1` and `eta ≠ -1`: the low `c` bits, for some
`1 ≤ c ≤ min left b`. -/
theorem mask_spec (s : DS) (b : ℕ) (hb1 : 1 ≤ b) (hb : b ≤ 6) (hl1 : 1 ≤ s.left.val) (hl : s.left.val ≤ 62)
    (he1 : -2 ^ 63 ≤ s.eta) (he2 : s.eta < 2 ^ 63) (he : s.eta ≠ -1) :
    ∃ c, 1 ≤ c ∧ c ≤ s.left.val ∧ c ≤ b ∧
      (s.mask ⟨2 ^ b - 1, by have : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hb; omega⟩).val =
        2 ^ c - 1 := by
  unfold DS.mask
  extract_lets room limit
  have hroom : 1 ≤ room.val := by
    simp only [room, Limb.ofInt]
    have := Int.bmod_emod (x := s.eta + 1) (m := 2 ^ 64)
    rw [Nat.cast_pow, Nat.cast_ofNat] at this
    rw [this]
    omega
  have hlim1 : 1 ≤ limit.val := by simp only [limit]; split <;> omega
  have hlim2 : limit.val ≤ s.left.val := by simp only [limit]; split <;> omega
  clear_value room limit
  have h64 : (64 - limit).val = 64 - limit.val := by
    rw [Fin.sub_def]; simp only; show (2 ^ 64 - limit.val + 64) % 2 ^ 64 = 64 - limit.val; omega
  have hshr : (Limb.shr 18446744073709551615 (64 - limit).val).val = 2 ^ limit.val - 1 := by
    simp only [Limb.shr, h64]
    show 18446744073709551615 / 2 ^ (64 - limit.val) = _
    generalize limit.val = L at hlim1 hlim2 ⊢
    have hp : 2 ^ 64 = 2 ^ L * 2 ^ (64 - L) := by rw [← pow_add]; congr 1; omega
    have h1 : 1 ≤ 2 ^ (64 - L) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, ← hp]; norm_num; omega
    · rw [Nat.sub_add_cancel h2, ← hp]; norm_num
  refine ⟨min limit.val b, by omega, by omega, by omega, ?_⟩
  rw [Limb.val_land, hshr]
  show (2 ^ limit.val - 1) &&& (2 ^ b - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.le_total limit.val b with h | h
  · rw [Nat.min_eq_left h, Nat.mod_eq_of_lt]
    have : 2 ^ limit.val ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
    have : 1 ≤ 2 ^ limit.val := Nat.one_le_two_pow
    omega
  · rw [Nat.min_eq_right h]
    obtain ⟨d, hd⟩ : ∃ d, limit.val = b + d := ⟨limit.val - b, by omega⟩
    rw [hd, pow_add]
    have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [show 2 ^ b * 2 ^ d - 1 = (2 ^ b - 1) + 2 ^ b * (2 ^ d - 1) by
      zify [hb1, hd1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ b * 2 ^ d ≠ 0)]; ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ## The invariant -/

section
variable (f0 g0 : Limb)

/-- The invariant at the entry of the loop: `i = 62 - left` divsteps done, the first row bounded
by `2 ^ i`, the second by `2 ^ (i + c)` with `2 ^ c ∣ g`, and the rows mapping `(f0, g0)` to
`2 ^ i (f, g)` modulo `2 ^ 64`. -/
structure DS.Inv (s : DS) (c : ℕ) : Prop where
  left_pos : 1 ≤ s.left.val
  left_le : s.left.val ≤ 62
  c_le : c ≤ s.left.val
  dvd : 2 ^ c ∣ s.g.val
  row1 : |s.u.sgn| + |s.v.sgn| ≤ 2 ^ (62 - s.left.val)
  row2 : |s.q.sgn| + |s.r.sgn| ≤ 2 ^ (62 - s.left.val + c)
  odd : s.f.val % 2 = 1
  cong1 : s.u.sgn * f0.val + s.v.sgn * g0.val ≡ 2 ^ (62 - s.left.val) * s.f.val [ZMOD 2 ^ 64]
  cong2 : s.q.sgn * f0.val + s.r.sgn * g0.val ≡ 2 ^ (62 - s.left.val) * s.g.val [ZMOD 2 ^ 64]
  det : s.u.sgn * s.r.sgn - s.v.sgn * s.q.sgn = 2 ^ (62 - s.left.val)
  eta : s.eta.bmod (2 ^ 64) = s.eta

/-- The state before `cancel`: divsteps left, both rows bounded by `2 ^ i`, and `eta ≠ -1`. -/
structure DS.Pre (s : DS) : Prop where
  left1 : 1 ≤ s.left.val
  left_le : s.left.val ≤ 62
  row1 : |s.u.sgn| + |s.v.sgn| ≤ 2 ^ (62 - s.left.val)
  row2 : |s.q.sgn| + |s.r.sgn| ≤ 2 ^ (62 - s.left.val)
  odd : s.f.val % 2 = 1
  cong1 : s.u.sgn * f0.val + s.v.sgn * g0.val ≡ 2 ^ (62 - s.left.val) * s.f.val [ZMOD 2 ^ 64]
  cong2 : s.q.sgn * f0.val + s.r.sgn * g0.val ≡ 2 ^ (62 - s.left.val) * s.g.val [ZMOD 2 ^ 64]
  det : s.u.sgn * s.r.sgn - s.v.sgn * s.q.sgn = 2 ^ (62 - s.left.val)
  eta : s.eta.bmod (2 ^ 64) = s.eta
  eta_ne : s.eta ≠ -1

variable {f0 g0}

theorem abs_le_of_sum {a b B : ℤ} (h : |a| + |b| ≤ B) : |a| ≤ B ∧ |b| ≤ B :=
  ⟨by linarith [abs_nonneg b], by linarith [abs_nonneg a]⟩

/-- Adding `w < 2 ^ c` times `f` to `g`, and the first row to the second as often, when that
clears `c` low bits of `g`. -/
theorem cancel_core {s : DS} (hs : s.Pre f0 g0) (w : Limb) (c : ℕ) (hcl : c ≤ s.left.val)
    (hw : w.val < 2 ^ c) (hdvd : 2 ^ c ∣ (s.g + s.f * w).val) :
    ({ s with g := s.g + s.f * w, q := s.q + s.u * w, r := s.r + s.v * w } : DS).Inv f0 g0 c := by
  have hi : 62 - s.left.val + c ≤ 62 := by have := hs.left_le; omega
  have hP : (2 : ℤ) ^ (62 - s.left.val + c) ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) hi
  have hw' : (w.val : ℤ) ≤ 2 ^ c - 1 := by
    have : ((w.val + 1 : ℕ) : ℤ) ≤ ((2 ^ c : ℕ) : ℤ) := by exact_mod_cast hw
    push_cast at this; linarith
  have hw0 : (0 : ℤ) ≤ w.val := by positivity
  have hpow : (2 : ℤ) ^ (62 - s.left.val + c) = 2 ^ (62 - s.left.val) * 2 ^ c := pow_add _ _ _
  have hI : (0 : ℤ) ≤ 2 ^ (62 - s.left.val) := by positivity
  -- The new second row, exactly.
  have hu := abs_le_of_sum hs.row1
  have hbu : |s.u.sgn| * (w.val : ℤ) ≤ 2 ^ (62 - s.left.val) * (2 ^ c - 1) :=
    mul_le_mul hu.1 hw' hw0 hI
  have hbv : |s.v.sgn| * (w.val : ℤ) ≤ 2 ^ (62 - s.left.val) * (2 ^ c - 1) :=
    mul_le_mul hu.2 hw' hw0 hI
  have hq := abs_le_of_sum hs.row2
  have hq' : (s.q + s.u * w).sgn = s.q.sgn + s.u.sgn * w.val :=
    sgn_add_mul (by nlinarith)
  have hr' : (s.r + s.v * w).sgn = s.r.sgn + s.v.sgn * w.val :=
    sgn_add_mul (by nlinarith)
  refine ⟨hs.left1, hs.left_le, hcl, hdvd, hs.row1, ?_, hs.odd, hs.cong1, ?_, ?_, hs.eta⟩
  · simp only [hq', hr']
    calc |s.q.sgn + s.u.sgn * w.val| + |s.r.sgn + s.v.sgn * w.val|
        ≤ (|s.q.sgn| + |s.u.sgn| * w.val) + (|s.r.sgn| + |s.v.sgn| * w.val) := by
          apply add_le_add
          · exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_of_nonneg hw0]))
          · exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_of_nonneg hw0]))
      _ ≤ 2 ^ (62 - s.left.val + c) := by
          rw [hpow]
          have : (|s.u.sgn| + |s.v.sgn|) * (w.val : ℤ) ≤ 2 ^ (62 - s.left.val) * (2 ^ c - 1) :=
            mul_le_mul hs.row1 hw' hw0 hI
          nlinarith [hs.row2]
  · simp only [hq', hr']
    have hg := (val_add s.g (s.f * w)).trans ((Int.ModEq.refl _).add (val_mul s.f w))
    calc (s.q.sgn + s.u.sgn * w.val) * f0.val + (s.r.sgn + s.v.sgn * w.val) * g0.val
        = (s.q.sgn * f0.val + s.r.sgn * g0.val) + w.val * (s.u.sgn * f0.val + s.v.sgn * g0.val) := by
          ring
      _ ≡ 2 ^ (62 - s.left.val) * s.g.val + w.val * (2 ^ (62 - s.left.val) * s.f.val)
          [ZMOD 2 ^ 64] := hs.cong2.add (hs.cong1.mul_left _)
      _ = 2 ^ (62 - s.left.val) * (s.g.val + s.f.val * w.val) := by ring
      _ ≡ 2 ^ (62 - s.left.val) * (s.g + s.f * w).val [ZMOD 2 ^ 64] := (hg.symm.mul_left _)
  · simp only [hq', hr']
    linear_combination hs.det

end

section
variable {f0 g0 : Limb}

theorem modEq_two_pow_of_le {a b : ℤ} {c d : ℕ} (h : a ≡ b [ZMOD 2 ^ d]) (hcd : c ≤ d) :
    a ≡ b [ZMOD 2 ^ c] :=
  Int.ModEq.of_dvd (pow_dvd_pow 2 hcd) h

theorem land_low (x : Limb) (c : ℕ) : x.val &&& (2 ^ c - 1) = x.val % 2 ^ c :=
  Nat.and_two_pow_sub_one_eq_mod _ _

theorem dvd_of_modEq {G P : ℤ} {c : ℕ} (h : G ≡ P [ZMOD 2 ^ c]) (hP : (2 : ℤ) ^ c ∣ P) :
    2 ^ c ∣ G := by
  have := h.dvd  -- 2^c ∣ P - G
  have : (2 : ℤ) ^ c ∣ P - (P - G) := dvd_sub hP this
  simpa using this

theorem cancel_63 {s : DS} (hs : s.Pre f0 g0) : ∃ c, 1 ≤ c ∧ (s.cancel 63).Inv f0 g0 c := by
  obtain ⟨c, hc1, hcl, hc6, hm⟩ := mask_spec s 6 (by decide) le_rfl hs.left1 hs.left_le
    (by have := (bmod_range s.eta).1; rw [hs.eta] at this; have := Int.le_bmod (x := s.eta)
          (m := 2 ^ 64) (by decide); rw [hs.eta] at this; simp only [Nat.reducePow] at this ⊢; omega)
    (by have := Int.bmod_lt (x := s.eta) (m := 2 ^ 64) (by decide); rw [hs.eta] at this
        simp only [Nat.reducePow] at this ⊢; omega) hs.eta_ne
  have hmult : s.mult 63 = s.f * s.g * (s.f * s.f - 2) &&& s.mask ⟨2 ^ 6 - 1, by decide⟩ := by
    simp only [DS.mult]; rfl
  set X := s.f * s.g * (s.f * s.f - 2)
  have hw : (s.mult 63).val = X.val % 2 ^ c := by
    rw [hmult, Limb.val_land, hm, land_low]
  refine ⟨c, hc1, cancel_core hs _ c hcl (by rw [hw]; exact Nat.mod_lt _ (by positivity)) ?_⟩
  have hX : (X.val : ℤ) ≡ s.f.val * s.g.val * (s.f.val * s.f.val - 2) [ZMOD 2 ^ 64] :=
    (val_mul _ _).trans (((val_mul _ _)).mul ((val_sub _ _).trans
      ((val_mul _ _).sub (Int.ModEq.refl _))))
  have hG : (((s.g + s.f * s.mult 63).val : ℕ) : ℤ) ≡
      s.g.val + s.f.val * (s.f.val * s.g.val * (s.f.val * s.f.val - 2)) [ZMOD 2 ^ c] := by
    refine modEq_two_pow_of_le ((val_add _ _).trans ((Int.ModEq.refl _).add (val_mul _ _)))
      (by omega) |>.trans ((Int.ModEq.refl _).add (Int.ModEq.mul_left _ ?_))
    rw [hw]
    push_cast
    exact (Int.mod_modEq _ _).trans (modEq_two_pow_of_le hX (by omega))
  have h64 := inv64 s.f.val s.g.val (by exact_mod_cast hs.odd)
  have := dvd_of_modEq hG (dvd_trans (pow_dvd_pow 2 hc6) (by norm_num at h64 ⊢; exact h64))
  exact_mod_cast this

theorem cancel_15 {s : DS} (hs : s.Pre f0 g0) : ∃ c, 1 ≤ c ∧ (s.cancel 15).Inv f0 g0 c := by
  obtain ⟨c, hc1, hcl, hc4, hm⟩ := mask_spec s 4 (by decide) (by decide) hs.left1 hs.left_le
    (by have := Int.le_bmod (x := s.eta) (m := 2 ^ 64) (by decide); rw [hs.eta] at this
        simp only [Nat.reducePow] at this ⊢; omega)
    (by have := Int.bmod_lt (x := s.eta) (m := 2 ^ 64) (by decide); rw [hs.eta] at this
        simp only [Nat.reducePow] at this ⊢; omega) hs.eta_ne
  have hmult : s.mult 15 = (0 - (s.f + Limb.shl ((s.f + 1) &&& 4) 1)) * s.g &&&
      s.mask ⟨2 ^ 4 - 1, by decide⟩ := by
    simp only [DS.mult, show ((15 : Limb) = 63) = False by decide, ite_false]; rfl
  set X := (0 - (s.f + Limb.shl ((s.f + 1) &&& 4) 1)) * s.g
  have hw : (s.mult 15).val = X.val % 2 ^ c := by
    rw [hmult, Limb.val_land, hm, land_low]
  refine ⟨c, hc1, cancel_core hs _ c hcl (by rw [hw]; exact Nat.mod_lt _ (by positivity)) ?_⟩
  set t := (s.f.val + 1) % 2 ^ 64 &&& 4
  have ht : (((s.f + 1) &&& 4).val : ℤ) = t := by
    rw [Limb.val_land, Fin.val_add]; rfl
  have hX : (X.val : ℤ) ≡ (0 - (s.f.val + t * 2)) * s.g.val [ZMOD 2 ^ 64] := by
    refine (val_mul _ _).trans (Int.ModEq.mul_right _ ((val_sub _ _).trans ?_))
    simp only [Fin.val_zero, Nat.cast_zero]
    refine Int.ModEq.sub (Int.ModEq.refl _) ((val_add _ _).trans (Int.ModEq.add_left _ ?_))
    rw [← ht]
    exact val_shl _ _
  have hG : (((s.g + s.f * s.mult 15).val : ℕ) : ℤ) ≡
      s.g.val + s.f.val * ((0 - (s.f.val + t * 2)) * s.g.val) [ZMOD 2 ^ c] := by
    refine modEq_two_pow_of_le ((val_add _ _).trans ((Int.ModEq.refl _).add (val_mul _ _)))
      (by omega) |>.trans ((Int.ModEq.refl _).add (Int.ModEq.mul_left _ ?_))
    rw [hw]
    push_cast
    exact (Int.mod_modEq _ _).trans (modEq_two_pow_of_le hX (by omega))
  have h16 := inv16 s.f.val hs.odd
  have hP : (2 : ℤ) ^ c ∣ s.g.val + s.f.val * ((0 - (s.f.val + t * 2)) * s.g.val) := by
    refine dvd_trans (pow_dvd_pow 2 hc4) ?_
    obtain ⟨k, hk⟩ := h16
    push_cast at hk
    exact ⟨-(s.g.val * k), by linear_combination (-(s.g.val : ℤ)) * hk⟩
  have := dvd_of_modEq hG hP
  exact_mod_cast this

end

/-! ## The loop -/

/-- What `divsteps` returns for `f0, g0`: the transition matrix. -/
structure TSpec (f0 g0 : Limb) (U V Q R : ℤ) : Prop where
  row1 : |U| + |V| ≤ 2 ^ 62
  row2 : |Q| + |R| ≤ 2 ^ 62
  cong1 : U * f0.val + V * g0.val ≡ 0 [ZMOD 2 ^ 62]
  cong2 : Q * f0.val + R * g0.val ≡ 0 [ZMOD 2 ^ 62]
  det : U * R - V * Q = 2 ^ 62
  odd1 : U * f0.val + V * g0.val ≡ 2 ^ 62 [ZMOD 2 ^ 63]
  even_u : 2 ∣ U
  even_v : 2 ∣ V

theorem bmod_ne_neg_one {x : ℤ} (h1 : 1 ≤ x) (h2 : x ≤ 2 ^ 63) : x.bmod (2 ^ 64) ≠ -1 := by
  intro h
  have := Int.bmod_emod (x := x) (m := 2 ^ 64)
  rw [h, Nat.cast_pow, Nat.cast_ofNat] at this
  omega

theorem eta_range {x : ℤ} (h : x.bmod (2 ^ 64) = x) : -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  have h1 := Int.le_bmod (x := x) (m := 2 ^ 64) (by decide)
  have h2 := Int.bmod_lt (x := x) (m := 2 ^ 64) (by decide)
  rw [h] at h1 h2
  simp only [Nat.reducePow] at h1 h2 ⊢
  constructor <;> omega

theorem run_spec (f0 g0 : Limb) : ∀ n (s : DS) c, s.Inv f0 g0 c → s.left.val - c ≤ n → ∀ bits,
    ∃ eta' U V Q R, s.run bits = pure (I eta', ⟨I U, I V, I Q, I R⟩) ∧
      eta'.bmod (2 ^ 64) = eta' ∧ TSpec f0 g0 U V Q R := by
  intro n
  induction n with
  | zero => ?_
  | succ m ih => ?_
  all_goals
    intro s c hs hn bits
    rw [b1_step s bits hs.eta]
    obtain ⟨hz1, hg, hodd, hcz⟩ := zeros_spec s hs.left_le
    have hcz := hcz c hs.c_le hs.dvd
    set z := s.zeros.val with hzdef
    have hleft : s.shift.left.val = s.left.val - z := by
      show (s.left - s.zeros).val = _
      rw [Fin.sub_def]; show (2 ^ 64 - s.zeros.val + s.left.val) % 2 ^ 64 = _
      have := s.left.isLt; omega
    have hi : 62 - s.shift.left.val = 62 - s.left.val + z := by rw [hleft]; have := hs.left_le; omega
    have hP : (2 : ℤ) ^ (62 - s.left.val + z) ≤ 2 ^ 62 :=
      pow_le_pow_right₀ (by norm_num) (by have := hs.left_le; omega)
    have hpow : (2 : ℤ) ^ (62 - s.left.val + z) = 2 ^ (62 - s.left.val) * 2 ^ z := pow_add _ _ _
    have h2z : (0 : ℤ) < 2 ^ z := by positivity
    have hu := abs_le_of_sum hs.row1
    have hsu : s.shift.u.sgn = s.u.sgn * 2 ^ z :=
      sgn_shl ((mul_le_mul_of_nonneg_right hu.1 h2z.le).trans (hpow.symm.le.trans hP))
    have hsv : s.shift.v.sgn = s.v.sgn * 2 ^ z :=
      sgn_shl ((mul_le_mul_of_nonneg_right hu.2 h2z.le).trans (hpow.symm.le.trans hP))
    have hsg : (s.shift.g.val : ℤ) * 2 ^ z = s.g.val := by
      show ((s.g.val / 2 ^ z : ℕ) : ℤ) * 2 ^ z = _
      have : s.g.val / 2 ^ z * 2 ^ z = s.g.val := by rw [Nat.mul_comm]; exact hg.symm
      exact_mod_cast this
    -- The state after the shift.
    have row1 : |s.shift.u.sgn| + |s.shift.v.sgn| ≤ 2 ^ (62 - s.shift.left.val) := by
      rw [hsu, hsv, hi, hpow, abs_mul, abs_mul, abs_of_pos h2z]
      nlinarith [hs.row1]
    have row2 : |s.shift.q.sgn| + |s.shift.r.sgn| ≤ 2 ^ (62 - s.shift.left.val) := by
      rw [hi]
      exact hs.row2.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have cong1 : s.shift.u.sgn * f0.val + s.shift.v.sgn * g0.val ≡
        2 ^ (62 - s.shift.left.val) * s.shift.f.val [ZMOD 2 ^ 64] := by
      rw [hsu, hsv, hi, hpow]
      have := hs.cong1.mul_right (2 ^ z)
      calc s.u.sgn * 2 ^ z * f0.val + s.v.sgn * 2 ^ z * g0.val
          = (s.u.sgn * f0.val + s.v.sgn * g0.val) * 2 ^ z := by ring
        _ ≡ 2 ^ (62 - s.left.val) * s.f.val * 2 ^ z [ZMOD 2 ^ 64] := this
        _ = 2 ^ (62 - s.left.val) * 2 ^ z * s.shift.f.val := by
          show _ = _ * (s.f.val : ℤ); ring
    have cong2 : s.shift.q.sgn * f0.val + s.shift.r.sgn * g0.val ≡
        2 ^ (62 - s.shift.left.val) * s.shift.g.val [ZMOD 2 ^ 64] := by
      rw [hi, hpow]
      calc s.shift.q.sgn * f0.val + s.shift.r.sgn * g0.val
          = s.q.sgn * f0.val + s.r.sgn * g0.val := rfl
        _ ≡ 2 ^ (62 - s.left.val) * s.g.val [ZMOD 2 ^ 64] := hs.cong2
        _ = 2 ^ (62 - s.left.val) * 2 ^ z * s.shift.g.val := by rw [← hsg]; ring
    have det : s.shift.u.sgn * s.shift.r.sgn - s.shift.v.sgn * s.shift.q.sgn =
        2 ^ (62 - s.shift.left.val) := by
      rw [hsu, hsv, hi, hpow]
      show s.u.sgn * 2 ^ z * s.r.sgn - s.v.sgn * 2 ^ z * s.q.sgn = _
      linear_combination (2 : ℤ) ^ z * hs.det
    have heta : s.shift.eta.bmod (2 ^ 64) = s.shift.eta := Int.bmod_bmod
    have hodd' : s.shift.left.val ≠ 0 → s.shift.g.val % 2 = 1 := fun h => hodd (by omega)
    split_ifs with h0 hneg
    · -- No divsteps left: the matrix.
      have h62 : 62 - s.shift.left.val = 62 := by rw [h0]; rfl
      rw [h62] at row1 row2 cong1 cong2 det
      have hz0 : 1 ≤ z := by have := hs.left_pos; omega
      have h2 : (2 : ℤ) ∣ 2 ^ z := dvd_pow_self 2 (by omega)
      refine ⟨_, _, _, _, _, rfl, heta, row1, row2, ?_, ?_, det, ?_, ?_, ?_⟩
      · exact (modEq_two_pow_of_le cong1 (by omega)).trans
          (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
      · exact (modEq_two_pow_of_le cong2 (by omega)).trans
          (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
      · refine (modEq_two_pow_of_le cong1 (by omega)).trans ?_
        obtain ⟨k, hk⟩ : ∃ k, (s.f.val : ℤ) = 2 * k + 1 := ⟨s.f.val / 2, by
          have := hs.odd; omega⟩
        rw [show s.shift.f = s.f from rfl, hk]
        exact Int.modEq_iff_dvd.mpr ⟨-k, by ring⟩
      · rw [hsu]; exact Dvd.dvd.mul_left h2 _
      · rw [hsv]; exact Dvd.dvd.mul_left h2 _
    all_goals
      have hl0 : s.shift.left.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hl1 : 1 ≤ s.shift.left.val := Nat.one_le_iff_ne_zero.mpr hl0
      have hll : s.shift.left.val ≤ 62 := by have := hs.left_le; omega
      have hI : (2 : ℤ) ^ (62 - s.shift.left.val) ≤ 2 ^ 62 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      first
      | (have hm : s.left.val - c ≤ 0 := hn
         omega)
      | skip
  · -- `eta < 0`: swap, then cancel up to six bits.
    have hu' := abs_le_of_sum row1
    have hpre : s.shift.swap.Pre f0 g0 := by
      have hnu : (0 - s.shift.u).sgn = -s.shift.u.sgn := sgn_neg (hu'.1.trans hI)
      have hnv : (0 - s.shift.v).sgn = -s.shift.v.sgn := sgn_neg (hu'.2.trans hI)
      have he := eta_range heta
      refine ⟨hl1, hll, row2, ?_, hodd' hl0, cong2, ?_, ?_, Int.bmod_bmod,
        bmod_ne_neg_one (by omega) (by omega)⟩
      · show |(0 - s.shift.u).sgn| + |(0 - s.shift.v).sgn| ≤ _
        rw [hnu, hnv, abs_neg, abs_neg]; exact row1
      · show (0 - s.shift.u).sgn * f0.val + (0 - s.shift.v).sgn * g0.val ≡
          2 ^ (62 - s.shift.left.val) * (0 - s.shift.f).val [ZMOD 2 ^ 64]
        rw [hnu, hnv]
        calc -s.shift.u.sgn * f0.val + -s.shift.v.sgn * g0.val
            = -(s.shift.u.sgn * f0.val + s.shift.v.sgn * g0.val) := by ring
          _ ≡ -(2 ^ (62 - s.shift.left.val) * s.shift.f.val) [ZMOD 2 ^ 64] := cong1.neg
          _ = 2 ^ (62 - s.shift.left.val) * (0 - (s.shift.f.val : ℤ)) := by ring
          _ ≡ 2 ^ (62 - s.shift.left.val) * (0 - s.shift.f).val [ZMOD 2 ^ 64] :=
            Int.ModEq.mul_left _ (by simpa using (val_sub 0 s.shift.f).symm)
      · show s.shift.q.sgn * (0 - s.shift.v).sgn - s.shift.r.sgn * (0 - s.shift.u).sgn =
          2 ^ (62 - s.shift.left.val)
        rw [hnu, hnv]
        linear_combination det
    obtain ⟨c', hc', hinv⟩ := cancel_63 hpre
    exact ih _ c' hinv (by show s.shift.left.val - c' ≤ m; omega) _
  · -- `eta ≥ 0`: cancel up to four bits.
    have hpre : s.shift.Pre f0 g0 :=
      ⟨hl1, hll, row1, row2, hs.odd, cong1, cong2, det, heta, by omega⟩
    obtain ⟨c', hc', hinv⟩ := cancel_15 hpre
    exact ih _ c' hinv (by show s.shift.left.val - c' ≤ m; omega) _

theorem sgn_one : (1 : Limb).sgn = 1 := by decide
theorem sgn_zero : (0 : Limb).sgn = 0 := by decide

open Precompiles.Exported.Shared in
/-- `divsteps` on an odd `f0` returns, with an `eta` for the next call, the transition matrix
of 62 divsteps. -/
theorem divsteps_spec (eta : ℤ) (he : eta.bmod (2 ^ 64) = eta) (f0 g0 : Limb)
    (hf : f0.val % 2 = 1) :
    ∃ eta' U V Q R, divsteps (I eta) f0.w g0.w = pure (I eta', ⟨I U, I V, I Q, I R⟩) ∧
      eta'.bmod (2 ^ 64) = eta' ∧ TSpec f0 g0 U V Q R := by
  have hinv : (⟨1, 0, 0, 1, f0, g0, 62, eta⟩ : DS).Inv f0 g0 0 := by
    have h62 : (62 : Limb).val = 62 := rfl
    refine ⟨by simp only [h62]; omega, by simp only [h62]; omega, by omega, by simp, ?_, ?_, hf, ?_, ?_, ?_, he⟩ <;>
      simp only [sgn_one, sgn_zero, h62] <;> norm_num
  exact run_spec f0 g0 62 _ 0 hinv (by show (62 : Limb).val - 0 ≤ 62; decide) default

end FeProofs.Precompiles
