import FeProofs.Precompiles.Inverse.DivstepsSpec

/-!
# Precompiles: `update_fg`

`update_fg` multiplies `(f, g)`, each five signed 62-bit limbs, by the transition matrix and
divides by `2 ^ 62`, with one `i128` carry chain per row.  `fg_row` is one row on integers:
with limbs and matrix entries below `2 ^ 62`, no `i128` operation wraps, and the five limbs out
are the chain's remainders and its last quotient (`update_fg_eq`).  When the row's combination
`u f + v g` is a multiple of `2 ^ 62`, the limbs out denote `(u f + v g) / 2 ^ 62`
(`fgRow_value`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

/-! ## `i128` words that do not wrap -/

section
variable {x y : ℤ}

theorem range_of_abs (h : |x| ≤ 2 ^ 126) : -2 ^ 255 ≤ x ∧ x < 2 ^ 255 := by
  rw [abs_le] at h; constructor <;> linarith

theorem bmod128_of_abs (h : |x| ≤ 2 ^ 126) : x.bmod (2 ^ 128) = x := by
  rw [abs_le] at h
  apply Int.bmod_eq_of_le <;> norm_num <;> linarith

theorem mulW128 (hx : |x| ≤ 2 ^ 126) (hy : |y| ≤ 2 ^ 126) (h : |x * y| ≤ 2 ^ 126) :
    IntTy.mulW (.i 128) (I x) (I y) = I (x * y) := by
  rw [mulW_i 128 (by decide) (range_of_abs hx).1 (range_of_abs hx).2 (range_of_abs hy).1
    (range_of_abs hy).2, bmod128_of_abs h]

theorem addW128 (hx : |x| ≤ 2 ^ 126) (hy : |y| ≤ 2 ^ 126) (h : |x + y| ≤ 2 ^ 126) :
    IntTy.addW (.i 128) (I x) (I y) = I (x + y) := by
  rw [addW_i 128 (by decide) (range_of_abs hx).1 (range_of_abs hx).2 (range_of_abs hy).1
    (range_of_abs hy).2, bmod128_of_abs h]

theorem abs_div62 (h : |x| ≤ 2 ^ 126) : |x / 2 ^ 62| ≤ 2 ^ 64 := by
  rw [abs_le] at h ⊢
  constructor
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) h.1
    have e : (-2 ^ 126 : ℤ) / 2 ^ 62 = -2 ^ 64 := by norm_num
    linarith
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) h.2
    have e : (2 ^ 126 : ℤ) / 2 ^ 62 = 2 ^ 64 := by norm_num
    linarith

theorem shr128 (h : |x| ≤ 2 ^ 126) :
    IntTy.shr (.i 128) (I x) (UInt256.ofNat 62) = I (x / 2 ^ 62) := by
  rw [shr_i 128 (by decide) (range_of_abs h).1 (range_of_abs h).2 (by decide),
    bmod128_of_abs ((abs_div62 h).trans (by norm_num))]

/-- The low 62 bits of an `i128`, through its `i64` truncation. -/
theorem low62 (x : ℤ) :
    I (((I x).toNat : ℤ).bmod (2 ^ 64)) &&& UInt256.ofNat 4611686018427387903 = I (x % 2 ^ 62) := by
  rw [I_land_M62]
  apply congrArg I
  have h1 := Int.bmod_emod (x := ((I x).toNat : ℤ)) (m := 2 ^ 64)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h1
  rw [← Int.emod_emod_of_dvd _ (show (2 : ℤ) ^ 62 ∣ 2 ^ 64 by norm_num), h1,
    Int.emod_emod_of_dvd _ (show (2 : ℤ) ^ 62 ∣ 2 ^ 64 by norm_num), I_toNat_cast,
    Int.emod_emod_of_dvd _ (show (2 : ℤ) ^ 62 ∣ 2 ^ 256 by norm_num)]

/-- An `i128` that fits `i64`, through its truncation. -/
theorem top64 (h : |x| ≤ 2 ^ 62) : I (((I x).toNat : ℤ).bmod (2 ^ 64)) = I x := by
  apply congrArg I
  rw [← Int.emod_bmod, I_toNat_cast]
  rw [show ((2 ^ 64 : ℕ) : ℤ) = 2 ^ 64 by norm_num,
    Int.emod_emod_of_dvd _ (show (2 : ℤ) ^ 64 ∣ 2 ^ 256 by norm_num)]
  have e := Int.emod_bmod x (2 ^ 64)
  rw [Nat.cast_pow, Nat.cast_ofNat] at e
  rw [e]
  rw [abs_le] at h
  apply Int.bmod_eq_of_le <;> norm_num <;> linarith

end

/-! ## One row -/

/-- The product of one matrix row with a limb of `f` and of `g`. -/
abbrev lc (U V x y : ℤ) : ℤ := U * x + V * y

/-- The carries of one row of `update_fg`. -/
def fgC (U V : ℤ) (a b : ℕ → ℤ) : ℕ → ℤ
  | 0 => lc U V (a 0) (b 0)
  | k + 1 => fgC U V a b k / 2 ^ 62 + lc U V (a (k + 1)) (b (k + 1))

theorem abs_lc {U V x y : ℤ} (hU : |U| ≤ 2 ^ 62) (hV : |V| ≤ 2 ^ 62) (hx : |x| ≤ 2 ^ 62)
    (hy : |y| ≤ 2 ^ 62) : |U * x| ≤ 2 ^ 124 ∧ |V * y| ≤ 2 ^ 124 ∧ |lc U V x y| ≤ 2 ^ 125 := by
  have h1 : |U * x| ≤ 2 ^ 124 := by
    rw [abs_mul]; calc |U| * |x| ≤ 2 ^ 62 * 2 ^ 62 := mul_le_mul hU hx (abs_nonneg _) (by positivity)
      _ = 2 ^ 124 := by norm_num
  have h2 : |V * y| ≤ 2 ^ 124 := by
    rw [abs_mul]; calc |V| * |y| ≤ 2 ^ 62 * 2 ^ 62 := mul_le_mul hV hy (abs_nonneg _) (by positivity)
      _ = 2 ^ 124 := by norm_num
  exact ⟨h1, h2, (abs_add_le _ _).trans (by linarith)⟩

theorem abs_fgC {U V : ℤ} {a b : ℕ → ℤ} (hU : |U| ≤ 2 ^ 62) (hV : |V| ≤ 2 ^ 62)
    (ha : ∀ i, |a i| ≤ 2 ^ 62) (hb : ∀ i, |b i| ≤ 2 ^ 62) : ∀ k, |fgC U V a b k| ≤ 2 ^ 126
  | 0 => (abs_lc hU hV (ha 0) (hb 0)).2.2.trans (by norm_num)
  | k + 1 => by
    have := abs_div62 (abs_fgC hU hV ha hb k)
    have := (abs_lc hU hV (ha (k + 1)) (hb (k + 1))).2.2
    exact (abs_add_le _ _).trans (by linarith)

theorem abs_le126 {x : ℤ} (h : |x| ≤ 2 ^ 62) : |x| ≤ 2 ^ 126 := h.trans (by norm_num)

theorem fg_first {U V : ℤ} (hU : |U| ≤ 2 ^ 62) (hV : |V| ≤ 2 ^ 62) (x y : ℤ)
    (hx : |x| ≤ 2 ^ 62) (hy : |y| ≤ 2 ^ 62) :
    IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I U) (I x)) (IntTy.mulW (.i 128) (I V) (I y)) =
      I (lc U V x y) := by
  obtain ⟨h1, h2, h3⟩ := abs_lc hU hV hx hy
  rw [mulW128 (abs_le126 hU) (abs_le126 hx) (h1.trans (by norm_num)),
    mulW128 (abs_le126 hV) (abs_le126 hy) (h2.trans (by norm_num)),
    addW128 (h1.trans (by norm_num)) (h2.trans (by norm_num)) (h3.trans (by norm_num))]

section
variable {U V : ℤ} {a b : ℕ → ℤ} (hU : |U| ≤ 2 ^ 62) (hV : |V| ≤ 2 ^ 62)
  (ha : ∀ i, |a i| ≤ 2 ^ 62) (hb : ∀ i, |b i| ≤ 2 ^ 62)
include hU hV ha hb

theorem fg_step (k : ℕ) :
    IntTy.addW (.i 128) (IntTy.shr (.i 128) (I (fgC U V a b k)) (UInt256.ofNat 62))
        (IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I U) (I (a (k + 1))))
          (IntTy.mulW (.i 128) (I V) (I (b (k + 1))))) =
      I (fgC U V a b (k + 1)) := by
  have hC := abs_fgC hU hV ha hb k
  have hD := abs_div62 hC
  have hL := (abs_lc hU hV (ha (k + 1)) (hb (k + 1))).2.2
  rw [shr128 hC, fg_first hU hV _ _ (ha (k + 1)) (hb (k + 1)),
    addW128 (hD.trans (by norm_num)) (hL.trans (by norm_num)) (abs_fgC hU hV ha hb (k + 1))]
  rfl

theorem fg_last : IntTy.shr (.i 128) (I (fgC U V a b 4)) (UInt256.ofNat 62) =
    I (fgC U V a b 4 / 2 ^ 62) := shr128 (abs_fgC hU hV ha hb 4)

theorem fg_top (ha4 : |a 4| ≤ 2 ^ 20) (hb4 : |b 4| ≤ 2 ^ 20) :
    |fgC U V a b 4 / 2 ^ 62| ≤ 2 ^ 62 := by
  have hD := abs_div62 (abs_fgC hU hV ha hb 3)
  have h1 : |U * a 4| ≤ 2 ^ 82 := by
    rw [abs_mul]; calc |U| * |a 4| ≤ 2 ^ 62 * 2 ^ 20 := mul_le_mul hU ha4 (abs_nonneg _) (by positivity)
      _ = 2 ^ 82 := by norm_num
  have h2 : |V * b 4| ≤ 2 ^ 82 := by
    rw [abs_mul]; calc |V| * |b 4| ≤ 2 ^ 62 * 2 ^ 20 := mul_le_mul hV hb4 (abs_nonneg _) (by positivity)
      _ = 2 ^ 82 := by norm_num
  have hC : |fgC U V a b 4| ≤ 2 ^ 84 := by
    rw [show fgC U V a b 4 = fgC U V a b 3 / 2 ^ 62 + (U * a 4 + V * b 4) from fgC.eq_2 _ _ _ _ 3]
    have := abs_add_le (fgC U V a b 3 / 2 ^ 62) (U * a 4 + V * b 4)
    have := abs_add_le (U * a 4) (V * b 4)
    linarith
  rw [abs_le] at hC ⊢
  constructor
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) hC.1
    have e : (-2 ^ 84 : ℤ) / 2 ^ 62 = -2 ^ 22 := by norm_num
    linarith
  · have := Int.ediv_le_ediv (show (0 : ℤ) < 2 ^ 62 by norm_num) hC.2
    have e : (2 ^ 84 : ℤ) / 2 ^ 62 = 2 ^ 22 := by norm_num
    linarith

end

theorem idx_lits :
    (UInt256.ofNat 0).toNat = 0 ∧ (UInt256.ofNat 1).toNat = 1 ∧ (UInt256.ofNat 2).toNat = 2 ∧
    (UInt256.ofNat 3).toNat = 3 ∧ (UInt256.ofNat 4).toNat = 4 ∧ (UInt256.ofNat 5).toNat = 5 ∧
    UInt256.ofNat 1 + UInt256.ofNat 1 = UInt256.ofNat 2 ∧
    UInt256.ofNat 2 + UInt256.ofNat 1 = UInt256.ofNat 3 ∧
    UInt256.ofNat 3 + UInt256.ofNat 1 = UInt256.ofNat 4 ∧
    UInt256.ofNat 4 + UInt256.ofNat 1 = UInt256.ofNat 5 ∧
    UInt256.ofNat 1 - UInt256.ofNat 1 = UInt256.ofNat 0 ∧
    UInt256.ofNat 2 - UInt256.ofNat 1 = UInt256.ofNat 1 ∧
    UInt256.ofNat 3 - UInt256.ofNat 1 = UInt256.ofNat 2 ∧
    UInt256.ofNat 4 - UInt256.ofNat 1 = UInt256.ofNat 3 ∧
    UInt256.ofNat 5 - UInt256.ofNat 1 = UInt256.ofNat 4 := by decide

theorem vget5 {α : Type} [Inhabited α] (x0 x1 x2 x3 x4 : α) :
    #v[x0, x1, x2, x3, x4][0]! = x0 ∧ #v[x0, x1, x2, x3, x4][1]! = x1 ∧
    #v[x0, x1, x2, x3, x4][2]! = x2 ∧ #v[x0, x1, x2, x3, x4][3]! = x3 ∧
    #v[x0, x1, x2, x3, x4][4]! = x4 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lt5 : (0 : ℕ) < 5 ∧ (1 : ℕ) < 5 ∧ (2 : ℕ) < 5 ∧ (3 : ℕ) < 5 ∧ (4 : ℕ) < 5 ∧
    ((5 : ℕ) < 5) = False := by decide

theorem M62_SIGNED_eq : M62_SIGNED = pure (UInt256.ofNat 4611686018427387903) := rfl

/-- `update_fg` on limbs below `2 ^ 62` (the top ones below `2 ^ 20`), for a matrix with entries
below `2 ^ 62`: each row's carries' remainders, then its last quotient. -/
theorem update_fg_eq {U V Q R : ℤ} {a b : ℕ → ℤ} (hU : |U| ≤ 2 ^ 62) (hV : |V| ≤ 2 ^ 62)
    (hQ : |Q| ≤ 2 ^ 62) (hR : |R| ≤ 2 ^ 62) (ha : ∀ i, |a i| ≤ 2 ^ 62)
    (hb : ∀ i, |b i| ≤ 2 ^ 62) (ha4 : |a 4| ≤ 2 ^ 20) (hb4 : |b 4| ≤ 2 ^ 20) :
    update_fg_5 #v[I (a 0), I (a 1), I (a 2), I (a 3), I (a 4)]
        #v[I (b 0), I (b 1), I (b 2), I (b 3), I (b 4)] ⟨I U, I V, I Q, I R⟩ =
      pure (#v[I (fgC U V a b 1 % 2 ^ 62), I (fgC U V a b 2 % 2 ^ 62),
          I (fgC U V a b 3 % 2 ^ 62), I (fgC U V a b 4 % 2 ^ 62), I (fgC U V a b 4 / 2 ^ 62)],
        #v[I (fgC Q R a b 1 % 2 ^ 62), I (fgC Q R a b 2 % 2 ^ 62),
          I (fgC Q R a b 3 % 2 ^ 62), I (fgC Q R a b 4 % 2 ^ 62), I (fgC Q R a b 4 / 2 ^ 62)]) := by
  have z1 : IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I U) (I (a 0)))
      (IntTy.mulW (.i 128) (I V) (I (b 0))) = I (fgC U V a b 0) := fg_first hU hV _ _ (ha 0) (hb 0)
  have z2 : IntTy.addW (.i 128) (IntTy.mulW (.i 128) (I Q) (I (a 0)))
      (IntTy.mulW (.i 128) (I R) (I (b 0))) = I (fgC Q R a b 0) := fg_first hQ hR _ _ (ha 0) (hb 0)
  simp only [update_fg_5, update_fg_5_k1, update_fg_5_k2, pure_bind, vget5, z1, z2,
    checkIndex, idx_lits, lt5, if_true]
  iterate 5
    rw [update_fg_5_k2.loop.eq_1]
    simp only [idx_lits, vget5, lt5, checkIndex, fg_step hU hV ha hb, fg_step hQ hR ha hb, downcast_truncate_i128_i64_eq,
      low62, pure_bind, M62_SIGNED_eq, decide_true, decide_false, if_true, if_false,
      Bool.false_eq_true, fg_last hU hV ha hb, fg_last hQ hR ha hb,
      top64 (fg_top hU hV ha hb ha4 hb4), top64 (fg_top hQ hR ha hb ha4 hb4)]
  rfl

/-- The integer five signed 62-bit limbs denote. -/
def val5 (a : ℕ → ℤ) : ℤ := a 0 + 2 ^ 62 * a 1 + 2 ^ 124 * a 2 + 2 ^ 186 * a 3 + 2 ^ 248 * a 4

/-- The limbs `update_fg` returns for one row. -/
def fgOut (U V : ℤ) (a b : ℕ → ℤ) : ℕ → ℤ
  | 0 => fgC U V a b 1 % 2 ^ 62
  | 1 => fgC U V a b 2 % 2 ^ 62
  | 2 => fgC U V a b 3 % 2 ^ 62
  | 3 => fgC U V a b 4 % 2 ^ 62
  | _ => fgC U V a b 4 / 2 ^ 62

/-- When the row's low combination is a multiple of `2 ^ 62`, the limbs out denote the row
times `(f, g)`, divided by `2 ^ 62`. -/
theorem fgOut_value (U V : ℤ) (a b : ℕ → ℤ) (h : 2 ^ 62 ∣ fgC U V a b 0) :
    2 ^ 62 * val5 (fgOut U V a b) = U * val5 a + V * val5 b := by
  obtain ⟨q0, hq0⟩ := h
  have e : ∀ k, fgC U V a b k = 2 ^ 62 * (fgC U V a b k / 2 ^ 62) + fgC U V a b k % 2 ^ 62 :=
    fun k => (Int.mul_ediv_add_emod _ _).symm
  have c1 : fgC U V a b 1 = fgC U V a b 0 / 2 ^ 62 + lc U V (a 1) (b 1) := rfl
  have c2 : fgC U V a b 2 = fgC U V a b 1 / 2 ^ 62 + lc U V (a 2) (b 2) := rfl
  have c3 : fgC U V a b 3 = fgC U V a b 2 / 2 ^ 62 + lc U V (a 3) (b 3) := rfl
  have c4 : fgC U V a b 4 = fgC U V a b 3 / 2 ^ 62 + lc U V (a 4) (b 4) := rfl
  have c0 : fgC U V a b 0 = lc U V (a 0) (b 0) := rfl
  have hd0 : fgC U V a b 0 / 2 ^ 62 = q0 := by rw [hq0]; simp
  simp only [val5, fgOut, lc] at *
  rw [hd0] at c1
  linear_combination -(2 : ℤ) ^ 62 * e 1 - 2 ^ 124 * e 2 - 2 ^ 186 * e 3 - 2 ^ 248 * e 4 +
    2 ^ 62 * c1 + 2 ^ 124 * c2 + 2 ^ 186 * c3 + 2 ^ 248 * c4 - hq0 + c0

theorem fgOut_low (U V : ℤ) (a b : ℕ → ℤ) {i : ℕ} (hi : i < 4) :
    0 ≤ fgOut U V a b i ∧ fgOut U V a b i < 2 ^ 62 := by
  have h := fun k => Int.emod_nonneg (fgC U V a b k) (show (2 : ℤ) ^ 62 ≠ 0 by norm_num)
  have h' := fun k => Int.emod_lt_of_pos (fgC U V a b k) (show (0 : ℤ) < 2 ^ 62 by norm_num)
  interval_cases i <;> exact ⟨h _, h' _⟩

end FeProofs.Precompiles
