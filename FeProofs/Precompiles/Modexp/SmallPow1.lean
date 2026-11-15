import FeProofs.Precompiles.Modexp.SmallPowMem

/-!
# Modexp: the loops of `small_power<1>`

The exported `small_power_1` runs five loops over 22 registers (`r0` … `r21`); most are
temporaries that a loop writes and nothing after it reads.  Each lemma here takes one loop from
its start to its exit, as an equation of model computations, for any values of the registers it
does not read:

- `newton_loop1`: `small_power_1.b1`, the Newton steps of the inverse (`newton`);
- `table_loop1`: `small_power_1.b1.b8`, the table of odd powers (`tbl`), held in the vector `tabV`;
- `square_loop1`: `small_power_1.b1.b12.b18`, the squarings before a window (`ssq`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

theorem has05_eq (r : Lib.Range_Known_0_Known_5) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_0_5 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 5)) := by
  simp only [Lib.Range_has_0_5, range_has_eq (lo := 0) (hi := 5) hk (by norm_num) (by norm_num),
    bind_pure]

theorem has1_eq (N : ℕ) (hN : N < 2 ^ 256) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_1 ⟨(), UInt256.ofNat N⟩ (UInt256.ofNat k) = pure (decide (1 ≤ k ∧ k < N)) := by
  simp only [Lib.Range_has_1, range_has_eq (lo := 1) hk (by norm_num) hN, bind_pure]

theorem two_w : UInt256.ofNat 2 = Limb.w ⟨2, by norm_num⟩ := rfl

/-- The loop of Newton steps, from step `i`. -/
theorem newton_loop1 (x : Exponent) (base value : Lib.MemArray_u64) (a : Limb) r1 r2 r3 r4 r5 r6
    r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 :
    ∀ n i (y : Limb), i + n = 5 →
      small_power_1.b1 x base value a.w y.w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
          r17 r18 r19 r20 r21 (UInt256.ofNat i) =
        small_power_1.b1 x base value a.w ((newton a)^[n] y).w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
          r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 (UInt256.ofNat 5)
  | 0, i, y, h => by rw [show i = 5 by omega]; rfl
  | n + 1, i, y, h => by
    rw [small_power_1.b1.eq_1]
    simp only [has05_eq r8 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 5) = True from
      eq_true (by omega), decide_true, if_true, Lib.Range_at_0_5, Lib.Range_next_0_5,
      next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, mulW64_eq, two_w, subW64_eq]
    rw [Function.iterate_succ_apply]
    exact newton_loop1 x base value a r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
      r18 r19 r20 r21 n (i + 1) _ (by omega)

/-- The squarings before a window, from bit `k` of `[i, j)`; the temporaries `r16`, `r17` end as
    the loop leaves them. -/
theorem square_loop1 (x : Exponent) (wd : UInt256) (wn : Window) (m : L4) (inv : Limb) (i j : ℕ)
    (hj : j < 2 ^ 256) r0 r2 r3 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r18 r19 r20 r21 :
    ∀ n k (p : L4) (r16 r17 : Wide), k + n = j → i ≤ k →
      ∃ r16' r17', small_power_1.b1.b12.b18 x wd wn r0 ⟨toW m, inv.w⟩ r2 r3 (toW p) r5 r6 r7 r8 r9
          r10 r11 r12 r13 r14 ⟨UInt256.ofNat i, UInt256.ofNat j⟩ r16 r17 r18 r19 r20 r21
          (UInt256.ofNat k) =
        small_power_1.b1.b12.b17 x wd wn r0 ⟨toW m, inv.w⟩ r2 r3 (toW ((ssq 1 m inv)^[n] p)) r5 r6
          r7 r8 r9 r10 r11 r12 r13 r14 ⟨UInt256.ofNat i, UInt256.ofNat j⟩ r16' r17' r18 r19 r20 r21
  | 0, k, p, r16, r17, h, hik => by
    refine ⟨r16, r17, ?_⟩
    rw [small_power_1.b1.b12.b18.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) hj (show k < 2 ^ 256 by omega),
      show (i ≤ k ∧ k < j) = False from eq_false (by omega), decide_false, Bool.false_eq_true,
      if_false, pure_bind]
    rfl
  | n + 1, k, p, r16, r17, h, hik => by
    rw [small_power_1.b1.b12.b18.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) hj (show k < 2 ^ 256 by omega),
      show (i ≤ k ∧ k < j) = True from eq_true (by omega), decide_true, if_true,
      Lib.Range_Unknown_Unknown_at, Lib.Range_Unknown_Unknown_next,
      next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind, smul1_eq]
    rw [Function.iterate_succ_apply]
    exact square_loop1 x wd wn m inv i j hj r0 r2 r3 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r18 r19
      r20 r21 n (k + 1) (ssq 1 m inv p) _ _ (by omega) (by omega)

/-! ## The table -/

/-- An empty entry. -/
def W0 : Wide := ⟨UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩

/-- The table with its first `c` entries filled. -/
def tabV (t : ℕ → L4) (c : ℕ) : Vector Wide 64 :=
  Vector.ofFn fun j => if j.val < c then toW (t j.val) else W0

theorem tabV_get (t : ℕ → L4) {c k : ℕ} (hk : k < c) (h64 : k < 64) : (tabV t c)[k]! = toW (t k) := by
  simp [tabV, getElem!_pos, h64, hk]

theorem tabV_set (t : ℕ → L4) (c : ℕ) : (tabV t c).set! c (toW (t c)) = tabV t (c + 1) := by
  rw [tabV, set!_ofFn', tabV]
  congr 1
  funext j
  by_cases h : j.val = c
  · simp [h]
  · by_cases h' : j.val < c
    · simp [h, h', show j.val < c + 1 by omega]
    · simp [h, h', show ¬ j.val < c + 1 by omega]

theorem tabV_zero (t : ℕ → L4) : Vector.replicate 64 W0 = tabV t 0 := by
  apply Vector.ext; intro j hj; simp [tabV]

/-- The loop filling the table, from entry `k` to `E`; `r14` ends as the loop leaves it. -/
theorem table_loop1 (K : UInt256 → Small_1 → Vector Wide 64 → Wide → Wide → UInt256 → Bool →
      Lib.MemArray_u64 → Lib.Range_Known_0_Known_5 → Wide → Wide → Wide → Wide →
      Lib.Range_Known_1_Unknown → Wide → Lib.Range_Unknown_Unknown → Wide → Wide → Wide → Wide →
      Wide → Wide → FeM Option_MemArray_u64)
    (m : L4) (inv : Limb) (t0 : L4) (E : ℕ) (hE : E ≤ 64) r0 r4 r5 r6 r7 r8 r9 r10 r11 r12 r15
    r16 r17 r18 r19 r20 r21 :
    ∀ n k (r14 : Wide), k + n = E → 1 ≤ k →
      ∃ r14', small_power_1.b1.b8 K r0 ⟨toW m, inv.w⟩ (tabV (tbl 1 m inv t0) k)
          (toW (smul 1 m inv t0 t0)) r4 r5 r6 r7 r8 r9 r10 r11 r12 ⟨(), UInt256.ofNat E⟩ r14 r15 r16
          r17 r18 r19 r20 r21 (UInt256.ofNat k) =
        K r0 ⟨toW m, inv.w⟩ (tabV (tbl 1 m inv t0) E) (toW (smul 1 m inv t0 t0)) r4 r5 r6 r7 r8 r9
          r10 r11 r12 ⟨(), UInt256.ofNat E⟩ r14' r15 r16 r17 r18 r19 r20 r21
  | 0, k, r14, h, hk => by
    refine ⟨r14, ?_⟩
    rw [small_power_1.b1.b8.eq_1]
    simp only [has1_eq E (by omega) (show k < 2 ^ 256 by omega),
      show (1 ≤ k ∧ k < E) = False from eq_false (by omega), decide_false, Bool.false_eq_true,
      if_false, pure_bind]
    rw [show k = E by omega]
  | n + 1, k, r14, h, hk => by
    rw [small_power_1.b1.b8.eq_1]
    simp only [has1_eq E (by omega) (show k < 2 ^ 256 by omega),
      show (1 ≤ k ∧ k < E) = True from eq_true (by omega), decide_true, if_true, Lib.Range_at_1,
      Lib.Range_next_1, next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind,
      sub_lit (show k < 2 ^ 256 by omega) hk, checkIndex_ok (show k - 1 < 64 by omega) (by norm_num),
      checkIndex_ok (show k < 64 by omega) (by norm_num), toNat_lit (show k - 1 < 2 ^ 256 by omega),
      toNat_lit (show k < 2 ^ 256 by omega), tabV_get _ (show k - 1 < k by omega) (by omega),
      smul1_eq]
    rw [show smul 1 m inv (tbl 1 m inv t0 (k - 1)) (smul 1 m inv t0 t0) = tbl 1 m inv t0 k by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl, tabV_set]
    exact table_loop1 K m inv t0 E hE r0 r4 r5 r6 r7 r8 r9 r10 r11 r12 r15 r16 r17 r18 r19 r20
      r21 n (k + 1) _ (by omega) (by omega)

end FeProofs.Modexp
