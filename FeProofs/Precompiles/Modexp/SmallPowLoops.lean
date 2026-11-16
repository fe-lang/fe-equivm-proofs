import FeProofs.Precompiles.Modexp.SmallPowMem
import FeProofs.Precompiles.Modexp.Family

/-!
# Modexp: the loops of `small_power<L>`

The exported `small_power_L` runs five loops over 22 registers (`r0` … `r21`); most are
temporaries that a loop writes and nothing after it reads.  Each lemma here takes one loop from
its start to its exit, as an equation of model computations, for any values of the registers it
does not read.  The four copies `L = 1 … 4` are the same text, so each lemma is stated and proved
once by `limb_family` (`ℓ` stands for `L`):

- `newton_loopℓ`: `small_power_ℓ.loop`, the Newton steps of the inverse (`newton`);
- `table_loopℓ`: `small_power_ℓ.loop.loop_4`, the table of odd powers (`tbl`), held in the vector `tabV`;
- `square_loopℓ`: `small_power_ℓ.loop.loop_1.loop_3`, the squarings before a window (`ssq`);
- `walkℓ`: `small_power_ℓ.loop.loop_1`, the window walk, with invariant `WInv`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

limb_family [1, 2, 3, 4]

/-- The loop of Newton steps, from step `i`. -/
theorem newton_loopℓ (x : Exponent) (base value : Lib.MemArray_u64) (a : Limb) r1 r2 r3 r4 r5 r6
    r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 :
    ∀ n i (y : Limb), i + n = 5 →
      small_power_ℓ.loop x base value a.w y.w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
          r17 r18 r19 r20 r21 (UInt256.ofNat i) =
        small_power_ℓ.loop x base value a.w ((newton a)^[n] y).w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
          r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 (UInt256.ofNat 5)
  | 0, i, y, h => by rw [show i = 5 by omega]; rfl
  | n + 1, i, y, h => by
    rw [small_power_ℓ.loop.eq_1]
    simp only [has05_eq r8 (show i < 2 ^ 256 by omega), show (0 ≤ i ∧ i < 5) = True from
      eq_true (by omega), decide_true, ite_true, Lib.Range_at_0_5, Lib.Range_next_0_5,
      next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, mulW64_eq, two_w, subW64_eq]
    rw [Function.iterate_succ_apply]
    exact newton_loopℓ x base value a r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
      r18 r19 r20 r21 n (i + 1) _ (by omega)

/-- The squarings before a window, from bit `k` of `[i, j)`; the temporaries `r16`, `r17` end as
    the loop leaves them. -/
theorem square_loopℓ (x : Exponent) (wd : UInt256) (wn : Window) (m : L4) (inv : Limb) (i j : ℕ)
    (hj : j < 2 ^ 256) r0 r2 r3 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r18 r19 r20 r21 :
    ∀ n k (p : L4) (r16 r17 : Wide), k + n = j → i ≤ k →
      ∃ r16' r17', small_power_ℓ.loop.loop_1.loop_3 x wd wn r0 ⟨toW m, inv.w⟩ r2 r3 (toW p) r5 r6 r7 r8 r9
          r10 r11 r12 r13 r14 ⟨UInt256.ofNat i, UInt256.ofNat j⟩ r16 r17 r18 r19 r20 r21
          (UInt256.ofNat k) =
        small_power_ℓ.loop.loop_1.loop_2 x wd wn r0 ⟨toW m, inv.w⟩ r2 r3 (toW ((ssq ℓ m inv)^[n] p)) r5 r6
          r7 r8 r9 r10 r11 r12 r13 r14 ⟨UInt256.ofNat i, UInt256.ofNat j⟩ r16' r17' r18 r19 r20 r21
  | 0, k, p, r16, r17, h, hik => by
    refine ⟨r16, r17, ?_⟩
    rw [small_power_ℓ.loop.loop_1.loop_3.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) hj (show k < 2 ^ 256 by omega),
      show (i ≤ k ∧ k < j) = False from eq_false (by omega), decide_false, Bool.false_eq_true,
      ite_false, pure_bind]
    rfl
  | n + 1, k, p, r16, r17, h, hik => by
    rw [small_power_ℓ.loop.loop_1.loop_3.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) hj (show k < 2 ^ 256 by omega),
      show (i ≤ k ∧ k < j) = True from eq_true (by omega), decide_true, ite_true,
      Lib.Range_Unknown_Unknown_at, Lib.Range_Unknown_Unknown_next,
      next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind, smulℓ_eq]
    rw [Function.iterate_succ_apply]
    exact square_loopℓ x wd wn m inv i j hj r0 r2 r3 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r18 r19
      r20 r21 n (k + 1) (ssq ℓ m inv p) _ _ (by omega) (by omega)

/-- The loop filling the table, from entry `k` to `E`; `r14` ends as the loop leaves it. -/
theorem table_loopℓ (K : UInt256 → Small_ℓ → Vector Wide 64 → Wide → Wide → UInt256 → Bool →
      Lib.MemArray_u64 → Lib.Range_Known_0_Known_5 → Wide → Wide → Wide → Wide →
      Lib.Range_Known_1_Unknown → Wide → Lib.Range_Unknown_Unknown → Wide → Wide → Wide → Wide →
      Wide → Wide → FeM Option_MemArray_u64)
    (m : L4) (inv : Limb) (t0 : L4) (E : ℕ) (hE : E ≤ 64) r0 r4 r5 r6 r7 r8 r9 r10 r11 r12 r15
    r16 r17 r18 r19 r20 r21 :
    ∀ n k (r14 : Wide), k + n = E → 1 ≤ k →
      ∃ r14', small_power_ℓ.loop.loop_4 K r0 ⟨toW m, inv.w⟩ (tabV (tbl ℓ m inv t0) k)
          (toW (smul ℓ m inv t0 t0)) r4 r5 r6 r7 r8 r9 r10 r11 r12 ⟨(), UInt256.ofNat E⟩ r14 r15 r16
          r17 r18 r19 r20 r21 (UInt256.ofNat k) =
        K r0 ⟨toW m, inv.w⟩ (tabV (tbl ℓ m inv t0) E) (toW (smul ℓ m inv t0 t0)) r4 r5 r6 r7 r8 r9
          r10 r11 r12 ⟨(), UInt256.ofNat E⟩ r14' r15 r16 r17 r18 r19 r20 r21
  | 0, k, r14, h, hk => by
    refine ⟨r14, ?_⟩
    rw [small_power_ℓ.loop.loop_4.eq_1]
    simp only [has1_eq E (by omega) (show k < 2 ^ 256 by omega),
      show (1 ≤ k ∧ k < E) = False from eq_false (by omega), decide_false, Bool.false_eq_true,
      ite_false, pure_bind]
    rw [show k = E by omega]
  | n + 1, k, r14, h, hk => by
    rw [small_power_ℓ.loop.loop_4.eq_1]
    simp only [has1_eq E (by omega) (show k < 2 ^ 256 by omega),
      show (1 ≤ k ∧ k < E) = True from eq_true (by omega), decide_true, ite_true, Lib.Range_at_1,
      Lib.Range_next_1, next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind,
      sub_lit (show k < 2 ^ 256 by omega) hk, checkIndex_ok (show k - 1 < 64 by omega) (by norm_num),
      checkIndex_ok (show k < 64 by omega) (by norm_num), toNat_lit (show k - 1 < 2 ^ 256 by omega),
      toNat_lit (show k < 2 ^ 256 by omega), tabV_get _ (show k - 1 < k by omega) (by omega),
      smulℓ_eq]
    rw [show smul ℓ m inv (tbl ℓ m inv t0 (k - 1)) (smul ℓ m inv t0 t0) = tbl ℓ m inv t0 k by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl, tabV_set]
    exact table_loopℓ K m inv t0 E hE r0 r4 r5 r6 r7 r8 r9 r10 r11 r12 r15 r16 r17 r18 r19 r20
      r21 n (k + 1) _ (by omega) (by omega)


/-- After the squarings, a window ending in a set bit, already started: multiply by its entry. -/
theorem b17_oddℓ (x : Exponent) (wd : UInt256) (m : L4) (inv : Limb) (t : ℕ → L4) (c j k : ℕ)
    (hk : k < c) (hc : c ≤ 64) (p : L4) r0 r3 r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
    r20 r21 :
    small_power_ℓ.loop.loop_1.loop_2 x wd ⟨UInt256.ofNat j, UInt256.ofNat k, true⟩ r0 ⟨toW m, inv.w⟩
        (tabV t c) r3 (toW p) r5 true r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 =
      small_power_ℓ.loop.loop_1 x wd r0 ⟨toW m, inv.w⟩ (tabV t c) r3 (toW (smul ℓ m inv p (t k)))
        (UInt256.ofNat j) true r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 (toW p) (toW (t k)) r20
        r21 := by
  rw [small_power_ℓ.loop.loop_1.loop_2.eq_1]
  simp only [ite_true, checkIndex_ok (show k < 64 by omega) (by norm_num),
    toNat_lit (show k < 2 ^ 256 by omega), tabV_get t hk (by omega), pure_bind, smulℓ_eq]

/-- The first window: its entry. -/
theorem b17_firstℓ (x : Exponent) (wd : UInt256) (sm : Small_ℓ) (t : ℕ → L4) (c j k : ℕ)
    (hk : k < c) (hc : c ≤ 64) (r4 : Wide) r0 r3 r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    r19 r20 r21 :
    small_power_ℓ.loop.loop_1.loop_2 x wd ⟨UInt256.ofNat j, UInt256.ofNat k, true⟩ r0 sm (tabV t c) r3 r4
        r5 false r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 =
      small_power_ℓ.loop.loop_1 x wd r0 sm (tabV t c) r3 (toW (t k)) (UInt256.ofNat j) true r7 r8 r9 r10
        r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 := by
  rw [small_power_ℓ.loop.loop_1.loop_2.eq_1]
  simp only [ite_true, Bool.false_eq_true, ite_false, checkIndex_ok (show k < 64 by omega)
    (by norm_num), toNat_lit (show k < 2 ^ 256 by omega), tabV_get t hk (by omega), pure_bind]

/-- A zero bit: on to the next. -/
theorem b17_evenℓ (x : Exponent) (wd : UInt256) (j : ℕ) (e : UInt256) r0 r1 r2 r3 r4 r5 r6 r7 r8
    r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 :
    small_power_ℓ.loop.loop_1.loop_2 x wd ⟨UInt256.ofNat j, e, false⟩ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
        r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 =
      small_power_ℓ.loop.loop_1 x wd r0 r1 r2 r3 r4 (UInt256.ofNat j) r6 r7 r8 r9 r10 r11 r12 r13 r14
        r15 r16 r17 r18 r19 r20 r21 := by
  rw [small_power_ℓ.loop.loop_1.loop_2.eq_1]
  simp only [Bool.false_eq_true, ite_false]

/-- **The walk of `small_power<L>`**, from bit `i` to the end of the exponent: the power ends
    standing for `b ^ e`. -/
theorem walkℓ {x : Exponent} {e total top : ℕ} {w : World} (hx : ExpAt x e total top w.memory)
    (I : Env) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ (64 * ℓ))
    (hcop : Nat.Coprime (2 ^ (64 * ℓ)) (nat4 m)) (t0 : L4) (b : ℕ)
    (h0 : MRep (2 ^ (64 * ℓ)) m t0 b) (width : ℕ) (hw : 1 ≤ width ∧ width ≤ 7) (he : e ≠ 0)
    r0 r3 r7 r8 r9 r10 r11 r12 r13 r14 r20 r21 :
    ∀ n i (st : Bool) (p : L4) r15 r16 r17 r18 r19, total - i ≤ n → i ≤ total →
      WInv ℓ m e total b i st p →
      ∃ (p' : L4) (r15' : Lib.Range_Unknown_Unknown) (r16' r17' r18' r19' : Wide), MRep (2 ^ (64 * ℓ)) m p' (b ^ e) ∧
        (small_power_ℓ.loop.loop_1 x (UInt256.ofNat width) r0 ⟨toW m, inv.w⟩
            (tabV (tbl ℓ m inv t0) (2 ^ (width - 1))) r3 (toW p) (UInt256.ofNat i) st r7 r8 r9 r10
            r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21).exec I w =
          (small_power_ℓ.loop.loop_1 x (UInt256.ofNat width) r0 ⟨toW m, inv.w⟩
            (tabV (tbl ℓ m inv t0) (2 ^ (width - 1))) r3 (toW p') (UInt256.ofNat total) true r7 r8
            r9 r10 r11 r12 r13 r14 r15' r16' r17' r18' r19' r20 r21).exec I w
  | n, i, st, p, r15, r16, r17, r18, r19, hn, hit, hst => by
    rcases Nat.lt_or_eq_of_le hit with hlt | heq
    swap
    · subst heq
      cases st
      · exact absurd (by simpa [WInv, prefixOf_total] using hst) he
      · exact ⟨p, r15, r16, r17, r18, r19, by simpa [WInv, prefixOf_total] using hst, rfl⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ht := hx.total_lt
    have hc : 2 ^ (width - 1) ≤ 64 := by
      have : width - 1 ≤ 6 := by omega
      exact le_trans (Nat.pow_le_pow_right (by norm_num) this) (by norm_num)
    have hR := mrep_mul ℓ (by omega) m
    rw [small_power_ℓ.loop.loop_1.eq_1]
    simp only [hx.total_eq, toNat_lit (show i < 2 ^ 256 by omega),
      toNat_lit (show total < 2 ^ 256 by omega), show (i < total) = True from eq_true hlt,
      decide_true, ite_true, Fe.M.exec_bind, window_exec hx I hlt (show 1 ≤ width ∧ width ≤ 64 by omega)]
    by_cases hb : bitOf e total i = 0
    · have hwin : win e total i width = ⟨UInt256.ofNat (i + 1), UInt256.ofNat 0, false⟩ := by
        simp [win, hb]
      have hpre := bit_step e total i hlt
      rw [hb, Nat.add_zero] at hpre
      rw [hwin]
      cases st
      · simp only [Bool.false_eq_true, ite_false]
        rw [b17_evenℓ]
        exact walkℓ hx I m inv hinv hm hcop t0 b h0 width hw he r0 r3 r7 r8 r9 r10 r11 r12 r13 r14
          r20 r21 n' (i + 1) false p _ _ _ _ _ (by omega) (by omega)
          (by simp only [WInv] at hst ⊢; rw [hpre, hst])
      · simp only [ite_true, Lib.Range_Unknown_Unknown_start, pure_bind]
        obtain ⟨r16', r17', hsq⟩ := square_loopℓ x (UInt256.ofNat width) _ m inv i (i + 1)
          (by omega) r0 _ r3 _ _ r7 r8 r9 r10 r11 r12 r13 r14 r18 r19 r20 r21 1 i p r16 r17
          (by omega) le_rfl
        rw [hsq, b17_evenℓ]
        refine walkℓ hx I m inv hinv hm hcop t0 b h0 width hw he r0 r3 r7 r8 r9 r10 r11 r12 r13 r14
          r20 r21 n' (i + 1) true _ _ _ _ _ _ (by omega) (by omega) ?_
        simp only [WInv] at hst ⊢
        have := ssq_iter ℓ (by omega) m inv hinv hm hcop 1 p _ hst
        rw [hpre, show b ^ (2 * prefixOf e total i + 0) = (b ^ prefixOf e total i) ^ 2 ^ 1 by ring]
        exact this
    · have hb1 : bitOf e total i = 1 := by have := bitOf_lt e total i; omega
      obtain ⟨hj1, hj2, hj3, hj4⟩ := winEnd_bounds e total i width hlt hw.1 hb1
      have hk := entry_lt hlt hw.1 hb1
      have hkd := entry_digit hlt hw.1 hb1
      have hwin : win e total i width = ⟨UInt256.ofNat (winEnd e total i width),
          UInt256.ofNat ((digitOf e total i (winEnd e total i width) - 1) / 2), true⟩ := by
        simp [win, hb]
      have hstep := window_step e total i (winEnd e total i width) hj1.le hj2
      rw [hwin]
      have htb := tbl_rep ℓ (by omega) m inv hinv hm hcop t0 b h0
        ((digitOf e total i (winEnd e total i width) - 1) / 2)
      rw [hkd] at htb
      cases st
      · simp only [Bool.false_eq_true, ite_false]
        rw [b17_firstℓ _ _ _ _ _ _ _ hk hc]
        refine walkℓ hx I m inv hinv hm hcop t0 b h0 width hw he r0 r3 r7 r8 r9 r10 r11 r12 r13
          r14 r20 r21 n' _ true _ _ _ _ _ _ (by omega) hj2 ?_
        simp only [WInv] at hst ⊢
        rw [hstep, hst, Nat.zero_mul, Nat.zero_add]
        exact htb
      · simp only [ite_true, Lib.Range_Unknown_Unknown_start, pure_bind]
        obtain ⟨r16', r17', hsq⟩ := square_loopℓ x (UInt256.ofNat width) _ m inv i
          (winEnd e total i width) (by omega) r0 _ r3 _ _ r7 r8 r9 r10 r11 r12 r13 r14 r18 r19
          r20 r21 (winEnd e total i width - i) i p r16 r17 (by omega) le_rfl
        rw [hsq, b17_oddℓ _ _ _ _ _ _ _ _ hk hc]
        refine walkℓ hx I m inv hinv hm hcop t0 b h0 width hw he r0 r3 r7 r8 r9 r10 r11 r12 r13
          r14 r20 r21 n' _ true _ _ _ _ _ _ (by omega) hj2 ?_
        simp only [WInv] at hst ⊢
        have hs := ssq_iter ℓ (by omega) m inv hinv hm hcop (winEnd e total i width - i) p _ hst
        rw [hstep, pow_add b, pow_mul b]
        exact hR _ _ inv _ _ hinv hm hcop hs htb

end_limb_family

end FeProofs.Modexp
