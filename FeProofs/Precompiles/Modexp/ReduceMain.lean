import FeProofs.Precompiles.Modexp.ReduceSub

/-!
# Modexp: the Knuth main loop of `Modulus::reduce`

`Modulus_reduce.loop_2` runs `j` down from `count + 1 - n` to `0`; each step takes the window of
limbs `[j, j + n]` of the normalised dividend to its remainder by the normalised divisor `D`.
Its invariant `KInv` (over the `T = count + 1` limbs) says the limbs above the window are zero,
the top `n` limbs of the window are below `D`, and the whole is congruent to the dividend
`N0` modulo `D`.

- `mulsub_exit`, `addback_exit`: the top limb of the window, and the continuation;
- `kinv_step`: a window replaced by its remainder keeps `KInv` one limb lower;
- `main_step`, `main_loop`: the loop.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## The exits of the inner loops -/

/-- **After the multiply-subtract**: the top limb `high - carry - borrow`, then the add-back if
    that borrows, else the next step. -/
theorem mulsub_exit (md : Exported.Modexp.Modulus) (cnt wp mp sh d1w d0w : UInt256) {Mem : ByteArray}
    {K n j : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hjn : j + n < K)
    (hi q c b : Limb) (f : ℕ → Limb) (w : World) (I : Env) (r0 r1 r2 r6 : UInt256)
    (r7 : Lib.Range_Unknown_Unknown) (r9 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    (Modulus_reduce.loop_2.loop_3 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hi.w q.w r0 r1 r2 (UInt256.ofNat j)
        c.w b.w r6 r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1 (UInt256.ofNat n)).exec I
        { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      if hbit (sbbD hi c b) = 0 then
        (Modulus_reduce.loop_2 md cnt (UInt256.ofNat n) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat j) c.w b.w
          r6 r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf (Function.update f (j + n) (loD (sbbD hi c b))) K) }
      else
        (Modulus_reduce.loop_2.loop_3.loop_5 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hi.w q.w r0 r1 r2
          (UInt256.ofNat j) c.w b.w (UInt256.ofNat 0) r7 ⟨(), UInt256.ofNat n⟩ ⟨(), UInt256.ofNat n⟩ r10
          r11 v1 (UInt256.ofNat 0)).exec I
          { w with memory := putLimbs Mem wp.toNat (lf (Function.update f (j + n) (loD (sbbD hi c b))) K) } := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  rw [Modulus_reduce.loop_2.loop_3.eq_1]
  simp only [has0_eq' n (by omega) (show n < 2 ^ 256 by omega),
    show (0 ≤ n ∧ n < n) = False from eq_false (by omega), decide_false, Bool.false_eq_true, if_false,
    pure_bind, sbb_w, down128_eq, add_lit (show j + n < 2 ^ 256 by omega), Fe.M.exec_bind,
    limb_lit wp (show wp.toNat + 8 * (j + n) < UInt256.size by omega),
    store_lf f hK hs (show j + n < K by omega), shr127_eq, ne_eq, limb_eq_zero_w,
    Modulus_reduce.loop_2.loop_3.loop_4.eq_1, Lib.Range_start_0]
  by_cases h : hbit (sbbD hi c b) = 0
  · simp only [h, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h, not_false_eq_true, decide_true, if_true, if_false]

/-- **After the add-back**: the top limb plus the carry, then the next step. -/
theorem addback_exit (md : Exported.Modexp.Modulus) (cnt wp mp sh d1w d0w hw qw : UInt256)
    {Mem : ByteArray} {K n j : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hjn : j + n < K) (a : Limb) (f : ℕ → Limb) (w : World) (I : Env) (r0 r1 r2 r4 r5 : UInt256)
    (r7 : Lib.Range_Unknown_Unknown) (r8 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    (Modulus_reduce.loop_2.loop_3.loop_5 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hw qw r0 r1 r2
        (UInt256.ofNat j) r4 r5 a.w r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1 (UInt256.ofNat n)).exec I
        { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      (Modulus_reduce.loop_2 md cnt (UInt256.ofNat n) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat j) r4 r5 a.w
        r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1).exec I
        { w with memory := (putLimbs Mem wp.toNat
          (lf (Function.update f (j + n) (addMod (f (j + n)) a)) K)) } := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hl := load_lf (w := w) f hK hs (i := j + n) (by omega) I
  rw [Modulus_reduce.loop_2.loop_3.loop_5.eq_1]
  simp only [has0_eq' n (by omega) (show n < 2 ^ 256 by omega),
    show (0 ≤ n ∧ n < n) = False from eq_false (by omega), decide_false, Bool.false_eq_true, if_false,
    pure_bind, add_lit (show j + n < 2 ^ 256 by omega), Fe.M.exec_bind,
    limb_lit wp (show wp.toNat + 8 * (j + n) < UInt256.size by omega), hl, addW64_eq,
    store_lf f hK hs (show j + n < K by omega), Modulus_reduce.loop_2.loop_3.loop_4.eq_1]

/-! ## The invariant -/

/-- **The invariant of the main loop at `J`**: over the `T` limbs of the normalised dividend
    `N0`, the limbs from `J + n` are zero, the `n` limbs from `J` are below `D`, the whole is
    `N0` modulo `D`, and the limbs past `T` are those of `F`. -/
structure KInv (f F : ℕ → Limb) (D N0 T n J : ℕ) : Prop where
  le : J + n ≤ T
  above : ∀ k, T ≤ k → f k = F k
  zero : ∀ k, J + n ≤ k → k < T → f k = 0
  cong : wv f 0 T % D = N0 % D
  top : wv f J n < D

/-- **A window replaced by its remainder**: `KInv` at `J + 1` becomes `KInv` at `J`. -/
theorem kinv_step {f g F : ℕ → Limb} {D N0 T n J : ℕ} (h : KInv f F D N0 T n (J + 1))
    (hD : 0 < D) (hDn : D ≤ 2 ^ (64 * n)) (hout : ∀ k, k < J ∨ J + n < k → g k = f k)
    (hw : wv g J (n + 1) = wv f J (n + 1) % D) : KInv g F D N0 T n J := by
  have hle := h.le
  have hR := Nat.mod_lt (wv f J (n + 1)) hD
  have htop : g (J + n) = 0 := by
    have e := wv_succ g J n
    have := wv_lt g J n
    by_contra hne
    have hpos : 1 ≤ (g (J + n)).val := Nat.pos_of_ne_zero (fun e' => hne (Fin.ext e'))
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * (g (J + n)).val := Nat.le_mul_of_pos_right _ hpos
    linarith
  refine ⟨by omega, fun k hk => by rw [hout k (by omega)]; exact h.above k hk, fun k hk hk' => ?_, ?_, ?_⟩
  · rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · rw [hout k (by omega)]; exact h.zero k (by omega) hk'
    · exact htop
  · have split : ∀ u : ℕ → Limb, wv u 0 T = wv u 0 J + 2 ^ (64 * J) * (wv u J (n + 1) +
        2 ^ (64 * (n + 1)) * wv u (J + (n + 1)) (T - (J + (n + 1)))) := fun u => by
      conv_lhs => rw [show T = J + ((n + 1) + (T - (J + (n + 1)))) by omega]
      rw [wv_add, Nat.zero_add, wv_add]
    have e1 : wv g 0 J = wv f 0 J := wv_congr fun i hi => hout _ (by omega)
    have e2 : wv g (J + (n + 1)) (T - (J + (n + 1))) = wv f (J + (n + 1)) (T - (J + (n + 1))) :=
      wv_congr fun i _ => hout _ (by omega)
    rw [← h.cong, split g, split f, e1, e2, hw]
    exact (((Nat.mod_modEq _ D).add_right _).mul_left _).add_left _
  · have e := wv_succ g J n
    rw [htop, hw] at e
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at e
    omega

/-! ## One step of the main loop -/

/-- **A step from its digit**: with an estimate `q` in `[W / D, W / D + 1]` for the window `W` of
    `n + 1 = m + 3` limbs at `J`, the multiply-subtract, its exit and the add-back if needed leave
    `KInv` at `J` and go on to the next step. -/
theorem after_qhat (md : Exported.Modexp.Modulus) (cnt wp mp sh d1w d0w : UInt256) {Mem : ByteArray}
    {K Dn N0 T m : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hTK : T ≤ K)
    (hm : LimbsAt Mem mp.toNat (limbsOf Dn (m + 2)))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * (m + 2) ≤ wp.toNat) (hD0 : 0 < Dn)
    (hDlt : Dn < 2 ^ (64 * (m + 2))) (F : ℕ → Limb) (w : World) (I : Env) (r0 r1 r2 r6 : UInt256)
    (r7 : Lib.Range_Unknown_Unknown) (r9 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) (J : ℕ) (f : ℕ → Limb)
    (hI : KInv f F Dn N0 T (m + 2) (J + 1)) (q : Limb) (hq1 : wv f J (m + 2 + 1) / Dn ≤ q.val)
    (hq2 : q.val ≤ wv f J (m + 2 + 1) / Dn + 1) :
    ∃ (g : ℕ → Limb) (r4' r5' r6' : UInt256) (r9' : Lib.Range_Known_0_Unknown),
      KInv g F Dn N0 T (m + 2) J ∧
      (Modulus_reduce.loop_2.loop_3 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w d0w (f (J + (m + 2))).w q.w r0
          r1 r2 (UInt256.ofNat J) (UInt256.ofNat 0) (UInt256.ofNat 0) r6 r7 ⟨(), UInt256.ofNat (m + 2)⟩
          r9 r10 r11 v1 (UInt256.ofNat 0)).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        (Modulus_reduce.loop_2 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat J)
          r4' r5' r6' r7 ⟨(), UInt256.ofNat (m + 2)⟩ r9' r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf g K) } := by
  have hle := hI.le
  have hjn : J + (m + 2) < K := by omega
  have hDn : Dn ≤ 2 ^ (64 * (m + 2)) := hDlt.le
  have hwD : wv (limbAt Dn) 0 (m + 2) = Dn := by
    rw [wv_limbAt, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hDlt]
  obtain ⟨f', c', b', hb', hout', hid', he⟩ := mulsub_loop md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w
    d0w (f (J + (m + 2))).w hK hs hjn hm hd q f w I r0 r1 r2 r6 r7 r9 r10 r11 v1 (m + 2) 0 f 0 0
    (UInt256.ofNat 0) (UInt256.ofNat 0) rfl rfl (by omega) (by simp) (fun _ _ => rfl) (by simp [wv])
  rw [he, mulsub_exit md cnt wp mp sh d1w d0w hK hs hjn (f (J + (m + 2))) q c' b' f' w I r0 r1 r2 r6 r7
    r9 r10 r11 v1]
  rw [hwD] at hid'
  obtain ⟨hi, hhi⟩ : ∃ hi, f (J + (m + 2)) = hi := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, sbbD hi c' b' = S := ⟨_, rfl⟩
  rw [hhi, hS]
  have hS1 := sbbD_lo hi c' b' hb'
  rw [hS] at hS1
  have hfb : (hbit S).val ≤ 1 := hS ▸ hbit_le hi c' b' hb'
  have hW : wv f J (m + 2 + 1) = wv f J (m + 2) + 2 ^ (64 * (m + 2)) * hi.val := by
    rw [wv_succ, hhi]
  have hf2 : wv (Function.update f' (J + (m + 2)) (loD S)) J (m + 2 + 1) =
      wv f' J (m + 2) + 2 ^ (64 * (m + 2)) * (loD S).val := by
    rw [wv_succ, wv_update_out f' (Or.inr le_rfl), Function.update_self]
  have key : wv (Function.update f' (J + (m + 2)) (loD S)) J (m + 2 + 1) + q.val * Dn =
      wv f J (m + 2 + 1) + (hbit S).val * 2 ^ (64 * (m + 2 + 1)) := by
    rw [hf2, hW, pow_succ64]
    zify at hid' hS1 ⊢
    linear_combination hid' + (2 : ℤ) ^ (64 * (m + 2)) * hS1
  obtain ⟨k0, k1⟩ := knuth_step hD0 hq1 hq2 (wv_lt _ J _) hfb key
  have hout2 : ∀ k, k < J ∨ J + (m + 2) < k → Function.update f' (J + (m + 2)) (loD S) k = f k :=
    fun k hk => by rw [Function.update_of_ne (by omega)]; exact hout' k (by omega)
  by_cases hz : hbit S = 0
  · rw [if_pos hz]
    exact ⟨_, c'.w, b'.w, r6, r9, kinv_step hI hD0 hDn hout2 (k0 (by rw [hz]; rfl)), rfl⟩
  · rw [if_neg hz]
    have h1 : (hbit S).val = 1 := by
      have : (hbit S).val ≠ 0 := fun e => hz (Fin.ext e)
      omega
    have k1' := k1 h1
    obtain ⟨f3, a', ha', hout3, hid3, he3⟩ := addback_loop md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w
      d0w hi.w q.w hK hs hjn hm hd (Function.update f' (J + (m + 2)) (loD S)) w I r0 r1 r2 c'.w b'.w r7
      ⟨(), UInt256.ofNat (m + 2)⟩ r10 r11 v1 (m + 2) 0 _ 0 (UInt256.ofNat 0) rfl (by omega) (by simp)
      (fun _ _ => rfl) (by simp [wv])
    rw [he3, addback_exit md cnt wp mp sh d1w d0w hi.w q.w hK hs hjn a' f3 w I r0 r1 r2 c'.w b'.w r7
      ⟨(), UInt256.ofNat (m + 2)⟩ r10 r11 v1]
    have h3top : f3 (J + (m + 2)) = loD S := by
      rw [hout3 _ (Or.inr le_rfl), Function.update_self]
    rw [hwD, wv_update_out f' (Or.inr le_rfl)] at hid3
    refine ⟨_, c'.w, b'.w, a'.w, ⟨(), UInt256.ofNat (m + 2)⟩, kinv_step hI hD0 hDn
      (fun k hk => by
        rw [Function.update_of_ne (by omega), hout3 k (by omega)]; exact hout2 k hk) ?_, rfl⟩
    rw [h3top]
    have hlt := wv_lt (Function.update f3 (J + (m + 2)) (addMod (loD S) a')) J (m + 2 + 1)
    rw [wv_succ, wv_update_out f3 (Or.inr le_rfl), Function.update_self] at hlt ⊢
    rw [hf2] at k1'
    have hR := Nat.mod_lt (wv f J (m + 2 + 1)) hD0
    have hdm := Nat.mod_add_div ((loD S).val + a'.val) (2 ^ 64)
    have he1 : ((loD S).val + a'.val) / 2 ^ 64 ≤ 1 := by
      have := (loD S).isLt
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
    simp only [addMod] at hlt ⊢
    rw [pow_succ64 (m + 2)] at hlt k1'
    generalize ((loD S).val + a'.val) / 2 ^ 64 = e at hdm he1
    generalize ((loD S).val + a'.val) % 2 ^ 64 = t at hdm hlt ⊢
    have eqn : wv f3 J (m + 2) + 2 ^ (64 * (m + 2)) * t + 2 ^ (64 * (m + 2)) * 2 ^ 64 * e =
        wv f J (m + 2 + 1) % Dn + 2 ^ (64 * (m + 2)) * 2 ^ 64 := by
      zify at hdm hid3 k1' ⊢
      linear_combination hid3 + k1' + (2 : ℤ) ^ (64 * (m + 2)) * hdm
    have hDP : Dn ≤ 2 ^ (64 * (m + 2)) * 2 ^ 64 := le_trans hDn (Nat.le_mul_of_pos_right _ (by norm_num))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he1 with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero] at eqn
      rw [eqn] at hlt
      exact absurd hlt (Nat.not_lt.mpr (Nat.le_add_left _ _))
    · rw [Nat.mul_one] at eqn
      exact Nat.add_right_cancel eqn

theorem wv_two (f : ℕ → Limb) (a : ℕ) : wv f a 2 = (f a).val + 2 ^ 64 * (f (a + 1)).val := by
  have e := wv_succ f a 1
  rw [wv_one, Nat.mul_one] at e
  exact e

theorem wv_three (f : ℕ → Limb) (a : ℕ) :
    wv f a 3 = (f a).val + 2 ^ 64 * (f (a + 1)).val + 2 ^ 128 * (f (a + 2)).val := by
  have e := wv_succ f a 2
  rw [wv_two] at e
  exact e

/-- `β - 1`, the digit when the top two limbs of the window are those of the divisor. -/
def qmax : Limb := ⟨18446744073709551615, by norm_num⟩

theorem qmax_w : qmax.w = UInt256.ofNat 18446744073709551615 := rfl

theorem w_inj_eq (x y : Limb) : (x.w = y.w) = (x = y) := propext Limb.w_inj

/-- The digit `Modulus::reduce` estimates from the top three limbs of the window. -/
def qsel (hi nx th d1 d0 v : Limb) : Limb := if hi = d1 ∧ nx = d0 then qmax else div32 hi nx th d1 d0 v

/-- **The head of a step**: the top three limbs of the window and the digit, then the
    multiply-subtract from limb `0`. -/
theorem main_head (md : Exported.Modexp.Modulus) (cnt wp mp sh : UInt256) {Mem : ByteArray} {K m J : ℕ}
    (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hjn : J + (m + 2) < K)
    (d1 d0 v : Limb) (hrec : md.reciprocal = v.w) (f : ℕ → Limb) (w : World) (I : Env)
    (r0 r1 r2 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown) (r8 r9 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    (Modulus_reduce.loop_2 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1.w d0.w r0 r1 r2 (UInt256.ofNat (J + 1))
        r4 r5 r6 r7 r8 r9 r10 r11 v1).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      (Modulus_reduce.loop_2.loop_3 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1.w d0.w (f (J + (m + 2))).w
        (qsel (f (J + (m + 2))) (f (J + m + 1)) (f (J + m)) d1 d0 v).w r0 r1 r2 (UInt256.ofNat J)
        (UInt256.ofNat 0) (UInt256.ofNat 0) r6 r7 ⟨(), UInt256.ofNat (m + 2)⟩ r9 r10 r11 v1
        (UInt256.ofNat 0)).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hl2 := load_lf (w := w) f hK hs (i := J + (m + 2)) (by omega) I
  have hl1 := load_lf (w := w) f hK hs (i := J + m + 1) (by omega) I
  have hl0 := load_lf (w := w) f hK hs (i := J + m) (by omega) I
  rw [Modulus_reduce.loop_2.eq_1]
  simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), toNat_lit (show J + 1 < 2 ^ 256 by omega),
    show 0 < J + 1 by omega, decide_true, if_true,
    sub_lit (show J + 1 < 2 ^ 256 by omega) (show 1 ≤ J + 1 by omega), Nat.add_sub_cancel,
    add_lit (show J + (m + 2) < 2 ^ 256 by omega),
    sub_lit (show J + (m + 2) < 2 ^ 256 by omega) (show 1 ≤ J + (m + 2) by omega),
    sub_lit (show J + (m + 2) < 2 ^ 256 by omega) (show 2 ≤ J + (m + 2) by omega),
    show J + (m + 2) - 1 = J + m + 1 by omega, show J + (m + 2) - 2 = J + m by omega,
    limb_lit wp (show wp.toNat + 8 * (J + (m + 2)) < UInt256.size by omega),
    limb_lit wp (show wp.toNat + 8 * (J + m + 1) < UInt256.size by omega),
    limb_lit wp (show wp.toNat + 8 * (J + m) < UInt256.size by omega), pure_bind, Fe.M.exec_bind,
    hl2, hl1, w_inj_eq, hrec, Lib.Range_start_0, qsel]
  by_cases h1 : f (J + (m + 2)) = d1
  · by_cases h2 : f (J + m + 1) = d0
    · simp only [decide_eq_true h1, decide_eq_true h2, if_true, if_pos (And.intro h1 h2), qmax_w]
    · simp only [decide_eq_true h1, decide_eq_false h2, if_true, Bool.false_eq_true, if_false,
        if_neg (fun h : _ ∧ _ => h2 h.2), Fe.M.exec_bind, hl0, div_3by2_eq, pure_bind]
  · simp only [decide_eq_false h1, Bool.false_eq_true, if_false, if_neg (fun h : _ ∧ _ => h1 h.1),
      Fe.M.exec_bind, hl0, div_3by2_eq, pure_bind]

/-- **The digit is exact or one too large**, from the window's and the divisor's top limbs. -/
theorem qsel_bounds {f : ℕ → Limb} {Dn J m : ℕ} (hDlt : Dn < 2 ^ (64 * (m + 2)))
    (hd1 : 2 ^ 63 ≤ (limbAt Dn (m + 1)).val) (htop : wv f (J + 1) (m + 2) < Dn) :
    wv f J (m + 2 + 1) / Dn ≤
        (qsel (f (J + (m + 2))) (f (J + m + 1)) (f (J + m)) (limbAt Dn (m + 1)) (limbAt Dn m)
          (recip32 (limbAt Dn (m + 1)) (limbAt Dn m) hd1)).val ∧
      (qsel (f (J + (m + 2))) (f (J + m + 1)) (f (J + m)) (limbAt Dn (m + 1)) (limbAt Dn m)
          (recip32 (limbAt Dn (m + 1)) (limbAt Dn m) hd1)).val ≤ wv f J (m + 2 + 1) / Dn + 1 := by
  have hwD : wv (limbAt Dn) 0 (m + 2) = Dn := by
    rw [wv_limbAt, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hDlt]
  have hDdec : Dn = ((limbAt Dn (m + 1)).val * 2 ^ 64 + (limbAt Dn m).val) * 2 ^ (64 * m) +
      wv (limbAt Dn) 0 m := by
    have e := wv_add (limbAt Dn) 0 m 2
    rw [hwD, Nat.zero_add, wv_two] at e
    conv_lhs => rw [e]
    ring
  have hWdec : wv f J (m + 2 + 1) = (((f (J + (m + 2))).val * 2 ^ 64 + (f (J + m + 1)).val) * 2 ^ 64 +
      (f (J + m)).val) * 2 ^ (64 * m) + wv f J m := by
    rw [show m + 2 + 1 = m + 3 by ring, wv_add, wv_three, show J + m + 2 = J + (m + 2) by ring]
    ring
  have hWD : wv f J (m + 2 + 1) < Dn * 2 ^ 64 := by
    rw [wv_low]
    have := (f J).isLt
    nlinarith
  have hd0 := (limbAt Dn m).isLt
  have hu0 := (f (J + m)).isLt
  have hu1 := (f (J + m + 1)).isLt
  have hb := qhat_bounds (T := (f (J + (m + 2))).val * 2 ^ 64 + (f (J + m + 1)).val)
    (u0 := (f (J + m)).val) (D' := (limbAt Dn (m + 1)).val * 2 ^ 64 + (limbAt Dn m).val) hu0
    (by nlinarith) (by positivity) (wv_lt f J m) (wv_lt (limbAt Dn) 0 m) hDdec hWdec hWD
  obtain ⟨hTD, hlo, hhi⟩ := hb
  simp only [qsel]
  by_cases hc : f (J + (m + 2)) = limbAt Dn (m + 1) ∧ f (J + m + 1) = limbAt Dn m
  · have hT : (f (J + (m + 2))).val * 2 ^ 64 + (f (J + m + 1)).val =
        (limbAt Dn (m + 1)).val * 2 ^ 64 + (limbAt Dn m).val := by rw [hc.1, hc.2]
    rw [if_pos hT] at hlo hhi
    rw [if_pos hc]
    exact ⟨hlo, hhi⟩
  · have hT : (f (J + (m + 2))).val * 2 ^ 64 + (f (J + m + 1)).val ≠
        (limbAt Dn (m + 1)).val * 2 ^ 64 + (limbAt Dn m).val := fun e =>
      hc ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    rw [if_neg hT] at hlo hhi
    rw [if_neg hc, div32_val _ _ _ _ _ hd1 (lt_of_le_of_ne hTD hT)]
    rw [show (f (J + (m + 2))).val * 2 ^ 128 + (f (J + m + 1)).val * 2 ^ 64 + (f (J + m)).val =
      ((f (J + (m + 2))).val * 2 ^ 64 + (f (J + m + 1)).val) * 2 ^ 64 + (f (J + m)).val by ring]
    exact ⟨hlo, hhi⟩

/-! ## The main loop -/

/-- **One step of the main loop**, from `J + 1` to `J`. -/
theorem main_step (md : Exported.Modexp.Modulus) (cnt wp mp sh : UInt256) {Mem : ByteArray}
    {K Dn N0 T m : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hTK : T ≤ K)
    (hm : LimbsAt Mem mp.toNat (limbsOf Dn (m + 2)))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * (m + 2) ≤ wp.toNat) (hD0 : 0 < Dn)
    (hDlt : Dn < 2 ^ (64 * (m + 2))) (hd1 : 2 ^ 63 ≤ (limbAt Dn (m + 1)).val)
    (hrec : md.reciprocal = (recip32 (limbAt Dn (m + 1)) (limbAt Dn m) hd1).w) (F : ℕ → Limb)
    (w : World) (I : Env) (r0 r1 r2 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r8 r9 r10 : Lib.Range_Known_0_Unknown) (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64)
    (J : ℕ) (f : ℕ → Limb) (hI : KInv f F Dn N0 T (m + 2) (J + 1)) :
    ∃ (g : ℕ → Limb) (r4' r5' r6' : UInt256) (r8' r9' : Lib.Range_Known_0_Unknown),
      KInv g F Dn N0 T (m + 2) J ∧
      (Modulus_reduce.loop_2 md cnt (UInt256.ofNat (m + 2)) wp mp sh (limbAt Dn (m + 1)).w (limbAt Dn m).w
          r0 r1 r2 (UInt256.ofNat (J + 1)) r4 r5 r6 r7 r8 r9 r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        (Modulus_reduce.loop_2 md cnt (UInt256.ofNat (m + 2)) wp mp sh (limbAt Dn (m + 1)).w (limbAt Dn m).w
          r0 r1 r2 (UInt256.ofNat J) r4' r5' r6' r7 r8' r9' r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf g K) } := by
  have hle := hI.le
  obtain ⟨hq1, hq2⟩ := qsel_bounds (f := f) (J := J) hDlt hd1 hI.top
  obtain ⟨g, a, b, c, r9', hg, he⟩ := after_qhat md cnt wp mp sh (limbAt Dn (m + 1)).w (limbAt Dn m).w
    hK hs hTK hm hd hD0 hDlt F w I r0 r1 r2 r6 r7 r9 r10 r11 v1 J f hI _ hq1 hq2
  exact ⟨g, a, b, c, _, r9', hg, by
    rw [main_head md cnt wp mp sh hK hs (by omega) _ _ _ hrec f w I r0 r1 r2 r4 r5 r6 r7 r8 r9 r10 r11 v1,
      he]⟩

theorem wv_zeros {f : ℕ → Limb} {a : ℕ} : ∀ {k}, (∀ i < k, f (a + i) = 0) → wv f a k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [wv_succ, wv_zeros (fun i hi => h i (by omega)), h k (by omega)]; rfl

/-- **The main loop** from `J` down, then the denormalisation and the clearing: the first
    `count + 1` limbs become those of `X mod M`, for the dividend `X * 2 ^ s` and the divisor
    `M * 2 ^ s` of `n = m + 2` limbs. -/
theorem main_loop (md : Exported.Modexp.Modulus) (wp mp : UInt256) {Mem : ByteArray}
    {K M X s count m : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hcK : count + 1 ≤ K) (hn : m + 2 ≤ count) (hs64 : s < 64)
    (hm : LimbsAt Mem mp.toNat (limbsOf (M * 2 ^ s) (m + 2)))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * (m + 2) ≤ wp.toNat) (hM0 : 0 < M)
    (hDlt : M * 2 ^ s < 2 ^ (64 * (m + 2))) (hd1 : 2 ^ 63 ≤ (limbAt (M * 2 ^ s) (m + 1)).val)
    (hrec : md.reciprocal = (recip32 (limbAt (M * 2 ^ s) (m + 1)) (limbAt (M * 2 ^ s) m) hd1).w)
    (F : ℕ → Limb) (w : World) (I : Env) (r0 r1 r2 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r10 : Lib.Range_Known_0_Unknown) (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ J (f : ℕ → Limb) (r4 r5 r6 : UInt256) (r8 r9 : Lib.Range_Known_0_Unknown),
      KInv f F (M * 2 ^ s) (X * 2 ^ s) (count + 1) (m + 2) J →
      (Modulus_reduce.loop_2 md (UInt256.ofNat count) (UInt256.ofNat (m + 2)) wp mp (UInt256.ofNat s)
          (limbAt (M * 2 ^ s) (m + 1)).w (limbAt (M * 2 ^ s) m).w r0 r1 r2 (UInt256.ofNat J) r4 r5 r6 r7
          r8 r9 r10 r11 v1).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        some (.ok (((), v1), { w with memory := (putLimbs Mem wp.toNat
          (lf (fun k => if k < count + 1 then limbAt (X % M) k else F k) K)) }))
  | J + 1, f, r4, r5, r6, r8, r9, hI => by
    obtain ⟨g, a, b, c, r8', r9', hg, he⟩ := main_step md (UInt256.ofNat count) wp mp (UInt256.ofNat s)
      hK hs hcK hm hd (by positivity) hDlt hd1 hrec F w I r0 r1 r2 r4 r5 r6 r7 r8 r9 r10 r11 v1 J f hI
    rw [he]
    exact main_loop md wp mp hK hs hcK hn hs64 hm hd hM0 hDlt hd1 hrec F w I r0 r1 r2 r7 r10 r11 v1 J g
      a b c r8' r9' hg
  | 0, f, r4, r5, r6, r8, r9, hI => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hD0 : 0 < M * 2 ^ s := by positivity
    have hR : X % M * 2 ^ s = X * 2 ^ s % (M * 2 ^ s) := (Nat.mul_mod_mul_right _ _ _).symm
    have hRlt : X % M * 2 ^ s < M * 2 ^ s := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hM0) (by positivity)
    have hzero := hI.zero
    simp only [Nat.zero_add] at hzero
    have hw0 : wv f 0 (count + 1) = wv f 0 (m + 2) := by
      have e := wv_add f 0 (m + 2) (count + 1 - (m + 2))
      rw [show m + 2 + (count + 1 - (m + 2)) = count + 1 by omega,
        wv_zeros (f := f) (a := 0 + (m + 2)) (k := count + 1 - (m + 2))
          (fun i hi => hzero _ (by omega) (by omega)), Nat.mul_zero, Nat.add_zero] at e
      exact e
    have hv : wv f 0 (m + 2) = X % M * 2 ^ s := by
      have := hI.cong
      rw [hw0, Nat.mod_eq_of_lt hI.top] at this
      rw [this, hR]
    have hz : ∀ k, m + 2 ≤ k → limbAt (X % M * 2 ^ s) k = 0 := fun k hk => Fin.ext (by
      simp only [limbAt]
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hRlt.trans hDlt) (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      rfl)
    rw [Modulus_reduce.loop_2.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), lt_irrefl, decide_false, Bool.false_eq_true,
      if_false, pure_bind, Lib.Range_start_0]
    rw [denorm_loop wp hK hs hn hcK hs64 (R := X % M) (lt_of_lt_of_le (Nat.mod_lt _ hM0)
        (le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hDlt.le))
      (fun k => if k < count + 1 then 0 else F k) w I r0 r1 r2 (UInt256.ofNat 0) r4 r5 r6 r7 r8 r9 r11 v1
      (m + 2) 0 f (by omega) (fun k _ => by
        beta_reduce
        by_cases h1 : k < m + 2
        · rw [if_neg (by omega), if_pos (by omega), ← Nat.zero_add k, eq_limbAt_of_wv hv h1, Nat.zero_add]
        · by_cases h2 : k < count + 1
          · rw [hzero k (by omega) h2]
            by_cases h3 : k ≤ m + 2
            · rw [if_neg (by omega), if_pos h3, hz k (by omega)]
            · rw [if_neg (by omega), if_neg h3, if_pos h2]
          · rw [hI.above k (by omega), if_neg (by omega), if_neg (by omega), if_neg h2])]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr fun k _ => ?_)
    dsimp only
    split_ifs <;> rfl

end FeProofs.Modexp
