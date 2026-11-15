import FeProofs.Precompiles.Modexp.ReduceSub

/-!
# Modexp: the Knuth main loop of `Modulus::reduce`

`Modulus_reduce.b25` runs `j` down from `count + 1 - n` to `0`; each step takes the window of
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
    (Modulus_reduce.b25.b32 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hi.w q.w r0 r1 r2 (UInt256.ofNat j)
        c.w b.w r6 r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1 (UInt256.ofNat n)).exec I
        { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      if hbit (sbbD hi c b) = 0 then
        (Modulus_reduce.b25 md cnt (UInt256.ofNat n) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat j) c.w b.w
          r6 r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf (Function.update f (j + n) (loD (sbbD hi c b))) K) }
      else
        (Modulus_reduce.b25.b32.b39 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hi.w q.w r0 r1 r2
          (UInt256.ofNat j) c.w b.w (UInt256.ofNat 0) r7 ⟨(), UInt256.ofNat n⟩ ⟨(), UInt256.ofNat n⟩ r10
          r11 v1 (UInt256.ofNat 0)).exec I
          { w with memory := putLimbs Mem wp.toNat (lf (Function.update f (j + n) (loD (sbbD hi c b))) K) } := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  rw [Modulus_reduce.b25.b32.eq_1]
  simp only [has0_eq' n (by omega) (show n < 2 ^ 256 by omega),
    show (0 ≤ n ∧ n < n) = False from eq_false (by omega), decide_false, Bool.false_eq_true, if_false,
    pure_bind, sbb_w, down128_eq, add_lit (show j + n < 2 ^ 256 by omega), Fe.M.exec_bind,
    limb_lit wp (show wp.toNat + 8 * (j + n) < UInt256.size by omega),
    store_lf f hK hs (show j + n < K by omega), shr127_eq, ne_eq, limb_eq_zero_w,
    Modulus_reduce.b25.b32.b38.eq_1, Lib.Range_start_0]
  by_cases h : hbit (sbbD hi c b) = 0
  · simp only [h, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h, not_false_eq_true, decide_true, if_true, if_false]

/-- **After the add-back**: the top limb plus the carry, then the next step. -/
theorem addback_exit (md : Exported.Modexp.Modulus) (cnt wp mp sh d1w d0w hw qw : UInt256)
    {Mem : ByteArray} {K n j : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hjn : j + n < K) (a : Limb) (f : ℕ → Limb) (w : World) (I : Env) (r0 r1 r2 r4 r5 : UInt256)
    (r7 : Lib.Range_Unknown_Unknown) (r8 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    (Modulus_reduce.b25.b32.b39 md cnt (UInt256.ofNat n) wp mp sh d1w d0w hw qw r0 r1 r2
        (UInt256.ofNat j) r4 r5 a.w r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1 (UInt256.ofNat n)).exec I
        { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      (Modulus_reduce.b25 md cnt (UInt256.ofNat n) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat j) r4 r5 a.w
        r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1).exec I
        { w with memory := (putLimbs Mem wp.toNat
          (lf (Function.update f (j + n) (addMod (f (j + n)) a)) K)) } := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hl := load_lf (w := w) f hK hs (i := j + n) (by omega) I
  rw [Modulus_reduce.b25.b32.b39.eq_1]
  simp only [has0_eq' n (by omega) (show n < 2 ^ 256 by omega),
    show (0 ≤ n ∧ n < n) = False from eq_false (by omega), decide_false, Bool.false_eq_true, if_false,
    pure_bind, add_lit (show j + n < 2 ^ 256 by omega), Fe.M.exec_bind,
    limb_lit wp (show wp.toNat + 8 * (j + n) < UInt256.size by omega), hl, addW64_eq,
    store_lf f hK hs (show j + n < K by omega), Modulus_reduce.b25.b32.b38.eq_1]

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
      (Modulus_reduce.b25.b32 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w d0w (f (J + (m + 2))).w q.w r0
          r1 r2 (UInt256.ofNat J) (UInt256.ofNat 0) (UInt256.ofNat 0) r6 r7 ⟨(), UInt256.ofNat (m + 2)⟩
          r9 r10 r11 v1 (UInt256.ofNat 0)).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        (Modulus_reduce.b25 md cnt (UInt256.ofNat (m + 2)) wp mp sh d1w d0w r0 r1 r2 (UInt256.ofNat J)
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

end FeProofs.Modexp
