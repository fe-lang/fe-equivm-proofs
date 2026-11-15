import FeProofs.Precompiles.Modexp.ReduceLoops
import FeProofs.Precompiles.Modexp.Knuth

/-!
# Modexp: the multiply-subtract and the add-back of `Modulus::reduce`

One step of Knuth division at limb `j` subtracts `q̂ D` from the window of limbs `[j, j + n]`
(`Modulus_reduce.b25.b32`), and adds `D` back once when that borrows
(`Modulus_reduce.b25.b32.b39`).  `D` is the normalised modulus, the limbs `limbAt Dn` of an array
at `mp` apart from the work array.  The invariants are identities of window values:

- `mulsub_loop`: after `i` limbs, `S_i + q̂ D_i = W_i + (carry + borrow) β^i`;
- `addback_loop`: after `i` limbs, `S_i + carry β^i = S'_i + D_i`;

and `mulsub_exit`, `addback_exit` store the top limb and continue.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

theorem mac_w (q m c : Limb) :
    IntTy.addW (.u 128) (IntTy.mulW (.u 128) q.w m.w) c.w = (addD (mulD q m) (L2D c)).w := by
  rw [mulW128_eq, addW128_DL]

theorem sbb_w (x y b : Limb) :
    IntTy.subW (.u 128) (IntTy.subW (.u 128) x.w y.w) b.w = (sbbD x y b).w := by
  rw [subW128_LL, subW128_DL]; rfl

theorem adc_w (x m a : Limb) :
    IntTy.addW (.u 128) (IntTy.addW (.u 128) x.w m.w) a.w = (addD (addD (L2D x) (L2D m)) (L2D a)).w := by
  rw [addW128_LL, addW128_DL]

/-- **A limb of the modulus**, read while the work array is being written. -/
theorem load_mod {w : World} {Mem : ByteArray} {wp mp : UInt256} {K Dn n : ℕ} (f : ℕ → Limb)
    (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hm : LimbsAt Mem mp.toNat (limbsOf Dn n))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * n ≤ wp.toNat) {i : ℕ} (hi : i < n) (I : Env) :
    (mloadInt (.u 64) (UInt256.ofNat (mp.toNat + 8 * i))).exec I
        { w with memory := putLimbs Mem wp.toNat (lf f K) } =
      some (.ok ((limbAt Dn i).w, { w with memory := putLimbs Mem wp.toNat (lf f K) })) := by
  have hK' : wp.toNat + 8 * (lf f K).length ≤ Mem.size := by simpa using hK
  have hm' := LimbsAt.putLimbs_other hm hK' (by simpa using hd)
  have := load_exec (w := { w with memory := putLimbs Mem wp.toNat (lf f K) }) hm' (i := i)
    (by simpa using hi) (by rw [putLimbs_size hK']; exact hs) I
  rwa [limbsOf_get Dn n i hi] at this

theorem hbit_le (x y b : Limb) (hb : b.val ≤ 1) : (hbit (sbbD x y b)).val ≤ 1 := by
  rw [sbbD_hbit x y b hb]; split_ifs <;> norm_num

theorem pow_succ64 (i : ℕ) : (2 : ℕ) ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by
  rw [Nat.mul_add, Nat.mul_one, pow_add]

/-! ## Multiply-subtract -/

/-- **The multiply-subtract** `w[j + i] -= q̂ m[i]` with carry and borrow, from limb `i` to `n`. -/
theorem mulsub_loop (md : Exported.Modexp.Modulus) (cnt nW wp mp sh d1w d0w hw : UInt256)
    {Mem : ByteArray} {K Dn n j : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hjn : j + n < K) (hm : LimbsAt Mem mp.toNat (limbsOf Dn n))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * n ≤ wp.toNat) (q : Limb) (f0 : ℕ → Limb)
    (w : World) (I : Env) (r0 r1 r2 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r9 r10 : Lib.Range_Known_0_Unknown) (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ m i (f : ℕ → Limb) (c b : Limb) (rc rb : UInt256), rc = c.w → rb = b.w → i + m = n →
      b.val ≤ 1 → (∀ k, k < j ∨ j + i ≤ k → f k = f0 k) →
      wv f j i + q.val * wv (limbAt Dn) 0 i = wv f0 j i + (c.val + b.val) * 2 ^ (64 * i) →
      ∃ (f' : ℕ → Limb) (c' b' : Limb), b'.val ≤ 1 ∧ (∀ k, k < j ∨ j + n ≤ k → f' k = f0 k) ∧
        wv f' j n + q.val * wv (limbAt Dn) 0 n = wv f0 j n + (c'.val + b'.val) * 2 ^ (64 * n) ∧
        (Modulus_reduce.b25.b32 md cnt nW wp mp sh d1w d0w hw q.w r0 r1 r2 (UInt256.ofNat j) rc rb r6
            r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1 (UInt256.ofNat i)).exec I
            { w with memory := putLimbs Mem wp.toNat (lf f K) } =
          (Modulus_reduce.b25.b32 md cnt nW wp mp sh d1w d0w hw q.w r0 r1 r2 (UInt256.ofNat j) c'.w
            b'.w r6 r7 ⟨(), UInt256.ofNat n⟩ r9 r10 r11 v1 (UInt256.ofNat n)).exec I
            { w with memory := putLimbs Mem wp.toNat (lf f' K) }
  | 0, i, f, c, b, rc, rb, hrc, hrb, hm0, hb, hout, hid => by
    subst hrc hrb
    obtain rfl : i = n := by omega
    exact ⟨f, c, b, hb, hout, hid, rfl⟩
  | m + 1, i, f, c, b, rc, rb, hrc, hrb, hmi, hb, hout, hid => by
    subst hrc hrb
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hin : i < n := by omega
    have hmb := hm.1
    simp only [limbsOf_length] at hmb
    have hfx : f (i + j) = f0 (i + j) := hout _ (Or.inr (by omega))
    have hlm := load_mod (w := w) f hK hs hm hd hin I
    have hlx := load_lf (w := w) f hK hs (i := i + j) (by omega) I
    rw [hfx] at hlx
    obtain ⟨P, hP⟩ : ∃ P, addD (mulD q (limbAt Dn i)) (L2D c) = P := ⟨_, rfl⟩
    obtain ⟨S, hS'⟩ : ∃ S, sbbD (f0 (i + j)) (loD P) b = S := ⟨_, rfl⟩
    have h1 := sbbD_lo (f0 (i + j)) (loD P) b hb
    have h2 : (loD P).val + (hiD P).val * 2 ^ 64 = q.val * (limbAt Dn i).val + c.val := by
      rw [← mac128_val, hP]; simp only [loD, hiD]; omega
    rw [hS'] at h1
    have hb' : (hbit S).val ≤ 1 := hS' ▸ hbit_le _ _ _ hb
    obtain ⟨f', c', b', hb'', hout', hid', he⟩ := mulsub_loop md cnt nW wp mp sh d1w d0w hw hK hs hjn
      hm hd q f0 w I r0 r1 r2 r6 r7 r9 r10 r11 v1 m (i + 1) (Function.update f (i + j) (loD S))
      (hiD P) (hbit S) _ _ rfl rfl (by omega) hb'
      (fun k hk => by rw [Function.update_of_ne (by omega)]; exact hout k (by omega))
      (by
        rw [wv_succ, wv_succ, wv_succ, wv_update_out f (Or.inr (by omega)), Nat.zero_add,
          show j + i = i + j by ring, Function.update_self, pow_succ64]
        zify at h1 h2 hid ⊢
        linear_combination hid + (2 : ℤ) ^ (64 * i) * h1 - (2 : ℤ) ^ (64 * i) * h2)
    refine ⟨f', c', b', hb'', hout', hid', ?_⟩
    rw [Modulus_reduce.b25.b32.eq_1]
    simp only [has0_eq' n (by omega) (show i < 2 ^ 256 by omega),
      show (0 ≤ i ∧ i < n) = True from eq_true (by omega), decide_true, if_true, Lib.Range_at_0,
      Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      limb_lit mp (show mp.toNat + 8 * i < UInt256.size by omega), hlm, mac_w, hP, shr64_eq,
      down128_limb_eq, down128_eq, add_lit (show i + j < 2 ^ 256 by omega),
      limb_lit wp (show wp.toNat + 8 * (i + j) < UInt256.size by omega), hlx, sbb_w, hS',
      store_lf f hK hs (show i + j < K by omega), shr127_eq]
    exact he

/-! ## Add-back -/

/-- **The add-back** `w[j + i] += m[i]` with carry, from limb `i` to `n`. -/
theorem addback_loop (md : Exported.Modexp.Modulus) (cnt nW wp mp sh d1w d0w hw qw : UInt256)
    {Mem : ByteArray} {K Dn n j : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size)
    (hjn : j + n < K) (hm : LimbsAt Mem mp.toNat (limbsOf Dn n))
    (hd : wp.toNat + 8 * K ≤ mp.toNat ∨ mp.toNat + 8 * n ≤ wp.toNat) (f0 : ℕ → Limb)
    (w : World) (I : Env) (r0 r1 r2 r4 r5 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r8 r10 : Lib.Range_Known_0_Unknown) (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ m i (f : ℕ → Limb) (a : Limb) (ra : UInt256), ra = a.w → i + m = n → a.val ≤ 1 →
      (∀ k, k < j ∨ j + i ≤ k → f k = f0 k) →
      wv f j i + a.val * 2 ^ (64 * i) = wv f0 j i + wv (limbAt Dn) 0 i →
      ∃ (f' : ℕ → Limb) (a' : Limb), a'.val ≤ 1 ∧ (∀ k, k < j ∨ j + n ≤ k → f' k = f0 k) ∧
        wv f' j n + a'.val * 2 ^ (64 * n) = wv f0 j n + wv (limbAt Dn) 0 n ∧
        (Modulus_reduce.b25.b32.b39 md cnt nW wp mp sh d1w d0w hw qw r0 r1 r2 (UInt256.ofNat j) r4 r5 ra
            r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1 (UInt256.ofNat i)).exec I
            { w with memory := putLimbs Mem wp.toNat (lf f K) } =
          (Modulus_reduce.b25.b32.b39 md cnt nW wp mp sh d1w d0w hw qw r0 r1 r2 (UInt256.ofNat j) r4 r5
            a'.w r7 r8 ⟨(), UInt256.ofNat n⟩ r10 r11 v1 (UInt256.ofNat n)).exec I
            { w with memory := putLimbs Mem wp.toNat (lf f' K) }
  | 0, i, f, a, ra, hra, hm0, ha, hout, hid => by
    subst hra
    obtain rfl : i = n := by omega
    exact ⟨f, a, ha, hout, hid, rfl⟩
  | m + 1, i, f, a, ra, hra, hmi, ha, hout, hid => by
    subst hra
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hin : i < n := by omega
    have hmb := hm.1
    simp only [limbsOf_length] at hmb
    have hfx : f (i + j) = f0 (i + j) := hout _ (Or.inr (by omega))
    have hlm := load_mod (w := w) f hK hs hm hd hin I
    have hlx := load_lf (w := w) f hK hs (i := i + j) (by omega) I
    rw [hfx] at hlx
    obtain ⟨P, hP⟩ : ∃ P, addD (addD (L2D (f0 (i + j))) (L2D (limbAt Dn i))) (L2D a) = P := ⟨_, rfl⟩
    have h1 : (loD P).val + (hiD P).val * 2 ^ 64 = (f0 (i + j)).val + (limbAt Dn i).val + a.val := by
      rw [← add128_val, hP]; simp only [loD, hiD]; omega
    have ha' : (hiD P).val ≤ 1 := by
      have := (f0 (i + j)).isLt; have := (limbAt Dn i).isLt; have := (loD P).isLt
      by_contra h
      have : 2 * 2 ^ 64 ≤ (hiD P).val * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨f', a', ha'', hout', hid', he⟩ := addback_loop md cnt nW wp mp sh d1w d0w hw qw hK hs hjn
      hm hd f0 w I r0 r1 r2 r4 r5 r7 r8 r10 r11 v1 m (i + 1) (Function.update f (i + j) (loD P))
      (hiD P) _ rfl (by omega) ha'
      (fun k hk => by rw [Function.update_of_ne (by omega)]; exact hout k (by omega))
      (by
        rw [wv_succ, wv_succ, wv_succ, wv_update_out f (Or.inr (by omega)), Nat.zero_add,
          show j + i = i + j by ring, Function.update_self, pow_succ64]
        zify at h1 hid ⊢
        linear_combination hid + (2 : ℤ) ^ (64 * i) * h1)
    refine ⟨f', a', ha'', hout', hid', ?_⟩
    rw [Modulus_reduce.b25.b32.b39.eq_1]
    simp only [has0_eq' n (by omega) (show i < 2 ^ 256 by omega),
      show (0 ≤ i ∧ i < n) = True from eq_true (by omega), decide_true, if_true, Lib.Range_at_0,
      Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      add_lit (show i + j < 2 ^ 256 by omega),
      limb_lit wp (show wp.toNat + 8 * (i + j) < UInt256.size by omega), hlx,
      limb_lit mp (show mp.toNat + 8 * i < UInt256.size by omega), hlm, adc_w, hP, down128_eq,
      store_lf f hK hs (show i + j < K by omega), shr64_eq, down128_limb_eq]
    exact he

end FeProofs.Modexp
