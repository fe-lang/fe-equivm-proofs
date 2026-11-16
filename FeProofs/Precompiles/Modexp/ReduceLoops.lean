import FeProofs.Precompiles.Modexp.TryNew

/-!
# Modexp: the loops of `Modulus::reduce` around the division

`Modulus::reduce(work, count)` works on the limbs of `work` through the raw pointer `wp`, over 12
registers (`r0` … `r11`) that its loops share.  Memory holds `putLimbs Mem wp (lf f K)` (see
`Work.lean`), and each lemma here takes one loop from a state to its exit, for any values of the
registers it does not read:

- `zero_loop9`, `zero_loop50`: `Modulus_reduce.loop` (limbs `count .. n` set to zero when
  `count < n`) and `Modulus_reduce.loop_2.loop_6.loop_7` (limbs `n .. count` cleared at the end);
- `shift_loop`: `Modulus_reduce.loop_8`, the dividend shifted left by `s`, from the top limb down;
- `rem_loop`: `Modulus_reduce.loop_1`, the `n = 1` path, 2-by-1 remainders from the top;
- `denorm_loop`: `Modulus_reduce.loop_2.loop_6`, the remainder shifted back right by `s`, then the
  clearing.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- A limb shifted left by `s` inside 64 bits. -/
def shlL (x : Limb) (s : ℕ) : Limb := ⟨x.val * 2 ^ s % 2 ^ 64, Nat.mod_lt _ (by norm_num)⟩

theorem store_lf0 {w : World} {M : ByteArray} {p K : ℕ} (f : ℕ → Limb) (hK : p + 8 * K ≤ M.size)
    (hs : M.size < UInt256.size) {i : ℕ} (hi : i < K) (I : Env) :
    (mstoreInt (.u 64) (UInt256.ofNat (p + 8 * i)) (UInt256.ofNat 0)).exec I
        { w with memory := putLimbs M p (lf f K) } =
      some (.ok ((), { w with memory := putLimbs M p (lf (Function.update f i 0) K) })) :=
  store_lf f hK hs hi 0 I

theorem add_lit {a b : ℕ} (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := ofNat_add_ofNat h

/-! ## Zeroing -/

/-- **`for i in lo..hi { *limb(wp, i) = 0 }`** before the division (`count < n`). -/
theorem zero_loop9 (wp : UInt256) {Mem : ByteArray} {K lo hi : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size)
    (hs : Mem.size < UInt256.size) (hhi : hi ≤ K) (w : World) (I : Env) (v1 : Lib.MemArray_u64)
    (r0 r1 r2 r3 r4 r5 r6 : UInt256) (r8 r9 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) :
    ∀ m i (f : ℕ → Limb), i + m = hi → lo ≤ i →
      (Modulus_reduce.loop wp r0 r1 r2 r3 r4 r5 r6 ⟨UInt256.ofNat lo, UInt256.ofNat hi⟩ r8 r9 r10 r11 v1
          (UInt256.ofNat i)).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        some (.ok (((), v1), { w with memory := (putLimbs Mem wp.toNat
          (lf (fun k => if i ≤ k ∧ k < hi then 0 else f k) K)) }))
  | 0, i, f, hm, hl => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [Modulus_reduce.loop.eq_1]
    simp only [has_uu (show lo < 2 ^ 256 by omega) (show hi < 2 ^ 256 by omega)
      (show i < 2 ^ 256 by omega), show (lo ≤ i ∧ i < hi) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, ite_false, pure_bind, Fe.M.exec_pure]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr fun k _ => ?_)
    rw [ite_eq_right (by omega)]
  | m + 1, i, f, hm, hl => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [Modulus_reduce.loop.eq_1]
    simp only [has_uu (show lo < 2 ^ 256 by omega) (show hi < 2 ^ 256 by omega)
      (show i < 2 ^ 256 by omega), show (lo ≤ i ∧ i < hi) = True from eq_true (by omega),
      decide_true, ite_true, Lib.Range_Unknown_Unknown_at, Lib.Range_Unknown_Unknown_next,
      next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      limb_lit wp (show wp.toNat + 8 * i < UInt256.size by omega),
      store_lf0 f hK hs (show i < K by omega)]
    rw [zero_loop9 wp hK hs hhi w I v1 r0 r1 r2 r3 r4 r5 r6 r8 r9 r10 r11 m (i + 1) _ (by omega)
      (by omega)]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr ?_)
    intro k _
    by_cases hk : k = i
    · subst hk; simp [show k < hi by omega]
    · rw [Function.update_of_ne hk]
      by_cases h1 : i + 1 ≤ k ∧ k < hi
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- **`for i in lo..hi { *limb(wp, i) = 0 }`** after the division. -/
theorem zero_loop50 (wp : UInt256) {Mem : ByteArray} {K lo hi : ℕ} (hK : wp.toNat + 8 * K ≤ Mem.size)
    (hs : Mem.size < UInt256.size) (hhi : hi ≤ K) (w : World) (I : Env) (v1 : Lib.MemArray_u64)
    (r0 r1 r2 r3 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r8 r9 r10 : Lib.Range_Known_0_Unknown) :
    ∀ m i (f : ℕ → Limb), i + m = hi → lo ≤ i →
      (Modulus_reduce.loop_2.loop_6.loop_7 wp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
          ⟨UInt256.ofNat lo, UInt256.ofNat hi⟩ v1 (UInt256.ofNat i)).exec I
          { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        some (.ok (((), v1), { w with memory := (putLimbs Mem wp.toNat
          (lf (fun k => if i ≤ k ∧ k < hi then 0 else f k) K)) }))
  | 0, i, f, hm, hl => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [Modulus_reduce.loop_2.loop_6.loop_7.eq_1]
    simp only [has_uu (show lo < 2 ^ 256 by omega) (show hi < 2 ^ 256 by omega)
      (show i < 2 ^ 256 by omega), show (lo ≤ i ∧ i < hi) = False from eq_false (by omega),
      decide_false, Bool.false_eq_true, ite_false, pure_bind, Fe.M.exec_pure]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr fun k _ => ?_)
    rw [ite_eq_right (by omega)]
  | m + 1, i, f, hm, hl => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [Modulus_reduce.loop_2.loop_6.loop_7.eq_1]
    simp only [has_uu (show lo < 2 ^ 256 by omega) (show hi < 2 ^ 256 by omega)
      (show i < 2 ^ 256 by omega), show (lo ≤ i ∧ i < hi) = True from eq_true (by omega),
      decide_true, ite_true, Lib.Range_Unknown_Unknown_at, Lib.Range_Unknown_Unknown_next,
      next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      limb_lit wp (show wp.toNat + 8 * i < UInt256.size by omega),
      store_lf0 f hK hs (show i < K by omega)]
    rw [zero_loop50 wp hK hs hhi w I v1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 m (i + 1) _ (by omega)
      (by omega)]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr ?_)
    intro k _
    by_cases hk : k = i
    · subst hk; simp [show k < hi by omega]
    · rw [Function.update_of_ne hk]
      by_cases h1 : i + 1 ≤ k ∧ k < hi
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-! ## The normalising shift -/

/-- The limbs during the normalising shift at `i`: below `i` those of `X`, limb `i` shifted, the
    rest up to `count` those of `X * 2 ^ s`, past `count` those of `F`. -/
def shiftF (X s count i : ℕ) (F : ℕ → Limb) (k : ℕ) : Limb :=
  if k < i then limbAt X k else if k = i then shlL (limbAt X i) s
  else if k ≤ count then limbAt (X * 2 ^ s) k else F k

/-- **The normalising shift** `while i > 0 { w[i] |= w[i-1] >> (64-s); w[i-1] <<= s; i -= 1 }`,
    from `i` down; it exits into `K15`. -/
theorem shift_loop (wp : UInt256) {Mem : ByteArray} {K X s count : ℕ}
    (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hs0 : 0 < s) (hs64 : s < 64)
    (hc : count < K) (F : ℕ → Limb) (w : World) (I : Env)
    (K15 : UInt256 → UInt256 → UInt256 → UInt256 → UInt256 → UInt256 → UInt256 →
      Lib.Range_Unknown_Unknown → Lib.Range_Known_0_Unknown → Lib.Range_Known_0_Unknown →
      Lib.Range_Known_0_Unknown → Lib.Range_Unknown_Unknown → Lib.MemArray_u64 → FeM (Unit × Lib.MemArray_u64))
    (r1 r2 r3 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown) (r8 r9 r10 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ i (f : ℕ → Limb), i ≤ count → (∀ k < K, f k = shiftF X s count i F k) →
      (Modulus_reduce.loop_8 wp (UInt256.ofNat s) K15 (UInt256.ofNat i) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
          v1).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        (K15 (UInt256.ofNat 0) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v1).exec I
          { w with memory := putLimbs Mem wp.toNat (lf (shiftF X s count 0 F) K) }
  | 0, f, _, hf => by
    rw [Modulus_reduce.loop_8.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), lt_irrefl, decide_false, Bool.false_eq_true,
      ite_false]
    rw [lf_congr hf]
  | i + 1, f, hi, hf => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hl1 := load_lf (w := w) f hK hs (i := i + 1) (by omega) I
    have hl0 := load_lf (w := w) f hK hs (i := i) (by omega) I
    rw [hf _ (by omega)] at hl1 hl0
    simp only [shiftF, lt_irrefl, ite_false, ite_true, show i < i + 1 by omega]
      at hl1 hl0
    have e1 : (shlL (limbAt X (i + 1)) s).w ||| (limbAt X i).w >>> UInt256.ofNat (64 - s) =
        (limbAt (X * 2 ^ s) (i + 1)).w := by
      have := (shlL (limbAt X (i + 1)) s).isLt
      have := (limbAt X i).isLt
      rw [limb_shr _ (show 64 - s < 256 by omega), Limb.w,
        lor_lit (by omega) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
      have h := limbAt_shl X hs0 hs64 (show 1 ≤ i + 1 by omega)
      rw [Nat.add_sub_cancel] at h
      simp only [shlL, h]; rfl
    have e2 : IntTy.shl (.u 64) (limbAt X i).w (UInt256.ofNat s) = (shlL (limbAt X i) s).w := by
      rw [shl64_lit _ (by omega)]; rfl
    have hl0' := load_lf (w := w) (Function.update f (i + 1) (limbAt (X * 2 ^ s) (i + 1))) hK hs
      (i := i) (by omega) I
    rw [Function.update_of_ne (show i ≠ i + 1 by omega), hf _ (by omega)] at hl0'
    simp only [shiftF, show i < i + 1 by omega, ite_true] at hl0'
    rw [Modulus_reduce.loop_8.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), toNat_lit (show i + 1 < 2 ^ 256 by omega),
      show 0 < i + 1 by omega, decide_true, ite_true,
      sub_lit (show i + 1 < 2 ^ 256 by omega) (show 1 ≤ i + 1 by omega), Nat.add_sub_cancel,
      limb_lit wp (show wp.toNat + 8 * (i + 1) < UInt256.size by omega),
      limb_lit wp (show wp.toNat + 8 * i < UInt256.size by omega), pure_bind, Fe.M.exec_bind, hl1, hl0,
      sub64_eq hs64, e1, store_lf f hK hs (show i + 1 < K by omega), hl0', e2,
      store_lf _ hK hs (show i < K by omega)]
    apply shift_loop wp hK hs hs0 hs64 hc F w I K15 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v1 i _ (by omega)
    intro k hk
    simp only [Function.update_apply]
    rw [hf k hk]
    simp only [shiftF]
    split_ifs <;> first | omega | (subst_vars; rfl)

/-! ## One-limb divisors -/

/-- A limb shifted right by `s`. -/
def shrL (x : Limb) (s : ℕ) : Limb := ⟨x.val / 2 ^ s, lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt⟩

theorem shr_shrL (x : Limb) {s : ℕ} (hs : s < 256) : x.w >>> UInt256.ofNat s = (shrL x s).w :=
  limb_shr x hs

/-- A write at the pointer itself, limb `0`. -/
theorem store_lf_base {w : World} {M : ByteArray} {p : UInt256} {K : ℕ} (f : ℕ → Limb)
    (hK : p.toNat + 8 * K ≤ M.size) (hs : M.size < UInt256.size) (hK0 : 0 < K) (x : Limb) (I : Env) :
    (mstoreInt (.u 64) p x.w).exec I { w with memory := putLimbs M p.toNat (lf f K) } =
      some (.ok ((), { w with memory := putLimbs M p.toNat (lf (Function.update f 0 x) K) })) := by
  have h := store_lf (w := w) f hK hs hK0 x I
  rwa [Nat.mul_zero, Nat.add_zero, ofNat_toNat] at h

theorem mod_step (W x d : ℕ) : (W % d * 2 ^ 64 + x) % d = (x + 2 ^ 64 * W) % d := by
  rw [Nat.add_comm, Nat.mul_comm]
  exact (((Nat.mod_modEq W d).mul_left _).add_left _)

/-- **The `n = 1` path**: from limb `i` down, the remainder `r` of the limbs `[i, T)` of `f0` by
    `d`, each limb cleared once read; then limb `0` is the remainder shifted right by `s`. -/
theorem rem_loop (md : Exported.Modexp.Modulus) (wp : UInt256) {Mem : ByteArray} {K T s : ℕ}
    (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hT : T ≤ K) (hK0 : 0 < K)
    (hs64 : s < 64) {d : Limb} (hd : 2 ^ 63 ≤ d.val) (hrec : md.reciprocal = (recip21L d hd).w)
    (f0 : ℕ → Limb) (w : World) (I : Env) (r0 r3 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown)
    (r8 r9 r10 : Lib.Range_Known_0_Unknown) (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ i (r : Limb) (f : ℕ → Limb), i ≤ T → r.val = wv f0 i (T - i) % d.val →
      (∀ k < K, f k = if i ≤ k ∧ k < T then 0 else f0 k) →
      ∃ q : Limb, q.val = wv f0 0 T % d.val / 2 ^ s ∧
        (Modulus_reduce.loop_1 md wp (UInt256.ofNat s) d.w r0 r.w (UInt256.ofNat i) r3 r4 r5 r6 r7 r8 r9
            r10 r11 v1).exec I { w with memory := putLimbs Mem wp.toNat (lf f K) } =
          some (.ok (((), v1), { w with memory := (putLimbs Mem wp.toNat
            (lf (Function.update (fun k => if k < T then 0 else f0 k) 0 q) K)) }))
  | 0, r, f, _, hr, hf => by
    refine ⟨shrL r s, by rw [shrL]; simp only [hr, Nat.sub_zero], ?_⟩
    rw [Modulus_reduce.loop_1.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), lt_irrefl, decide_false, Bool.false_eq_true,
      ite_false, shr_shrL r (show s < 256 by omega), Fe.M.exec_bind,
      store_lf_base f hK hs hK0 (shrL r s) I, Fe.M.exec_pure]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr ?_)
    intro k hk
    simp only [Function.update_apply]
    rw [hf k hk]
    split_ifs <;> first | omega | rfl
  | i + 1, r, f, hi, hr, hf => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hdpos : 0 < d.val := by omega
    have hl := load_lf (w := w) f hK hs (i := i) (by omega) I
    rw [hf i (by omega), ite_eq_right (by omega)] at hl
    rw [Modulus_reduce.loop_1.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), toNat_lit (show i + 1 < 2 ^ 256 by omega),
      show 0 < i + 1 by omega, decide_true, ite_true,
      sub_lit (show i + 1 < 2 ^ 256 by omega) (show 1 ≤ i + 1 by omega), Nat.add_sub_cancel,
      limb_lit wp (show wp.toNat + 8 * i < UInt256.size by omega), pure_bind, Fe.M.exec_bind, hl,
      hrec, rem_2by1_eq, store_lf0 f hK hs (show i < K by omega)]
    apply rem_loop md wp hK hs hT hK0 hs64 hd hrec f0 w I r0 r3 r4 r5 r6 r7 r8 r9 r10 r11 v1 i _ _
      (by omega)
    · rw [rem21_eq _ _ _ hd (by rw [hr]; exact Nat.mod_lt _ hdpos), hr, mod_step,
        show T - i = T - (i + 1) + 1 by omega, wv_low]
    · intro k hk
      simp only [Function.update_apply]
      rw [hf k hk]
      split_ifs <;> first | omega | rfl

/-! ## Denormalising and clearing -/

/-- **The denormalising loop** `w[i] = w[i] >> s | w[i+1] << (64 - s)` for `i < n`, from `i` up,
    then the clearing of limbs `n .. count`: the limbs of `V = R * 2 ^ s` become those of `R`,
    with zeros up to `count`. -/
theorem denorm_loop (wp : UInt256) {Mem : ByteArray} {K n count s R : ℕ}
    (hK : wp.toNat + 8 * K ≤ Mem.size) (hs : Mem.size < UInt256.size) (hn : n ≤ count)
    (hcK : count + 1 ≤ K) (hs64 : s < 64) (hR : R < 2 ^ (64 * n)) (F : ℕ → Limb) (w : World) (I : Env)
    (r0 r1 r2 r3 r4 r5 r6 : UInt256) (r7 : Lib.Range_Unknown_Unknown) (r8 r9 : Lib.Range_Known_0_Unknown)
    (r11 : Lib.Range_Unknown_Unknown) (v1 : Lib.MemArray_u64) :
    ∀ m i (f : ℕ → Limb), i + m = n →
      (∀ k < K, f k = if k < i then limbAt R k else if k ≤ n then limbAt (R * 2 ^ s) k else F k) →
      (Modulus_reduce.loop_2.loop_6 (UInt256.ofNat count) (UInt256.ofNat n) wp (UInt256.ofNat s) r0 r1 r2 r3
          r4 r5 r6 r7 r8 r9 ⟨(), UInt256.ofNat n⟩ r11 v1 (UInt256.ofNat i)).exec I
          { w with memory := putLimbs Mem wp.toNat (lf f K) } =
        some (.ok (((), v1), { w with memory := (putLimbs Mem wp.toNat
          (lf (fun k => if k < count + 1 then limbAt R k else F k) K)) }))
  | 0, i, f, hi, hf => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [Modulus_reduce.loop_2.loop_6.eq_1]
    simp only [has0_eq' n (by omega) (show i < 2 ^ 256 by omega),
      show (0 ≤ i ∧ i < n) = False from eq_false (by omega), decide_false, pure_bind,
      Bool.false_eq_true, ite_false, add_lit (show count + 1 < 2 ^ 256 by omega),
      Lib.Range_Unknown_Unknown_start]
    rw [zero_loop50 wp hK hs hcK w I v1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 ⟨(), UInt256.ofNat n⟩
      (count + 1 - n) n f (by omega) le_rfl]
    congr 4
    refine congrArg (putLimbs Mem wp.toNat) (lf_congr ?_)
    intro k hk
    rw [hf k hk]
    have hz : ∀ k, n ≤ k → limbAt R k = 0 := fun k hk' => Fin.ext (by
      simp only [limbAt]
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hR (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      rfl)
    split_ifs <;> first | omega | rfl | (rw [hz k (by omega)])
  | m + 1, i, f, hi, hf => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hV : R * 2 ^ s / 2 ^ s = R := Nat.mul_div_cancel _ (by positivity)
    have hl := load_lf (w := w) f hK hs (i := i) (by omega) I
    rw [hf i (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at hl
    rw [Modulus_reduce.loop_2.loop_6.eq_1]
    simp only [has0_eq' n (by omega) (show i < 2 ^ 256 by omega),
      show (0 ≤ i ∧ i < n) = True from eq_true (by omega), decide_true, ite_true, Lib.Range_at_0,
      Lib.Range_next_0, next_eq (show i + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      limb_lit wp (show wp.toNat + 8 * i < UInt256.size by omega), hl,
      shr_shrL _ (show s < 256 by omega),
      ofNat_eq_iff (show s < 2 ^ 256 by omega) (show 0 < 2 ^ 256 by norm_num)]
    have hnext : ∀ x : Limb, x = limbAt R i →
        (∀ k < K, Function.update f i x k =
          if k < i + 1 then limbAt R k else if k ≤ n then limbAt (R * 2 ^ s) k else F k) := by
      intro x hx k hk
      simp only [Function.update_apply]
      rw [hf k hk]
      split_ifs <;> first | omega | (subst_vars; rfl)
    by_cases hs0 : s = 0
    · subst hs0
      have e : (shrL (limbAt (R * 2 ^ 0) i) 0).w ||| UInt256.ofNat 0 = (limbAt R i).w := by
        rw [Limb.w, lor_lit (lt_trans (shrL _ 0).isLt (by norm_num)) (by norm_num), Nat.or_zero]
        simp only [shrL, pow_zero, Nat.div_one, Nat.mul_one]; rfl
      simp only [decide_true, ite_true, Fe.M.exec_bind, e,
        store_lf f hK hs (show i < K by omega)]
      exact denorm_loop wp hK hs hn hcK hs64 hR F w I r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 v1 m (i + 1) _
        (by omega) (hnext _ rfl)
    · have hl1 := load_lf (w := w) f hK hs (i := i + 1) (by omega) I
      rw [hf (i + 1) (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at hl1
      have e : (shrL (limbAt (R * 2 ^ s) i) s).w |||
          IntTy.shl (.u 64) (limbAt (R * 2 ^ s) (i + 1)).w (UInt256.ofNat (64 - s)) = (limbAt R i).w := by
        have := (limbAt (R * 2 ^ s) i).isLt
        have := (limbAt (R * 2 ^ s) (i + 1)).isLt
        rw [shl64_lit _ (by omega), Limb.w,
          lor_lit (lt_trans (shrL _ s).isLt (by norm_num)) (by omega)]
        have h := limbAt_shr (R * 2 ^ s) (show 0 < s by omega) hs64 i
        rw [hV] at h
        simp only [shrL, h]; rfl
      simp only [show decide (s = 0) = false from decide_eq_false hs0, Bool.false_eq_true, ite_false,
        add_lit (show i + 1 < 2 ^ 256 by omega),
        limb_lit wp (show wp.toNat + 8 * (i + 1) < UInt256.size by omega), pure_bind, Fe.M.exec_bind,
        hl1, sub64_eq hs64, e,
        store_lf f hK hs (show i < K by omega)]
      exact denorm_loop wp hK hs hn hcK hs64 hR F w I r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 v1 m (i + 1) _
        (by omega) (hnext _ rfl)

end FeProofs.Modexp
