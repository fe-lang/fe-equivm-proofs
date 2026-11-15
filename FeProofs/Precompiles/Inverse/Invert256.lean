import FeProofs.Precompiles.Inverse.Invert
import FeProofs.Precompiles.Field.MontCorrect

/-!
# Precompiles: `invert_256` and `Mont::inverse`

`invert_256` cuts four 64-bit limbs into five signed 62-bit ones, runs `invert`, and joins the
result back (`invert_256_spec`); `Mont::inverse` multiplies the inverse of the representation
`x R` by `R³`, which gives the representation of `x⁻¹` (`inverse_rep`).  `modSpec_of` checks a
modulus's `SIGNED_62` and `INV62`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

/-! ## Joining and cutting limbs -/

theorem Limb.val_lor (x y : Limb) : (x ||| y).val = x.val ||| y.val := by
  obtain ⟨x, hx⟩ := x; obtain ⟨y, hy⟩ := y
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 64) hx hy)

theorem lor_add {x y k : ℕ} (hx : x < 2 ^ k) (hy : 2 ^ k ∣ y) : x ||| y = x + y := by
  obtain ⟨z, rfl⟩ := hy
  rw [Nat.lor_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

/-- `x | (y << j)` as a sum, when `x` fits below bit `j`. -/
theorem join_val (x y : Limb) {j : ℕ} (hj : j ≤ 64) (hx : x.val < 2 ^ j) :
    (x ||| y.shl j).val = x.val + y.val * 2 ^ j % 2 ^ 64 := by
  rw [Limb.val_lor]
  show x.val ||| y.val * 2 ^ j % 2 ^ 64 = _
  apply lor_add hx
  have h : (2 : ℕ) ^ j ∣ 2 ^ 64 := pow_dvd_pow 2 hj
  exact (Nat.dvd_mod_iff h).mpr (dvd_mul_left _ _)

theorem shr_val (x : Limb) (k : ℕ) : (x.shr k).val = x.val / 2 ^ k := rfl

theorem sgn_small {x : Limb} (h : x.val < 2 ^ 63) : x.sgn = x.val :=
  sgn_eq (Int.ModEq.refl _) (by have : (0 : ℤ) ≤ x.val := by positivity
                                linarith) (by exact_mod_cast h)

theorem w_shr (x : Limb) (k : ℕ) (hk : k < 2 ^ 64) : x.w >>> UInt256.ofNat k = (x.shr k).w :=
  shr_w x ⟨k, hk⟩

theorem shl_w' (x : Limb) (k : ℕ) (hk : k < 2 ^ 64) :
    IntTy.shl (.u 64) x.w (UInt256.ofNat k) = (x.shl k).w := shl_w x ⟨k, hk⟩

theorem vget4 {α : Type} [Inhabited α] (x0 x1 x2 x3 : α) :
    #v[x0, x1, x2, x3][0]! = x0 ∧ #v[x0, x1, x2, x3][1]! = x1 ∧
    #v[x0, x1, x2, x3][2]! = x2 ∧ #v[x0, x1, x2, x3][3]! = x3 := ⟨rfl, rfl, rfl, rfl⟩

theorem lt4 : (0 : ℕ) < 4 ∧ (1 : ℕ) < 4 ∧ (2 : ℕ) < 4 ∧ (3 : ℕ) < 4 := by decide

/-- The five signed 62-bit limbs `invert_256` cuts four 64-bit ones into. -/
def cut (a : L4) : ℕ → ℤ
  | 0 => (a.l0.val % 2 ^ 62 : ℕ)
  | 1 => ((a.l0.val / 2 ^ 62 + a.l1.val * 2 ^ 2 % 2 ^ 64) % 2 ^ 62 : ℕ)
  | 2 => ((a.l1.val / 2 ^ 60 + a.l2.val * 2 ^ 4 % 2 ^ 64) % 2 ^ 62 : ℕ)
  | 3 => ((a.l2.val / 2 ^ 58 + a.l3.val * 2 ^ 6 % 2 ^ 64) % 2 ^ 62 : ℕ)
  | _ => (a.l3.val / 2 ^ 56 : ℕ)

theorem M62_val : ((4611686018427387903 : Limb)).val = 2 ^ 62 - 1 := rfl

theorem land62 (x : Limb) : (x &&& 4611686018427387903).val = x.val % 2 ^ 62 := by
  rw [Limb.val_land, M62_val, land_low]

theorem cut_eqs (a : L4) :
    (a.l0 &&& 4611686018427387903).sgn = cut a 0 ∧
    ((a.l0.shr 62 ||| a.l1.shl 2) &&& 4611686018427387903).sgn = cut a 1 ∧
    ((a.l1.shr 60 ||| a.l2.shl 4) &&& 4611686018427387903).sgn = cut a 2 ∧
    ((a.l2.shr 58 ||| a.l3.shl 6) &&& 4611686018427387903).sgn = cut a 3 ∧
    (a.l3.shr 56).sgn = cut a 4 := by
  have h0 := a.l0.isLt; have h1 := a.l1.isLt; have h2 := a.l2.isLt; have h3 := a.l3.isLt
  have lt62 : ∀ y : ℕ, y % 2 ^ 62 < 2 ^ 63 := fun y => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sgn_small (by rw [land62]; exact lt62 _), land62]; rfl
  · rw [sgn_small (by rw [land62]; exact lt62 _), land62,
      join_val _ _ (by norm_num) (by rw [shr_val]; omega), shr_val]; rfl
  · rw [sgn_small (by rw [land62]; exact lt62 _), land62,
      join_val _ _ (by norm_num) (by rw [shr_val]; omega), shr_val]; rfl
  · rw [sgn_small (by rw [land62]; exact lt62 _), land62,
      join_val _ _ (by norm_num) (by rw [shr_val]; omega), shr_val]; rfl
  · rw [sgn_small (by rw [shr_val]; omega), shr_val]; rfl

theorem cut_canon (a : L4) : Canon (cut a) := by
  intro i hi
  interval_cases i <;> simp only [cut] <;> constructor <;> push_cast <;> omega

theorem cut_lim (a : L4) : Lim (cut a) := by
  have h3 := a.l3.isLt
  intro i
  rcases Nat.lt_or_ge i 4 with h | h
  · have := cut_canon a i h; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩
    show |((a.l3.val / 2 ^ 56 : ℕ) : ℤ)| ≤ _
    rw [abs_of_nonneg (by positivity)]
    have : a.l3.val / 2 ^ 56 < 2 ^ 8 := by omega
    exact_mod_cast this.le.trans (by norm_num)

theorem val5_cut (a : L4) : val5 (cut a) = Mont.val a := by
  have h0 := a.l0.isLt; have h1 := a.l1.isLt; have h2 := a.l2.isLt; have h3 := a.l3.isLt
  simp only [val5, cut, Mont.val]
  push_cast
  omega

/-- The four 64-bit limbs `invert_256` joins five 62-bit ones into. -/
def join (o : ℕ → ℤ) : L4 :=
  ⟨Limb.ofInt (o 0) ||| (Limb.ofInt (o 1)).shl 62,
   (Limb.ofInt (o 1)).shr 2 ||| (Limb.ofInt (o 2)).shl 60,
   (Limb.ofInt (o 2)).shr 4 ||| (Limb.ofInt (o 3)).shl 58,
   (Limb.ofInt (o 3)).shr 6 ||| (Limb.ofInt (o 4)).shl 56⟩

theorem ofInt_val_of {x : ℤ} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : ((Limb.ofInt x).val : ℤ) = x := by
  rw [Limb.ofInt_val, Int.emod_eq_of_lt h0 h1]

theorem val_join {o : ℕ → ℤ} (ho : Canon o) (h4 : 0 ≤ o 4) (h4' : o 4 < 2 ^ 8) :
    (Mont.val (join o) : ℤ) = val5 o := by
  have e : ∀ i < 4, ((Limb.ofInt (o i)).val : ℤ) = o i := fun i hi =>
    ofInt_val_of (ho i hi).1 (by linarith [(ho i hi).2])
  have e4 : ((Limb.ofInt (o 4)).val : ℤ) = o 4 := ofInt_val_of h4 (by linarith)
  have b : ∀ i < 4, (Limb.ofInt (o i)).val < 2 ^ 62 := fun i hi => by
    have := (ho i hi).2; rw [← e i hi] at this; exact_mod_cast this
  have b4 : (Limb.ofInt (o 4)).val < 2 ^ 8 := by rw [← e4] at h4'; exact_mod_cast h4'
  have hN : Mont.val (join o) = (Limb.ofInt (o 0)).val + 2 ^ 62 * (Limb.ofInt (o 1)).val +
      2 ^ 124 * (Limb.ofInt (o 2)).val + 2 ^ 186 * (Limb.ofInt (o 3)).val +
      2 ^ 248 * (Limb.ofInt (o 4)).val := by
    have := b 0 (by decide); have := b 1 (by decide); have := b 2 (by decide)
    have := b 3 (by decide)
    unfold join Mont.val
    rw [join_val _ _ (by norm_num) (by omega),
      join_val _ _ (by norm_num) (by rw [shr_val]; omega),
      join_val _ _ (by norm_num) (by rw [shr_val]; omega),
      join_val _ _ (by norm_num) (by rw [shr_val]; omega),
      shr_val, shr_val, shr_val]
    omega
  rw [hN]
  push_cast
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e4]
  rfl

theorem top_nonneg {o : ℕ → ℤ} (ho : Canon o) (h0 : 0 ≤ val5 o) (h1 : val5 o < 2 ^ 256) :
    0 ≤ o 4 ∧ o 4 < 2 ^ 8 := by
  have := ho 0 (by decide); have := ho 1 (by decide); have := ho 2 (by decide)
  have := ho 3 (by decide)
  unfold val5 at h0 h1
  constructor <;> omega

/-- `invert_256` on a canonical `x < m`: every run diverges or returns `x⁻¹ mod m`, `0` for
`x = 0`, the world unchanged. -/
theorem invert_256_spec {m : ℕ → ℤ} {inv : Limb} (hm : ModSpec m inv) (hm1 : 1 < val5 m)
    (a : L4) (ha : (Mont.val a : ℤ) < val5 m)
    (hcop : (Mont.val a : ℤ) ≠ 0 → IsCoprime (val5 m) (Mont.val a)) (env : Env) (w : World) :
    (invert_256 #v[a.l0.w, a.l1.w, a.l2.w, a.l3.w] (vec5 m) inv.w).exec env w = none ∨
      ∃ c : L4, (invert_256 #v[a.l0.w, a.l1.w, a.l2.w, a.l3.w] (vec5 m) inv.w).exec env w =
          some (.ok (#v[c.l0.w, c.l1.w, c.l2.w, c.l3.w], w)) ∧ (Mont.val c : ℤ) < val5 m ∧
        (if (Mont.val a : ℤ) = 0 then Mont.val c = 0 else (Mont.val c : ℤ) * Mont.val a ≡ 1 [ZMOD val5 m]) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := cut_eqs a
  simp only [invert_256, invert_256_k1, invert_256_k2, invert_256_k3, invert_256_k4, invert_256_k5,
    checkIndex, idx_lits, pure_bind, M62_eq, land_w, w_shr _ _ (by decide : 62 < 2 ^ 64),
    w_shr _ _ (by decide : 60 < 2 ^ 64), w_shr _ _ (by decide : 58 < 2 ^ 64),
    w_shr _ _ (by decide : 56 < 2 ^ 64), shl_w' _ _ (by decide : 2 < 2 ^ 64),
    shl_w' _ _ (by decide : 4 < 2 ^ 64), shl_w' _ _ (by decide : 6 < 2 ^ 64), lor_w,
    downcast_u64_i64_w, vget4, vget5, lt4, lt5, ite_true, c0, c1, c2, c3, c4]
  have hv := val5_cut a
  rw [Fe.M.exec_bind]
  rcases invert_5_spec hm hm1 (cut_canon a) (cut_lim a) (by rw [hv]; exact Int.natCast_nonneg _) (by rw [hv]; exact ha)
    (by rw [hv]; exact hcop) env w with h | ⟨out, h, hco, h0, h1, hinv⟩
  · simp only [vec5] at h
    rw [h]; exact Or.inl rfl
  · simp only [vec5] at h
    rw [h]
    have ht := top_nonneg hco h0 (by linarith [hm.lt])
    simp only [vget5, downcast_i64_u64_I, pure_bind, lor_w, w_shr _ _ (by decide : 2 < 2 ^ 64),
      w_shr _ _ (by decide : 4 < 2 ^ 64), w_shr _ _ (by decide : 6 < 2 ^ 64),
      shl_w' _ _ (by decide : 62 < 2 ^ 64), shl_w' _ _ (by decide : 60 < 2 ^ 64),
      shl_w' _ _ (by decide : 58 < 2 ^ 64), shl_w' _ _ (by decide : 56 < 2 ^ 64), Fe.M.exec_pure]
    have hj := val_join hco ht.1 ht.2
    refine Or.inr ⟨join out, rfl, by rw [hj]; exact h1, ?_⟩
    rw [← hv]
    split
    · rename_i hz; rw [ite_eq_left hz] at hinv; exact_mod_cast hj.trans hinv
    · rename_i hz; rw [ite_eq_right hz] at hinv; rw [hj]; exact hinv

/-! ## `Mont::inverse` -/

/-- From an inverse of the representation `a = x R` and `R3 = R ^ 3 mod p`, `mul` gives the
representation of `x⁻¹`. -/
theorem inverse_rep {K : Modulus} (hK : K.Valid) [Fact K.p.Prime] {R3 : ℕ}
    (hR3 : R3 = (2 ^ 256) ^ 3 % K.p) {a c : L4} {x : ZMod K.p} (ha : Mont.Rep K a x)
    (hc : Mont.val c < K.p)
    (hinv : if (Mont.val a : ℤ) = 0 then Mont.val c = 0 else (Mont.val c : ℤ) * Mont.val a ≡ 1 [ZMOD K.p]) :
    Mont.Rep K (Mont.mul K c (Mont.raw R3)) x⁻¹ := by
  have hpl := K.p_lt
  have hp0 : 0 < K.p := (Fact.out : K.p.Prime).pos
  have hR3' : Mont.val (Mont.raw R3) = R3 := Mont.val_raw (by rw [hR3]; exact lt_trans (Nat.mod_lt _ hp0) hpl)
  obtain ⟨hlt, hm⟩ := Mont.mul_spec hK c (Mont.raw R3) hc
  refine ⟨hlt, (Mont.R_isUnit hK).mul_right_cancel ?_⟩
  rw [hm, hR3', hR3, ZMod.natCast_mod, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  by_cases hz : (Mont.val a : ℤ) = 0
  · rw [ite_eq_left hz] at hinv
    have hx : x = 0 := by
      have := ha.2
      rw [show Mont.val a = 0 by exact_mod_cast hz, Nat.cast_zero] at this
      exact ((Mont.R_isUnit hK).mul_left_eq_zero.mp this.symm)
    rw [hinv, hx, inv_zero]; simp
  · rw [ite_eq_right hz] at hinv
    have hc' : (Mont.val c : ZMod K.p) * Mont.val a = 1 := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hinv
      push_cast at this; exact this
    rw [ha.2] at hc'
    have hx : x ≠ 0 := by rintro rfl; simp at hc'
    have hR := (Mont.R_isUnit hK).ne_zero
    have : (Mont.val c : ZMod K.p) = (x * 2 ^ 256)⁻¹ := eq_inv_of_mul_eq_one_left hc'
    rw [this, mul_inv]
    generalize (2 : ZMod K.p) ^ 256 = R at hR ⊢
    rw [show R ^ 3 = R * (R * R) by ring, mul_assoc, inv_mul_cancel_left₀ hR]
    ring

theorem coprime_of_lt {p a : ℕ} (hp : p.Prime) (h0 : (a : ℤ) ≠ 0) (h1 : a < p) :
    IsCoprime (p : ℤ) a := by
  rw [Nat.isCoprime_iff_coprime]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)

theorem modSpec_of {m : ℕ → ℤ} {inv : Limb} {q : ℕ} (hv : val5 m = q)
    (hc : ∀ i < 4, 0 ≤ m i ∧ m i < 2 ^ 62) (hl : ∀ i, |m i| ≤ 2 ^ 62) (ht : |m 4| ≤ 2 ^ 8)
    (hq : 0 < q ∧ q < 2 ^ 256 ∧ q % 2 = 1) (hi : m 0 * inv.val ≡ 1 [ZMOD 2 ^ 62]) :
    ModSpec m inv :=
  ⟨hc, hl, ht, by rw [hv]; exact_mod_cast hq.1, by rw [hv]; exact_mod_cast hq.2.1,
    by rw [hv]; exact_mod_cast hq.2.2, hi⟩

end FeProofs.Precompiles
