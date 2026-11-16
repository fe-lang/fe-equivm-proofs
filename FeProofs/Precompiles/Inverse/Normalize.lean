import FeProofs.Precompiles.Inverse.UpdateDE
import Fe.EVM.Entry

/-!
# Precompiles: `is_zero`, `add_if_negative`, `carry` and `normalize`

The helpers that finish `invert`, on five limbs held as integers.  `add_if_negative` adds the
modulus when the top limb is negative, `carry` brings every limb but the top one into
`[0, 2 ^ 62)` without changing the value, and `normalize` uses them to return `sign · r mod m`
in `[0, m)` for `r ∈ (-2m, m)` (`normalize_spec`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

/-- The word vector of five integer limbs. -/
abbrev vec5 (a : ℕ → ℤ) : Vector UInt256 5 := #v[I (a 0), I (a 1), I (a 2), I (a 3), I (a 4)]

/-- `i64` words in range, in the form the helpers need. -/
def R64 (x : ℤ) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

theorem bmod64_of_R64 {x : ℤ} (h : R64 x) : x.bmod (2 ^ 64) = x := by
  apply Int.bmod_eq_of_le <;> norm_num <;> [exact h.1; exact h.2]

theorem R64_wide {x : ℤ} (h : R64 x) : -2 ^ 255 ≤ x ∧ x < 2 ^ 255 := by
  obtain ⟨h1, h2⟩ := h; constructor <;> linarith

theorem addW64r {x y : ℤ} (hx : R64 x) (hy : R64 y) (h : R64 (x + y)) :
    IntTy.addW (.i 64) (I x) (I y) = I (x + y) := by
  rw [addW_i 64 (by decide) (R64_wide hx).1 (R64_wide hx).2 (R64_wide hy).1 (R64_wide hy).2,
    bmod64_of_R64 h]

theorem subW64r {x y : ℤ} (hx : R64 x) (hy : R64 y) (h : R64 (x - y)) :
    IntTy.subW (.i 64) (I x) (I y) = I (x - y) := by
  rw [subW_i 64 (by decide) (R64_wide hx).1 (R64_wide hx).2 (R64_wide hy).1 (R64_wide hy).2,
    bmod64_of_R64 h]

theorem shr62 {x : ℤ} (h : R64 x) :
    IntTy.shr (.i 64) (I x) (UInt256.ofNat 62) = I (x / 2 ^ 62) := by
  rw [shr_i 64 (by decide) (R64_wide h).1 (R64_wide h).2 (by decide)]
  apply congrArg I
  apply Int.bmod_eq_of_le <;> norm_num <;> obtain ⟨h1, h2⟩ := h <;> omega

theorem I_xor_neg_one (x : ℤ) : I x ^^^ I (-1) = I (-1 - x) := by
  apply word_eq_of_toNat
  have h := congrArg BitVec.toNat (BitVec.xor_allOnes (x := (BitVec.ofFin (I x).val : BitVec 256)))
  simp only [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_not, BitVec.toNat_ofFin] at h
  change (I x).toNat ^^^ (2 ^ 256 - 1) = 2 ^ 256 - 1 - (I x).toNat at h
  change ((I x).toNat ^^^ (I (-1)).toNat) % 2 ^ 256 = _
  rw [show (I (-1)).toNat = 2 ^ 256 - 1 by rw [I_toNat]; rfl, h,
    Nat.mod_eq_of_lt (by have := I_toNat_lt x; omega)]
  have h1 := I_toNat_cast x
  have h2 := I_toNat_cast (-1 - x)
  have h3 := I_toNat_lt x
  have h4 := Int.emod_emod_of_dvd x (dvd_refl ((2 : ℤ) ^ 256))
  zify [show (I x).toNat ≤ 2 ^ 256 - 1 by omega]
  rw [h2, h1]
  omega

theorem I_xor_zero (x : ℤ) : I x ^^^ I 0 = I x := by
  apply word_eq_of_toNat
  change ((I x).toNat ^^^ (I 0).toNat) % 2 ^ 256 = _
  rw [show (I 0).toNat = 0 from rfl, Nat.xor_zero, Nat.mod_eq_of_lt (I_toNat_lt x)]

/-! ## `is_zero` -/

theorem I_eq_zero_iff {x : ℤ} (h : R64 x) : I x = UInt256.ofNat 0 ↔ x = 0 := by
  constructor
  · intro hx
    have := congrArg UInt256.toNat hx
    rw [toNat_lit (by decide)] at this
    have h1 := I_toNat_cast x
    rw [this] at h1
    obtain ⟨a, b⟩ := h
    omega
  · rintro rfl; rfl

theorem is_zero_5_eq (a : ℕ → ℤ) (ha : ∀ i, R64 (a i)) :
    is_zero_5 (vec5 a) = pure (decide (a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0)) := by
  simp only [is_zero_5]
  have hadd : ∀ k < 5, checkedAdd (UInt256.ofNat k) (UInt256.ofNat 1) = pure (UInt256.ofNat (k + 1)) := by
    intro k hk
    unfold checkedAdd
    rw [toNat_lit (by omega), toNat_lit (by decide), ite_eq_right (by change ¬ 2 ^ 256 ≤ _; omega)]
    congr 1
    exact (Fe.EVM.ofNat_add_ofNat (by change k + 1 < 2 ^ 256; omega))
  have a0 : checkedAdd (UInt256.ofNat 0) (UInt256.ofNat 1) = pure (UInt256.ofNat 1) := hadd 0 (by decide)
  have a1 : checkedAdd (UInt256.ofNat 1) (UInt256.ofNat 1) = pure (UInt256.ofNat 2) := hadd 1 (by decide)
  have a2 : checkedAdd (UInt256.ofNat 2) (UInt256.ofNat 1) = pure (UInt256.ofNat 3) := hadd 2 (by decide)
  have a3 : checkedAdd (UInt256.ofNat 3) (UInt256.ofNat 1) = pure (UInt256.ofNat 4) := hadd 3 (by decide)
  have a4 : checkedAdd (UInt256.ofNat 4) (UInt256.ofNat 1) = pure (UInt256.ofNat 5) := hadd 4 (by decide)
  iterate 6
    rw [is_zero_5.loop.eq_1]
    simp only [vec5, idx_lits, vget5, lt5, checkIndex, pure_bind, ite_true, decide_true, decide_false,
      ite_false, ne_eq, I_eq_zero_iff (ha _), decide_not, a0, a1, a2, a3, a4]
  by_cases h0 : a 0 = 0 <;> by_cases h1 : a 1 = 0 <;> by_cases h2 : a 2 = 0 <;>
    by_cases h3 : a 3 = 0 <;> by_cases h4 : a 4 = 0 <;> simp [h0, h1, h2, h3, h4]

/-! ## `add_if_negative` and `carry` -/

theorem zero_add_one_lit : UInt256.ofNat 0 + UInt256.ofNat 1 = UInt256.ofNat 1 := by decide

theorem set5 {α : Type} (x0 x1 x2 x3 x4 y : α) :
    (#v[x0, x1, x2, x3, x4]).set! 0 y = #v[y, x1, x2, x3, x4] ∧
    (#v[x0, x1, x2, x3, x4]).set! 1 y = #v[x0, y, x2, x3, x4] ∧
    (#v[x0, x1, x2, x3, x4]).set! 2 y = #v[x0, x1, y, x3, x4] ∧
    (#v[x0, x1, x2, x3, x4]).set! 3 y = #v[x0, x1, x2, y, x4] ∧
    (#v[x0, x1, x2, x3, x4]).set! 4 y = #v[x0, x1, x2, x3, y] := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `add_if_negative`: add `m` when the top limb is negative. -/
def addNeg (r m : ℕ → ℤ) (i : ℕ) : ℤ := r i + if r 4 < 0 then m i else 0

/-- `carry`: every limb but the top one into `[0, 2 ^ 62)`. -/
def carryT (r : ℕ → ℤ) : ℕ → ℤ
  | 0 => r 0
  | k + 1 => r (k + 1) + carryT r k / 2 ^ 62

def carryL (r : ℕ → ℤ) (i : ℕ) : ℤ := if i < 4 then carryT r i % 2 ^ 62 else carryT r 4

theorem I_land_if (y : ℤ) (c : Prop) [Decidable c] :
    I y &&& I (if c then -1 else 0) = I (if c then y else 0) := I_land_sign y c

theorem sign63 {x : ℤ} (h : R64 x) :
    IntTy.shr (.i 64) (I x) (UInt256.ofNat 63) = I (if x < 0 then -1 else 0) := shr63 h.1 h.2

/-- Limbs well inside `i64`. -/
def Small (r : ℕ → ℤ) : Prop := ∀ i ≤ 4, -2 ^ 62 < r i ∧ r i < 2 ^ 62

theorem R64_of_small {x : ℤ} (h : -2 ^ 62 < x ∧ x < 2 ^ 62) : R64 x := by
  obtain ⟨a, b⟩ := h; constructor <;> linarith

theorem add_if_negative_eq (r m : ℕ → ℤ) (hr : Small r) (hm : Small m) :
    add_if_negative_5 (vec5 r) (vec5 m) = pure (vec5 (addNeg r m)) := by
  have hs : ∀ i ≤ 4, IntTy.addW (.i 64) (I (r i)) (I (if r 4 < 0 then m i else 0)) =
      I (addNeg r m i) := by
    intro i hi
    have := hr i hi; have := hm i hi
    refine addW64r (R64_of_small (hr i hi)) ?_ ?_
    · split; exact R64_of_small (hm i hi); exact ⟨by norm_num, by norm_num⟩
    · unfold R64; split <;> constructor <;> linarith
  simp only [add_if_negative_5, vec5, idx_lits, vget5, lt5, checkIndex, pure_bind, ite_true,
    sign63 (R64_of_small (hr 4 le_rfl))]
  iterate 6
    rw [add_if_negative_5.loop.eq_1]
    simp only [idx_lits, zero_add_one_lit, vget5, lt5, checkIndex, pure_bind, ite_true, ite_false,
      decide_true, decide_false, Bool.false_eq_true, I_land_if, hs 0 (by decide), hs 1 (by decide),
      hs 2 (by decide), hs 3 (by decide), hs 4 (by decide), set5]

/-- Limbs with room for `carry`. -/
def Mid (r : ℕ → ℤ) : Prop := ∀ i ≤ 4, -2 ^ 63 + 2 ≤ r i ∧ r i ≤ 2 ^ 63 - 2

theorem div62_range {x : ℤ} (h : R64 x) : -2 ≤ x / 2 ^ 62 ∧ x / 2 ^ 62 ≤ 1 := by
  obtain ⟨a, b⟩ := h; constructor <;> omega

theorem R64_carryT {r : ℕ → ℤ} (hr : Mid r) : ∀ k ≤ 4, R64 (carryT r k)
  | 0, _ => by
    show R64 (r 0)
    exact ⟨by linarith [(hr 0 (by omega)).1], by linarith [(hr 0 (by omega)).2]⟩
  | k + 1, hk => by
    have := div62_range (R64_carryT hr k (by omega))
    have := hr (k + 1) hk
    show R64 (r (k + 1) + carryT r k / 2 ^ 62)
    constructor <;> linarith

theorem R64_of_abs {x : ℤ} (h : |x| ≤ 2 ^ 63 - 1) : R64 x := by
  rw [abs_le] at h; constructor <;> linarith

theorem carry_5_eq (r : ℕ → ℤ) (hr : Mid r) : carry_5 (vec5 r) = pure (vec5 (carryL r)) := by
  have hc := R64_carryT hr
  have hs : ∀ k ≤ 3, IntTy.addW (.i 64) (I (r (k + 1)))
      (IntTy.shr (.i 64) (I (carryT r k)) (UInt256.ofNat 62)) = I (carryT r (k + 1)) := by
    intro k hk
    rw [shr62 (hc k (by omega))]
    have hq := div62_range (hc k (by omega))
    exact addW64r ⟨by linarith [(hr (k + 1) (by omega)).1], by linarith [(hr (k + 1) (by omega)).2]⟩
      ⟨by linarith, by linarith⟩ (hc (k + 1) (by omega))
  have h0 : I (r 0) = I (carryT r 0) := rfl
  simp only [carry_5, vec5, h0]
  iterate 5
    rw [carry_5.loop.eq_1]
    simp only [idx_lits, zero_add_one_lit, vget5, lt5, checkIndex, pure_bind, ite_true, ite_false,
      decide_true, decide_false, Bool.false_eq_true, hs 0 (by decide), hs 1 (by decide),
      hs 2 (by decide), hs 3 (by decide), set5, M62_SIGNED_eq, I_land_M62]
  rfl

/-- `normalize`'s negation, limb by limb. -/
def negL (c : Prop) [Decidable c] (r : ℕ → ℤ) (i : ℕ) : ℤ := if c then -r i else r i

theorem xor_sub_sign {x : ℤ} (c : Prop) [Decidable c] (hx : -2 ^ 63 + 2 ≤ x ∧ x ≤ 2 ^ 63 - 2) :
    IntTy.subW (.i 64) (I x ^^^ I (if c then -1 else 0)) (I (if c then -1 else 0)) =
      I (if c then -x else x) := by
  split
  · rw [I_xor_neg_one, subW64r ⟨by linarith [hx.2], by linarith [hx.1]⟩ ⟨by norm_num, by norm_num⟩
      ⟨by linarith [hx.2], by linarith [hx.1]⟩]
    ring_nf
  · rw [I_xor_zero, subW64r ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by norm_num, by norm_num⟩
      ⟨by linarith [hx.1], by linarith [hx.2]⟩, sub_zero]

theorem Mid_addNeg {r m : ℕ → ℤ} (hr : Small r) (hm : Small m) : Mid (addNeg r m) := by
  intro i hi
  have := hr i hi; have := hm i hi
  unfold addNeg
  split <;> constructor <;> linarith

theorem Mid_negL {r : ℕ → ℤ} (c : Prop) [Decidable c] (hr : Mid r) : Mid (negL c r) := by
  intro i hi
  have := hr i hi
  unfold negL
  split <;> constructor <;> linarith

/-- `normalize` as its four passes. -/
theorem normalize_5_eq (r m : ℕ → ℤ) (s : ℤ) (hr : Small r) (hm : Small m) (hs : R64 s)
    (h2 : Small (carryL (negL (s < 0) (addNeg r m)))) :
    normalize_5 (vec5 r) (I s) (vec5 m) =
      pure (vec5 (carryL (addNeg (carryL (negL (s < 0) (addNeg r m))) m))) := by
  have hmid := Mid_addNeg hr hm
  have hn : ∀ i ≤ 4, IntTy.subW (.i 64) (I (addNeg r m i) ^^^ I (if s < 0 then -1 else 0))
      (I (if s < 0 then -1 else 0)) = I (negL (s < 0) (addNeg r m) i) :=
    fun i hi => xor_sub_sign (s < 0) (hmid i hi)
  have hc1 := carry_5_eq _ (Mid_negL (s < 0) hmid)
  have ha2 := add_if_negative_eq _ _ h2 hm
  have hc2 := carry_5_eq _ (Mid_addNeg h2 hm)
  simp only [normalize_5, add_if_negative_eq r m hr hm, pure_bind, sign63 hs]
  simp only [vec5] at hc1 ha2 hc2 ⊢
  iterate 6
    rw [normalize_5.loop.eq_1]
    simp only [idx_lits, zero_add_one_lit, vget5, lt5, checkIndex, pure_bind, ite_true, ite_false,
      decide_true, decide_false, Bool.false_eq_true, hn 0 (by decide), hn 1 (by decide),
      hn 2 (by decide), hn 3 (by decide), hn 4 (by decide), set5]
  simp only [hc1, pure_bind, ha2, hc2]

/-! ## What the passes compute -/

/-- Canonical limbs: all but the top one in `[0, 2 ^ 62)`. -/
def Canon (a : ℕ → ℤ) : Prop := ∀ i < 4, 0 ≤ a i ∧ a i < 2 ^ 62

theorem val5_addNeg (r m : ℕ → ℤ) :
    val5 (addNeg r m) = val5 r + if r 4 < 0 then val5 m else 0 := by
  unfold val5 addNeg; split <;> ring

theorem val5_negL (c : Prop) [Decidable c] (r : ℕ → ℤ) :
    val5 (negL c r) = if c then -val5 r else val5 r := by
  unfold val5 negL; split <;> ring

theorem val5_carryL (r : ℕ → ℤ) : val5 (carryL r) = val5 r := by
  have e : ∀ k, carryT r k = 2 ^ 62 * (carryT r k / 2 ^ 62) + carryT r k % 2 ^ 62 :=
    fun k => (Int.mul_ediv_add_emod _ _).symm
  have c1 : carryT r 1 = r 1 + carryT r 0 / 2 ^ 62 := rfl
  have c2 : carryT r 2 = r 2 + carryT r 1 / 2 ^ 62 := rfl
  have c3 : carryT r 3 = r 3 + carryT r 2 / 2 ^ 62 := rfl
  have c4 : carryT r 4 = r 4 + carryT r 3 / 2 ^ 62 := rfl
  have c0 : carryT r 0 = r 0 := rfl
  simp only [val5, carryL, show (0 : ℕ) < 4 by decide, show (1 : ℕ) < 4 by decide,
    show (2 : ℕ) < 4 by decide, show (3 : ℕ) < 4 by decide, show ¬ (4 : ℕ) < 4 by decide,
    ite_true, ite_false]
  linear_combination -e 0 - 2 ^ 62 * e 1 - 2 ^ 124 * e 2 - 2 ^ 186 * e 3 + 2 ^ 62 * c1 +
    2 ^ 124 * c2 + 2 ^ 186 * c3 + 2 ^ 248 * c4 + c0

theorem canon_carryL (r : ℕ → ℤ) : Canon (carryL r) := by
  intro i hi
  simp only [carryL, hi, ite_true]
  exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- Canonical limbs of a value in `(-2 ^ 256, 2 ^ 256)` have a small top limb. -/
theorem top_small {a : ℕ → ℤ} (ha : Canon a) (h1 : -2 ^ 257 < val5 a) (h2 : val5 a < 2 ^ 257) :
    -2 ^ 10 ≤ a 4 ∧ a 4 ≤ 2 ^ 9 := by
  have h0 := ha 0 (by decide); have h1' := ha 1 (by decide)
  have h2' := ha 2 (by decide); have h3 := ha 3 (by decide)
  unfold val5 at h1 h2
  constructor <;> omega

theorem small_of_canon {a : ℕ → ℤ} (ha : Canon a) (h1 : -2 ^ 257 < val5 a) (h2 : val5 a < 2 ^ 257) :
    Small a := by
  intro i hi
  have ht := top_small ha h1 h2
  rcases Nat.lt_or_ge i 4 with h | h
  · have := ha i h; constructor <;> linarith
  · obtain rfl : i = 4 := by omega
    constructor <;> linarith [ht.1, ht.2]

/-- `normalize`: for `r ∈ (-2m, m)` on canonical limbs, `± r mod m` on canonical limbs, the sign
being that of the top limb `s` of `f`. -/
theorem normalize_spec (r m : ℕ → ℤ) (s : ℤ) (hr : Canon r) (hm : Canon m) (hs : R64 s)
    (hM : 0 < val5 m) (hM2 : val5 m < 2 ^ 256) (hR1 : -2 * val5 m < val5 r)
    (hR2 : val5 r < val5 m) :
    ∃ out, normalize_5 (vec5 r) (I s) (vec5 m) = pure (vec5 out) ∧ Canon out ∧
      0 ≤ val5 out ∧ val5 out < val5 m ∧
      val5 out ≡ (if s < 0 then -val5 r else val5 r) [ZMOD val5 m] := by
  have hrs := small_of_canon hr (by linarith) (by linarith)
  have hms := small_of_canon hm (by linarith) (by linarith)
  have hsg := val5_neg_iff hr
  have hb1 : -val5 m < val5 (addNeg r m) ∧ val5 (addNeg r m) < val5 m := by
    rw [val5_addNeg]
    by_cases h : r 4 < 0
    · have := hsg.mpr h; rw [ite_eq_left h]; constructor <;> linarith
    · have : ¬ val5 r < 0 := fun h' => h (hsg.mp h')
      rw [ite_eq_right h]; constructor <;> linarith
  have hb2 : -val5 m < val5 (negL (s < 0) (addNeg r m)) ∧
      val5 (negL (s < 0) (addNeg r m)) < val5 m := by
    rw [val5_negL]; split <;> constructor <;> linarith [hb1.1, hb1.2]
  have hC1 := canon_carryL (negL (s < 0) (addNeg r m))
  have hvC1 := val5_carryL (negL (s < 0) (addNeg r m))
  have h2 : Small (carryL (negL (s < 0) (addNeg r m))) :=
    small_of_canon hC1 (by rw [hvC1]; linarith [hb2.1]) (by rw [hvC1]; linarith [hb2.2])
  refine ⟨_, normalize_5_eq r m s hrs hms hs h2, canon_carryL _, ?_⟩
  rw [val5_carryL, val5_addNeg, hvC1]
  have hsg2 := val5_neg_iff hC1
  rw [hvC1] at hsg2
  have hc : val5 (negL (s < 0) (addNeg r m)) ≡ (if s < 0 then -val5 r else val5 r)
      [ZMOD val5 m] := by
    rw [val5_negL, val5_addNeg]
    split_ifs <;> simp [Int.ModEq, Int.add_emod_right]
  by_cases h : carryL (negL (s < 0) (addNeg r m)) 4 < 0
  · have := hsg2.mpr h
    rw [ite_eq_left h]
    refine ⟨by linarith [hb2.1], by linarith, ?_⟩
    exact (Int.ModEq.trans (by simp [Int.ModEq]) hc)
  · have : ¬ val5 (negL (s < 0) (addNeg r m)) < 0 := fun h' => h (hsg2.mp h')
    rw [ite_eq_right h, _root_.add_zero]
    exact ⟨by linarith, hb2.2, hc⟩

end FeProofs.Precompiles
