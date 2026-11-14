import FeProofs.Ecrecover.MontCorrect

/-!
# Ecrecover: `pow`

`Mont::pow` is square-and-multiply over the 256 bits of the exponent, most significant first.
`Mont.pow` is the loop as a pure function (`powLoop`, with `k` bits to go), `pow_Base` shows the
exported `Mont_pow_Base` is `pure` of it, and `pow_rep` that it computes `x ^ e`.  The loop
counts down from 256, so the exported fixpoint returns on every input.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ecrecover

namespace Mont

variable (K : Modulus)

/-- The loop of `pow` with `k` bits of the exponent `e` to go: square, then multiply by `a`
when bit `k - 1` is set. -/
def powLoop (a : L4) (e : ℕ) : ℕ → L4 → L4
  | 0, r => r
  | k + 1, r => powLoop a e k (if e / 2 ^ k % 2 = 1 then mul K (mul K r r) a else mul K r r)

/-- `pow`: `a ^ e` from `one`, over 256 bits. -/
def pow (a : L4) (e : ℕ) : L4 := powLoop K a e 256 (new K 1)

variable {K}

theorem powLoop_rep (hK : K.Valid) {a : L4} {x : ZMod K.p} (ha : Rep K a x) (e : ℕ) :
    ∀ k r y, Rep K r y → Rep K (powLoop K a e k r) (y ^ 2 ^ k * x ^ (e % 2 ^ k))
  | 0, r, y, hr => by simpa [powLoop, Nat.mod_one] using hr
  | k + 1, r, y, hr => by
    unfold powLoop
    have hsq := mul_rep hK hr hr
    split_ifs with hb
    · convert powLoop_rep hK ha e k _ _ (mul_rep hK hsq ha) using 1
      rw [Nat.mod_pow_succ, hb]; ring
    · have hb0 : e / 2 ^ k % 2 = 0 := by have := Nat.mod_two_eq_zero_or_one (e / 2 ^ k); omega
      convert powLoop_rep hK ha e k _ _ hsq using 1
      rw [Nat.mod_pow_succ, hb0]; ring

/-- `pow a e` represents `x ^ e`, for an exponent below `2 ^ 256`. -/
theorem pow_rep (hK : K.Valid) (hR : K.R2 = 2 ^ 512 % K.p) (h1 : 1 < K.p) {a : L4}
    {x : ZMod K.p} (ha : Rep K a x) {e : ℕ} (he : e < 2 ^ 256) : Rep K (pow K a e) (x ^ e) := by
  have := powLoop_rep hK ha e 256 _ _ (one_rep hK hR h1)
  rwa [one_pow, one_mul, Nat.mod_eq_of_lt he] at this

end Mont

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

theorem sub_one_u64 {k : ℕ} (hk : k + 1 < 2 ^ 64) :
    IntTy.sub (.u 64) (UInt256.ofNat (k + 1)) (UInt256.ofNat 1) = pure (UInt256.ofNat k) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show k + 1 < 2 ^ 256 by omega), toNat_lit (show 1 < 2 ^ 256 by decide)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

theorem land_one_toNat (x : UInt256) : (x &&& UInt256.ofNat 1).toNat = x.toNat % 2 := by
  change (UInt256.land x _).toNat = _
  rw [uland_toNat, toNat_lit (by decide), Nat.and_one_is_mod]

/-- Bit `k` of a word, as `pow` tests it. -/
theorem bit_test (e : UInt256) {k : ℕ} (hk : k < 256) :
    decide (e >>> UInt256.ofNat k &&& UInt256.ofNat 1 = UInt256.ofNat 1) =
      decide (e.toNat / 2 ^ k % 2 = 1) := by
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    rwa [land_one_toNat, shiftRight_toNat _ hk, toNat_lit (by decide)] at this
  · intro h
    apply word_eq_of_toNat
    rw [land_one_toNat, shiftRight_toNat _ hk, toNat_lit (by decide), h]

/-- The exported loop of `pow`, with `k` bits to go, is `powLoop`. -/
theorem pow_loop_Base (a : L4) (e : UInt256) :
    ∀ k ≤ 256, ∀ (r : L4) (r2 r3 : Mont_Base),
      Mont_pow_Base.b1 (toB a) e (toB r) (UInt256.ofNat k) r2 r3 =
        pure (toB (Mont.powLoop KB a e.toNat k r))
  | 0, _, r, r2, r3 => by
    rw [Mont_pow_Base.b1.eq_1]
    simp [toNat_lit (show 0 < 2 ^ 256 by decide), Mont.powLoop]
  | k + 1, hk, r, r2, r3 => by
    rw [Mont_pow_Base.b1.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by decide), toNat_lit (show k + 1 < 2 ^ 256 by omega),
      show 0 < k + 1 by omega, decide_true, if_true, sub_one_u64 (show k + 1 < 2 ^ 64 by omega),
      pure_bind, square_Base, bit_test e (show k < 256 by omega), Mont.powLoop]
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      simp only [mul_Base, pure_bind, pow_loop_Base a e k (by omega), if_pos h]
    · rename_i h
      simp only [decide_eq_true_eq] at h
      simp only [pow_loop_Base a e k (by omega), if_neg h]

theorem pow_Base (a : L4) (e : UInt256) :
    Mont_pow_Base (toB a) e = pure (toB (Mont.pow KB a e.toNat)) := by
  simp only [Mont_pow_Base, one_Base, pure_bind]
  exact pow_loop_Base a e 256 le_rfl _ _ _

end FeProofs.Ecrecover
