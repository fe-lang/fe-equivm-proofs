import FeProofs.Precompiles.Exported.Blake2F
import FeProofs.Precompiles.Inverse.Signed
import Ethereum.BLAKE2

/-!
# Blake2F: `mix` and `ten_rounds` are pure

fevm's BLAKE2 F keeps its working vector and message block as `[u64; 16]`, which the exporter
prints as `Vector UInt256 16` of words below `2 ^ 64`.  `toV v` is the vector of the sixteen
words of EVMLean's `BLAKE2.Words` structure, each as a word (`lw`).  On it the exported `mix` at
each of the eight index patterns of a round is `pure` of `G` on `Words` (`GW`), and eight of them
are EVMLean's `roundWith`; `ten_rounds` is ten rounds of `roundFast` from any round index that
is a multiple of ten (`ten_rounds_eq`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Blake2F

open FeProofs.Precompiles
open Precompiles.Exported.Blake2F
open Ethereum.BLAKE2 (Words)

/-! ## 64-bit words -/

/-- A 64-bit word as the exported code holds it. -/
def lw (x : UInt64) : UInt256 := UInt256.ofNat x.toNat

theorem lw_lt (x : UInt64) : x.toNat < 2 ^ 256 := lt_trans x.toNat_lt (by decide)

@[simp] theorem lw_toNat (x : UInt64) : (lw x).toNat = x.toNat := toNat_lit (lw_lt x)

theorem lw_inj {x y : UInt64} : lw x = lw y ↔ x = y := by
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    simp only [lw_toNat] at this
    exact UInt64.toNat_inj.mp this
  · rintro rfl; rfl

theorem add_lw (x y : UInt64) : Lib.u64_wrapping_add (lw x) (lw y) = pure (lw (x + y)) := by
  simp only [Lib.u64_wrapping_add, lw, addW_u64 (lw_lt x) (lw_lt y), UInt64.toNat_add]

theorem xor_lw (x y : UInt64) : lw x ^^^ lw y = lw (x ^^^ y) := by
  apply word_eq_of_toNat
  change (UInt256.xor _ _).toNat = _
  rw [lw_toNat, UInt64.toNat_xor]
  change ((x.toNat % 2 ^ 256) ^^^ (y.toNat % 2 ^ 256)) % 2 ^ 256 = _
  rw [Nat.mod_eq_of_lt (lw_lt x), Nat.mod_eq_of_lt (lw_lt y),
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 256) (lw_lt x) (lw_lt y))]

theorem sub64 {k : ℕ} (hk : k ≤ 64) :
    IntTy.sub (.u 64) (UInt256.ofNat 64) (UInt256.ofNat k) = pure (UInt256.ofNat (64 - k)) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show 64 < 2 ^ 256 by decide), toNat_lit (show k < 2 ^ 256 by omega)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

theorem rotr_toNat (x : UInt64) {k : ℕ} (hk0 : 0 < k) (hk : k < 64) :
    (BLAKE2.rotr x (UInt64.ofNat k)).toNat = x.toNat / 2 ^ k ||| x.toNat * 2 ^ (64 - k) % 2 ^ 64 := by
  have hko : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; omega
  have h64 : (64 : UInt64).toNat = 64 := rfl
  have hsub : (64 - UInt64.ofNat k).toNat = 64 - k := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hko, h64]; omega), hko, h64]
  simp only [BLAKE2.rotr, UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hko,
    hsub, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show 64 - k < 64 by omega),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem rotate_lw (x : UInt64) {k : ℕ} (hk0 : 0 < k) (hk : k < 64) :
    rotate_right (lw x) (UInt256.ofNat k) = pure (lw (BLAKE2.rotr x (UInt64.ofNat k))) := by
  have hx := x.toNat_lt
  simp only [rotate_right, sub64 (show k ≤ 64 by omega), pure_bind, lw,
    ushr_eq (lw_lt x) (show k < 256 by omega), shl_u64 (lw_lt x) (show 64 - k < 256 by omega)]
  rw [lor_eq (lt_of_le_of_lt (Nat.div_le_self _ _) (lw_lt x))
      (lt_trans (Nat.mod_lt _ (by decide)) (by decide)), rotr_toNat x hk0 hk]

theorem rotate_lw32 (x : UInt64) : rotate_right (lw x) (UInt256.ofNat 32) = pure (lw (BLAKE2.rotr x 32)) :=
  rotate_lw x (by decide) (by decide)
theorem rotate_lw24 (x : UInt64) : rotate_right (lw x) (UInt256.ofNat 24) = pure (lw (BLAKE2.rotr x 24)) :=
  rotate_lw x (by decide) (by decide)
theorem rotate_lw16 (x : UInt64) : rotate_right (lw x) (UInt256.ofNat 16) = pure (lw (BLAKE2.rotr x 16)) :=
  rotate_lw x (by decide) (by decide)
theorem rotate_lw63 (x : UInt64) : rotate_right (lw x) (UInt256.ofNat 63) = pure (lw (BLAKE2.rotr x 63)) :=
  rotate_lw x (by decide) (by decide)

/-! ## The working vector -/

/-- The sixteen words, as the exported `[u64; 16]`. -/
def toV (v : Words) : Vector UInt256 16 :=
  #v[lw v.w0, lw v.w1, lw v.w2, lw v.w3, lw v.w4, lw v.w5, lw v.w6, lw v.w7, lw v.w8, lw v.w9,
    lw v.w10, lw v.w11, lw v.w12, lw v.w13, lw v.w14, lw v.w15]

theorem toV_get (v : Words) {k : ℕ} (hk : k < 16) : (toV v)[k]! = lw (v.get k) := by
  interval_cases k <;> rfl

theorem toV_set (v : Words) {k : ℕ} (hk : k < 16) (x : UInt64) :
    (toV v).set! k (lw x) = toV (v.set k x) := by
  interval_cases k <;> rfl

theorem checkIndex_lt {k n : ℕ} (h : k < n) (hn : n < 2 ^ 256) :
    checkIndex (UInt256.ofNat k) n = pure () := by
  simp [checkIndex, toNat_lit (show k < 2 ^ 256 by omega), h]

/-- `G` (§ 3.1) on `Words`: EVMLean's `G` on `v.toArray` is `GW v` (`BLAKE2.G_eq`). -/
def GW (v : Words) (a b c d : ℕ) (x y : UInt64) : Words :=
  let q := BLAKE2.mix (v.get a) (v.get b) (v.get c) (v.get d) x y
  (((v.set a q.a).set b q.b).set c q.c).set d q.d

/-- `mix` at fixed indices: unfold the pieces, read and write the vector through `toV`, and
compare. -/
macro "mix_tac" : tactic => `(tactic| (
  simp (config := { decide := true }) only [mix, mix_k1, mix_k2, mix_k3, mix_k4, checkIndex_lt,
    pure_bind, toNat_lit, toV_get,
    toV_set, add_lw, xor_lw, rotate_lw32, rotate_lw24, rotate_lw16,
    rotate_lw63]
  simp only [GW, BLAKE2.mix, Words.get, Words.set]))

theorem mix_0_4_8_12 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 0) (UInt256.ofNat 4) (UInt256.ofNat 8) (UInt256.ofNat 12)
      (lw x) (lw y) = pure ((), toV (GW v 0 4 8 12 x y)) := by
  mix_tac

theorem mix_1_5_9_13 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 1) (UInt256.ofNat 5) (UInt256.ofNat 9) (UInt256.ofNat 13)
      (lw x) (lw y) = pure ((), toV (GW v 1 5 9 13 x y)) := by
  mix_tac

theorem mix_2_6_10_14 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 2) (UInt256.ofNat 6) (UInt256.ofNat 10) (UInt256.ofNat 14)
      (lw x) (lw y) = pure ((), toV (GW v 2 6 10 14 x y)) := by
  mix_tac

theorem mix_3_7_11_15 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 3) (UInt256.ofNat 7) (UInt256.ofNat 11) (UInt256.ofNat 15)
      (lw x) (lw y) = pure ((), toV (GW v 3 7 11 15 x y)) := by
  mix_tac

theorem mix_0_5_10_15 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 0) (UInt256.ofNat 5) (UInt256.ofNat 10) (UInt256.ofNat 15)
      (lw x) (lw y) = pure ((), toV (GW v 0 5 10 15 x y)) := by
  mix_tac

theorem mix_1_6_11_12 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 1) (UInt256.ofNat 6) (UInt256.ofNat 11) (UInt256.ofNat 12)
      (lw x) (lw y) = pure ((), toV (GW v 1 6 11 12 x y)) := by
  mix_tac

theorem mix_2_7_8_13 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 2) (UInt256.ofNat 7) (UInt256.ofNat 8) (UInt256.ofNat 13)
      (lw x) (lw y) = pure ((), toV (GW v 2 7 8 13 x y)) := by
  mix_tac

theorem mix_3_4_9_14 (v : Words) (x y : UInt64) :
    mix (toV v) (UInt256.ofNat 3) (UInt256.ofNat 4) (UInt256.ofNat 9) (UInt256.ofNat 14)
      (lw x) (lw y) = pure ((), toV (GW v 3 4 9 14 x y)) := by
  mix_tac

/-! ## Rounds -/

/-- Eight `G`s on the columns and diagonals are EVMLean's `roundWith`. -/
theorem round_GW (v : Words) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt64) :
    GW (GW (GW (GW (GW (GW (GW (GW v 0 4 8 12 x0 x1) 1 5 9 13 x2 x3) 2 6 10 14 x4 x5) 3 7 11 15 x6 x7) 0 5 10 15 x8 x9) 1 6 11 12 x10 x11) 2 7 8 13 x12 x13) 3 4 9 14 x14 x15 =
      BLAKE2.roundWith v x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by
  simp only [GW, Words.get, Words.set, BLAKE2.roundWith]

set_option maxRecDepth 100000 in
set_option linter.loopingSimpArgs false in
/-- `ten_rounds`: rounds `i, …, i + 9` of `roundFast`, for `i` a multiple of ten. -/
theorem ten_rounds_eq (m v : Words) {i : ℕ} (hi : i % 10 = 0) :
    ten_rounds (toV v) (toV m) = pure ((), toV (BLAKE2.roundsFast m 10 i v)) := by
  have h1 : (i + 1) % 10 = 1 := by omega
  have h2 : (i + 2) % 10 = 2 := by omega
  have h3 : (i + 3) % 10 = 3 := by omega
  have h4 : (i + 4) % 10 = 4 := by omega
  have h5 : (i + 5) % 10 = 5 := by omega
  have h6 : (i + 6) % 10 = 6 := by omega
  have h7 : (i + 7) % 10 = 7 := by omega
  have h8 : (i + 8) % 10 = 8 := by omega
  have h9 : (i + 9) % 10 = 9 := by omega
  simp (config := { decide := true }) only [ten_rounds, ten_rounds_k1, ten_rounds_k2, ten_rounds_k3, ten_rounds_k4, ten_rounds_k5, ten_rounds_k6, ten_rounds_k7, ten_rounds_k8, ten_rounds_k9, ten_rounds_k10, ten_rounds_k11, ten_rounds_k12, ten_rounds_k13, ten_rounds_k14, ten_rounds_k15, ten_rounds_k16, ten_rounds_k17, ten_rounds_k18, ten_rounds_k19, ten_rounds_k20, ten_rounds_k21, ten_rounds_k22, ten_rounds_k23, ten_rounds_k24, ten_rounds_k25, ten_rounds_k26, ten_rounds_k27, ten_rounds_k28, ten_rounds_k29, ten_rounds_k30, ten_rounds_k31, ten_rounds_k32, ten_rounds_k33, ten_rounds_k34, ten_rounds_k35, ten_rounds_k36, checkIndex_lt, pure_bind, toNat_lit, toV_get, Words.get,
    mix_0_4_8_12, mix_1_5_9_13, mix_2_6_10_14, mix_3_7_11_15, mix_0_5_10_15, mix_1_6_11_12, mix_2_7_8_13, mix_3_4_9_14]
  simp only [round_GW, BLAKE2.roundsFast, BLAKE2.roundFast, hi, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end FeProofs.Blake2F
