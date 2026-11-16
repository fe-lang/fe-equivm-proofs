import FeProofs.Precompiles.Blake2F.Mix
import FeProofs.Precompiles.Field.Checked
import FeProofs.Precompiles.Casts

/-!
# Blake2F: the round loops

`compress` runs the rounds as blocks of ten (`ten_rounds`) while ten or more remain, then one at
a time, each reading its message words through `SIGMA[(round % 10) * 16 + k]`.  From round `r`
of `total`, the second loop gives `roundsFast` to `total` (`rest_spec`), and the first does too
from any multiple of ten (`tens_spec`), so the two give EVMLean's rounds for every count below
`2 ^ 64`.  Both loops count up to `total`, so they return on every input.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Blake2F

open FeProofs.Precompiles
open Precompiles.Exported.Blake2F
open Ethereum.BLAKE2 (Words)

/-! ## The flattened permutations -/

/-- `SIGMA` of the Fe code: the ten permutations, flattened. -/
def sigmaV : Vector UInt256 160 :=
  Vector.ofFn fun i : Fin 160 => UInt256.ofNat ((BLAKE2.SIGMA[i.val / 16]!)[i.val % 16]!)

set_option maxRecDepth 10000 in
theorem SIGMA_eq : SIGMA = pure sigmaV := by
  simp only [SIGMA, SIGMA_k1, SIGMA_k2, SIGMA_k3, SIGMA_k4, SIGMA_k5, SIGMA_k6]
  rfl

/-! ## Vectors as functions -/

theorem getElem!_ofFn {α : Type} {n : ℕ} [Inhabited α] (f : Fin n → α) {i : ℕ} (h : i < n) :
    (Vector.ofFn f)[i]! = f ⟨i, h⟩ := by
  simp [h]

theorem set!_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (x : α) :
    (Vector.ofFn f).set! i x = Vector.ofFn (fun j => if j.val = i then x else f j) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.set!, Vector.getElem_mk, Vector.toArray_ofFn, Array.set!, Vector.getElem_ofFn]
  rw [Array.getElem_setIfInBounds]
  · by_cases hji : i = j
    · subst hji; simp
    · have : ¬ j = i := fun e => hji e.symm
      simp only [hji, this, ↓reduceIte]
      exact Array.getElem_ofFn ..
  · simpa using hj

theorem replicate_ofFn {α : Type} {n : ℕ} (x : α) :
    Vector.replicate n x = Vector.ofFn (fun _ => x) := by
  apply Vector.ext; intro j hj; simp

theorem sigmaV_get {n : ℕ} (hn : n < 160) :
    sigmaV[n]! = UInt256.ofNat ((BLAKE2.SIGMA[n / 16]!)[n % 16]!) :=
  getElem!_ofFn _ hn

theorem sig_lt {j k : ℕ} (hj : j < 10) (hk : k < 16) : (BLAKE2.SIGMA[j]!)[k]! < 16 := by
  interval_cases j <;> interval_cases k <;> decide

/-- Round `r` reads the message words `σ[r mod 10]` names. -/
theorem roundFast_get (m v : Words) (r : ℕ) :
    BLAKE2.roundFast m v r = BLAKE2.roundWith v (m.get ((BLAKE2.SIGMA[r % 10]!)[0]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[1]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[2]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[3]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[4]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[5]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[6]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[7]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[8]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[9]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[10]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[11]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[12]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[13]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[14]!)) (m.get ((BLAKE2.SIGMA[r % 10]!)[15]!)) := by
  unfold BLAKE2.roundFast
  have hj : r % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize r % 10 = j at hj ⊢
  interval_cases j <;> rfl

/-! ## Word arithmetic of the loops -/

theorem sub64' {a b : ℕ} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    IntTy.sub (.u 64) (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a - b)) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show a < 2 ^ 256 by omega), toNat_lit (show b < 2 ^ 256 by omega)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

theorem add64 {a b : ℕ} (h : a + b < 2 ^ 64) :
    IntTy.add (.u 64) (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a + b)) := by
  simp only [IntTy.add, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show a < 2 ^ 256 by omega), toNat_lit (show b < 2 ^ 256 by omega)]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

theorem mul64 {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a * b < 2 ^ 64) :
    IntTy.mul (.u 64) (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a * b)) := by
  simp only [IntTy.mul, IntTy.checked, IntTy.Fits, IntTy.val, IntTy.wrap,
    toNat_lit (show a < 2 ^ 256 by omega), toNat_lit (show b < 2 ^ 256 by omega)]
  have h' : ((a : ℤ) * b) = ((a * b : ℕ) : ℤ) := by push_cast; ring
  rw [h', if_pos (by constructor <;> omega)]
  congr 2
  omega

/-! ## The loop of single rounds -/

set_option maxRecDepth 10000 in
/-- One pass of the loop of single rounds: round `r` with `σ[r mod 10]`. -/
theorem rest_step {T r : ℕ} (hT : T < 2 ^ 64) (hr : r < T) (m v : Words) r0 r4 r5 r6 r7 r8 :
    compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4 (UInt256.ofNat T) r0 (toV m) (toV v) (UInt256.ofNat r)
        r4 r5 r6 r7 r8 =
      compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4 (UInt256.ofNat T) r0 (toV m)
        (toV (BLAKE2.roundFast m v r)) (UInt256.ofNat (r + 1)) r4 r5 r6 r7 r8 := by
  have hj : r % 10 < 10 := Nat.mod_lt _ (by decide)
  have hrem : checkedRem (UInt256.ofNat r) (UInt256.ofNat 10) = pure (UInt256.ofNat (r % 10)) := by
    rw [checkedRem_lit _ (by decide) (by decide), toNat_lit (by omega)]
  have hmul : IntTy.mul (.u 64) (UInt256.ofNat (r % 10)) (UInt256.ofNat 16) =
      pure (UInt256.ofNat (r % 10 * 16)) := mul64 (by omega) (by decide) (by omega)
  rw [compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.eq_1, roundFast_get]
  simp only [toNat_lit (show r < 2 ^ 256 by omega), toNat_lit (show T < 2 ^ 256 by omega),
    decide_eq_true hr, if_true, hrem, hmul, downcast_u64_usize, SIGMA_eq, pure_bind]
  generalize r % 10 = j at hj ⊢
  have t0 : (UInt256.ofNat (j * 16)).toNat = j * 16 := toNat_lit (by omega)
  have c0 : checkIndex (UInt256.ofNat (j * 16)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g0 : sigmaV[j * 16]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[0]!) := by
    rw [sigmaV_get (by omega), show (j * 16) / 16 = j by omega, show (j * 16) % 16 = 0 by omega]
  have u0 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[0]!)).toNat = (BLAKE2.SIGMA[j]!)[0]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d0 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[0]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m0 : (toV m)[(BLAKE2.SIGMA[j]!)[0]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[0]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a1 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 1) = pure (UInt256.ofNat (j * 16 + 1)) :=
    checkedAdd_small (by omega)
  have t1 : (UInt256.ofNat (j * 16 + 1)).toNat = j * 16 + 1 := toNat_lit (by omega)
  have c1 : checkIndex (UInt256.ofNat (j * 16 + 1)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g1 : sigmaV[j * 16 + 1]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[1]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 1) / 16 = j by omega, show (j * 16 + 1) % 16 = 1 by omega]
  have u1 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[1]!)).toNat = (BLAKE2.SIGMA[j]!)[1]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d1 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[1]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m1 : (toV m)[(BLAKE2.SIGMA[j]!)[1]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[1]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a2 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 2) = pure (UInt256.ofNat (j * 16 + 2)) :=
    checkedAdd_small (by omega)
  have t2 : (UInt256.ofNat (j * 16 + 2)).toNat = j * 16 + 2 := toNat_lit (by omega)
  have c2 : checkIndex (UInt256.ofNat (j * 16 + 2)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g2 : sigmaV[j * 16 + 2]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[2]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 2) / 16 = j by omega, show (j * 16 + 2) % 16 = 2 by omega]
  have u2 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[2]!)).toNat = (BLAKE2.SIGMA[j]!)[2]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d2 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[2]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m2 : (toV m)[(BLAKE2.SIGMA[j]!)[2]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[2]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a3 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 3) = pure (UInt256.ofNat (j * 16 + 3)) :=
    checkedAdd_small (by omega)
  have t3 : (UInt256.ofNat (j * 16 + 3)).toNat = j * 16 + 3 := toNat_lit (by omega)
  have c3 : checkIndex (UInt256.ofNat (j * 16 + 3)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g3 : sigmaV[j * 16 + 3]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[3]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 3) / 16 = j by omega, show (j * 16 + 3) % 16 = 3 by omega]
  have u3 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[3]!)).toNat = (BLAKE2.SIGMA[j]!)[3]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d3 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[3]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m3 : (toV m)[(BLAKE2.SIGMA[j]!)[3]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[3]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a4 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 4) = pure (UInt256.ofNat (j * 16 + 4)) :=
    checkedAdd_small (by omega)
  have t4 : (UInt256.ofNat (j * 16 + 4)).toNat = j * 16 + 4 := toNat_lit (by omega)
  have c4 : checkIndex (UInt256.ofNat (j * 16 + 4)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g4 : sigmaV[j * 16 + 4]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[4]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 4) / 16 = j by omega, show (j * 16 + 4) % 16 = 4 by omega]
  have u4 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[4]!)).toNat = (BLAKE2.SIGMA[j]!)[4]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d4 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[4]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m4 : (toV m)[(BLAKE2.SIGMA[j]!)[4]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[4]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a5 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 5) = pure (UInt256.ofNat (j * 16 + 5)) :=
    checkedAdd_small (by omega)
  have t5 : (UInt256.ofNat (j * 16 + 5)).toNat = j * 16 + 5 := toNat_lit (by omega)
  have c5 : checkIndex (UInt256.ofNat (j * 16 + 5)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g5 : sigmaV[j * 16 + 5]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[5]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 5) / 16 = j by omega, show (j * 16 + 5) % 16 = 5 by omega]
  have u5 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[5]!)).toNat = (BLAKE2.SIGMA[j]!)[5]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d5 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[5]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m5 : (toV m)[(BLAKE2.SIGMA[j]!)[5]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[5]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a6 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 6) = pure (UInt256.ofNat (j * 16 + 6)) :=
    checkedAdd_small (by omega)
  have t6 : (UInt256.ofNat (j * 16 + 6)).toNat = j * 16 + 6 := toNat_lit (by omega)
  have c6 : checkIndex (UInt256.ofNat (j * 16 + 6)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g6 : sigmaV[j * 16 + 6]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[6]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 6) / 16 = j by omega, show (j * 16 + 6) % 16 = 6 by omega]
  have u6 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[6]!)).toNat = (BLAKE2.SIGMA[j]!)[6]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d6 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[6]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m6 : (toV m)[(BLAKE2.SIGMA[j]!)[6]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[6]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a7 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 7) = pure (UInt256.ofNat (j * 16 + 7)) :=
    checkedAdd_small (by omega)
  have t7 : (UInt256.ofNat (j * 16 + 7)).toNat = j * 16 + 7 := toNat_lit (by omega)
  have c7 : checkIndex (UInt256.ofNat (j * 16 + 7)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g7 : sigmaV[j * 16 + 7]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[7]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 7) / 16 = j by omega, show (j * 16 + 7) % 16 = 7 by omega]
  have u7 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[7]!)).toNat = (BLAKE2.SIGMA[j]!)[7]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d7 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[7]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m7 : (toV m)[(BLAKE2.SIGMA[j]!)[7]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[7]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a8 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 8) = pure (UInt256.ofNat (j * 16 + 8)) :=
    checkedAdd_small (by omega)
  have t8 : (UInt256.ofNat (j * 16 + 8)).toNat = j * 16 + 8 := toNat_lit (by omega)
  have c8 : checkIndex (UInt256.ofNat (j * 16 + 8)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g8 : sigmaV[j * 16 + 8]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[8]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 8) / 16 = j by omega, show (j * 16 + 8) % 16 = 8 by omega]
  have u8 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[8]!)).toNat = (BLAKE2.SIGMA[j]!)[8]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d8 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[8]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m8 : (toV m)[(BLAKE2.SIGMA[j]!)[8]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[8]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a9 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 9) = pure (UInt256.ofNat (j * 16 + 9)) :=
    checkedAdd_small (by omega)
  have t9 : (UInt256.ofNat (j * 16 + 9)).toNat = j * 16 + 9 := toNat_lit (by omega)
  have c9 : checkIndex (UInt256.ofNat (j * 16 + 9)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g9 : sigmaV[j * 16 + 9]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[9]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 9) / 16 = j by omega, show (j * 16 + 9) % 16 = 9 by omega]
  have u9 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[9]!)).toNat = (BLAKE2.SIGMA[j]!)[9]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d9 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[9]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m9 : (toV m)[(BLAKE2.SIGMA[j]!)[9]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[9]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a10 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 10) = pure (UInt256.ofNat (j * 16 + 10)) :=
    checkedAdd_small (by omega)
  have t10 : (UInt256.ofNat (j * 16 + 10)).toNat = j * 16 + 10 := toNat_lit (by omega)
  have c10 : checkIndex (UInt256.ofNat (j * 16 + 10)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g10 : sigmaV[j * 16 + 10]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[10]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 10) / 16 = j by omega, show (j * 16 + 10) % 16 = 10 by omega]
  have u10 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[10]!)).toNat = (BLAKE2.SIGMA[j]!)[10]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d10 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[10]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m10 : (toV m)[(BLAKE2.SIGMA[j]!)[10]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[10]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a11 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 11) = pure (UInt256.ofNat (j * 16 + 11)) :=
    checkedAdd_small (by omega)
  have t11 : (UInt256.ofNat (j * 16 + 11)).toNat = j * 16 + 11 := toNat_lit (by omega)
  have c11 : checkIndex (UInt256.ofNat (j * 16 + 11)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g11 : sigmaV[j * 16 + 11]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[11]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 11) / 16 = j by omega, show (j * 16 + 11) % 16 = 11 by omega]
  have u11 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[11]!)).toNat = (BLAKE2.SIGMA[j]!)[11]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d11 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[11]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m11 : (toV m)[(BLAKE2.SIGMA[j]!)[11]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[11]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a12 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 12) = pure (UInt256.ofNat (j * 16 + 12)) :=
    checkedAdd_small (by omega)
  have t12 : (UInt256.ofNat (j * 16 + 12)).toNat = j * 16 + 12 := toNat_lit (by omega)
  have c12 : checkIndex (UInt256.ofNat (j * 16 + 12)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g12 : sigmaV[j * 16 + 12]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[12]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 12) / 16 = j by omega, show (j * 16 + 12) % 16 = 12 by omega]
  have u12 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[12]!)).toNat = (BLAKE2.SIGMA[j]!)[12]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d12 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[12]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m12 : (toV m)[(BLAKE2.SIGMA[j]!)[12]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[12]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a13 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 13) = pure (UInt256.ofNat (j * 16 + 13)) :=
    checkedAdd_small (by omega)
  have t13 : (UInt256.ofNat (j * 16 + 13)).toNat = j * 16 + 13 := toNat_lit (by omega)
  have c13 : checkIndex (UInt256.ofNat (j * 16 + 13)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g13 : sigmaV[j * 16 + 13]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[13]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 13) / 16 = j by omega, show (j * 16 + 13) % 16 = 13 by omega]
  have u13 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[13]!)).toNat = (BLAKE2.SIGMA[j]!)[13]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d13 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[13]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m13 : (toV m)[(BLAKE2.SIGMA[j]!)[13]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[13]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a14 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 14) = pure (UInt256.ofNat (j * 16 + 14)) :=
    checkedAdd_small (by omega)
  have t14 : (UInt256.ofNat (j * 16 + 14)).toNat = j * 16 + 14 := toNat_lit (by omega)
  have c14 : checkIndex (UInt256.ofNat (j * 16 + 14)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g14 : sigmaV[j * 16 + 14]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[14]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 14) / 16 = j by omega, show (j * 16 + 14) % 16 = 14 by omega]
  have u14 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[14]!)).toNat = (BLAKE2.SIGMA[j]!)[14]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d14 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[14]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m14 : (toV m)[(BLAKE2.SIGMA[j]!)[14]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[14]!)) :=
    toV_get m (sig_lt hj (by decide))
  have a15 : checkedAdd (UInt256.ofNat (j * 16)) (UInt256.ofNat 15) = pure (UInt256.ofNat (j * 16 + 15)) :=
    checkedAdd_small (by omega)
  have t15 : (UInt256.ofNat (j * 16 + 15)).toNat = j * 16 + 15 := toNat_lit (by omega)
  have c15 : checkIndex (UInt256.ofNat (j * 16 + 15)) 160 = pure () := checkIndex_lt (by omega) (by decide)
  have g15 : sigmaV[j * 16 + 15]! = UInt256.ofNat ((BLAKE2.SIGMA[j]!)[15]!) := by
    rw [sigmaV_get (by omega), show (j * 16 + 15) / 16 = j by omega, show (j * 16 + 15) % 16 = 15 by omega]
  have u15 : (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[15]!)).toNat = (BLAKE2.SIGMA[j]!)[15]! :=
    toNat_lit (lt_trans (sig_lt hj (by decide)) (by decide))
  have d15 : checkIndex (UInt256.ofNat ((BLAKE2.SIGMA[j]!)[15]!)) 16 = pure () :=
    checkIndex_lt (sig_lt hj (by decide)) (by decide)
  have m15 : (toV m)[(BLAKE2.SIGMA[j]!)[15]!]! = lw (m.get ((BLAKE2.SIGMA[j]!)[15]!)) :=
    toV_get m (sig_lt hj (by decide))
  simp only [t0, c0, g0, u0, d0, m0, a1, t1, c1, g1, u1, d1, m1, a2, t2, c2, g2, u2, d2, m2, a3, t3, c3, g3, u3, d3, m3, a4, t4, c4, g4, u4, d4, m4, a5, t5, c5, g5, u5, d5, m5, a6, t6, c6, g6, u6, d6, m6, a7, t7, c7, g7, u7, d7, m7, a8, t8, c8, g8, u8, d8, m8, a9, t9, c9, g9, u9, d9, m9, a10, t10, c10, g10, u10, d10, m10, a11, t11, c11, g11, u11, d11, m11, a12, t12, c12, g12, u12, d12, m12, a13, t13, c13, g13, u13, d13, m13, a14, t14, c14, g14, u14, d14, m14, a15, t15, c15, g15, u15, d15, m15, mix_0_4_8_12, mix_1_5_9_13, mix_2_6_10_14, mix_3_7_11_15, mix_0_5_10_15, mix_1_6_11_12, mix_2_7_8_13, mix_3_4_9_14, pure_bind,
    add64 (show r + 1 < 2 ^ 64 by omega), round_GW]

theorem roundsFast_succ (m : Words) :
    ∀ k i v, BLAKE2.roundsFast m (k + 1) i v = BLAKE2.roundFast m (BLAKE2.roundsFast m k i v) (i + k)
  | 0, i, v => rfl
  | k + 1, i, v => by
    rw [BLAKE2.roundsFast, roundsFast_succ m k (i + 1), BLAKE2.roundsFast,
      show i + 1 + k = i + (k + 1) by omega]

theorem roundsFast_add (m : Words) (l : ℕ) :
    ∀ k i v, BLAKE2.roundsFast m (k + l) i v = BLAKE2.roundsFast m l (i + k) (BLAKE2.roundsFast m k i v)
  | 0, i, v => by simp [BLAKE2.roundsFast]
  | k + 1, i, v => by
    rw [show k + 1 + l = (k + l) + 1 by omega, BLAKE2.roundsFast, BLAKE2.roundsFast,
      show k + l = k + l from rfl]
    have := roundsFast_add m l k (i + 1) (BLAKE2.roundFast m v i)
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    rw [← this]

/-- The loop of single rounds runs the rounds from `r` to `total`, then the final loop. -/
theorem rest_spec {T : ℕ} (hT : T < 2 ^ 64) (m v0 : Words) r0 r4 r5 r6 r7 r8 :
    ∀ n r, r + n = T →
      compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4 (UInt256.ofNat T) r0 (toV m)
          (toV (BLAKE2.roundsFast m r 0 v0)) (UInt256.ofNat r) r4 r5 r6 r7 r8 =
        compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.loop_5 r0 (toV m) (toV (BLAKE2.roundsFast m T 0 v0))
          (UInt256.ofNat T) r4 r5 r6 r7 (Range_Known_0_Known_8.mk () ()) (UInt256.ofNat 0)
  | 0, r, h => by
    subst h
    rw [compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.eq_1]
    simp [Lib.Range_start_0_8]
  | n + 1, r, h => by
    have hs := roundsFast_succ m r 0 v0
    rw [Nat.zero_add] at hs
    rw [rest_step hT (by omega), ← hs]
    exact rest_spec hT m v0 r0 r4 r5 r6 r7 r8 n (r + 1) (by omega)

/-! ## The loop of ten rounds -/

/-- The loop of ten rounds, from a multiple of ten, and then the loop of single rounds: the
rounds from `r` to `total`, then the final loop. -/
theorem tens_spec {T : ℕ} (hT : T < 2 ^ 64) (m v0 : Words) r0 r4 r5 r6 r8 :
    ∀ n r r7, r % 10 = 0 → r + n = T → ∃ r7',
      compress_MemBuffer.loop.loop_1.loop_2.loop_3 (UInt256.ofNat T) r0 (toV m)
          (toV (BLAKE2.roundsFast m r 0 v0)) (UInt256.ofNat r) r4 r5 r6 r7 r8 =
        compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.loop_5 r0 (toV m) (toV (BLAKE2.roundsFast m T 0 v0))
          (UInt256.ofNat T) r4 r5 r6 r7' (Range_Known_0_Known_8.mk () ()) (UInt256.ofNat 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r r7 hr h
    rw [compress_MemBuffer.loop.loop_1.loop_2.loop_3.eq_1, sub64' hT (show r ≤ T by omega)]
    simp only [pure_bind, toNat_lit (show T - r < 2 ^ 256 by omega),
      toNat_lit (show 10 < 2 ^ 256 by decide)]
    by_cases h10 : 10 ≤ T - r
    · simp only [h10, decide_true, if_true, ten_rounds_eq m _ hr, pure_bind,
        add64 (show r + 10 < 2 ^ 64 by omega)]
      have hs := roundsFast_add m 10 r 0 v0
      rw [Nat.zero_add] at hs
      rw [← hs]
      exact ih (n - 10) (by omega) (r + 10) (toV m) (by omega) (by omega)
    · simp only [h10, decide_false, Bool.false_eq_true, if_false]
      exact ⟨r7, rest_spec hT m v0 r0 r4 r5 r6 r7 r8 n r h⟩

/-! ## The output -/

/-- The new state words: `h[i] ^ (v[i] ^ v[i + 8])`. -/
def outW (H : Fin 8 → UInt64) (v : Words) (j : Fin 8) : UInt64 := H j ^^^ (v.get j ^^^ v.get (j + 8))

theorem has8 (r : Range_Known_0_Known_8) {k : ℕ} (hk : k < 2 ^ 256) :
    Range_has_0_8 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 8)) := by
  simp only [Lib.Range_has_0_8, range_has_eq (lo := 0) (hi := 8) hk (by decide) (by decide),
    bind_pure]

theorem has16 (r : Range_Known_0_Known_16) {k : ℕ} (hk : k < 2 ^ 256) :
    Range_has_0_16 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 16)) := by
  simp only [Lib.Range_has_0_16, range_has_eq (lo := 0) (hi := 16) hk (by decide) (by decide),
    bind_pure]

/-- The final loop: `h[i] ^= v[i] ^ v[i + 8]` for the words from `i` on. -/
theorem final_spec (v : Words) (H : Fin 8 → UInt64) r1 r3 r4 r5 r6 r7 r8 :
    ∀ n i, i + n = 8 →
      compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.loop_5
          (Vector.ofFn fun j => lw (if j.val < i then outW H v j else H j)) r1 (toV v) r3 r4 r5 r6
          r7 r8 (UInt256.ofNat i) =
        pure (Vector.ofFn fun j => lw (outW H v j))
  | 0, i, h => by
    subst h
    rw [compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.loop_5.eq_1]
    simp only [has8 _ (show 0 + 8 < 2 ^ 256 by decide)]
    simp
  | n + 1, i, h => by
    rw [compress_MemBuffer.loop.loop_1.loop_2.loop_3.loop_4.loop_5.eq_1]
    simp only [has8 _ (show i < 2 ^ 256 by omega), show 0 ≤ i ∧ i < 8 from ⟨by omega, by omega⟩,
      Lib.Range_at_0_8, Lib.Range_next_0_8, pure_bind, checkIndex_lt (show i < 16 by omega) (by decide), checkIndex_lt (show i < 8 by omega) (by decide),
      checkedAdd_small (show i + 8 < 2 ^ 256 by omega),
      checkIndex_lt (show i + 8 < 16 by omega) (by decide), toNat_lit (show i < 2 ^ 256 by omega),
      toNat_lit (show i + 8 < 2 ^ 256 by omega), toV_get v (show i < 16 by omega),
      toV_get v (show i + 8 < 16 by omega), getElem!_ofFn _ (show i < 8 by omega), lt_irrefl,
      if_false, xor_lw, set!_ofFn, next_eq (show i + 1 < 2 ^ 256 by omega)]
    have e : (fun j : Fin 8 => if j.val = i then lw (H ⟨i, by omega⟩ ^^^ (v.get i ^^^ v.get (i + 8)))
        else lw (if j.val < i then outW H v j else H j)) =
        fun j => lw (if j.val < i + 1 then outW H v j else H j) := by
      funext j
      by_cases hj : j.val = i
      · obtain ⟨jv, hjv⟩ := j
        simp only at hj
        subst hj
        simp [outW]
      · by_cases hj' : j.val < i
        · simp [hj, hj', show j.val < i + 1 by omega]
        · simp [hj, hj', show ¬ j.val < i + 1 by omega]
    rw [e]
    exact final_spec v H r1 r3 r4 r5 r6 r7 r8 n (i + 1) (by omega)

end FeProofs.Blake2F
