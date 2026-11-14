import FeProofs.Precompiles.Blake2F.Rounds
import FeProofs.Precompiles.Blake2F.Bytes

/-!
# Blake2F: `compress` on a buffer

On a buffer that holds 213 bytes `d` whose final byte is 0 or 1, the exported
`compress_MemBuffer` returns, with the world unchanged, the eight words of EVMLean's `BLAKE2.F` on
the input `compressInput` decodes from `d` (`compress_spec`): the state `h` and message `m` read
through `MemBuffer_lane_at` (`lane_exec`, `lane_word`), the round count through
`MemBuffer_byte_at`, the rounds by `Rounds.lean`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Blake2F

open FeProofs.Precompiles
open Precompiles.Exported.Blake2F
open Ethereum.BLAKE2 (Words)

/-! ## Words as functions -/

/-- The sixteen words `f 0, …, f 15`. -/
def wOf (f : ℕ → UInt64) : Words :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

theorem wOf_get (f : ℕ → UInt64) {k : ℕ} (hk : k < 16) : (wOf f).get k = f k := by
  interval_cases k <;> rfl

theorem wOf_set (f : ℕ → UInt64) {i : ℕ} (hi : i < 16) (x : UInt64) :
    (wOf f).set i x = wOf (fun k => if k = i then x else f k) := by
  interval_cases i <;> rfl

theorem wOf_congr {f g : ℕ → UInt64} (h : ∀ k < 16, f k = g k) : wOf f = wOf g := by
  simp only [wOf, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide),
    h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide),
    h 14 (by decide), h 15 (by decide)]

theorem ofArray_eq (a : Array UInt64) : Words.ofArray a = wOf (fun k => a[k]!) := rfl

theorem toV_wOf_get (f : ℕ → UInt64) {k : ℕ} (hk : k < 16) : (toV (wOf f))[k]! = lw (f k) := by
  rw [toV_get _ hk, wOf_get _ hk]

theorem toV_wOf_set (f : ℕ → UInt64) {i : ℕ} (hi : i < 16) (x : UInt64) :
    (toV (wOf f)).set! i (lw x) = toV (wOf (fun k => if k = i then x else f k)) := by
  rw [toV_set _ hi, wOf_set _ hi]

/-! ## Constants -/

/-- `IV` of the Fe code. -/
theorem IV_eq : IV = pure (Vector.ofFn fun i : Fin 8 => lw (BLAKE2.IV[i.val]!)) := by
  simp only [IV]
  rfl

theorem lw_zero : lw 0 = UInt256.ofNat 0 := rfl

/-! ## The round count -/

/-- The big-endian round count of the first four bytes, as `compressInput` reads it. -/
def roundsOf (d : ByteArray) : ℕ :=
  (byteAt d 0 <<< 24) ||| (byteAt d 1 <<< 16) ||| (byteAt d 2 <<< 8) ||| byteAt d 3

theorem roundsOf_lt (d : ByteArray) : roundsOf d < 2 ^ 32 := by
  have h0 := byteAt_lt d 0; have h1 := byteAt_lt d 1; have h2 := byteAt_lt d 2
  have h3 := byteAt_lt d 3
  unfold roundsOf
  simp only [Nat.shiftLeft_eq]
  apply Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (by omega) (by omega)) (by omega))
    (by omega)

theorem holds_len {b : Lib.MemBuffer} {d mem : ByteArray} (h : Holds b d mem) (hd : d.size = 213) :
    b.len = UInt256.ofNat 213 :=
  word_eq_of_toNat (by rw [h.len, hd]; rfl)

theorem rounds_exec {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) (hd : d.size = 213) :
    (rounds_MemBuffer b).exec I w = some (.ok (UInt256.ofNat (roundsOf d), w)) := by
  have hb := byteAt_lt d
  simp only [rounds_MemBuffer, Fe.M.exec_bind, len_exec, INPUT_LEN, Fe.M.exec_pure, holds_len h hd,
    decide_true, Lib.assert, Bool.not_true, Bool.false_eq_true, if_false,
    byte_exec h (show 0 < d.size by omega), byte_exec h (show 1 < d.size by omega),
    byte_exec h (show 2 < d.size by omega), byte_exec h (show 3 < d.size by omega),
    shl_u64 (show byteAt d 0 < 2 ^ 256 by have := hb 0; omega) (show 24 < 256 by decide),
    shl_u64 (show byteAt d 1 < 2 ^ 256 by have := hb 1; omega) (show 16 < 256 by decide),
    shl_u64 (show byteAt d 2 < 2 ^ 256 by have := hb 2; omega) (show 8 < 256 by decide)]
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  rw [Nat.mod_eq_of_lt (show byteAt d 0 * 2 ^ 24 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show byteAt d 1 * 2 ^ 16 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show byteAt d 2 * 2 ^ 8 < 2 ^ 64 by omega),
    lor_eq (by omega) (by omega),
    lor_eq (Nat.or_lt_two_pow (n := 256) (by omega) (by omega)) (by omega),
    lor_eq (Nat.or_lt_two_pow (n := 256) (Nat.or_lt_two_pow (n := 256) (by omega) (by omega))
      (by omega)) (by omega)]
  simp only [roundsOf, Nat.shiftLeft_eq]

/-! ## The input loops -/

/-- The little-endian word of the input at `off`, as the exported code holds it. -/
theorem lane_lw {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    {j : ℕ} (hj : j + 8 ≤ d.size) :
    (MemBuffer_lane_at b (UInt256.ofNat j)).exec I w = some (.ok (lw (BLAKE2.word d j), w)) := by
  rw [lane_exec h hj, lane_word]
  rfl

/-- The loop reading the state `h`, from word `i`. -/
theorem h_loop {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    (hd : d.size = 213) r1 r2 r3 r4 r5 r6 r7 r8 :
    ∀ n i, i + n = 8 →
      (compress_MemBuffer.b5 b (Vector.ofFn fun j : Fin 8 =>
          lw (if j.val < i then BLAKE2.word d (4 + 8 * j.val) else 0)) r1 r2 r3 r4 r5 r6 r7 r8
          (UInt256.ofNat i)).exec I w =
        (compress_MemBuffer.b5.b9 b (Vector.ofFn fun j : Fin 8 => lw (BLAKE2.word d (4 + 8 * j.val)))
          r1 r2 r3 r4 (Range_Known_0_Known_16.mk () ()) r6 r7 r8 (UInt256.ofNat 0)).exec I w
  | 0, i, hi => by
    subst hi
    rw [compress_MemBuffer.b5.eq_1]
    simp only [has8 _ (show 0 + 8 < 2 ^ 256 by decide), Lib.Range_start_0_16, pure_bind]
    simp
  | n + 1, i, hi => by
    rw [compress_MemBuffer.b5.eq_1]
    simp only [has8 _ (show i < 2 ^ 256 by omega),
      decide_eq_true (show 0 ≤ i ∧ i < 8 from ⟨by omega, by omega⟩), ↓reduceIte, Lib.Range_at_0_8, Lib.Range_next_0_8, pure_bind,
      checkedMul_small (show i < 2 ^ 256 by omega) (show 8 < 2 ^ 256 by decide)
        (show i * 8 < 2 ^ 256 by omega),
      checkedAdd_small (show 4 + i * 8 < 2 ^ 256 by omega),
      checkIndex_lt (show i < 8 by omega) (by decide), toNat_lit (show i < 2 ^ 256 by omega),
      next_eq (show i + 1 < 2 ^ 256 by omega), set!_ofFn]
    rw [Fe.M.exec_bind, lane_lw h (show 4 + i * 8 + 8 ≤ d.size by omega)]
    dsimp only
    have e : (fun j : Fin 8 => if j.val = i then lw (BLAKE2.word d (4 + i * 8))
        else lw (if j.val < i then BLAKE2.word d (4 + 8 * j.val) else 0)) =
        fun j => lw (if j.val < i + 1 then BLAKE2.word d (4 + 8 * j.val) else 0) := by
      funext j
      by_cases hj : j.val = i
      · simp [hj, Nat.mul_comm]
      · by_cases hj' : j.val < i
        · simp [hj, hj', show j.val < i + 1 by omega]
        · simp [hj, hj', show ¬ j.val < i + 1 by omega]
    rw [e]
    exact h_loop h hd r1 r2 r3 r4 r5 r6 r7 r8 n (i + 1) (by omega)

/-- The loop reading the message `m`, from word `i`. -/
theorem m_loop {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    (hd : d.size = 213) r0 r2 r3 r4 r5 r6 r7 r8 :
    ∀ n i, i + n = 16 →
      (compress_MemBuffer.b5.b9 b r0
          (toV (wOf fun k => if k < i then BLAKE2.word d (68 + 8 * k) else 0)) r2 r3 r4 r5 r6 r7 r8
          (UInt256.ofNat i)).exec I w =
        (compress_MemBuffer.b5.b9.b13 b r0 (toV (wOf fun k => BLAKE2.word d (68 + 8 * k)))
          (Vector.replicate 16 (UInt256.ofNat 0)) r3 r4 r5 (Range_Known_0_Known_8.mk () ()) r7 r8
          (UInt256.ofNat 0)).exec I w
  | 0, i, hi => by
    subst hi
    rw [compress_MemBuffer.b5.b9.eq_1]
    simp only [has16 _ (show 0 + 16 < 2 ^ 256 by decide), Lib.Range_start_0_8, pure_bind]
    simp only [show ¬ (0 ≤ 0 + 16 ∧ 0 + 16 < 16) by omega, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [wOf_congr (fun k hk => if_pos hk)]
  | n + 1, i, hi => by
    rw [compress_MemBuffer.b5.b9.eq_1]
    simp only [has16 _ (show i < 2 ^ 256 by omega),
      decide_eq_true (show 0 ≤ i ∧ i < 16 from ⟨by omega, by omega⟩), ↓reduceIte,
      Lib.Range_at_0_16, Lib.Range_next_0_16, pure_bind,
      checkedMul_small (show i < 2 ^ 256 by omega) (show 8 < 2 ^ 256 by decide)
        (show i * 8 < 2 ^ 256 by omega),
      checkedAdd_small (show 68 + i * 8 < 2 ^ 256 by omega),
      checkIndex_lt (show i < 16 by omega) (by decide), toNat_lit (show i < 2 ^ 256 by omega),
      next_eq (show i + 1 < 2 ^ 256 by omega)]
    rw [Fe.M.exec_bind, lane_lw h (show 68 + i * 8 + 8 ≤ d.size by omega)]
    dsimp only
    simp only [toV_wOf_set _ (show i < 16 by omega)]
    have e : (fun k => if k = i then BLAKE2.word d (68 + i * 8)
        else if k < i then BLAKE2.word d (68 + 8 * k) else 0) =
        fun k => if k < i + 1 then BLAKE2.word d (68 + 8 * k) else 0 := by
      funext k
      by_cases hk : k = i
      · simp [hk, Nat.mul_comm]
      · by_cases hk' : k < i
        · simp [hk, hk', show k < i + 1 by omega]
        · simp [hk, hk', show ¬ k < i + 1 by omega]
    rw [e]
    exact m_loop h hd r0 r2 r3 r4 r5 r6 r7 r8 n (i + 1) (by omega)

/-- The working vector before the loop of `v`: `h` in the first `i` words, `IV` in the first
`i` of the second half. -/
def vPart (H : ℕ → UInt64) (i : ℕ) (k : ℕ) : UInt64 :=
  if k < i then H k else if 8 ≤ k ∧ k < 8 + i then BLAKE2.IV[k - 8]! else 0

/-- The loop initialising `v` from `h` and `IV`, from word `i`. -/
theorem v_loop (H : ℕ → UInt64) (b : Lib.MemBuffer) r1 r3 r4 r5 r6 r7 r8 :
    ∀ n i, i + n = 8 →
      compress_MemBuffer.b5.b9.b13 b (Vector.ofFn fun j : Fin 8 => lw (H j.val)) r1
          (toV (wOf (vPart H i))) r3 r4 r5 r6 r7 r8 (UInt256.ofNat i) =
        compress_MemBuffer.b5.b9.b13 b (Vector.ofFn fun j : Fin 8 => lw (H j.val)) r1
          (toV (wOf (vPart H 8))) r3 r4 r5 r6 r7 r8 (UInt256.ofNat 8)
  | 0, i, hi => by subst hi; rfl
  | n + 1, i, hi => by
    rw [compress_MemBuffer.b5.b9.b13.eq_1]
    simp only [has8 _ (show i < 2 ^ 256 by omega),
      decide_eq_true (show 0 ≤ i ∧ i < 8 from ⟨by omega, by omega⟩), ↓reduceIte,
      Lib.Range_at_0_8, Lib.Range_next_0_8, pure_bind, IV_eq,
      checkIndex_lt (show i < 8 by omega) (by decide), checkIndex_lt (show i < 16 by omega) (by decide),
      checkedAdd_small (show i + 8 < 2 ^ 256 by omega),
      checkIndex_lt (show i + 8 < 16 by omega) (by decide), toNat_lit (show i < 2 ^ 256 by omega),
      toNat_lit (show i + 8 < 2 ^ 256 by omega), getElem!_ofFn _ (show i < 8 by omega),
      toV_wOf_set _ (show i < 16 by omega), toV_wOf_set _ (show i + 8 < 16 by omega),
      next_eq (show i + 1 < 2 ^ 256 by omega)]
    have e : (fun k => if k = i + 8 then BLAKE2.IV[i]! else
        if k = i then H i else vPart H i k) = vPart H (i + 1) := by
      funext k
      unfold vPart
      by_cases hk : k = i + 8
      · subst hk; simp [show ¬ i + 8 < i + 1 by omega, show i + 8 < 8 + (i + 1) by omega]
      · by_cases hk' : k = i
        · subst hk'; simp
        · by_cases h1 : k < i
          · simp [hk, hk', h1, show k < i + 1 by omega]
          · by_cases h2 : 8 ≤ k ∧ k < 8 + i
            · simp [hk, hk', h1, h2, show ¬ k < i + 1 by omega, show 8 ≤ k ∧ k < 8 + (i + 1) by omega]
            · simp [hk, hk', h1, h2, show ¬ k < i + 1 by omega,
                show ¬ (8 ≤ k ∧ k < 8 + (i + 1)) by omega]
    rw [e]
    exact v_loop H b r1 r3 r4 r5 r6 r7 r8 n (i + 1) (by omega)

/-! ## `compress` -/

theorem not_lw (x : UInt64) : IntTy.not (.u 64) (lw x) = lw (~~~x) := by
  have hx := x.toNat_lt
  have hz : (-(x.toNat : ℤ) - 1) % 2 ^ 64 = ((2 ^ 64 - 1 - x.toNat : ℕ) : ℤ) := by
    have e : (-(x.toNat : ℤ) - 1) = ((2 ^ 64 - 1 - x.toNat : ℕ) : ℤ) + 2 ^ 64 * (-1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by omega)]
  simp only [IntTy.not, IntTy.wrap, IntTy.val, lw, toNat_lit (lw_lt x), hz, Int.toNat_natCast,
    UInt64.toNat_not]
  rfl

/-- The state words `h` of the input. -/
def hOf (d : ByteArray) (k : ℕ) : UInt64 := BLAKE2.word d (4 + 8 * k)

/-- The message block of the input. -/
def mOf (d : ByteArray) : Words := wOf fun k => BLAKE2.word d (68 + 8 * k)

/-- The working vector before the rounds: `h`, `IV`, the counter and the final flag. -/
def vOf (d : ByteArray) : Words :=
  let v := fun k => if k = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 k
  let v := fun k => if k = 13 then v 13 ^^^ BLAKE2.word d 204 else v k
  wOf (if byteAt d 212 = 1 then fun k => if k = 14 then ~~~v 14 else v k else v)

/-- **`compress`**: on a buffer holding 213 bytes whose final byte is 0 or 1, the new state
words, with the world unchanged. -/
theorem compress_spec {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) (hd : d.size = 213) (hf : byteAt d 212 ≤ 1) :
    (compress_MemBuffer b).exec I w = some (.ok (Vector.ofFn fun j : Fin 8 =>
      lw (outW (fun j => hOf d j.val) (BLAKE2.roundsFast (mOf d) (roundsOf d) 0 (vOf d)) j), w)) := by
  have hb := byteAt_lt d 212
  unfold compress_MemBuffer
  simp only [Fe.M.exec_bind, len_exec, INPUT_LEN, holds_len h hd, decide_true, ↓reduceIte,
    byte_exec h (show 212 < d.size by omega), toNat_lit (show byteAt d 212 < 2 ^ 256 by omega),
    toNat_lit (show 1 < 2 ^ 256 by decide), decide_eq_true hf, Lib.assert, Bool.not_true,
    Bool.false_eq_true, Lib.Range_start_0_8, pure_bind]
  have e0 : Vector.replicate 8 (UInt256.ofNat 0) = Vector.ofFn fun j : Fin 8 =>
      lw (if j.val < 0 then BLAKE2.word d (4 + 8 * j.val) else 0) := by
    rw [replicate_ofFn]; rfl
  have e1 : Vector.replicate 16 (UInt256.ofNat 0) =
      toV (wOf fun k => if k < 0 then BLAKE2.word d (68 + 8 * k) else 0) := rfl
  rw [e0, h_loop h hd _ _ _ _ _ _ _ _ 8 0 rfl, e1, m_loop h hd _ _ _ _ _ _ _ _ 16 0 rfl,
    show Vector.replicate 16 (UInt256.ofNat 0) = toV (wOf (vPart (hOf d) 0)) from rfl,
    show (Vector.ofFn fun j : Fin 8 => lw (BLAKE2.word d (4 + 8 * j.val))) =
      Vector.ofFn fun j : Fin 8 => lw (hOf d j.val) from rfl,
    v_loop (hOf d) b _ _ _ _ _ _ _ 8 0 rfl, compress_MemBuffer.b5.b9.b13.eq_1]
  have hdec : decide (UInt256.ofNat (byteAt d 212) = UInt256.ofNat 1) = decide (byteAt d 212 = 1) := by
    apply decide_eq_decide.mpr
    constructor
    · intro e; have := congrArg UInt256.toNat e
      rwa [toNat_lit (show byteAt d 212 < 2 ^ 256 by omega), toNat_lit (by decide)] at this
    · intro e; rw [e]
  simp only [has8 _ (show 8 < 2 ^ 256 by decide), show ¬ (0 ≤ 8 ∧ 8 < 8) by omega, decide_false,
    Bool.false_eq_true, ↓reduceIte, pure_bind, Fe.M.exec_bind,
    lane_lw h (show 196 + 8 ≤ d.size by omega), lane_lw h (show 204 + 8 ≤ d.size by omega),
    byte_exec h (show 212 < d.size by omega), hdec,
    checkIndex_lt (show 12 < 16 by decide) (by decide), checkIndex_lt (show 13 < 16 by decide) (by decide),
    checkIndex_lt (show 14 < 16 by decide) (by decide), toNat_lit (show 12 < 2 ^ 256 by decide),
    toNat_lit (show 13 < 2 ^ 256 by decide), toNat_lit (show 14 < 2 ^ 256 by decide),
    toV_wOf_get _ (show 12 < 16 by decide), toV_wOf_get _ (show 13 < 16 by decide),
    toV_wOf_get _ (show 14 < 16 by decide), toV_wOf_set _ (show 12 < 16 by decide),
    toV_wOf_set _ (show 13 < 16 by decide), toV_wOf_set _ (show 14 < 16 by decide), xor_lw,
    not_lw]
  rw [show (wOf fun k => BLAKE2.word d (68 + 8 * k)) = mOf d from rfl]
  have tail : (do
      let v115 ← rounds_MemBuffer b
      compress_MemBuffer.b5.b9.b13.b20 v115 (Vector.ofFn fun j : Fin 8 => lw (hOf d j.val))
        (toV (mOf d)) (toV (vOf d)) (UInt256.ofNat 0) ⟨(), ()⟩ ⟨(), ()⟩ ⟨(), ()⟩ default
        default).exec I w =
      some (.ok (Vector.ofFn fun j : Fin 8 =>
        lw (outW (fun j => hOf d j.val) (BLAKE2.roundsFast (mOf d) (roundsOf d) 0 (vOf d)) j), w)) := by
    rw [Fe.M.exec_bind, rounds_exec h hd]
    dsimp only
    obtain ⟨r7', e⟩ := tens_spec (lt_trans (roundsOf_lt d) (by decide)) (mOf d) (vOf d)
      (Vector.ofFn fun j : Fin 8 => lw (hOf d j.val)) ⟨(), ()⟩ ⟨(), ()⟩ ⟨(), ()⟩ default
      (roundsOf d) 0 default rfl (by omega)
    rw [show toV (vOf d) = toV (BLAKE2.roundsFast (mOf d) 0 0 (vOf d)) from rfl, e]
    have e2 : (Vector.ofFn fun j : Fin 8 => lw (hOf d j.val)) = Vector.ofFn fun j : Fin 8 =>
        lw (if j.val < 0 then outW (fun j => hOf d j.val)
          (BLAKE2.roundsFast (mOf d) (roundsOf d) 0 (vOf d)) j else hOf d j.val) := by
      congr 1
    rw [e2, final_spec _ _ _ _ _ _ _ _ _ 8 0 rfl, Fe.M.exec_pure]
  by_cases hf1 : byteAt d 212 = 1
  · simp only [hf1, decide_true, ↓reduceIte]
    rw [show (wOf fun k => if k = 14 then ~~~if 14 = 13 then
        (if 13 = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 13) ^^^
          BLAKE2.word d 204
        else if 14 = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 14
        else if k = 13 then (if 13 = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196
          else vPart (hOf d) 8 13) ^^^ BLAKE2.word d 204
        else if k = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 k) =
        vOf d by simp [vOf, hf1]]
    exact tail
  · simp only [hf1, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [show (wOf fun k => if k = 13 then (if 13 = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196
          else vPart (hOf d) 8 13) ^^^ BLAKE2.word d 204
        else if k = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 k) =
        vOf d by simp [vOf, hf1]]
    exact tail

/-! ## Against EVMLean's `F` -/

theorem array_set_get {α : Type} [Inhabited α] (a : Array α) {i j : ℕ} (hi : i < a.size) (x : α) :
    (a.set! i x)[j]! = if j = i then x else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set! i x) j (by simpa using hj), getElem!_pos a j hj]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds hj]
    by_cases e : i = j
    · subst e; simp
    · simp [e, Ne.symm e]
  · rw [getElem!_neg (a.set! i x) j (by simpa using hj), getElem!_neg a j hj,
      if_neg (by omega)]

theorem ofFn_get {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

/-- The state words of the input, as `compressInput` decodes them. -/
def hArr (d : ByteArray) : Array UInt64 := Array.ofFn fun i : Fin 8 => BLAKE2.word d (4 + 8 * i.val)

/-- The message block of the input, as `compressInput` decodes it. -/
def mArr (d : ByteArray) : Array UInt64 := Array.ofFn fun i : Fin 16 => BLAKE2.word d (68 + 8 * i.val)

theorem mOf_eq (d : ByteArray) : Words.ofArray (mArr d) = mOf d := by
  rw [ofArray_eq, mOf]
  exact wOf_congr fun k hk => by rw [mArr, ofFn_get _ hk]

theorem IV_size : BLAKE2.IV.size = 8 := rfl

theorem vOf_eq (d : ByteArray) :
    let v := hArr d ++ BLAKE2.IV
    let v := (v.set! 12 (v[12]! ^^^ BLAKE2.word d 196)).set! 13 (v[13]! ^^^ BLAKE2.word d 204)
    let v := if decide (byteAt d 212 = 1) = true then v.set! 14 (~~~v[14]!) else v
    Words.ofArray v = vOf d := by
  intro v0 v1 v2
  have hs0 : v0.size = 16 := by simp [v0, hArr, IV_size]
  have g0 : ∀ k < 16, v0[k]! = vPart (hOf d) 8 k := by
    intro k hk
    simp only [v0, vPart, hOf]
    by_cases h8 : k < 8
    · rw [getElem!_pos _ _ (by simp [hArr, IV_size]; omega), Array.getElem_append_left
        (by simp [hArr]; omega), if_pos h8]
      simp [hArr]
    · rw [getElem!_pos _ _ (by simp [hArr, IV_size]; omega), Array.getElem_append_right
        (by simp [hArr]; omega), if_neg h8, if_pos ⟨by omega, by omega⟩,
        getElem!_pos _ _ (by rw [IV_size]; omega)]
      simp [hArr]
  have hs1 : v1.size = 16 := by simp [v1, hs0]
  have g1 : ∀ k < 16, v1[k]! = (fun k => if k = 13 then (if 13 = 12 then vPart (hOf d) 8 12 ^^^
      BLAKE2.word d 196 else vPart (hOf d) 8 13) ^^^ BLAKE2.word d 204
      else if k = 12 then vPart (hOf d) 8 12 ^^^ BLAKE2.word d 196 else vPart (hOf d) 8 k) k := by
    intro k hk
    simp only [v1]
    rw [array_set_get _ (by simp [hs0]), array_set_get _ (by omega), g0 13 (by decide),
      g0 12 (by decide), g0 k hk]
    by_cases e13 : k = 13
    · simp [e13]
    · by_cases e12 : k = 12
      · simp [e12]
      · simp [e13, e12]
  rw [ofArray_eq, vOf]
  apply wOf_congr
  intro k hk
  simp only [v2]
  by_cases hf : byteAt d 212 = 1
  · simp only [hf, decide_true, ↓reduceIte]
    rw [array_set_get _ (by omega), g1 14 (by decide), g1 k hk]
  · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact g1 k hk

/-- `compress`'s words are those of EVMLean's `F` on the decoded input. -/
theorem F_get (d : ByteArray) (j : Fin 8) :
    (BLAKE2.F (roundsOf d) (hArr d) (mArr d) (BLAKE2.word d 196) (BLAKE2.word d 204)
        (decide (byteAt d 212 = 1)))[j.val]! =
      outW (fun j => hOf d j.val) (BLAKE2.roundsFast (mOf d) (roundsOf d) 0 (vOf d)) j := by
  rw [BLAKE2.F_eq_Ffast _ (by simp [hArr]) (by simp [mArr])]
  unfold BLAKE2.Ffast
  simp only
  rw [vOf_eq, mOf_eq, ofFn_get _ j.isLt, BLAKE2.toArray_get _ (by omega),
    BLAKE2.toArray_get _ (by omega), outW, ← UInt64.xor_assoc]
  simp [hArr, hOf]

end FeProofs.Blake2F
