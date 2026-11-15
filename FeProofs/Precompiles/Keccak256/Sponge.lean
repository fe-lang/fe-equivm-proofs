import FeProofs.Precompiles.Keccak256.Permute
import FeProofs.Precompiles.Keccak256.Spec
import FeProofs.Precompiles.Ripemd160.Block

/-!
# Keccak: fevm's sponge on two words

The state `Keccak256 { lanes, position }` at a lane boundary `8 j` with lanes `toL s`:

- `update_word_spec`: `update_word x 32` at lane `j` with `j + 4 < 17` XORs the four lanes of
  the word, `laneOf x 0` to `laneOf x 3` (its bytes from `8 i`, little-endian: `chunk_eq`), into
  lanes `j` to `j + 3` (`absorb32`) and moves to `8 j + 32`, without a permutation;
- `pad_spec` and `finish_spec`: at lane `j < 17`, `pad` XORs `1` into lane `j` and `2 ^ 63` into
  lane 16 (`padS`) and permutes (`permute_spec`); `finish_word` returns the first four lanes,
  byte-swapped, as a big-endian word (`wordOf`).

For two words the absorbed and padded state is `mix64`, the final block EVMLean's `hash` absorbs
(`mix64_eq`, `Spec.lean`), and the 32 digest bytes are those of `wordOf` (`fromBE_digest`).  So
`new`, `update_word x 32`, `update_word y 32`, `finish_word` return the big-endian word of
`KEC (x ‖ y)` (`keccak_two_words`), total, and `KEC (x ‖ y)` is the 32 bytes of that word
(`kec_two_words`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Keccak

open FeProofs.Precompiles
open FeProofs.Blake2F (lw lw_lt lw_toNat xor_lw)
open Precompiles.Exported.EcrecoverPrecompile

/-! ## The lanes of a word -/

theorem dig (x S n : ℕ) (hn : n < 8) : x / 2 ^ S % 2 ^ 64 / 256 ^ n % 256 = x / 2 ^ (S + 8 * n) % 256 := by
  rw [show (256 : ℕ) ^ n = 2 ^ (n * 8) by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul, mul_comm],
    FeProofs.Ripemd160.byte_of_low _ _ hn, Nat.div_div_eq_div_mul, ← pow_add]

theorem be8_lt {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ} (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    be8 b0 b1 b2 b3 b4 b5 b6 b7 < 2 ^ 64 := by
  unfold be8; omega

theorem laneOf_toNat (a i : ℕ) : (laneOf a i).toNat =
    be8 (bt a (8 * i + 7)) (bt a (8 * i + 6)) (bt a (8 * i + 5)) (bt a (8 * i + 4))
      (bt a (8 * i + 3)) (bt a (8 * i + 2)) (bt a (8 * i + 1)) (bt a (8 * i)) := by
  have h : ∀ k, bt a k < 256 := fun k => Nat.mod_lt _ (by decide)
  rw [laneOf, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (be8_lt (h _) (h _) (h _) (h _) (h _) (h _)
    (h _) (h _))]

/-- Lane `i` of a word, as `update_word` and `word_at` make it: the eight bytes from `8 i`,
swapped to little-endian. -/
theorem chunk_eq (x : ℕ) {i : ℕ} (hi : i < 4) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (x / 2 ^ (192 - 64 * i) % 2 ^ 64)) =
      lw (laneOf x i) := by
  apply word_eq_of_toNat
  rw [swapBytes_u64_toNat (Nat.mod_lt _ (by decide)), lw_toNat, laneOf_toNat]
  simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    List.nil_append]
  simp (disch := decide) only [dig]
  interval_cases i <;> simp only [be8, bt, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.zero_mul,
    Nat.zero_add]

theorem chunk0 (x : UInt256) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (x.toNat / 2 ^ 192 % 2 ^ 64)) = lw (laneOf x.toNat 0) :=
  chunk_eq x.toNat (i := 0) (by decide)
theorem chunk1 (x : UInt256) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (x.toNat / 2 ^ 128 % 2 ^ 64)) = lw (laneOf x.toNat 1) :=
  chunk_eq x.toNat (i := 1) (by decide)
theorem chunk2 (x : UInt256) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (x.toNat / 2 ^ 64 % 2 ^ 64)) = lw (laneOf x.toNat 2) :=
  chunk_eq x.toNat (i := 2) (by decide)
theorem chunk3 (x : UInt256) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (x.toNat % 2 ^ 64)) = lw (laneOf x.toNat 3) := by
  rw [← chunk_eq x.toNat (i := 3) (by decide)]; simp

/-! ## Absorbing a word -/

theorem toL_get! (s : Vector UInt64 25) {k : ℕ} (hk : k < 25) : (toL s)[k]! = lw s[k]! := by
  simp [toL, getElem!_pos, hk]

theorem toL_set! (s : Vector UInt64 25) {k : ℕ} (hk : k < 25) (v : UInt64) :
    (toL s).set! k (lw v) = toL (s.set! k v) := by
  apply Vector.ext
  intro i hi
  rw [set!_eq _ _ hk, set!_eq _ _ hk]
  simp only [toL, Vector.getElem_set, Vector.getElem_map]
  split <;> rfl

theorem shl_zero (x : UInt256) : x <<< UInt256.ofNat 0 = x := by
  apply word_eq_of_toNat
  rw [shiftLeft_toNat _ (by decide) (by rw [pow_zero, mul_one]; exact x.val.isLt), pow_zero,
    one_mul]

/-- The state after absorbing the 32 bytes of the word `x` from lane `j`. -/
def absorb32 (s : Vector UInt64 25) (j : ℕ) (x : ℕ) : Vector UInt64 25 :=
  let s1 := s.set! j (s[j]! ^^^ laneOf x 0)
  let s2 := s1.set! (j + 1) (s1[j + 1]! ^^^ laneOf x 1)
  let s3 := s2.set! (j + 2) (s2[j + 2]! ^^^ laneOf x 2)
  s3.set! (j + 3) (s3[j + 3]! ^^^ laneOf x 3)

/-- **`update_word` of a whole word** at a lane boundary that leaves the block unfinished: the
four lanes of the word are XORed into the state, and no permutation runs. -/
theorem update_word_spec (s : Vector UInt64 25) {j : ℕ} (hj : j + 4 < 17) (x : UInt256) :
    Keccak256_update_word ⟨toL s, UInt256.ofNat (8 * j)⟩ x (UInt256.ofNat 32) =
      pure ((), ⟨toL (absorb32 s j x.toNat), UInt256.ofNat (8 * j + 32)⟩) := by
  have h32 : checkedSub (UInt256.ofNat 32) (UInt256.ofNat 32) = pure (UInt256.ofNat 0) := rfl
  have hne : decide (UInt256.ofNat 32 ≠ UInt256.ofNat 0) = true := by decide
  have hd8 : 8 * j / 8 = j := by omega
  have hm8 : 8 * j % 8 = 0 := by omega
  have hne136 : decide (UInt256.ofNat (8 * j + 32) = UInt256.ofNat 136) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have := congrArg UInt256.toNat h
    rw [toNat_lit (by omega), toNat_lit (by decide)] at this
    omega
  simp (disch := omega) only [Keccak256_update_word, toNat_lit, Lib.assert, decide_true, Bool.not_true,
    Bool.false_eq_true, if_false, pure_bind, hne, if_true, checkedAdd_small,
    show 8 * j + 32 ≤ 136 by omega, h32, checkedMul_small, Nat.zero_mul, shl_zero,
    shiftRight_toNat, downcast_truncate_u256_u64_eq, chunk0, chunk1, chunk2, chunk3,
    checkedDiv_lit, checkedRem_lit, hd8, hm8, FeProofs.Ripemd160.downcast_u64,
    checkIndex_lit, toL_get!, xor_lw, toL_set!, hne136, le_refl, Nat.zero_mod, absorb32]

/-! ## Padding and the digest word -/

/-- The padding at lane `j`: the suffix `0x01` at the next byte, which starts lane `j`, and the
final bit at byte 135. -/
def padS (s : Vector UInt64 25) (j : ℕ) : Vector UInt64 25 :=
  let s1 := s.set! j (s[j]! ^^^ 1)
  s1.set! 16 (s1[16]! ^^^ 0x8000000000000000)

theorem pad_spec (s : Vector UInt64 25) {j : ℕ} (hj : j < 17) :
    Keccak256_pad ⟨toL s, UInt256.ofNat (8 * j)⟩ =
      pure ((), ⟨toL (Keccak256.permute (padS s j)), UInt256.ofNat (8 * j)⟩) := by
  have hd8 : 8 * j / 8 = j := by omega
  have hm8 : 8 * j % 8 = 0 := by omega
  have h1 : IntTy.shl (.u 64) (UInt256.ofNat 1) (UInt256.ofNat 0) = lw 1 := rfl
  have h63 : UInt256.ofNat 9223372036854775808 = lw 0x8000000000000000 := rfl
  simp (disch := omega) only [Keccak256_pad, toNat_lit, checkedRem_lit, hm8, checkedMul_small,
    Nat.zero_mul, FeProofs.Ripemd160.downcast_u64, Nat.zero_mod, h1, checkedDiv_lit, hd8,
    checkIndex_lit, toL_get!, xor_lw, toL_set!, h63, pure_bind, permute_spec, padS]

/-- The value `swap_bytes` gives at `u64` of a lane. -/
def sw (L : UInt64) : ℕ := (List.range 8).foldl (fun acc n => acc * 256 + L.toNat / 256 ^ n % 256) 0

/-- The digest word of a state: the first four lanes, each byte-swapped, big-endian. -/
def wordOf (st : Vector UInt64 25) : ℕ :=
  ((sw st[0] * 2 ^ 64 + sw st[1]) * 2 ^ 64 + sw st[2]) * 2 ^ 64 + sw st[3]

theorem sw_lt (L : UInt64) : sw L < 2 ^ 64 := by
  have := foldl_digits_lt (fun n => L.toNat / 256 ^ n % 256) (fun n => Nat.mod_lt _ (by decide))
    (List.range 8) 0 0 (by decide)
  simpa using this

theorem swap_lw (L : UInt64) : IntTy.swapBytes (.u 64) (lw L) = UInt256.ofNat (sw L) := by
  apply word_eq_of_toNat
  rw [lw, swapBytes_u64_toNat L.toNat_lt, toNat_lit (lt_trans (sw_lt L) (by decide))]
  rfl

theorem lanes4 {a0 a1 a2 a3 : ℕ} (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64)
    (h3 : a3 < 2 ^ 64) :
    UInt256.ofNat a0 <<< UInt256.ofNat 192 ||| UInt256.ofNat a1 <<< UInt256.ofNat 128 |||
        UInt256.ofNat a2 <<< UInt256.ofNat 64 ||| UInt256.ofNat a3 =
      UInt256.ofNat (((a0 * 2 ^ 64 + a1) * 2 ^ 64 + a2) * 2 ^ 64 + a3) := by
  have l : ∀ {n : ℕ}, n < 2 ^ 64 → (UInt256.ofNat n).toNat = n := fun h =>
    toNat_lit (lt_trans h (by norm_num))
  apply word_eq_of_toNat
  change (UInt256.lor (UInt256.lor (UInt256.lor _ _) _) _).toNat = _
  rw [u256_lor_toNat_exact, u256_lor_toNat_exact, u256_lor_toNat_exact,
    shiftLeft_toNat _ (by decide) (by rw [l h0]; omega),
    shiftLeft_toNat _ (by decide) (by rw [l h1]; omega),
    shiftLeft_toNat _ (by decide) (by rw [l h2]; omega), l h0, l h1, l h2, l h3,
    toNat_lit (by omega)]
  have e1 : 2 ^ 192 * a0 ||| 2 ^ 128 * a1 = 2 ^ 128 * (2 ^ 64 * a0 + a1) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (show 2 ^ 128 * a1 < 2 ^ 192 by omega)]; ring
  have e2 : 2 ^ 128 * (2 ^ 64 * a0 + a1) ||| 2 ^ 64 * a2 =
      2 ^ 64 * ((2 ^ 64 * a0 + a1) * 2 ^ 64 + a2) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (show 2 ^ 64 * a2 < 2 ^ 128 by omega)]; ring
  have e3 : 2 ^ 64 * ((2 ^ 64 * a0 + a1) * 2 ^ 64 + a2) ||| a3 =
      ((a0 * 2 ^ 64 + a1) * 2 ^ 64 + a2) * 2 ^ 64 + a3 := by
    rw [← Nat.two_pow_add_eq_or_of_lt h3]; ring
  rw [e1, e2, e3]

/-- **`finish_word`** at lane `j`: pad, permute, and the digest word. -/
theorem finish_spec (s : Vector UInt64 25) {j : ℕ} (hj : j < 17) :
    Keccak256_finish_word ⟨toL s, UInt256.ofNat (8 * j)⟩ =
      pure (UInt256.ofNat (wordOf (Keccak256.permute (padS s j)))) := by
  simp only [Keccak256_finish_word, pad_spec s hj, pure_bind, checkIndex_lit (show 0 < 25 by decide)
    (by decide), checkIndex_lit (show 1 < 25 by decide) (by decide),
    checkIndex_lit (show 2 < 25 by decide) (by decide), checkIndex_lit (show 3 < 25 by decide)
    (by decide), toNat_lit (show 0 < 2 ^ 256 by decide), toNat_lit (show 1 < 2 ^ 256 by decide),
    toNat_lit (show 2 < 2 ^ 256 by decide), toNat_lit (show 3 < 2 ^ 256 by decide),
    toL_get! _ (show 0 < 25 by decide), toL_get! _ (show 1 < 25 by decide),
    toL_get! _ (show 2 < 25 by decide), toL_get! _ (show 3 < 25 by decide), swap_lw,
    lanes4 (sw_lt _) (sw_lt _) (sw_lt _) (sw_lt _), wordOf]
  simp [getElem!_pos]

/-! ## The digest bytes are the word's -/

theorem toBytes32_fromBE (D : ByteArray) (hD : D.size = 32) :
    Weierstrass.toBytes32 (fromByteArrayBigEndian D) = D := by
  have hlt : fromByteArrayBigEndian D < 2 ^ 256 := by
    have := fromBytes'_le (bs := D.toList.reverse)
    rw [List.length_reverse, byteArray_toList_eq, Array.length_toList] at this
    have h8 : D.data.size = 32 := hD
    rw [h8] at this
    rw [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp, byteArray_toList_eq]
    exact this
  rw [toBytes32_eq hlt]
  apply ByteArray.ext
  apply Array.ext'
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    show (UInt256.ofNat _).toByteArray.size = D.size
    rw [toByteArray_size, hD]
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian, fromByteArrayBigEndian_toByteArray,
      toNat_lit hlt]

theorem digest_size (st : Vector UInt64 25) : (digest st).size = 32 := Array.size_ofFn

theorem shr_byte (L : UInt64) (m : ℕ) (hm : m < 8) :
    (L.shiftRight (8 * m).toUInt64).toUInt8 = UInt8.ofNat (L.toNat / 2 ^ (8 * m)) := by
  change UInt8.ofNat (L >>> (8 * m).toUInt64).toNat = _
  rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 8 * m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * m < 64 by omega)]

theorem fromBE_digest (st : Vector UInt64 25) : fromByteArrayBigEndian (digest st) = wordOf st := by
  have e : (digest st).toList = List.ofFn fun i : Fin 32 =>
      UInt8.ofNat ((st[Fin.ofNat 25 (i.val / 8)]).toNat / 2 ^ (8 * (i.val % 8))) := by
    rw [byteArray_toList_eq]
    show (Array.ofFn _).toList = _
    rw [Array.toList_ofFn]
    congr 1
    funext i
    exact shr_byte _ _ (Nat.mod_lt _ (by decide))
  rw [fromByteArrayBigEndian, e, fromBytesBigEndian_ofFn
    (fun n => (st[Fin.ofNat 25 (n / 8)]).toNat / 2 ^ (8 * (n % 8))) 32]
  simp only [wordOf, sw, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Fin.ofNat,
    Fin.getElem_fin, Nat.reducePow]
  ring

/-! ## Two words -/

/-- The state after absorbing the words `x` and `y` and padding, before the permutation. -/
def state2 (x y : ℕ) : Vector UInt64 25 :=
  padS (absorb32 (absorb32 (Vector.replicate 25 0) 0 x) 4 y) 8

theorem mix64_eq (x y : ℕ) : mix64 x y = state2 x y := by
  apply Vector.ext
  intro i hi
  simp (disch := decide) only [state2, padS, absorb32, set!_eq]
  interval_cases i <;> simp [mix64, getElem!_pos]

/-- The digest word of `x ‖ y`. -/
def hashWord (x y : ℕ) : ℕ := wordOf (Keccak256.permute (state2 x y))

/-- **EVMLean's Keccak-256 of two words** is the 32 bytes of `hashWord`. -/
theorem kec_two_words (x y : ℕ) :
    KEC (Weierstrass.toBytes32 x ++ Weierstrass.toBytes32 y) = Weierstrass.toBytes32 (hashWord x y) := by
  rw [KEC, hash64, mix64_eq, hashWord, ← fromBE_digest,
    toBytes32_fromBE _ (digest_size _)]

theorem hashWord_eq (x y : ℕ) :
    hashWord x y = fromByteArrayBigEndian (KEC (Weierstrass.toBytes32 x ++ Weierstrass.toBytes32 y)) := by
  rw [kec_two_words, hashWord, ← fromBE_digest, toBytes32_fromBE _ (digest_size _)]

theorem new_eq : Keccak256_new = pure ⟨toL (Vector.replicate 25 0), UInt256.ofNat 0⟩ := by
  simp only [Keccak256_new, toL, Vector.map_replicate]
  rfl

theorem update_first (x : UInt256) :
    Keccak256_update_word ⟨toL (Vector.replicate 25 0), UInt256.ofNat 0⟩ x (UInt256.ofNat 32) =
      pure ((), ⟨toL (absorb32 (Vector.replicate 25 0) 0 x.toNat), UInt256.ofNat 32⟩) :=
  update_word_spec (Vector.replicate 25 0) (j := 0) (by decide) x

theorem update_second (s : Vector UInt64 25) (y : UInt256) :
    Keccak256_update_word ⟨toL s, UInt256.ofNat 32⟩ y (UInt256.ofNat 32) =
      pure ((), ⟨toL (absorb32 s 4 y.toNat), UInt256.ofNat 64⟩) :=
  update_word_spec s (j := 4) (by decide) y

theorem finish_two (x y : ℕ) :
    Keccak256_finish_word ⟨toL (absorb32 (absorb32 (Vector.replicate 25 0) 0 x) 4 y),
      UInt256.ofNat 64⟩ = pure (UInt256.ofNat (hashWord x y)) :=
  finish_spec _ (j := 8) (by decide)

/-- **fevm's Keccak-256 of two words**: after `new`, `update_word x 32` and `update_word y 32`,
`finish_word` returns the big-endian word of EVMLean's `KEC (x ‖ y)`. -/
theorem keccak_two_words (x y : UInt256) :
    (do
      let k ← Keccak256_new
      let (_, k) ← Keccak256_update_word k x (UInt256.ofNat 32)
      let (_, k) ← Keccak256_update_word k y (UInt256.ofNat 32)
      Keccak256_finish_word k) =
    pure (UInt256.ofNat (fromByteArrayBigEndian
      (KEC (Weierstrass.toBytes32 x.toNat ++ Weierstrass.toBytes32 y.toNat)))) := by
  simp only [new_eq, pure_bind, update_first, update_second, finish_two]
  rw [← hashWord_eq]

end FeProofs.Keccak
