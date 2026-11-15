import FeProofs.Precompiles.Field.Words
import Reasoning.Memory
import Fe.EVM.Entry

/-!
# Precompiles: the input buffer

The precompiles read their input through std's `MemBuffer`, filled by `calldatacopy`.  This file
says what the buffer functions return on a buffer that holds given bytes `d` in memory
(`Holds`): `MemBuffer_len_1` its length, `MemBuffer_byte_at` a byte, `MemBuffer_lane_at` the
little-endian value of eight bytes.

The bytes are read as numbers: `byteAt d j` is the byte at `j`, zero past the end, and
`beAt d off n` the big-endian number of the `n` bytes from `off`, zero-padded.  It is what
`fromByteArrayBigEndian` gives of `d.readBytes off n` (`readBytes_be`), the EVM's reading of call
data, and of any window of memory that holds them (`Holds.read`).

What a contract reading its input through these functions can use:
- `Holds`, and `len_exec`, `byte_exec`, `lane_exec`: the buffer functions on a buffer that holds
  `d`; `swap_be8` and `swap_swap_beAt`: `swap_bytes` at `u64` of eight bytes.
- `beAt_add`, `beAt_tail`, `beAt_lt`, `fromByteArrayBigEndian_extract`, `readBytes_be`: reading
  bytes as numbers.
- `toBytes32_eq`: `Weierstrass.toBytes32` of a number below `2 ^ 256` is its word's bytes.
- `le8`, `write_le_exec`, `le8_write_append`, `le8_read`: eight bytes written little-endian
  (`MemBuffer_write_le_u64`), with `swap_low8` and `swapBytes_u64_toNat`.
- `copyInput`, each contract's `input()`: `input_exec` and `input_holds`, the buffer it makes
  holds the call data.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory
open scoped FeProofs.Lib

namespace FeProofs.Precompiles

/-! ## Bytes as numbers -/

/-- The byte of `d` at `j`, zero past its end. -/
def byteAt (d : ByteArray) (j : ℕ) : ℕ := (d.toList.getD j 0).toNat

/-- The big-endian number of the `n` bytes of `d` from `off`, zero past its end. -/
def beAt (d : ByteArray) (off : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => beAt d off n * 256 + byteAt d (off + n)

theorem byteAt_lt (d : ByteArray) (j : ℕ) : byteAt d j < 256 := (d.toList.getD j 0).toNat_lt

theorem byteAt_of_ge {d : ByteArray} {j : ℕ} (h : d.size ≤ j) : byteAt d j = 0 := by
  have hl : d.toList.length = d.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : d.toList.length ≤ j)]

theorem beAt_lt (d : ByteArray) (off n : ℕ) : beAt d off n < 2 ^ (8 * n) := by
  induction n with
  | zero => simp [beAt]
  | succ n ih =>
    have := byteAt_lt d (off + n)
    rw [beAt, show 8 * (n + 1) = 8 * n + 8 by ring, pow_add]
    have : beAt d off n * 256 + byteAt d (off + n) < (beAt d off n + 1) * 256 := by omega
    calc _ < (beAt d off n + 1) * 256 := this
      _ ≤ 2 ^ (8 * n) * 2 ^ 8 := Nat.mul_le_mul (by omega) (by norm_num)

theorem beAt_add (d : ByteArray) (off m n : ℕ) :
    beAt d off (m + n) = beAt d off m * 2 ^ (8 * n) + beAt d (off + m) n := by
  induction n with
  | zero => simp [beAt]
  | succ n ih =>
    rw [← Nat.add_assoc, beAt, ih, beAt, show off + (m + n) = off + m + n by ring,
      show 8 * (n + 1) = 8 * n + 8 by ring, pow_add]
    ring

/-- Past the end there are only zeros. -/
theorem beAt_tail {d : ByteArray} {off m : ℕ} (h : d.size ≤ off + m) (k : ℕ) :
    beAt d off (m + k) = beAt d off m * 2 ^ (8 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, beAt, ih, byteAt_of_ge (by omega), show 8 * (k + 1) = 8 * k + 8 by ring,
      pow_add]
    ring

theorem fromBytesBigEndian_snoc (l : List UInt8) (b : UInt8) :
    fromBytesBigEndian (l ++ [b]) = fromBytesBigEndian l * 256 + b.toNat := by
  rw [fromBytesBigEndian_append]
  simp [fromBytesBigEndian, fromBytes']

/-- The bytes from `off` that `d` has, as a list. -/
theorem fromBytesBigEndian_take_drop (d : ByteArray) (off n : ℕ) (h : off + n ≤ d.size) :
    fromBytesBigEndian ((d.toList.drop off).take n) = beAt d off n := by
  have hl : d.toList.length = d.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  induction n with
  | zero => simp [beAt, fromBytesBigEndian, fromBytes']
  | succ n ih =>
    have hlt : off + n < d.toList.length := by omega
    rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hlt, Option.toList_some,
      fromBytesBigEndian_snoc, ih (by omega), beAt]
    simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

/-- A window that `d` covers. -/
theorem fromByteArrayBigEndian_extract (d : ByteArray) (off n : ℕ) (h : off + n ≤ d.size) :
    fromByteArrayBigEndian (d.extract off (off + n)) = beAt d off n := by
  rw [fromByteArrayBigEndian, byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, ← byteArray_toList_eq, show off + n - off = n by omega]
  exact fromBytesBigEndian_take_drop d off n h

/-- The list of the bytes from `off` that `d` has, padded with zeros to `n`. -/
theorem fromBytesBigEndian_padded (d : ByteArray) (off n : ℕ) :
    fromBytesBigEndian ((d.toList.drop off).take n ++
      List.replicate (n - ((d.toList.drop off).take n).length) 0) = beAt d off n := by
  have hl : d.toList.length = d.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [fromBytesBigEndian_append_zeros, List.length_take, List.length_drop, hl]
  by_cases h : off + n ≤ d.size
  · rw [fromBytesBigEndian_take_drop d off n h, min_eq_left (by omega), Nat.sub_self]
    simp
  · obtain ⟨k, hk⟩ : ∃ k, n = (d.size - off) + k := ⟨n - (d.size - off), by omega⟩
    rw [min_eq_right (by omega), hk, List.take_add, beAt_tail (by omega)]
    have hdrop : (List.drop (d.size - off) (List.drop off d.toList)) = [] := by
      rw [List.drop_drop, List.drop_eq_nil_of_le (by omega)]
    rw [hdrop, List.take_nil, List.append_nil]
    by_cases ho : off ≤ d.size
    · rw [fromBytesBigEndian_take_drop d off _ (by omega)]
      congr 2
      omega
    · rw [show d.size - off = 0 by omega]
      simp [beAt, fromBytesBigEndian, fromBytes']

/-- **The EVM's reading of call data** gives `beAt`. -/
theorem readBytes_be (d : ByteArray) (off n : ℕ) (hoff : off < 2 ^ 64) (hn : n < 2 ^ 64) :
    fromByteArrayBigEndian (d.readBytes off n) = beAt d off n := by
  unfold ByteArray.readBytes
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hoff, hn⟩)]
  have hc : (d.copySlice off ByteArray.empty 0 n).toList = (d.toList.drop off).take n := by
    rw [ByteArray.copySlice_eq_append, byteArray_toList_eq, byteArray_toList_eq]
    simp [Array.toList_extract, List.extract_eq_take_drop]
  have hsz : (d.copySlice off ByteArray.empty 0 n).size =
      ((d.toList.drop off).take n).length := by
    rw [← hc, byteArray_toList_eq, Array.length_toList]; rfl
  rw [fromByteArrayBigEndian, byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
    ← byteArray_toList_eq, hc, byteArray_zeroes_toList, hsz]
  exact fromBytesBigEndian_padded d off n

/-- **Call data read as if extended with zeros**, as EVMLean's precompile specifications read it,
    gives `beAt`. -/
theorem readWithPadding_be (d : ByteArray) (off n : ℕ) :
    fromByteArrayBigEndian (d.readWithPadding off n) = beAt d off n := by
  have hl : d.toList.length = d.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hr : (d.readWithoutPadding off n).toList = (d.toList.drop off).take n := by
    unfold ByteArray.readWithoutPadding
    split_ifs with h
    · rw [List.drop_eq_nil_of_le (by omega), List.take_nil, byteArray_toList_eq]; rfl
    · rw [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
        ← byteArray_toList_eq]
      by_cases hn : n ≤ d.size
      · rw [Nat.min_eq_left hn, Nat.add_sub_cancel_left]
      · rw [Nat.min_eq_right (by omega), Nat.add_sub_cancel_left,
          List.take_of_length_le (by rw [List.length_drop, hl]; omega),
          List.take_of_length_le (by rw [List.length_drop, hl]; omega)]
  have hsz : (d.readWithoutPadding off n).size = ((d.toList.drop off).take n).length := by
    rw [← hr, byteArray_toList_eq, Array.length_toList]; rfl
  unfold ByteArray.readWithPadding
  rw [fromByteArrayBigEndian, byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
    ← byteArray_toList_eq, hr, byteArray_zeroes_toList, hsz]
  exact fromBytesBigEndian_padded d off n

/-- The `n` bytes of `a`, big-endian, as `toBytes32` cuts them, read back. -/
theorem fromBytesBigEndian_ofFn_shift (n a : ℕ) :
    fromBytesBigEndian (List.ofFn fun i : Fin n => (a >>> (8 * (n - 1 - i.val))).toUInt8) =
      a % 2 ^ (8 * n) := by
  induction n generalizing a with
  | zero => simp [fromBytesBigEndian, fromBytes', Nat.mod_one]
  | succ n ih =>
    rw [List.ofFn_succ_last, fromBytesBigEndian_snoc]
    have hf : (fun i : Fin n => (a >>> (8 * (n + 1 - 1 - (Fin.castSucc i).val))).toUInt8) =
        fun i : Fin n => ((a >>> 8) >>> (8 * (n - 1 - i.val))).toUInt8 := by
      funext i
      rw [← Nat.shiftRight_add]
      congr 2
      have := i.isLt
      simp only [Fin.val_castSucc]
      omega
    rw [hf, ih, Fin.val_last, show n + 1 - 1 - n = 0 by omega, Nat.mul_zero, Nat.shiftRight_zero,
      Nat.shiftRight_eq_div_pow, show 8 * (n + 1) = 8 + 8 * n by ring, pow_add, Nat.mod_mul]
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    norm_num
    ring

/-- **`toBytes32` of a number below `2 ^ 256`** is its word's bytes. -/
theorem toBytes32_eq {a : ℕ} (ha : a < 2 ^ 256) :
    Weierstrass.toBytes32 a = (UInt256.ofNat a).toByteArray := by
  apply ByteArray.ext
  apply Array.ext'
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    show (Array.ofFn _).size = (UInt256.ofNat a).toByteArray.size
    rw [Array.size_ofFn, toByteArray_size]
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian, fromByteArrayBigEndian_toByteArray,
      toNat_lit ha, fromByteArrayBigEndian, byteArray_toList_eq]
    show fromBytesBigEndian (Array.ofFn _).toList = a
    rw [Array.toList_ofFn, fromBytesBigEndian_ofFn_shift, Nat.mod_eq_of_lt ha]

/-! ## Swapping the bytes of a `u64` -/

theorem div256 {q b : ℕ} (h : b < 256) : (q * 256 + b) / 256 = q := by omega
theorem mod256 {q b : ℕ} (h : b < 256) : (q * 256 + b) % 256 = b := by omega
theorem div256_pow (x k : ℕ) : x / 256 ^ (k + 1) = x / 256 / 256 ^ k := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

/-- The big-endian number of eight bytes. -/
def be8 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : ℕ :=
  ((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7

/-- `swap_bytes` at `u64` of a big-endian number of eight bytes is the number of the bytes in
    reverse order. -/
theorem swap_be8 {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ} (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    IntTy.swapBytes (.u 64) (UInt256.ofNat (be8 b0 b1 b2 b3 b4 b5 b6 b7)) =
      UInt256.ofNat (be8 b7 b6 b5 b4 b3 b2 b1 b0) := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = be8 b0 b1 b2 b3 b4 b5 b6 b7 := ⟨_, rfl⟩
  rw [← hxdef]
  have hx : x < 2 ^ 64 := by rw [hxdef, be8]; omega
  have q1 : x / 256 = be8 0 b0 b1 b2 b3 b4 b5 b6 := by rw [hxdef, be8, div256 h7, be8]; try ring
  have q2 : x / 256 / 256 = be8 0 0 b0 b1 b2 b3 b4 b5 := by rw [q1, be8, div256 h6, be8]; try ring
  have q3 : x / 256 / 256 / 256 = be8 0 0 0 b0 b1 b2 b3 b4 := by
    rw [q2, be8, div256 h5, be8]; try ring
  have q4 : x / 256 / 256 / 256 / 256 = be8 0 0 0 0 b0 b1 b2 b3 := by
    rw [q3, be8, div256 h4, be8]; try ring
  have q5 : x / 256 / 256 / 256 / 256 / 256 = be8 0 0 0 0 0 b0 b1 b2 := by
    rw [q4, be8, div256 h3, be8]; try ring
  have q6 : x / 256 / 256 / 256 / 256 / 256 / 256 = be8 0 0 0 0 0 0 b0 b1 := by
    rw [q5, be8, div256 h2, be8]; try ring
  have q7 : x / 256 / 256 / 256 / 256 / 256 / 256 / 256 = be8 0 0 0 0 0 0 0 b0 := by
    rw [q6, be8, div256 h1, be8]; try ring
  have d0 : x / 256 ^ 0 % 256 = b7 := by rw [pow_zero, Nat.div_one, hxdef, be8, mod256 h7]
  have d1 : x / 256 ^ 1 % 256 = b6 := by rw [pow_one, q1, be8, mod256 h6]
  have d2 : x / 256 ^ 2 % 256 = b5 := by rw [div256_pow, pow_one, q2, be8, mod256 h5]
  have d3 : x / 256 ^ 3 % 256 = b4 := by rw [div256_pow, div256_pow, pow_one, q3, be8, mod256 h4]
  have d4 : x / 256 ^ 4 % 256 = b3 := by
    rw [div256_pow, div256_pow, div256_pow, pow_one, q4, be8, mod256 h3]
  have d5 : x / 256 ^ 5 % 256 = b2 := by
    rw [div256_pow, div256_pow, div256_pow, div256_pow, pow_one, q5, be8, mod256 h2]
  have d6 : x / 256 ^ 6 % 256 = b1 := by
    rw [div256_pow, div256_pow, div256_pow, div256_pow, div256_pow, pow_one, q6, be8, mod256 h1]
  have d7 : x / 256 ^ 7 % 256 = b0 := by
    rw [div256_pow, div256_pow, div256_pow, div256_pow, div256_pow, div256_pow,
      pow_one, q7, be8]
    simp [Nat.mod_eq_of_lt h0]
  simp only [IntTy.swapBytes, IntTy.pattern, IntTy.bits, IntTy.wrap, List.range_succ,
    List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ulit_toNat' _ (lt_trans hx (by decide)), Nat.mod_eq_of_lt hx, d0, d1, d2, d3, d4, d5, d6, d7]
  apply congrArg UInt256.ofNat
  norm_cast
  rw [Int.toNat_natCast, Nat.mod_eq_of_lt (by omega), be8, Nat.zero_mul, Nat.zero_add]

/-- Swapping twice gives the eight bytes back. -/
theorem swap_swap_beAt (d : ByteArray) (j : ℕ) :
    IntTy.swapBytes (.u 64) (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d j 8))) =
      UInt256.ofNat (beAt d j 8) := by
  have e : beAt d j 8 = be8 (byteAt d j) (byteAt d (j + 1)) (byteAt d (j + 2))
      (byteAt d (j + 3)) (byteAt d (j + 4)) (byteAt d (j + 5)) (byteAt d (j + 6))
      (byteAt d (j + 7)) := by simp [beAt, be8]
  have h := byteAt_lt d
  rw [e, swap_be8 (h _) (h _) (h _) (h _) (h _) (h _) (h _) (h _),
    swap_be8 (h _) (h _) (h _) (h _) (h _) (h _) (h _) (h _)]

/-! ## Little-endian bytes -/

/-- The eight bytes of `x`, least significant first. -/
def le8 (x : ℕ) : ByteArray := ⟨Array.ofFn fun k : Fin 8 => UInt8.ofNat (x / 256 ^ k.val)⟩

theorem le8_size (x : ℕ) : (le8 x).size = 8 := Array.size_ofFn

theorem fromBytesBigEndian_ofFn (g : ℕ → ℕ) (m : ℕ) :
    fromBytesBigEndian (List.ofFn fun k : Fin m => UInt8.ofNat (g k.val)) =
      (List.range m).foldl (fun acc n => acc * 256 + g n % 256) 0 := by
  induction m with
  | zero => simp [fromBytesBigEndian, fromBytes']
  | succ m ih =>
    rw [List.ofFn_succ_last, fromBytesBigEndian_snoc, List.range_succ, List.foldl_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat']
    rw [ih]

/-- The low eight bytes of a word, big-endian, as `mstoreInt (.u 64)` writes them. -/
theorem fromByteArrayBigEndian_low8 (y : UInt256) :
    fromByteArrayBigEndian (y.toByteArray.extract 24 32) = y.toNat % 2 ^ 64 := by
  have hs := toByteArray_size (v := y)
  have hsplit : y.toByteArray = y.toByteArray.extract 0 24 ++ y.toByteArray.extract 24 32 := by
    rw [ByteArray.extract_append_extract, Nat.zero_min, Nat.max_eq_right (by omega), ← hs,
      ByteArray.extract_zero_size]
  have hlt : fromByteArrayBigEndian (y.toByteArray.extract 24 32) < 2 ^ 64 := by
    have := fromBytes'_le (bs := (y.toByteArray.extract 24 32).toList.reverse)
    rw [List.length_reverse, byteArray_toList_eq, Array.length_toList] at this
    have h8 : (y.toByteArray.extract 24 32).data.size = 8 := by
      show (y.toByteArray.extract 24 32).size = 8
      rw [ByteArray.size_extract, hs]; rfl
    rw [h8] at this
    rw [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp, byteArray_toList_eq]
    exact this
  have h := fromByteArrayBigEndian_toByteArray y
  rw [hsplit, fromByteArrayBigEndian_append, ByteArray.size_extract, hs] at h
  rw [← h]
  simp only [show min 32 32 - 24 = 8 from rfl]
  omega

theorem foldl_digits_cast (f : ℕ → ℕ) (l : List ℕ) (acc : ℕ) :
    l.foldl (fun a n => a * 256 + (f n : ℤ)) (acc : ℤ) =
      ((l.foldl (fun a n => a * 256 + f n) acc : ℕ) : ℤ) := by
  induction l generalizing acc with
  | nil => rfl
  | cons n l ih => simp only [List.foldl_cons]; rw [← ih]; push_cast; rfl

theorem foldl_digits_lt (f : ℕ → ℕ) (hf : ∀ n, f n < 256) (l : List ℕ) (acc k : ℕ)
    (hacc : acc < 256 ^ k) : l.foldl (fun a n => a * 256 + f n) acc < 256 ^ (k + l.length) := by
  induction l generalizing acc k with
  | nil => simpa using hacc
  | cons n l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [show k + (l.length + 1) = (k + 1) + l.length by ring]
    apply ih
    have := hf n
    rw [pow_succ]
    nlinarith

/-- The value `swap_bytes` gives at `u64`: the bytes of `x` from the least significant. -/
theorem swapBytes_u64_toNat {x : ℕ} (hx : x < 2 ^ 64) :
    (IntTy.swapBytes (.u 64) (UInt256.ofNat x)).toNat =
      (List.range 8).foldl (fun acc n => acc * 256 + x / 256 ^ n % 256) 0 := by
  have hlt := foldl_digits_lt (fun n => x / 256 ^ n % 256) (fun n => Nat.mod_lt _ (by decide))
    (List.range 8) 0 0 (by decide)
  simp only [List.length_range, Nat.zero_add] at hlt
  have hc := foldl_digits_cast (fun n => x / 256 ^ n % 256) (List.range 8) 0
  simp only [Nat.cast_zero] at hc
  simp only [IntTy.swapBytes, IntTy.pattern, IntTy.bits, IntTy.wrap,
    ulit_toNat' _ (lt_trans hx (by decide)), Nat.mod_eq_of_lt hx, show 64 / 8 = 8 from rfl]
  have hlt' : (List.range 8).foldl (fun acc n => acc * 256 + x / 256 ^ n % 256) 0 < 2 ^ 64 := by
    simpa using hlt
  rw [hc, show ((2 : ℤ) ^ 64) = ((2 ^ 64 : ℕ) : ℤ) by norm_num, ← Int.natCast_mod,
    Int.toNat_natCast, Nat.mod_eq_of_lt hlt', ulit_toNat' _ (lt_trans hlt' (by decide))]

/-- **`swap_bytes` at `u64`, written big-endian, is the bytes little-endian.** -/
theorem swap_low8 {x : ℕ} (hx : x < 2 ^ 64) :
    (IntTy.swapBytes (.u 64) (UInt256.ofNat x)).toByteArray.extract 24 32 = le8 x := by
  have hs := toByteArray_size (v := IntTy.swapBytes (.u 64) (UInt256.ofNat x))
  have hlt := foldl_digits_lt (fun n => x / 256 ^ n % 256) (fun n => Nat.mod_lt _ (by decide))
    (List.range 8) 0 0 (by decide)
  simp only [List.length_range, Nat.zero_add] at hlt
  apply ByteArray.ext
  apply Array.ext'
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    show (ByteArray.extract _ 24 32).size = (le8 x).size
    rw [ByteArray.size_extract, hs, le8_size]; rfl
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian, fromByteArrayBigEndian_low8,
      swapBytes_u64_toNat hx, Nat.mod_eq_of_lt (by simpa using hlt), fromByteArrayBigEndian,
      byteArray_toList_eq]
    show _ = fromBytesBigEndian (Array.ofFn _).toList
    rw [Array.toList_ofFn, fromBytesBigEndian_ofFn (fun n => x / 256 ^ n) 8]

/-! ## A buffer that holds bytes -/

open Lib (MemBuffer)
open Exported.Shared

/-- The buffer `b` holds the bytes `d` in the memory `mem`: its length is theirs and they lie at
    its pointer, inside memory, which is smaller than `2 ^ 256` bytes. -/
structure Holds (b : MemBuffer) (d : ByteArray) (mem : ByteArray) : Prop where
  len : b.len.toNat = d.size
  bound : b.ptr.toNat + d.size ≤ mem.size
  bytes : mem.extract b.ptr.toNat (b.ptr.toNat + d.size) = d
  small : mem.size < UInt256.size

/-- Memory reads a window of the bytes. -/
theorem Holds.read {b : MemBuffer} {d mem : ByteArray} (h : Holds b d mem) {j n : ℕ}
    (hn : 0 < n) (hn64 : n < 2 ^ 64) (hj : j + n ≤ d.size) :
    fromByteArrayBigEndian (mem.readWithPadding (b.ptr.toNat + j) n) = beAt d j n := by
  rw [readWithPadding_eq_extract' _ _ _ hn hn64 (by have := h.bound; omega),
    ← fromByteArrayBigEndian_extract d j n hj]
  conv_rhs => rw [← h.bytes]
  rw [ByteArray.extract_extract, show b.ptr.toNat + j + n = min (b.ptr.toNat + (j + n))
    (b.ptr.toNat + d.size) by omega]

/-- The address `j` bytes into the buffer. -/
theorem Holds.ptr_add {b : MemBuffer} {d mem : ByteArray} (h : Holds b d mem) {j : ℕ}
    (hj : j < d.size) : (b.ptr + UInt256.ofNat j).toNat = b.ptr.toNat + j := by
  have := h.bound; have := h.small
  rw [uadd_toNat, ulit_toNat' _ (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Memory that grows still holds the bytes. -/
theorem Holds.append {b : MemBuffer} {d mem : ByteArray} (h : Holds b d mem) (X : ByteArray)
    (hs : mem.size + X.size < UInt256.size) : Holds b d (mem ++ X) := by
  have hb := h.bound
  refine ⟨h.len, by rw [ByteArray.size_append]; omega, ?_, by rw [ByteArray.size_append]; exact hs⟩
  rw [ByteArray.extract_append, h.bytes, show b.ptr.toNat - mem.size = 0 by omega,
    show b.ptr.toNat + d.size - mem.size = 0 by omega, ByteArray.extract_same, ByteArray.append_empty]

theorem len_exec (b : MemBuffer) (I : Env) (w : World) :
    (MemBuffer_len_1 b).exec I w = some (.ok (b.len, w)) := rfl

/-- **A byte** of the buffer. -/
theorem byte_exec {b : MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    {j : ℕ} (hj : j < d.size) :
    (MemBuffer_byte_at b (UInt256.ofNat j)).exec I w =
      some (.ok (UInt256.ofNat (byteAt d j), w)) := by
  have hjn : (UInt256.ofNat j).toNat = j :=
    ulit_toNat' _ (by have := h.bound; have := h.small; omega)
  have hr := h.read (j := j) (n := 1) (by omega) (by omega) (by omega)
  have hb := byteAt_lt d j
  simp only [beAt, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hr
  simp [MemBuffer_byte_at, Lib.MemBuffer_index_ref, mloadInt, IntTy.cast, IntTy.val, IntTy.wrap,
    IntTy.bits, hjn, h.len, Nat.not_le.mpr hj, h.ptr_add hj, hr]
  rw [ulit_toNat' _ (by unfold UInt256.size; omega)]
  norm_cast
  rw [Int.toNat_natCast, Nat.mod_eq_of_lt hb]

/-- The two steps of `MemBuffer_byte_at`, for a contract that inlines it: the address of the
    byte, -/
theorem index_exec {b : MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    {j : ℕ} (hj : j < d.size) :
    (Lib.MemBuffer_index_ref b (UInt256.ofNat j)).exec I w =
      some (.ok (b.ptr + UInt256.ofNat j, w)) := by
  have hjn : (UInt256.ofNat j).toNat = j :=
    ulit_toNat' _ (by have := h.bound; have := h.small; omega)
  simp [Lib.MemBuffer_index_ref, hjn, h.len, Nat.not_le.mpr hj]

/-- and the byte there. -/
theorem load_byte_exec {b : MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) {j : ℕ} (hj : j < d.size) :
    (mloadInt (.u 8) (b.ptr + UInt256.ofNat j)).exec I w =
      some (.ok (UInt256.ofNat (byteAt d j), w)) := by
  have hb := byte_exec (I := I) h hj
  rw [MemBuffer_byte_at, Fe.M.exec_bind, index_exec h hj] at hb
  simpa using hb

set_option maxRecDepth 10000 in
/-- **Eight bytes** of the buffer, read little-endian: the bytes of their big-endian number
    swapped. -/
theorem lane_exec {b : MemBuffer} {d : ByteArray} {I : Env} {w : World} (h : Holds b d w.memory)
    {j : ℕ} (hj : j + 8 ≤ d.size) :
    (MemBuffer_lane_at b (UInt256.ofNat j)).exec I w =
      some (.ok (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d j 8)), w)) := by
  have hjn : (UInt256.ofNat j).toNat = j :=
    ulit_toNat' _ (by have := h.bound; have := h.small; omega)
  have hr := h.read (j := j) (n := 8) (by omega) (by omega) hj
  have hb := beAt_lt d j 8
  have hsub : (b.len.sub (UInt256.ofNat j)).toNat = d.size - j := by
    rw [usub_toNat (by rw [h.len, hjn]; omega), h.len, hjn]
  have t8 : (UInt256.ofNat 8).toNat = 8 := rfl
  simp [MemBuffer_lane_at, Lib.MemBuffer_read_le_u64, Lib.MemBuffer_span_ref,
    Lib.MemSlice_u8_read_le_u64, Lib.MemSlice_u8_value_ptr_u64, Lib.cast_u8_u64,
    Lib.MemSlice_from_raw_parts_ref_u8, checkedSub, mloadInt, IntTy.cast, IntTy.val, IntTy.wrap,
    IntTy.bits, hjn, h.len, h.ptr_add (show j < d.size by omega), hr, hsub, t8,
    show ¬ d.size < j by omega, show ¬ d.size - j < 8 by omega]
  have hb' : beAt d j 8 < 18446744073709551616 := hb
  rw [ulit_toNat' _ (by unfold UInt256.size; omega), Int.emod_eq_of_lt (by positivity) (by omega),
    Int.toNat_natCast]

/-- **Eight bytes written little-endian** into a buffer whose capacity is its length, inside
    memory: the buffer is unchanged and memory gets the bytes `le8 x` at `off`. -/
theorem write_le_exec {b : MemBuffer} {I : Env} {w : World} {off x : ℕ}
    (hcap : b.capacity = b.len) (hoff : off + 8 ≤ b.len.toNat)
    (hroom : b.ptr.toNat + b.len.toNat ≤ w.memory.size) (hsmall : w.memory.size < UInt256.size)
    (hx : x < 2 ^ 64) :
    (Lib.MemBuffer_write_le_u64 b (UInt256.ofNat off) (UInt256.ofNat x)).exec I w =
      some (.ok (((), b),
        { w with memory := (le8 x).write 0 w.memory (b.ptr.toNat + off) 8 })) := by
  have hn : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have hsub : (b.len - UInt256.ofNat off).toNat = b.len.toNat - off := by
    rw [show b.len - UInt256.ofNat off = UInt256.sub _ _ from rfl, usub_toNat (by omega), hn]
  have h8 : (UInt256.ofNat off + UInt256.ofNat 8).toNat = off + 8 := by
    rw [uadd_toNat, hn, show (UInt256.ofNat 8).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hp : (b.ptr + UInt256.ofNat off).toNat = b.ptr.toNat + off := by
    rw [uadd_toNat, hn, Nat.mod_eq_of_lt (by omega)]
  simp [Lib.MemBuffer_write_le_u64, Lib.MemBuffer_extend_over_u64, Lib.cast_u8_u64, mstoreInt,
    hcap, hn, hsub, h8, hp, show (UInt256.ofNat 8).toNat = 8 from rfl,
    show ¬ b.len.toNat < off by omega, show ¬ b.len.toNat - off < 8 by omega,
    show ¬ b.len.toNat < off + 8 by omega]
  rw [show (IntTy.u 64).bits / 8 = 8 from rfl, show 32 - 8 = 24 from rfl, swap_low8 hx]

/-- Eight bytes written over the start of `C`, after `A ++ B`. -/
theorem le8_write_append (A B C : ByteArray) (x : ℕ) (hC : 8 ≤ C.size) :
    (le8 x).write 0 (A ++ B ++ C) (A.size + B.size) 8 =
      A ++ (B ++ le8 x) ++ C.extract 8 C.size := by
  rw [write_eq_gen _ _ _ _ (by decide) (by rw [le8_size]) (by simp [ByteArray.size_append]; omega)]
  have hAB : (A ++ B ++ C).extract 0 (A.size + B.size) = A ++ B :=
    ByteArray.extract_append_eq_left (by simp [ByteArray.size_append])
  have hC' : (A ++ B ++ C).extract (A.size + B.size + 8) (A ++ B ++ C).size =
      C.extract 8 C.size := by
    rw [show A.size + B.size + 8 = (A ++ B).size + 8 by simp [ByteArray.size_append],
      show (A ++ B ++ C).size = (A ++ B).size + C.size by simp [ByteArray.size_append],
      ByteArray.extract_append_size_add]
  rw [hAB, hC', show (le8 x).extract 0 8 = le8 x by
    rw [← le8_size x]; exact ByteArray.extract_zero_size, ByteArray.append_assoc (a := A)]

/-- The bytes written read back. -/
theorem le8_read (mem : ByteArray) (x p : ℕ) (hp : p + 8 ≤ mem.size) :
    ((le8 x).write 0 mem p 8).readWithPadding p 8 = le8 x := by
  have hsz := byteArray_write_size_of_inBounds (le8 x) mem p 8 (by rw [le8_size]) hp
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (by omega),
    write_eq_gen _ _ _ _ (by decide) (by rw [le8_size]) hp, ByteArray.extract_append,
    ByteArray.extract_append]
  simp [ByteArray.size_extract, le8_size, show min p mem.size = p by omega]
  rw [ByteArray.extract_eq_empty_iff.mpr (by simp [ByteArray.size_extract]), ByteArray.empty_append,
    ByteArray.extract_extract, show min (0 + 8) 8 = 8 from rfl, ← le8_size x,
    Nat.add_zero, ByteArray.extract_zero_size]

/-! ## The input buffer -/

/-- `input()`, as each precompile's contract has it (`input_Evm`, `input_Evm_1`, `input_Evm_2`,
    each equal to this by `rfl`): a buffer of the call data's size, the call data copied in. -/
def copyInput : FeM MemBuffer := do
  let mut r1 : MemBuffer := default
  let v1 ← Lib.Evm_calldatasize
  let v2 := v1
  let v3 ← Lib.downcast_unchecked_u256_usize v2
  let v4 ← Lib.MemBuffer_new v3
  let v5 := v4
  r1 := v5
  let v7 := (UInt256.ofNat 0)
  let v8 := (UInt256.ofNat 0)
  let (_, v10_0) ← Lib.Evm_calldatacopy r1 v7 v8 v2
  r1 := v10_0
  let v11 := r1
  return v11

/-- The memory after `input()`: a fresh zeroed buffer at the end, the call data copied in. -/
def inputMemory (mem cd : ByteArray) : ByteArray :=
  cd.write 0 ((⟨Array.replicate cd.size 0⟩ : ByteArray).write 0
    (mem ++ ⟨Array.replicate cd.size 0⟩) mem.size cd.size) mem.size cd.size

/-- The buffer `input()` makes. -/
def inputBuffer (mem cd : ByteArray) : MemBuffer :=
  ⟨UInt256.ofNat mem.size, UInt256.ofNat cd.size, UInt256.ofNat cd.size⟩

theorem inputMemory_size (mem cd : ByteArray) :
    (inputMemory mem cd).size = mem.size + cd.size := by
  have hz : (⟨Array.replicate cd.size 0⟩ : ByteArray).size = cd.size := Array.size_replicate
  rw [inputMemory, byteArray_write_size_of_inBounds _ _ _ _ le_rfl (by
      rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
        ByteArray.size_append, hz]),
    byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
    ByteArray.size_append, hz]

/-- **The buffer `input()` makes holds the call data.** -/
theorem input_holds (mem cd : ByteArray) (hmem : mem.size + cd.size < UInt256.size) :
    Holds (inputBuffer mem cd) cd (inputMemory mem cd) := by
  have hz : (⟨Array.replicate cd.size 0⟩ : ByteArray).size = cd.size := Array.size_replicate
  have hp : (UInt256.ofNat mem.size).toNat = mem.size :=
    toNat_lit (by unfold UInt256.size at hmem; omega)
  have hsz := inputMemory_size mem cd
  refine ⟨toNat_lit (by unfold UInt256.size at hmem; omega), by simp [inputBuffer, hp, hsz],
    ?_, by omega⟩
  simp only [inputBuffer, hp]
  by_cases h0 : cd.size = 0
  · rw [h0, Nat.add_zero, ByteArray.extract_same]
    exact (ByteArray.size_eq_zero_iff.mp h0).symm
  rw [inputMemory, write_eq_gen _ _ _ _ h0 le_rfl (by
      rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
        ByteArray.size_append, hz])]
  have hX : ((⟨Array.replicate cd.size 0⟩ : ByteArray).write 0
      (mem ++ ⟨Array.replicate cd.size 0⟩) mem.size cd.size).size = mem.size + cd.size := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
      ByteArray.size_append, hz]
  rw [ByteArray.extract_append, ByteArray.extract_zero_size,
    ByteArray.extract_append_eq_right (by simp [ByteArray.size_extract, hX]) (by
      simp [ByteArray.size_extract, hX])]
  simp [ByteArray.size_append, ByteArray.size_extract, hX]

/-- **`input()`** allocates a buffer of the call data's size at the end of memory and copies the
    call data into it. -/
theorem input_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + I.calldata.size < UInt256.size) :
    copyInput.exec I w = some (.ok (inputBuffer w.memory I.calldata,
      { w with memory := inputMemory w.memory I.calldata })) := by
  have hc : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    toNat_lit (by unfold UInt256.size at hmem; omega)
  have hsub : (UInt256.ofNat I.calldata.size).sub (UInt256.ofNat 0) =
      UInt256.ofNat I.calldata.size :=
    word_eq_of_toNat (by rw [usub_toNat (by rw [toNat0]; omega), toNat0, Nat.sub_zero])
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have h0a : UInt256.ofNat 0 + UInt256.ofNat I.calldata.size = UInt256.ofNat I.calldata.size :=
    word_eq_of_toNat (by rw [uadd_toNat, toNat0, Nat.zero_add, hc, Nat.mod_eq_of_lt (by omega)])
  have hms : w.memory.size < UInt256.size := by omega
  by_cases h0 : I.calldata.size = 0
  · have he : UInt256.ofNat I.calldata.size = UInt256.ofNat 0 := by rw [h0]
    simp [copyInput, checkedAdd, checkedSub, alloc, zeroMem, toNatMax, toNatU64, toNat0,
      h0, Fe.EVM.add_zero, hmax, hms, inputBuffer, inputMemory, byteArray_write_len_zero]
  · have he : UInt256.ofNat I.calldata.size ≠ UInt256.ofNat 0 := fun e => h0 (by
      have := congrArg UInt256.toNat e; rwa [hc, toNat0] at this)
    simp [copyInput, checkedAdd, checkedSub, alloc, zeroMem, toNatMax, toNatU64, toNat0, hc,
      Fe.EVM.add_zero, hmax, hmem, hsub, h0a, Fe.EVM.calldatacopy, inputBuffer, inputMemory,
      show ¬ 18446744073709551615 < I.calldata.size by omega,
      show ¬ UInt256.size ≤ I.calldata.size by omega,
      show (UInt256.ofNat w.memory.size).toNat = w.memory.size from toNat_lit (by
        unfold UInt256.size at hmem; omega)]
    rw [if_neg he]
    simp

end FeProofs.Precompiles
