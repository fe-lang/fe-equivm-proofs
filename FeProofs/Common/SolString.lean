import Reasoning.ABI
import Reasoning.Storage
import Reasoning.StorageLoops
import Reasoning.SteleBody
import Reasoning.MemCascade
import FeProofs.Common.Memory
import FeProofs.Common.PackedByte

/-!
# Solidity strings in storage

Facts about a `string` field in Solidity's layout (Fe's `SolString`) that do not depend on any
bytecode:

- word arithmetic on literals;
- the head word: its long flag and length as Fe's `stored_len` computes them (`headFlag_odd`,
  `headLen_long`, `strHeadLen`, `strHeadBad`, `strOldWords`) and as Stele decodes it
  (`decodeHeader_cases`), panicking or reverting on a length that contradicts the flag;
- `leadWord w r`, Fe's `leading_bytes(w, count: r)` (the first `r` bytes of `w`), computed as
  `w & leadMask r` for `r < 32`, and `strHeadWord`, the head `store` writes for a short string;
- `wordsBytes f n`, the bytes of the words `f 0, …, f (n - 1)`, as Fe's load loop appends them and
  as Stele's `readSolidityBytesDataWordsFrom` reads them (`leadWords_eq`), and `strBytes`, the bytes
  Stele reads for a string field;
- memory writes at the end of memory, and `encodeString_eq`, the ABI encoding of a `string`;
- Stele's reads (`stringField_eval_ok`, `stringField_eval_revert`) and short-string assignments
  (`strStmt_ok`, `strStmt_revert`) of a string field under any Solidity layout, with Solidity 0.8's
  semantics, and `steleStrWrite_accountMap`, which reorders Stele's write (clear, then store the
  head) into Fe's (store the head, then clear).

LIBRARY CANDIDATES: `encodeString_eq` (`Reasoning/ABI.lean`), the string reads and writes
(`Reasoning/Storage.lean`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs

set_option maxRecDepth 2000000

/-- `n` zero bytes, as the ABI pads with them. -/
abbrev zpad (n : ℕ) : ByteArray := (List.replicate n (0 : UInt8)).toByteArray

@[simp] theorem zpad_size (n : ℕ) : (zpad n).size = n := by
  rw [list_toByteArray_size, List.length_replicate]

theorem zpad_zero : zpad 0 = ByteArray.empty := rfl

/-! ## Words -/

theorem u256_toNat_lt (w : UInt256) : w.toNat < 2 ^ 256 := w.val.isLt

theorem lit_toNat {n : ℕ} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := ulit_toNat' n h

theorem lit_add_eq {a b : ℕ} (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat, lit_toNat (n := a) (by omega), lit_toNat (n := b) (by omega),
    Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega), lit_toNat h]

theorem lit_ne_zero {n : ℕ} (h0 : n ≠ 0) (h : n < 2 ^ 256) :
    UInt256.ofNat n ≠ UInt256.ofNat 0 := fun he =>
  h0 (by simpa [lit_toNat h, lit_toNat (n := 0) (by omega)] using congrArg UInt256.toNat he)

theorem land_lit_toNat (w : UInt256) (k : ℕ) (m : UInt256) (hm : m.toNat = 2 ^ k - 1) :
    (UInt256.land w m).toNat = w.toNat % 2 ^ k := by
  rw [uland_toNat, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem lit_lt32 {n : ℕ} (h : n < 32) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) = ⟨1⟩ :=
  ult_one (by rw [lit_toNat (n := 32) (by omega), lit_toNat (n := n) (by omega)]; exact h)

theorem lit_ge32 {n : ℕ} (h : 32 ≤ n) (hn : n < 2 ^ 256) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) = ⟨0⟩ :=
  ult_zero (by rw [lit_toNat (n := 32) (by omega), lit_toNat hn]; exact h)

theorem shl5_toNat {W : ℕ} (hW : W < 2 ^ 64) :
    (UInt256.shiftLeft (UInt256.ofNat W) (UInt256.ofNat 5)).toNat = 32 * W := by
  have hw : (UInt256.ofNat W).toNat = W := lit_toNat (by omega)
  have hb : (UInt256.ofNat W).toNat * 2 ^ 5 < UInt256.size := by
    rw [hw]; change _ < 2 ^ 256; omega
  rw [shiftLeft_toNat_of_lt _ 5 (by decide) hb, hw]
  omega

theorem shl5_eq {W : ℕ} (hW : W < 2 ^ 64) :
    UInt256.shiftLeft (UInt256.ofNat W) (UInt256.ofNat 5) = UInt256.ofNat (32 * W) :=
  u256_inj (by rw [shl5_toNat hW, lit_toNat (by omega)])

theorem shr5_eq {W : ℕ} (hW : W < 2 ^ 64) :
    UInt256.shiftRight (UInt256.ofNat (32 * W)) (UInt256.ofNat 5) = UInt256.ofNat W := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 5 (by decide), lit_toNat (by omega), lit_toNat (by omega)]
  omega

/-! ## A string's header word

The bytecode reads a header's long flag as `head & 1` and its length as `head >> 1` (long) or
`(0xff & head) >> 1` (short); Stele decodes it with `solidityDecodeBytesLengthHeader`. -/

section
variable {head : UInt256}

theorem headFlag_odd (ho : head.toNat % 2 = 1) :
    UInt256.land head (UInt256.ofNat 1) = UInt256.ofNat 1 :=
  u256_inj (by rw [land_lit_toNat head 1 _ rfl, Nat.pow_one, ho]; rfl)

theorem headFlag_even (he : head.toNat % 2 = 0) :
    UInt256.land head (UInt256.ofNat 1) = UInt256.ofNat 0 :=
  u256_inj (by rw [land_lit_toNat head 1 _ rfl, Nat.pow_one, he]; rfl)

theorem headLen_long :
    UInt256.shiftRight head (UInt256.ofNat 1) = UInt256.ofNat (head.toNat / 2) := by
  have hh := u256_toNat_lt head
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), lit_toNat (by omega), Nat.pow_one]

theorem headLen_short :
    UInt256.shiftRight (UInt256.land (UInt256.ofNat 255) head) (UInt256.ofNat 1) =
      UInt256.ofNat (head.toNat % 256 / 2) := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), u256_land_comm, land_lit_toNat head 8 _ rfl,
    lit_toNat (by omega), Nat.pow_one]
  rfl

end

/-- How Stele decodes a header word: a long string's length is `head / 2`, a short one's is in
the low byte; a length that contradicts the short/long flag reverts. -/
theorem decodeHeader_cases (head : UInt256) :
    (head.toNat % 2 = 1 ∧ 32 ≤ head.toNat / 2 ∧
      solidityDecodeBytesLengthHeader head = .ok (head.toNat / 2)) ∨
    (head.toNat % 2 = 0 ∧ head.toNat % 256 / 2 < 32 ∧
      solidityDecodeBytesLengthHeader head = .ok (head.toNat % 256 / 2)) ∨
    ((head.toNat % 2 = 1 ∧ head.toNat / 2 < 32 ∨
        head.toNat % 2 = 0 ∧ 32 ≤ head.toNat % 256 / 2) ∧
      solidityDecodeBytesLengthHeader head = .revert) := by
  have hflag : (UInt256.land head ⟨1⟩).toNat = head.toNat % 2 :=
    land_lit_toNat head 1 _ rfl
  have hdiv : (UInt256.div head ⟨2⟩).toNat = head.toNat / 2 := udiv_toNat _ _
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := rfl
  unfold solidityDecodeBytesLengthHeader
  rcases Nat.mod_two_eq_zero_or_one head.toNat with he | ho
  · have hf : UInt256.land head ⟨1⟩ = ⟨0⟩ := u256_inj (by rw [hflag, he]; rfl)
    have hlen : (UInt256.land (UInt256.div head ⟨2⟩) ⟨127⟩).toNat =
        head.toNat % 256 / 2 := by
      rw [land_lit_toNat _ 7 _ rfl, hdiv,
        show (256 : ℕ) = 2 * 2 ^ 7 by norm_num, Nat.mod_mul_right_div_self]
    simp only [hf, if_true]
    by_cases hs : head.toNat % 256 / 2 < 32
    · refine Or.inr (Or.inl ⟨he, hs, ?_⟩)
      rw [ult_one (by rw [hlen, h32]; exact hs), if_neg (by decide), hlen]
    · refine Or.inr (Or.inr ⟨Or.inr ⟨he, by omega⟩, ?_⟩)
      rw [ult_zero (by rw [hlen, h32]; omega), if_pos (by decide)]
  · have hf : UInt256.land head ⟨1⟩ = ⟨1⟩ := u256_inj (by rw [hflag, ho]; rfl)
    simp only [hf, show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide, if_false]
    by_cases hs : head.toNat / 2 < 32
    · refine Or.inr (Or.inr ⟨Or.inl ⟨ho, hs⟩, ?_⟩)
      rw [ult_one (by rw [hdiv, h32]; exact hs), if_pos (by decide)]
    · refine Or.inl ⟨ho, by omega, ?_⟩
      rw [ult_zero (by rw [hdiv, h32]; omega), if_neg (by decide), hdiv]

/-! ## Leading bytes of a word -/

/-- `~(~0 >> (8 * r))`: the mask of a word's first `r` bytes, as the bytecode computes it. -/
abbrev leadMask (r : UInt256) : UInt256 :=
  UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft r (UInt256.ofNat 3)))

/-- Fe's `leading_bytes(w, count: r)`. -/
def leadWord (w : UInt256) (r : ℕ) : UInt256 :=
  if r < 32 then UInt256.land w (leadMask (UInt256.ofNat r)) else w

theorem two_pow_sub_one_div (a b : ℕ) (hb : b ≤ a) :
    (2 ^ a - 1) / 2 ^ b = 2 ^ (a - b) - 1 := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  have hsplit : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← Nat.pow_add]; congr 1; omega
  have hpos' : 0 < 2 ^ (a - b) := Nat.two_pow_pos _
  have hle : 2 ^ b ≤ 2 ^ (a - b) * 2 ^ b := Nat.le_mul_of_pos_left _ hpos'
  rw [Nat.div_eq_iff hpos, hsplit, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ b)]
  omega

theorem leadMask_eq (r : ℕ) (hr : r < 32) :
    leadMask (UInt256.ofNat r) = UInt256.ofNat (2 ^ 256 - 2 ^ (8 * (32 - r))) := by
  have hshl : UInt256.shiftLeft (UInt256.ofNat r) (UInt256.ofNat 3) = UInt256.ofNat (8 * r) := by
    apply u256_inj
    rw [shiftLeft_toNat_of_lt _ 3 (by decide)
        (by rw [lit_toNat (by omega)]; change _ < 2 ^ 256; omega),
      lit_toNat (n := r) (by omega), lit_toNat (by omega)]
    omega
  have h1 : 1 ≤ 2 ^ (8 * (32 - r)) := Nat.one_le_two_pow
  have h2 : 2 ^ (8 * (32 - r)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
  apply u256_inj
  unfold leadMask
  rw [hshl, lnot_toNat_gen, shiftRight_toNat_of_lt _ _ (by omega), u256_lnot_zero_toNat,
    show UInt256.size = 2 ^ 256 from rfl, two_pow_sub_one_div 256 (8 * r) (by omega),
    lit_toNat (by omega), show 256 - 8 * r = 8 * (32 - r) by omega]
  omega

/-- The first `r` bytes of a word, zero-padded to a word. -/
theorem leadWord_toByteArray (w : UInt256) (r : ℕ) :
    (leadWord w r).toByteArray = w.toByteArray.extract 0 (min r 32) ++ zpad (32 - min r 32) := by
  unfold leadWord
  split
  · rename_i hr
    rw [Nat.min_eq_left hr.le, leadMask_eq r hr, u256_land_comm]
    have hextlen : (w.toByteArray.extract 0 r).toList.length = r := by
      rw [byteArray_extract0_toList, List.length_take, byteArray_toList_eq, Array.length_toList]
      have hsz : (w.toByteArray).data.size = 32 := toByteArray_size w
      omega
    have hlist : EVM.Word.toBytesBE
        (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ (8 * (32 - r)))) w) =
          (w.toByteArray.extract 0 r).toList ++ List.replicate (32 - r) 0 := by
      apply fromBytesBigEndian_inj_of_length
      · rw [word_toBytesBE_length_32, List.length_append, hextlen, List.length_replicate]; omega
      · rw [fromBytesBE_word, u256_land_high_mask_toNat w _ (by omega),
          fromBytesBigEndian_append_zeros, bytesBE_extract_high w r (by omega)]
    rw [toByteArray_eq_toBytesBE, hlist, mk_toArray_eq, list_toByteArray_append,
      byteArray_toList_toByteArray]
  · rename_i hr
    rw [Nat.min_eq_right (by omega), Nat.sub_self, toByteArray_extract_all, zpad_zero,
      ByteArray.append_empty]

/-! ## Words appended to memory -/

/-- The bytes of the words `f 0, …, f (n - 1)`. -/
def wordsBytes (f : ℕ → UInt256) : ℕ → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => wordsBytes f n ++ (f n).toByteArray

@[simp] theorem wordsBytes_size (f : ℕ → UInt256) (n : ℕ) :
    (wordsBytes f n).size = 32 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordsBytes, ByteArray.size_append, ih, toByteArray_size]; ring

theorem wordsBytes_succ' (f : ℕ → UInt256) (n : ℕ) :
    wordsBytes f (n + 1) = (f 0).toByteArray ++ wordsBytes (fun i => f (i + 1)) n := by
  induction n with
  | zero => rw [wordsBytes, wordsBytes, wordsBytes, empty_append, ByteArray.append_empty]
  | succ n ih => rw [wordsBytes, ih, wordsBytes, ByteArray.append_assoc]

/-- Stele's read of a long string's data words. -/
theorem readSolidityBytesDataWordsFrom_eq (evm : EVM.State) (base : UInt256) (idx n : ℕ) :
    readSolidityBytesDataWordsFrom evm base idx n =
      wordsBytes (fun i => EVM.storageLoad evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot base (idx + i))) n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih =>
    rw [readSolidityBytesDataWordsFrom, wordsBytes_succ', ih (idx + 1)]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

/-- Copying a `len`-byte string's words, each cut to the bytes left (`leading_bytes`), gives the
string followed by its ABI zero padding. -/
theorem leadWords_eq (f : ℕ → UInt256) (L : ℕ) (hL : 0 < L) :
    wordsBytes (fun i => leadWord (f i) (L - 32 * i)) ((L + 31) / 32) =
      (wordsBytes f ((L + 31) / 32)).extract 0 L ++ zpad (32 * ((L + 31) / 32) - L) := by
  obtain ⟨m, hm⟩ : ∃ m, (L + 31) / 32 = m + 1 := ⟨(L + 31) / 32 - 1, by omega⟩
  have hfull : ∀ n, n ≤ m →
      wordsBytes (fun i => leadWord (f i) (L - 32 * i)) n = wordsBytes f n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [wordsBytes, wordsBytes, ih (by omega), leadWord, if_neg (by omega)]
  rw [hm, wordsBytes, wordsBytes, hfull m le_rfl, leadWord_toByteArray,
    Nat.min_eq_left (by omega),
    extract_append_span _ _ 0 L (Nat.zero_le _) (by rw [wordsBytes_size]; omega),
    wordsBytes_size, ← wordsBytes_size f m, byteArray_extract_self, wordsBytes_size,
    ByteArray.append_assoc]
  congr 3
  omega

/-! ## The string Stele reads -/

/-- The bytes of the string at `slot` with length `L`, as Stele reads them: a short string's are
the header's leading bytes, a long one's the leading bytes of its data words. -/
def strBytes (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (L : ℕ) : ByteArray :=
  if L < 32 then (solcSlotWord σ ee slot).toByteArray.extract 0 L
  else (wordsBytes (fun i => solcSlotWord σ ee (solidityBytesDataSlot slot i))
    ((L + 31) / 32)).extract 0 L

theorem strBytes_size (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (L : ℕ) :
    (strBytes σ ee slot L).size = L := by
  unfold strBytes
  split
  · rw [ByteArray.size_extract, toByteArray_size]; omega
  · rw [ByteArray.size_extract, wordsBytes_size]; omega

/-! ## Memory -/

/-- A word stored at the end of memory is appended. -/
theorem wordWrite_end (w : UInt256) (B : ByteArray) {n : ℕ} (hn : n = B.size) :
    w.toByteArray.write 0 B n 32 = B ++ w.toByteArray := by
  subst hn
  rw [write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]), toByteArray_extract_all]

/-- A copy from past the end of its source (`CALLDATACOPY` from `CALLDATASIZE`) to the end of
memory leaves memory unchanged. -/
theorem write_past_end (src M : ByteArray) {a n : ℕ} (ha : src.size ≤ a) (hn : n ≠ 0) :
    src.write a M M.size n = M := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hn, if_pos ha]
  simp only [ByteArray.data_copySlice, Nat.sub_self, Nat.min_self, Nat.min_zero, Nat.zero_min,
    Nat.add_zero]
  rw [show M.size = M.data.size from rfl, Array.extract_size, Array.extract_size_left]
  simp

theorem memLoad_of_extract {M : ByteArray} {off : ℕ} {w : UInt256} (hoff : off < 2 ^ 256)
    (hsz : off + 32 ≤ M.size) (h : M.extract off (off + 32) = w.toByteArray) :
    memLoad (UInt256.ofNat off) M = w := by
  unfold memLoad
  rw [lit_toNat hoff, if_neg (by omega), readWithPadding_eq_extract _ _ hsz, h,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-! ## The ABI encoding of a returned `string` -/

/-- `abi.encode(string)`: the offset word `0x20`, the length word, and the bytes padded to
words. -/
theorem encodeString_eq (b : ByteArray) :
    encodeReturnValues? [.string] [.bytes b] =
      some ((UInt256.ofNat 32).toByteArray ++ ((UInt256.ofNat b.size).toByteArray ++
        (b ++ zpad (ABI.paddedSize b.size - b.size)))) := by
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
    encodeABIValue?, isDynamicABIType, staticABIEncodedSize?, Option.bind, bind, if_true,
    List.nil_append, List.append_nil, Nat.add_zero, List.length_nil]
  rw [mk_toArray_eq, list_toByteArray_append, list_toByteArray_append, natBytes_toByteArray',
    natBytes_toByteArray', ABI.padRightToWord, list_toByteArray_append,
    byteArray_toList_toByteArray, ABI.zeroBytes,
    show b.toList.length = b.size by rw [byteArray_toList_eq, Array.length_toList]; rfl]

/-! ## The data base of a long string -/

/-- `KECCAK256(s, 32)` over a slot stored at `s`: where the slot's long-string data starts. -/
theorem keccakWord_dataSlot (slot : UInt256) (mem : ByteArray) (s : ℕ) (hs : s < 2 ^ 32) :
    keccakWord (UInt256.ofNat s) (UInt256.ofNat 32) (slot.toByteArray.write 0 mem s 32) =
      solidityBytesDataBaseSlot slot := by
  unfold keccakWord
  rw [lit_toNat (n := s) (by omega), show (UInt256.ofNat 32).toNat = 32 from rfl,
    toByteArray_write_read_back_of_gap slot mem s (small_gap mem s hs)]
  exact keccakSlot_eq _

/-- `keccakWord_dataSlot` with the offset as a word, as it appears inside a trace. -/
theorem keccakWord_dataSlotWord (slot : UInt256) (mem : ByteArray) (s : ℕ) (hs : s < 2 ^ 32) :
    keccakWord (UInt256.ofNat s) (UInt256.ofNat 32)
        (slot.toByteArray.write 0 mem (UInt256.ofNat s).toNat 32) =
      solidityBytesDataBaseSlot slot := by
  rw [lit_toNat (n := s) (by omega)]
  exact keccakWord_dataSlot slot mem s hs

/-! ## Fe's `stored_len` and `store` -/

/-- The length a string head encodes, as Stele and Fe's `stored_len` decode it. -/
def strHeadLen (S : UInt256) : UInt256 :=
  if UInt256.land S ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ else UInt256.div S ⟨2⟩

/-- A head whose length contradicts its short/long flag: both sides revert. -/
def strHeadBad (S : UInt256) : Prop :=
  UInt256.sub (UInt256.land S ⟨1⟩) (UInt256.lt (strHeadLen S) ⟨32⟩) = ⟨0⟩

/-- The data words a string with head `S` occupies: none for a short one. -/
def strOldWords (S : UInt256) : ℕ :=
  if UInt256.land S ⟨1⟩ = ⟨0⟩ then 0 else ((strHeadLen S).toNat + 31) / 32

theorem land_one_cases (S : UInt256) : UInt256.land S ⟨1⟩ = ⟨0⟩ ∨ UInt256.land S ⟨1⟩ = ⟨1⟩ := by
  have h := uInt256_land_one_toNat S
  rcases Nat.mod_two_eq_zero_or_one S.toNat with h2 | h2
  · exact Or.inl (u256_inj (by rw [h, h2]; rfl))
  · exact Or.inr (u256_inj (by rw [h, h2]; rfl))

/-- A short head's length: `(S & 0xff) >> 1`. -/
theorem shortLen_eq (S : UInt256) :
    UInt256.shiftRight (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1) =
      UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), uland_toNat, uland_toNat, udiv_toNat,
    show (UInt256.ofNat 255).toNat = 255 from rfl, show (⟨2⟩ : UInt256).toNat = 2 from rfl,
    show (⟨127⟩ : UInt256).toNat = 127 from rfl, Nat.land_comm,
    show (255 : ℕ) = 2 ^ 8 - 1 from rfl, show (127 : ℕ) = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A long head's length: `S >> 1`. -/
theorem longLen_eq (S : UInt256) :
    UInt256.shiftRight S (UInt256.ofNat 1) = UInt256.div S ⟨2⟩ := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), udiv_toNat]
  rfl

theorem strHeadLen_long_lt (S : UInt256) : (UInt256.div S ⟨2⟩).toNat < 2 ^ 255 := by
  rw [udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from rfl]
  have hS : S.toNat < 2 ^ 256 := S.val.isLt
  omega

/-- A long head's data word count: `(31 + (S >> 1)) >> 5`. -/
theorem longWords_eq (S : UInt256) :
    UInt256.shiftRight (UInt256.ofNat 31 + UInt256.shiftRight S (UInt256.ofNat 1))
        (UInt256.ofNat 5) =
      UInt256.ofNat (((UInt256.div S ⟨2⟩).toNat + 31) / 32) := by
  have hlt := strHeadLen_long_lt S
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 5 (by decide), uadd_toNat, longLen_eq,
    show (UInt256.ofNat 31).toNat = 31 from rfl,
    Nat.mod_eq_of_lt (show 31 + (UInt256.div S ⟨2⟩).toNat < UInt256.size by
      change _ < 2 ^ 256; omega),
    ulit_toNat' _ (show ((UInt256.div S ⟨2⟩).toNat + 31) / 32 < UInt256.size by
      change _ < 2 ^ 256; omega)]
  omega

theorem strOldWords_lt (S : UInt256) : strOldWords S < 2 ^ 251 := by
  unfold strOldWords strHeadLen
  split
  · decide
  · have := strHeadLen_long_lt S
    omega

/-- The head `store` writes for a short value of `len` bytes whose first word is `w`. -/
def strHeadWord (w len : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land (leadMask len) (UInt256.land w (leadMask len)))
    (UInt256.shiftLeft len (UInt256.ofNat 1))

/-- The account map after `store` writes the short string `bytes` at `slot`: the head first, then
the old data words zeroed. -/
abbrev strWriteMap (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256) (bytes : ByteArray) :
    AccountMap :=
  clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ slot (solidityShortBytesWord bytes))
    (solidityBytesDataBaseSlot slot) ⟨0⟩ (strOldWords (solcSlotWord σ I slot))

/-! ## Stele: assigning a short string to a string field (Solidity 0.8) -/

/-- Stele's write of a short string at `slot`: zero the old data words, then store the head. -/
abbrev steleStrWrite (evm : EVM.State) (slot : UInt256) (bytes : ByteArray) : EVM.State :=
  Stele.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evm slot 0
      (strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
    evm.executionEnv.codeOwner slot (solidityShortBytesWord bytes)

theorem steleStrWrite_executionEnv (evm : EVM.State) (slot : UInt256) (bytes : ByteArray) :
    (steleStrWrite evm slot bytes).executionEnv = evm.executionEnv := by
  rw [steleStrWrite, storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv]

theorem strWrite_bad {cfg : Config} {layout : StorageLayout}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout) {evm : EVM.State} {er : EvaledStorageRef} {slot : UInt256} {bytes : ByteArray}
    (hlay : layout er = some (.anchor slot))
    (hbad : strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    cfg.storageBackend.write er .string (.bytes bytes) evm = .revert := by
  unfold strHeadBad strHeadLen at hbad
  rcases land_one_cases (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) with hf | hf
  · rw [if_pos hf] at hbad
    exact writeSolidityStringMalformedShort hbackend hlay rfl hf hbad
  · have hne : UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩ ≠
        ⟨0⟩ := by
      rw [hf]; decide
    rw [if_neg hne] at hbad
    exact writeSolidityStringMalformedLong hbackend hlay rfl hne hbad

theorem strWrite_ok {cfg : Config} {layout : StorageLayout}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout) {evm : EVM.State} {er : EvaledStorageRef} {slot : UInt256} {bytes : ByteArray}
    (hlay : layout er = some (.anchor slot)) (hsize : bytes.size < 32)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    cfg.storageBackend.write er .string (.bytes bytes) evm =
      .ok (steleStrWrite evm slot bytes) := by
  unfold strHeadBad strHeadLen at hok
  rcases land_one_cases (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) with hf | hf
  · have hw : strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) = 0 := by
      rw [strOldWords, if_pos hf]
    rw [if_pos hf] at hok
    rw [writeSolidityStringShortPacked hbackend hlay hsize rfl
      (checkBytesPacked_of_storageLoad_land_one_zero rfl hf) hf rfl hok, steleStrWrite, hw]
    rfl
  · have hne : UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩ ≠
        ⟨0⟩ := by
      rw [hf]; decide
    have hw : strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) =
        ((UInt256.div (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨2⟩).toNat + 31) /
          32 := by
      rw [strOldWords, if_neg hne, strHeadLen, if_neg hne]
    rw [if_neg hne] at hok
    rw [writeSolidityStringShortFromLongPrepared hbackend hlay hsize rfl hne rfl hok,
      clearSolidityBytesDataWordsFrom_executionEnv, steleStrWrite, hw]

theorem strRef_eval {cfg : Config} {c : ContractDecl} {L : Store} {evm : EVM.State} (base : Ident) :
    evalStorageRef cfg { contract := c, locals := L } evm { base := base, steps := [] } =
      .ok { base := base, steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalBytesLit {cfg : Config} {c : ContractDecl} {L : Store} {evm : EVM.State} (bytes : ByteArray) :
    evalExpr? cfg { contract := c, locals := L } evm (.bytesLit bytes) =
      .ok (.bytes bytes) := by
  rw [evalExpr?]; rfl

/-- `base = bytes` for a `string` field at `slot`, over a malformed head. -/
theorem strStmt_revert {cfg : Config} {c : ContractDecl} {layout : StorageLayout}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout) {L : Store} {evm : EVM.State} {base : Ident} {slot : UInt256}
    {bytes : ByteArray} (hL : L.get? base = none)
    (hty : storageTypeAt? c.storage { base := base, steps := [] } = some .string)
    (hlay : layout { base := base, steps := [] } = some (.anchor slot))
    (hbad : strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    ExecStmt cfg { contract := c, locals := L } evm
      (.assign .storage { base := base, steps := [] } (.bytesLit bytes)) .reverted :=
  ExecStmt.assignStoreRevert (evalBytesLit bytes) (by
    simp only [assignStorageRef?, resolveStorageRef?_ok hL (strRef_eval base) hty,
      strWrite_bad hbackend hlay hbad, bind, EvalResult.bind])

/-- `base = bytes` for a `string` field at `slot`, over a well-formed head. -/
theorem strStmt_ok {cfg : Config} {c : ContractDecl} {layout : StorageLayout}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout) {L : Store} {evm : EVM.State} {base : Ident} {slot : UInt256}
    {bytes : ByteArray} (hL : L.get? base = none)
    (hty : storageTypeAt? c.storage { base := base, steps := [] } = some .string)
    (hlay : layout { base := base, steps := [] } = some (.anchor slot))
    (hsize : bytes.size < 32) (hperm : evm.executionEnv.perm = true)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    ExecStmt cfg { contract := c, locals := L } evm
      (.assign .storage { base := base, steps := [] } (.bytesLit bytes))
      (.ok { contract := c, locals := L } (steleStrWrite evm slot bytes)) :=
  ExecStmt.assign (hperm := Or.inr hperm) (evalBytesLit bytes) (by
    simp only [assignStorageRef?, resolveStorageRef?_ok hL (strRef_eval base) hty,
      strWrite_ok hbackend hlay hsize hok, bind, EvalResult.bind, pure])

/-- Stele's string write leaves the account map Fe's `store` leaves: zeroing the old data words
    commutes with storing the head, when none of them is the head slot. -/
theorem steleStrWrite_accountMap (evm : EVM.State) (slot : UInt256)
    (bytes : ByteArray)
    (hns : ∀ i, i < strOldWords (solcSlotWord evm.accountMap evm.executionEnv slot) →
      slot ≠ solidityBytesDataBaseSlot slot + UInt256.ofNat i) :
    (steleStrWrite evm slot bytes).accountMap =
      strWriteMap evm.executionEnv evm.accountMap slot bytes := by
  rw [steleStrWrite, storageStore_accountMap, clearSolidityBytesDataWordsFrom_accountMap,
    strWriteMap, clearDataWordsForwardFrom_sstore_comm _ _ _ _ _ _
      hns]
  rfl

/-! ## Stele: reading a string field -/

theorem solidityStorageBackend_read_string (layout : StorageLayout) (er : EvaledStorageRef)
    (evm : EVM.State) :
    (solidityStorageBackend layout).read er .string evm =
      solidityValueResultToEval (solidityReadBytesValue? layout er evm) := by
  simp only [solidityStorageBackend, solidityReadStorage?]

section
variable {cfg : Config} {c : ContractDecl} {layout : StorageLayout} {σ σ₀ : AccountMap} {A : Substate}
  {I : ExecutionEnv} {g : Sat256} {field : Ident} {slot : UInt256}

theorem stringField_read (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? c.storage { base := field, steps := [] } = some .string) :
    evalExpr? cfg { contract := c, locals := ∅ } (initState σ σ₀ g A I)
        (.storage { base := field, steps := [] }) =
      solidityValueResultToEval (solidityReadBytesValue? cfg.storageBackend.locate?
        { base := field, steps := [] } (initState σ σ₀ g A I)) := by
  rw [evalExpr?, resolveStorageRef?_ok (er := { base := field, steps := [] }) (ty := .string)
    (by simp) (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]) hty]
  rw [hbackend]
  exact solidityStorageBackend_read_string _ _ _

/-- A well-formed header: Stele returns the string's bytes. -/
theorem stringField_eval_ok {L : ℕ}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? c.storage { base := field, steps := [] } = some .string)
    (hloc : cfg.storageBackend.locate? { base := field, steps := [] } = some (.anchor slot))
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ I slot) = .ok L) :
    evalExpr? cfg { contract := c, locals := ∅ } (initState σ σ₀ g A I)
      (.storage { base := field, steps := [] }) = .ok (.bytes (strBytes σ I slot L)) := by
  rw [stringField_read hbackend hty, solidityReadBytesValue?,
    solidityBytesBaseSlotAndLength?_ok_of_layout hloc (storageLoad_initState_solcSlotWord _) hdec]
  simp only [(storageLoad_initState_solcSlotWord _), strBytes, solidityBytesDataWordCount,
    readSolidityBytesDataWordsFrom_eq, Nat.zero_add]
  split <;> rfl

/-- A malformed header: Stele reverts. -/
theorem stringField_eval_revert
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? c.storage { base := field, steps := [] } = some .string)
    (hloc : cfg.storageBackend.locate? { base := field, steps := [] } = some (.anchor slot))
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ I slot) = .revert) :
    evalExpr? cfg { contract := c, locals := ∅ } (initState σ σ₀ g A I)
      (.storage { base := field, steps := [] }) = .revert := by
  rw [stringField_read hbackend hty, solidityReadBytesValue?,
    solidityBytesBaseSlotAndLength?_revert_of_layout hloc (storageLoad_initState_solcSlotWord _) hdec]
  rfl

end

/-- The ABI encoding of the string a header word decodes to (an offset word, a length word and
the padded bytes) is shorter than `2^64` bytes. -/
def stringReturnFits (head : UInt256) : Prop :=
  ∀ L, solidityDecodeBytesLengthHeader head = .ok L → 64 + ABI.paddedSize L < 2 ^ 64

end FeProofs
