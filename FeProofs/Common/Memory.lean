import Reasoning.Memory
import Reasoning.MemCascade
import Reasoning.HeapMemory

/-!
# Memory facts shared by the contracts

Sizes and untouched windows after writes, word writes, and two adjacent words.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs

theorem small_gap (mem : ByteArray) (off : Nat) (h : off < 2 ^ 32) : off - mem.size < USize.size :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h USize.le_size)

/-- Two words stored at `s` and `t = s + 32` read back as their concatenation. The offsets and the
length are parameters so that they match the literals a block summary leaves (after `u256_lits`). -/
theorem pairWords_read (mem : ByteArray) (a b : UInt256) (s t n : Nat) (ht : t = s + 32)
    (hn : n = 64) (hs : s + 32 < 2 ^ 32) :
    (b.toByteArray.write 0 (a.toByteArray.write 0 mem s 32) t 32).readWithPadding s n =
      a.toByteArray ++ b.toByteArray := by
  subst ht hn
  have h0 := toByteArray_write_size_ge_off_add32 a mem s (small_gap mem s (by omega))
  have h1 := toByteArray_write_size_ge_off_add32 b (a.toByteArray.write 0 mem s 32) (s + 32)
    (small_gap _ (s + 32) hs)
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ s 32 32 (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega),
    toByteArray_write_read_below_of_gap b _ (s + 32) s (by omega) (by omega)
      (small_gap _ (s + 32) hs),
    toByteArray_write_read_back_of_gap a mem s (small_gap mem s (by omega)),
    toByteArray_write_read_back_of_gap b _ (s + 32) (small_gap _ (s + 32) hs)]

/-- The memory after storing two words at `s` and `t = s + 32` reaches `s + 64`. -/
theorem pairWords_size (mem : ByteArray) (a b : UInt256) (s t : Nat) (ht : t = s + 32)
    (hs : s + 32 < 2 ^ 32) :
    s + 64 ≤ (b.toByteArray.write 0 (a.toByteArray.write 0 mem s 32) t 32).size := by
  subst ht
  have := toByteArray_write_size_ge_off_add32 b (a.toByteArray.write 0 mem s 32) (s + 32)
    (small_gap _ (s + 32) hs)
  omega

theorem gapSmall {d b : ℕ} (hd : d < 2 ^ 32) : d - b < USize.size := by
  have := USize.le_size; omega

/-- A write never shrinks memory. -/
theorem write_size_ge (src base : ByteArray) {srcOff dest len : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hgap : dest - base.size < USize.size) :
    base.size ≤ (src.write srcOff base dest len).size := by
  by_cases hd : dest ≤ base.size
  · rw [copyWindow_size src base srcOff dest len hpos hsrc hd]; omega
  · rw [write_from_gap_eq src base srcOff dest len hpos hsrc (by omega) hgap]
    simp only [ByteArray.size_append]; omega

/-- A write of `len` source bytes reaches `dest + len`. -/
theorem write_size_reach (src base : ByteArray) {srcOff dest len : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hgap : dest - base.size < USize.size) :
    dest + len ≤ (src.write srcOff base dest len).size := by
  by_cases hd : dest ≤ base.size
  · rw [copyWindow_size src base srcOff dest len hpos hsrc hd]; omega
  · rw [write_from_gap_eq src base srcOff dest len hpos hsrc (by omega) hgap]
    simp only [ByteArray.size_append, ByteArray.size_extract, ByteArray_zeroes_size]; omega

/-- A write leaves every window it does not overlap unchanged. -/
theorem write_extract_preserved (src base : ByteArray) {srcOff dest len i j : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ base.size)
    (hij : i ≤ j) (hj : j ≤ base.size) (hdisj : j ≤ dest ∨ dest + len ≤ i) :
    (src.write srcOff base dest len).extract i j = base.extract i j := by
  have hp : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [copyWindow_eq src base srcOff dest len hpos hsrc hdest]
  rcases hdisj with hl | hr
  · rw [extract_append_left _ _ i j (by rw [ByteArray.size_append, hp, hs]; omega),
      extract_append_left _ _ i j (by rw [hp]; exact hl), extract_extract_BA,
      show 0 + i = i from Nat.zero_add i, show min (0 + j) dest = j by omega]
  · rw [extract_append_right_window _ _ i j (by rw [ByteArray.size_append, hp, hs]; omega),
      ByteArray.size_append, hp, hs, extract_extract_BA,
      show dest + len + (i - (dest + len)) = i by omega,
      show min (dest + len + (j - (dest + len))) base.size = j by omega]

/-- A write at or above a window leaves it unchanged, even when the write extends memory. -/
theorem write_extract_below (src base : ByteArray) {srcOff dest len i j : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hgap : dest - base.size < USize.size)
    (hij : i ≤ j) (hj : j ≤ base.size) (hjd : j ≤ dest) :
    (src.write srcOff base dest len).extract i j = base.extract i j := by
  by_cases hd : dest ≤ base.size
  · exact write_extract_preserved src base hpos hsrc hd hij hj (Or.inl hjd)
  · rw [write_from_gap_eq src base srcOff dest len hpos hsrc (by omega) hgap,
      ByteArray.append_assoc, extract_append_left _ _ i j hj]

theorem wordWrite_size (w : UInt256) (base : ByteArray) {dest : Nat} (hgap : dest < 2 ^ 32) :
    base.size ≤ (w.toByteArray.write 0 base dest 32).size :=
  write_size_ge _ _ (by decide) (by rw [toByteArray_size]) (small_gap _ _ hgap)

/-- A 32-byte word write leaves a window it does not overlap unchanged. -/
theorem wordWrite_extract (w : UInt256) (base : ByteArray) {dest i j : Nat} (hij : i ≤ j)
    (hj : j ≤ base.size) (hd : j ≤ dest ∨ (dest + 32 ≤ i ∧ dest ≤ base.size))
    (hgap : dest < 2 ^ 32) :
    (w.toByteArray.write 0 base dest 32).extract i j = base.extract i j := by
  rcases hd with hd | ⟨hd, hb⟩
  · exact write_extract_below _ _ (by decide) (by rw [toByteArray_size]) (small_gap _ _ hgap) hij hj hd
  · exact write_extract_preserved _ _ (by decide) (by rw [toByteArray_size]) hb hij hj (Or.inr hd)

theorem write32_size_ge (src base : ByteArray) (dest : ℕ) (hsrc : 32 ≤ src.size)
    (hlo : dest ≤ base.size) : dest + 32 ≤ (src.write 0 base dest 32).size := by
  rw [write32_eq src base dest hsrc hlo, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract]
  omega

/-- `MLOAD(0x40)` is unchanged by writes at or above `0x60`. -/
theorem memLoad64_write (src base : ByteArray) {srcOff dest len : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hgap : dest - base.size < USize.size)
    (hd : 96 ≤ dest) (hb : 96 ≤ base.size) :
    memLoad (UInt256.ofNat 64) (src.write srcOff base dest len) = memLoad (UInt256.ofNat 64) base := by
  have hsz := write_size_ge src base hpos hsrc hgap (dest := dest)
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 from rfl, if_neg (by omega), if_neg (by omega),
    readWithPadding_eq_extract _ 64 (by omega), readWithPadding_eq_extract _ 64 (by omega),
    write_extract_below src base hpos hsrc hgap (by omega) (by omega) (by omega)]

/-- The 64-byte payload `abi.encodePacked(uint256(a), uint256(b))`. -/
abbrev pairPayload (a b : UInt256) : ByteArray :=
  ByteArray.mk (EVM.Word.toBytesBE a ++ EVM.Word.toBytesBE b).toArray

theorem pairPayload_eq (a b : UInt256) : pairPayload a b = a.toByteArray ++ b.toByteArray := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray a, ← word_toBytesBE_toByteArray_eq_toByteArray b,
    ← List.toByteArray_append]
  apply ByteArray.ext
  simp

end FeProofs
