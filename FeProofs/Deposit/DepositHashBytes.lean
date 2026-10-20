import FeProofs.Deposit.DepositHashStele

/-!
# FeDeposit `deposit()` hashing — EVM payload bytes

The bytecode builds the pubkey payload as `mstore(fp, mload(p))`,
`mstore(fp + 32, (mload(p + 32) >> 128) << 128)` (pc 650–697) and the second signature payload
from `mload(q + 64)` and a zero word.  These lemmas compute those payload words from the decoded
`bytes` in memory, independent of where the decoder put them.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

theorem byteArray_extract_split (b : ByteArray) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    b.extract i j ++ b.extract j k = b.extract i k := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_extract, Array.extract_append_extract,
    Nat.min_eq_left hij, Nat.max_eq_right hjk]

/-- An in-bounds `MLOAD` is the 32 bytes at its offset. -/
theorem memLoad_toByteArray (M : ByteArray) {p : ℕ} (hp : p + 32 ≤ M.size)
    (hb : p < UInt256.size) :
    (memLoad (UInt256.ofNat p) M).toByteArray = M.extract p (p + 32) := by
  unfold memLoad
  rw [ulit_toNat' p hb, if_neg (by omega), readWithPadding_eq_extract M p hp,
    toByteArray_ofNat_fromByteArrayBigEndian_of_size (by rw [ByteArray.size_extract]; omega)]

/-- `(w >> 128) << 128` keeps the word's first 16 bytes and zeroes the rest. -/
theorem highHalf_toByteArray (w : UInt256) :
    (UInt256.shiftLeft (UInt256.shiftRight w (UInt256.ofNat 128)) (UInt256.ofNat 128)).toByteArray =
      w.toByteArray.extract 0 16 ++ ByteArray.zeroes 16 := by
  have hw : w.toNat < 2 ^ 256 := w.val.isLt
  have hlen : (EVM.Word.toBytesBE w).length = 32 := word_toBytesBE_length_32 _
  have hlist : EVM.Word.toBytesBE (UInt256.shiftLeft (UInt256.shiftRight w (UInt256.ofNat 128))
      (UInt256.ofNat 128)) = (EVM.Word.toBytesBE w).take 16 ++ List.replicate 16 0 := by
    apply fromBytesBigEndian_inj_of_length
    · rw [word_toBytesBE_length_32, List.length_append, List.length_take, hlen,
        List.length_replicate]
      omega
    · have hdiv := fromBytesBigEndian_append_div ((EVM.Word.toBytesBE w).take 16)
        ((EVM.Word.toBytesBE w).drop 16)
      rw [List.take_append_drop, List.length_drop, hlen, fromBytesBE_word] at hdiv
      rw [fromBytesBE_word, fromBytesBigEndian_append_zeros, ← hdiv,
        ushlN_toNat _ 128 (by decide), ushrN_toNat _ 128 (by decide)]
      show w.toNat / 2 ^ 128 * 2 ^ 128 % 2 ^ 256 = w.toNat / 2 ^ (8 * (32 - 16)) * 2 ^ (8 * 16)
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw)]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray, hlist, list_toByteArray_append,
    replicate_toByteArray, toByteArray_eq_toBytesBE]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [List.data_toByteArray, ByteArray.data_extract]

/-- **The pubkey payload.**  With the 48 pubkey bytes at `p`, the two stored words are the pubkey
    followed by 16 zero bytes. -/
theorem pubkeyWords_eq (M pk : ByteArray) {p : ℕ} (hp : p + 64 ≤ M.size)
    (hb : p + 32 < UInt256.size) (hpk : M.extract p (p + 48) = pk) :
    (memLoad (UInt256.ofNat p) M).toByteArray ++
      (UInt256.shiftLeft (UInt256.shiftRight (memLoad (UInt256.ofNat (p + 32)) M) (UInt256.ofNat 128))
        (UInt256.ofNat 128)).toByteArray = pk ++ ByteArray.zeroes 16 := by
  rw [highHalf_toByteArray, memLoad_toByteArray M (by omega) (by omega),
    memLoad_toByteArray M (by omega) hb, extract_extract_BA,
    show min (p + 32 + 16) (p + 32 + 32) = p + 48 by omega, show p + 32 + 0 = p + 32 by omega,
    ← ByteArray.append_assoc, byteArray_extract_split M (by omega) (by omega), hpk]

/-- **The second signature payload.**  With the 96 signature bytes at `q`, `mload(q + 64)` is the
    signature's last word. -/
theorem sigTailWord_eq (M sig : ByteArray) {q : ℕ} (hq : q + 96 ≤ M.size)
    (hb : q + 64 < UInt256.size) (hsig : M.extract q (q + 96) = sig) :
    (memLoad (UInt256.ofNat (q + 64)) M).toByteArray ++ ByteArray.zeroes 32 =
      sig.extract 64 96 ++ ByteArray.zeroes 32 := by
  rw [memLoad_toByteArray M (by omega) hb, ← hsig, extract_extract_BA,
    show min (q + 96) (q + 96) = q + 96 by omega, show q + 64 + 32 = q + 96 by omega]

end FeProofs.Deposit
