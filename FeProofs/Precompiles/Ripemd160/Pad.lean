import Ethereum.RIPEMD160
import Mathlib.Tactic

/-!
# Ripemd160: the padded message byte by byte

EVMLean pads the message `d` of `n` bytes as `d`, `0x80`, zeros and the 64-bit little-endian bit
count, to `64 * blocksOf n` bytes (`pad_size`), with `blocksOf n = (n + 9 + 63) / 64`, the
exported `padded_blocks`.  `padByte d p` is its byte at `p` (`pad_get`): the message below `n`,
`0x80` at `n`, the count in the last eight bytes and zero between.
-/

namespace FeProofs.Ripemd160

open Ethereum

/-- The number of 64-byte blocks of the padded message, as `padded_blocks` computes it. -/
def blocksOf (n : ℕ) : ℕ := (n + 9 + 63) / 64

/-- The byte of the padded message at `p`. -/
def padByte (d : ByteArray) (p : ℕ) : UInt8 :=
  if p < d.size then d[p]!
  else if p = d.size then 0x80
  else if p < 64 * blocksOf d.size - 8 then 0
  else ((8 * d.size) >>> (8 * (p - (64 * blocksOf d.size - 8)))).toUInt8

theorem zeros_eq (n : ℕ) : n + 1 + (119 - n % 64) % 64 + 8 = 64 * blocksOf n := by
  unfold blocksOf; omega

theorem pad_size (d : ByteArray) : (RIPEMD160.pad d).size = 64 * blocksOf d.size := by
  rw [RIPEMD160.pad, ByteArray.size_append, ByteArray.size_append, ByteArray.size_push]
  change d.size + 1 + (Array.replicate _ (0 : UInt8)).size +
    (Array.ofFn fun i : Fin 8 => ((8 * d.size) >>> (8 * i.val)).toUInt8).size = _
  rw [Array.size_replicate, Array.size_ofFn, zeros_eq]

theorem push_get (d : ByteArray) (b : UInt8) {i : ℕ} (h : i < (d.push b).size) :
    (d.push b)[i] = if hi : i < d.size then d[i] else b := by
  simp only [ByteArray.push, ByteArray.getElem_eq_getElem_data, Array.getElem_push]
  rfl

theorem pad_get (d : ByteArray) {p : ℕ} (hp : p < 64 * blocksOf d.size) :
    (RIPEMD160.pad d)[p]! = padByte d p := by
  have hz := zeros_eq d.size
  have hs := pad_size d
  rw [getElem!_pos _ _ (by rw [hs]; exact hp)]
  unfold padByte RIPEMD160.pad
  have hA : (d.push 0x80).size = d.size + 1 := ByteArray.size_push
  have hZ : (ByteArray.mk (Array.replicate ((119 - d.size % 64) % 64) (0 : UInt8))).size =
      (119 - d.size % 64) % 64 := Array.size_replicate
  by_cases h1 : p < d.size + 1 + (119 - d.size % 64) % 64
  · rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, hA, hZ]; exact h1)]
    by_cases h2 : p < d.size + 1
    · rw [ByteArray.getElem_append_left (by rw [hA]; exact h2), push_get]
      by_cases h3 : p < d.size
      · rw [dif_pos h3, if_pos h3, getElem!_pos d p h3]
      · rw [dif_neg h3, if_neg h3, if_pos (by omega)]
    · rw [ByteArray.getElem_append_right (by rw [hA]; omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
      simp [ByteArray.getElem_eq_getElem_data]
  · rw [ByteArray.getElem_append_right (by rw [ByteArray.size_append, hA, hZ]; omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn, ByteArray.size_append, hA, hZ]
    congr 3
    omega

end FeProofs.Ripemd160
