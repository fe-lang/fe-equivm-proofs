import Fe.EVM.Refine
import Reasoning.Memory

/-!
# The ABI encoding of `bytes`, and of `Error(string)` and `Panic(uint256)`

A specification, as byte arrays, of what the exported std code encodes and decodes:

- `abiBytesTail d`: a `bytes` (or `string`) value's tail, its length word, its bytes, and zeros
  to a whole word;
- `abiEncodeBytes ds`: a tuple of `bytes` values, a head of offset words followed by their tails,
  each offset counted from the start of the tuple;
- `Error(string)` and `Panic(uint256)` payloads, the selector followed by the argument's encoding.

`assertData_eq` and `panicData_eq`: the model library's revert payloads (`assertData`, Fe's
`assert!` with a message, and `panicData`, a panic) are these encodings, for any message and
code.
-/

namespace FeProofs.Lib

open Ethereum Fe Fe.EVM

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

@[simp] theorem zeros_size' (n : Nat) : (zeros n).size = n := by simp [zeros, ByteArray.size]

/-- The zero bytes that pad `n` bytes to a whole number of words. -/
def padLen (n : Nat) : Nat := (32 - n % 32) % 32

theorem add_padLen (n : Nat) : n + padLen n = (n + 31) / 32 * 32 := by
  unfold padLen; omega

/-- The 32-byte big-endian word of `n`. -/
def wordOf (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

@[simp] theorem wordOf_size (n : Nat) : (wordOf n).size = 32 := by
  simp [wordOf, Reasoning.Theory.toByteArray_size]

/-- A `bytes` value's tail: its length word, its bytes, and zeros to a whole word. -/
def abiBytesTail (d : ByteArray) : ByteArray := wordOf d.size ++ d ++ zeros (padLen d.size)

theorem abiBytesTail_size (d : ByteArray) :
    (abiBytesTail d).size = 32 + (d.size + 31) / 32 * 32 := by
  simp only [abiBytesTail, ByteArray.size_append, wordOf_size, zeros_size']
  have := add_padLen d.size
  omega

/-- The head of a tuple of `bytes` values whose tails start at `off`: the offset of each tail. -/
def abiBytesHeads : List ByteArray → Nat → ByteArray
  | [], _ => .empty
  | d :: ds, off => wordOf off ++ abiBytesHeads ds (off + (abiBytesTail d).size)

/-- The tails of a tuple of `bytes` values, one after another. -/
def abiBytesTails : List ByteArray → ByteArray
  | [] => .empty
  | d :: ds => abiBytesTail d ++ abiBytesTails ds

/-- The ABI encoding of a tuple of `bytes` values: offset words, counted from the tuple's start,
    then the tails. -/
def abiEncodeBytes (ds : List ByteArray) : ByteArray :=
  abiBytesHeads ds (32 * ds.length) ++ abiBytesTails ds

/-- The selector of `Error(string)`. -/
def errorSelector : ByteArray := ⟨#[0x08, 0xc3, 0x79, 0xa0]⟩

/-- The selector of `Panic(uint256)`. -/
def panicSelector : ByteArray := ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩

/-- A failed `assert!` with a message reverts with `Error(string)` of the message's UTF-8 bytes:
    the selector, then the ABI encoding of a one-field tuple of a string. -/
theorem assertData_eq (msg : String) :
    assertData msg = errorSelector ++ abiEncodeBytes [msg.toUTF8] := by
  simp only [assertData, abiEncodeBytes, abiBytesHeads, abiBytesTails, abiBytesTail, wordOf,
    errorSelector, zeros, padLen, List.length_singleton, Nat.mul_one, ByteArray.append_empty,
    ByteArray.append_assoc]

/-- A panic reverts with `Panic(uint256)` of its code: the selector, then the code's word. -/
theorem panicData_eq (c : Nat) : panicData c = panicSelector ++ wordOf c := rfl

end FeProofs.Lib
