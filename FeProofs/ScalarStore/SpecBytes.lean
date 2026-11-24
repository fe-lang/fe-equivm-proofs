import Fe.EVM.SpecHost
import Reasoning.Memory
import Fe.EVM.Entry
import Fe.Sem.Theory.HostCodec

/-!
# fe-spec's byte codecs and EVMLean's

The interpreter reads and writes words as fe-spec's `bytesNat` and `natBytes` (big-endian), and
its EVM host (`Fe/EVM/SpecHost.lean`) reads calldata with `readWithPadding`; the exported model
and the bytecode proofs use `fromByteArrayBigEndian`, `UInt256.toByteArray` and `readBytes`.
They agree.
-/

open Ethereum Reasoning.Theory Fe.EVM

namespace FeProofs.Spec

theorem foldl_be (l : List UInt8) (a : Nat) :
    l.foldl (fun acc x => acc * 256 + x.toNat) a = a * 256 ^ l.length + fromBytes' l.reverse := by
  induction l generalizing a with
  | nil => simp [fromBytes']
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, fromBytes'_append, List.length_reverse,
      show (2 : ℕ) ^ (8 * xs.length) = 256 ^ xs.length by rw [pow_mul]; norm_num]
    simp only [fromBytes', List.length_cons, pow_succ, UInt8.toNat]
    have : (x.toFin : ℕ) = x.toBitVec.toNat := rfl
    rw [this]; ring

theorem bytesNat_eq (b : ByteArray) : Fe.Sem.bytesNat b = fromByteArrayBigEndian b := by
  unfold Fe.Sem.bytesNat fromByteArrayBigEndian fromBytesBigEndian
  rw [← Array.foldl_toList, foldl_be, Ethereum.byteArray_toList_eq]
  simp

theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  apply ByteArray.ext; exact Array.toList_inj.mp h

theorem bsize (b : ByteArray) : b.size = b.data.toList.length := (Array.length_toList).symm

theorem readBytes_zero_32 (cd : ByteArray) : cd.readBytes 0 32 = cd.readWithPadding 0 32 := by
  apply bytes_ext
  have hcs := copySlice32_toList cd
  have hsz : (cd.copySlice 0 ByteArray.empty 0 32).size = min 32 cd.size := by
    rw [bsize, hcs, List.length_take, bsize]
  unfold ByteArray.readBytes ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp only [show (0 < 2 ^ 64 && 32 < 2 ^ 64) = true by decide, ite_true]
  rw [ByteArray.toList_data_append, hcs]
  by_cases h0 : cd.size = 0
  · have hz : cd.data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [← bsize]; exact h0)
    simp [h0, hz, hsz, byteArray_zeroes_toList]
  · simp [h0, hsz, byteArray_zeroes_toList, ByteArray.data_extract,
      Array.toList_extract, List.extract, ByteArray.size_extract]

/-- The interpreter's selector, the first word of calldata over `2 ^ 224`, is the selector word
    the dispatcher compares. -/
theorem selector_eq (cd : ByteArray) :
    Fe.Sem.bytesNat (cd.readWithPadding 0 32) / 2 ^ 224 = (selWord cd).toNat := by
  rw [bytesNat_eq, selWord, readBytes_zero_32, uInt256OfByteArray_eq]
  have hlt := fromByteArrayBigEndian_readWithPadding0_32_lt cd
  simp only [UInt256.shiftRight, UInt256.toNat]
  split
  · exact absurd ‹_› (by decide)
  have e : (UInt256.ofNat (fromByteArrayBigEndian (cd.readWithPadding 0 32))).val.val =
      fromByteArrayBigEndian (cd.readWithPadding 0 32) := UInt256.toNat_ofNat_of_lt hlt
  show _ = ((UInt256.ofNat _).val.val >>> (224 : Fin UInt256.size).val) % UInt256.size
  rw [e, show ((224 : Fin UInt256.size).val) = 224 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hlt)]

/-- A word as the interpreter writes it is EVMLean's 32 bytes of it. -/
theorem natBytes_eq (v : Nat) (hv : v < UInt256.size) :
    Fe.Sem.natBytes v 32 = UInt256.toByteArray (UInt256.ofNat v) := by
  have h := toByteArray_ofNat_fromByteArrayBigEndian_of_size (Fe.Sem.natBytes_size v 32)
  rw [← bytesNat_eq, Fe.Sem.bytesNat_natBytes, Nat.mod_eq_of_lt (by simpa [UInt256.size] using hv)] at h
  exact h.symm

end FeProofs.Spec
