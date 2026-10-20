import FeProofs.Deposit.DepositHashBytes
import FeProofs.Deposit.DepositDecode
import FeProofs.Deposit.DepositRoutine

/-!
# FeDeposit `deposit()` — where the decoded `bytes` sit in memory

The decoder copies each `bytes` argument (length word and payload) from calldata into a fresh
allocation.  These lemmas read a payload window back out of such a copy, and keep it through
later writes that do not overlap it.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The decoded payload of the `bytes` argument whose head word is at relative offset `o` is the
    calldata window after its length word. -/
theorem dPayload_extract (cd : ByteArray) (o : ℕ) (h : 4 + o + 32 + dWord cd o ≤ cd.size) :
    cd.extract (4 + o + 32) (4 + o + 32 + dWord cd o) = dPayload cd o := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take,
    List.toList_toArray]
  rw [← byteArray_toList_eq, List.drop_drop]
  congr 2 <;> omega

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

/-- A write at or above a window leaves it unchanged, even when the write extends memory. -/
theorem write_extract_below (src base : ByteArray) {srcOff dest len i j : ℕ}
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hgap : dest - base.size < USize.size)
    (hij : i ≤ j) (hj : j ≤ base.size) (hjd : j ≤ dest) :
    (src.write srcOff base dest len).extract i j = base.extract i j := by
  by_cases hd : dest ≤ base.size
  · exact write_extract_preserved src base hpos hsrc hd hij hj (Or.inl hjd)
  · rw [write_from_gap_eq src base srcOff dest len hpos hsrc (by omega) hgap,
      ByteArray.append_assoc, extract_append_left _ _ i j hj]

/-- The decoder's memory before its copy: the free-pointer bump and the last-word clear. -/
abbrev rPreCopy (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) (z : ℕ) : ByteArray :=
  (UInt256.toByteArray ⟨0⟩).write 0
    ((F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray.write
      0 mem (UInt256.ofNat 64).toNat 32) z 32

theorem rMemAt_eq (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) :
    rMemAt ee mem p F = ee.calldata.write p.toNat (rPreCopy ee mem p F z) f (32 + L) := by
  show ee.calldata.write p.toNat _ F.toNat (UInt256.ofNat 32 + rLen ee p).toNat = _
  rw [hF, hlen, hz]

theorem rPreCopy_size (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {z : ℕ}
    (hgap : z < USize.size) : z + 32 ≤ (rPreCopy ee mem p F z).size :=
  write_size_reach _ _ (by decide) (by rw [toByteArray_size]) (by omega)

/-- **The decoder's copy, read back.**  After allocating at `F` (`F = f`) and copying the length
    word and the `L` payload bytes from calldata position `p`, the payload window holds the
    calldata payload. -/
theorem rMemAt_payload (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) (hfz : f ≤ z)
    (hgap : z < USize.size) (hcd : p.toNat + (32 + L) ≤ ee.calldata.size) :
    (rMemAt ee mem p F).extract (f + 32) (f + 32 + L) =
      ee.calldata.extract (p.toNat + 32) (p.toNat + 32 + L) := by
  have hsz := rPreCopy_size ee mem p F hgap
  rw [rMemAt_eq ee mem p F hF hlen hz]
  exact copyWindow_extract ee.calldata _ p.toNat f (32 + L) 32 L (by omega) hcd (by omega) (by omega)

/-- **Earlier allocations survive.**  A window between `0x60` and the new allocation `F = f`
    is unchanged by the decoder's free-pointer write, last-word clear and copy. -/
theorem rMemAt_below (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L i j : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) (hfz : f ≤ z)
    (hgap : z < USize.size) (hcd : p.toNat + (32 + L) ≤ ee.calldata.size)
    (hi : 96 ≤ i) (hij : i ≤ j) (hj : j ≤ mem.size) (hjf : j ≤ f) :
    (rMemAt ee mem p F).extract i j = mem.extract i j := by
  have hsz := rPreCopy_size ee mem p F hgap
  have hw32 : 32 ≤ (UInt256.toByteArray ⟨0⟩).size := by rw [toByteArray_size]
  have hu : 64 - mem.size < USize.size := Nat.lt_of_lt_of_le (by omega) USize.le_size
  have hm1 := write_size_ge
    (F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray mem
    (srcOff := 0) (dest := (UInt256.ofNat 64).toNat) (len := 32) (by decide) (by rw [toByteArray_size])
    (by show 64 - mem.size < USize.size; exact hu)
  have hm2 := write_size_ge (UInt256.toByteArray ⟨0⟩)
    ((F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray.write
      0 mem (UInt256.ofNat 64).toNat 32)
    (srcOff := 0) (dest := z) (len := 32) (by decide) hw32 (by omega)
  rw [rMemAt_eq ee mem p F hF hlen hz,
    write_extract_preserved ee.calldata _ (by omega) hcd (by omega) hij (by omega) (Or.inl hjf),
    write_extract_below _ _ (by decide) hw32 (by omega) hij (by omega) (by omega),
    write_extract_preserved _ _ (by decide) (by rw [toByteArray_size])
      (by show 64 ≤ mem.size; omega) hij hj (Or.inr (by show 64 + 32 ≤ i; omega))]

end FeProofs.Deposit
