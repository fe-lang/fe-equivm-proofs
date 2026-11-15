import FeProofs.Precompiles.LimbArray

/-!
# Precompiles: `MemSlice<u64>`

A `MemSlice<u64>` is a pointer and a length, like a `MemArray<u64>` without ownership.
`SliceAt s ls mem` says that `s` holds the limbs `ls` in `mem`, as `ArrayAt` does for arrays.

- `as_slice_ref_eq`, `as_slice_mut_eq` (`ArrayAt.slice`): an array's slice is its pointer and
  length; the `mut` form's write-back returns the array unchanged.
- `slice_ref_eq`, `slice_mut_eq`, `head_ref_eq`, `head_mut_eq` (`SliceAt.sub`, `SliceAt.head`):
  the `n` limbs from `i`, in bounds.
- `copy_from_exec`, `SliceAt.copy`: `dst.copy_from(src)` is `MCOPY` of `8 n` bytes; `dst` then
  holds what `src` held, even when the two overlap.
- `zero_exec`, `ArrayAt.zero`: `MemArray::zero` writes `8 n` zero bytes over the array.
- `LimbsAt.write_other`, `ArrayAt.write_other`, `SliceAt.write_other`: limbs apart from a write
  keep their values.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

open Lib (MemArray_u64 MemSlice_u64)

/-- The slice `s` holds the limbs `ls` in the memory `mem`, which is smaller than `2 ^ 256`
    bytes. -/
structure SliceAt (s : MemSlice_u64) (ls : List Limb) (mem : ByteArray) : Prop where
  len : s.len.toNat = ls.length
  limbs : LimbsAt mem s.ptr.toNat ls
  small : mem.size < UInt256.size

theorem ArrayAt.slice {a : MemArray_u64} {ls : List Limb} {mem : ByteArray} (h : ArrayAt a ls mem) :
    SliceAt ⟨a.ptr, a.len⟩ ls mem :=
  ⟨h.len, h.limbs, h.small⟩

theorem as_slice_ref_eq (a : MemArray_u64) : Lib.MemArray_as_slice_ref_u64 a = pure ⟨a.ptr, a.len⟩ := by
  simp [Lib.MemArray_as_slice_ref_u64, Lib.MemSlice_from_raw_parts_ref_u64]

theorem as_slice_mut_eq (a : MemArray_u64) :
    Lib.MemArray_as_slice_mut_u64 a = pure (⟨a.ptr, a.len⟩, fun _ => pure a) := by
  simp [Lib.MemArray_as_slice_mut_u64, Lib.MemSlice_from_raw_parts_mut_u64]

/-! ## Sub-slices -/

/-- Limbs `[i, i + n)` lie at `p + 8 i`. -/
theorem LimbsAt.sub {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls) {i n : ℕ}
    (hin : i + n ≤ ls.length) : LimbsAt mem (p + 8 * i) ((ls.drop i).take n) := by
  refine ⟨by simp only [List.length_take, List.length_drop]; have := h.1; omega, fun k hk => ?_⟩
  simp only [List.length_take, List.length_drop] at hk
  rw [List.getElem_take, List.getElem_drop, ← h.2 (i + k) (by omega)]
  congr 1; ring

theorem checkedSub_word {a : UInt256} {b : ℕ} (h : b ≤ a.toNat) :
    checkedSub a (UInt256.ofNat b) = pure (UInt256.ofNat (a.toNat - b)) := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  unfold checkedSub
  rw [toNat_lit (show b < 2 ^ 256 by omega), ite_eq_right (by omega)]
  congr 1
  apply word_eq_of_toNat
  rw [usub_toNat (by rw [toNat_lit (show b < 2 ^ 256 by omega)]; exact h),
    toNat_lit (show b < 2 ^ 256 by omega), toNat_lit (show a.toNat - b < 2 ^ 256 by omega)]

theorem slice_bounds {s : MemSlice_u64} {i n : ℕ} (hin : i + n ≤ s.len.toNat) :
    (UInt256.ofNat i).toNat = i ∧ (UInt256.ofNat n).toNat = n := by
  have := s.len.val.isLt
  exact ⟨toNat_lit (show i < 2 ^ 256 by change s.len.toNat < 2 ^ 256 at this; omega),
    toNat_lit (show n < 2 ^ 256 by change s.len.toNat < 2 ^ 256 at this; omega)⟩

/-- **`s.slice(i, n)`** in bounds: the `n` limbs from `i`. -/
theorem slice_ref_eq {s : MemSlice_u64} {i n : ℕ} (hin : i + n ≤ s.len.toNat)
    (hp : s.ptr.toNat + 8 * i < UInt256.size) :
    Lib.MemSlice_slice_ref_u64 s (UInt256.ofNat i) (UInt256.ofNat n) =
      pure ⟨UInt256.ofNat (s.ptr.toNat + 8 * i), UInt256.ofNat n⟩ := by
  obtain ⟨hi, hn⟩ := slice_bounds hin
  have hl : (UInt256.ofNat (s.len.toNat - i)).toNat = s.len.toNat - i :=
    toNat_lit (by have := s.len.val.isLt; change s.len.toNat < 2 ^ 256 at this; omega)
  simp [Lib.MemSlice_slice_ref_u64, hi, hn, show ¬ s.len.toNat < i by omega,
    checkedSub_word (show i ≤ s.len.toNat by omega), hl, show ¬ s.len.toNat - i < n by omega,
    elem_eq _ hp, Lib.MemSlice_from_raw_parts_ref_u64]

theorem slice_mut_eq {s : MemSlice_u64} {i n : ℕ} (hin : i + n ≤ s.len.toNat)
    (hp : s.ptr.toNat + 8 * i < UInt256.size) :
    Lib.MemSlice_slice_mut_u64 s (UInt256.ofNat i) (UInt256.ofNat n) =
      pure (⟨UInt256.ofNat (s.ptr.toNat + 8 * i), UInt256.ofNat n⟩, fun _ => pure s) := by
  obtain ⟨hi, hn⟩ := slice_bounds hin
  have hl : (UInt256.ofNat (s.len.toNat - i)).toNat = s.len.toNat - i :=
    toNat_lit (by have := s.len.val.isLt; change s.len.toNat < 2 ^ 256 at this; omega)
  simp [Lib.MemSlice_slice_mut_u64, hi, hn, show ¬ s.len.toNat < i by omega,
    checkedSub_word (show i ≤ s.len.toNat by omega), hl, show ¬ s.len.toNat - i < n by omega,
    elem_eq _ hp, Lib.MemSlice_from_raw_parts_mut_u64]

theorem ptr_add_zero (p : UInt256) : UInt256.ofNat (p.toNat + 8 * 0) = p := by
  rw [Nat.mul_zero, Nat.add_zero, ofNat_toNat]

/-- **`s.head(n)`**, `n` at most the length: the first `n` limbs. -/
theorem head_ref_eq {s : MemSlice_u64} {n : ℕ} (hn : n ≤ s.len.toNat) :
    Lib.MemSlice_head_ref_u64 s (UInt256.ofNat n) = pure ⟨s.ptr, UInt256.ofNat n⟩ := by
  have := s.ptr.val.isLt
  simp only [Lib.MemSlice_head_ref_u64,
    slice_ref_eq (s := s) (n := n) (i := 0) (by omega)
      (by change s.ptr.toNat < 2 ^ 256 at this; unfold UInt256.size; omega),
    ptr_add_zero, bind_pure]

theorem head_mut_eq {s : MemSlice_u64} {n : ℕ} (hn : n ≤ s.len.toNat) :
    Lib.MemSlice_head_mut_u64 s (UInt256.ofNat n) = pure (⟨s.ptr, UInt256.ofNat n⟩, fun _ => pure s) := by
  have := s.ptr.val.isLt
  simp [Lib.MemSlice_head_mut_u64,
    slice_mut_eq (s := s) (n := n) (i := 0) (by omega)
      (by change s.ptr.toNat < 2 ^ 256 at this; unfold UInt256.size; omega), ofNat_toNat]

/-- The sub-slice holds the limbs `[i, i + n)`. -/
theorem SliceAt.sub {s : MemSlice_u64} {ls : List Limb} {mem : ByteArray} (h : SliceAt s ls mem)
    {i n : ℕ} (hin : i + n ≤ ls.length) :
    SliceAt ⟨UInt256.ofNat (s.ptr.toNat + 8 * i), UInt256.ofNat n⟩ ((ls.drop i).take n) mem := by
  have hb := h.limbs.1
  have hs := h.small
  refine ⟨?_, ?_, hs⟩
  · simp only [List.length_take, List.length_drop]
    rw [toNat_lit (by unfold UInt256.size at hs; omega)]; omega
  · rw [toNat_lit (show s.ptr.toNat + 8 * i < 2 ^ 256 by unfold UInt256.size at hs; omega)]
    exact h.limbs.sub hin

theorem SliceAt.head {s : MemSlice_u64} {ls : List Limb} {mem : ByteArray} (h : SliceAt s ls mem)
    {n : ℕ} (hn : n ≤ ls.length) : SliceAt ⟨s.ptr, UInt256.ofNat n⟩ (ls.take n) mem := by
  have := h.sub (i := 0) (n := n) (by omega)
  rwa [ptr_add_zero, List.drop_zero] at this

/-! ## Writes over limbs -/

/-- A write apart from the limbs keeps them. -/
theorem LimbsAt.write_other {mem : ByteArray} {p : ℕ} {ks : List Limb} (h : LimbsAt mem p ks)
    {src : ByteArray} {so d n : ℕ} (hs : so + n ≤ src.size) (hd : d + n ≤ mem.size)
    (hdisj : d + n ≤ p ∨ p + 8 * ks.length ≤ d) : LimbsAt (src.write so mem d n) p ks :=
  h.congr (by rw [write_size_from _ _ _ _ _ hs hd]; exact h.1) (fun j _ _ => by
    rw [byteAt_write_from _ _ _ _ _ _ hs hd, ite_eq_right (by omega)])

/-- **A write of whole limbs** puts them at `d`. -/
theorem LimbsAt.write_same {src : ByteArray} {so : ℕ} {ls : List Limb} (h : LimbsAt src so ls)
    {mem : ByteArray} {d : ℕ} (hd : d + 8 * ls.length ≤ mem.size) :
    LimbsAt (src.write so mem d (8 * ls.length)) d ls := by
  refine ⟨by rw [write_size_from _ _ _ _ _ h.1 hd]; exact hd, fun k hk => ?_⟩
  rw [← h.2 k hk]
  apply beAt_congr
  intro j hj
  rw [byteAt_write_from _ _ _ _ _ _ h.1 hd, ite_eq_left (by omega)]
  congr 1; omega

theorem ArrayAt.write_other {a : MemArray_u64} {ls : List Limb} {mem : ByteArray}
    (h : ArrayAt a ls mem) {src : ByteArray} {so d n : ℕ} (hs : so + n ≤ src.size)
    (hd : d + n ≤ mem.size) (hdisj : d + n ≤ a.ptr.toNat ∨ a.ptr.toNat + 8 * ls.length ≤ d) :
    ArrayAt a ls (src.write so mem d n) :=
  ⟨h.len, h.limbs.write_other hs hd hdisj, by rw [write_size_from _ _ _ _ _ hs hd]; exact h.small⟩

theorem SliceAt.write_other {s : MemSlice_u64} {ls : List Limb} {mem : ByteArray}
    (h : SliceAt s ls mem) {src : ByteArray} {so d n : ℕ} (hs : so + n ≤ src.size)
    (hd : d + n ≤ mem.size) (hdisj : d + n ≤ s.ptr.toNat ∨ s.ptr.toNat + 8 * ls.length ≤ d) :
    SliceAt s ls (src.write so mem d n) :=
  ⟨h.len, h.limbs.write_other hs hd hdisj, by rw [write_size_from _ _ _ _ _ hs hd]; exact h.small⟩

/-! ## `copy_from` and `zero` -/

/-- **`dst.copy_from(src)`** of slices of equal length: `MCOPY` of their bytes. -/
theorem copy_from_exec {dst src : MemSlice_u64} (hl : src.len = dst.len)
    (h8 : 8 * src.len.toNat < UInt256.size) (I : Env) (w : World) :
    (Lib.MemSlice_copy_from_u64 dst src).exec I w =
      some (.ok (((), dst),
        { w with memory := w.memory.write src.ptr.toNat w.memory dst.ptr.toNat (8 * src.len.toNat) })) := by
  have hm : checkedMul src.len (UInt256.ofNat 8) = pure (UInt256.ofNat (8 * src.len.toNat)) := by
    have := src.len.val.isLt
    rw [← ofNat_toNat src.len, checkedMul_small (show src.len.toNat < 2 ^ 256 from this) (by norm_num)
      (by unfold UInt256.size at h8; omega), ofNat_toNat, Nat.mul_comm]
  have hne : (src.len ≠ dst.len) = False := by simp [hl]
  simp [Lib.MemSlice_copy_from_u64, hne, Lib.byte_ptr_u64, Lib.cast_u64_u8, Lib.MemSlice_as_bytes_u64,
    Lib.MemSlice_byte_len_u64, hm, Lib.MemSlice_from_raw_parts_ref_u8, Lib.copy, Lib.copy_raw,
    Lib.MemSlice_ptr_u8, Lib.MemSlice_len_u8, mcopy, Fe.M.exec_modify,
    toNat_lit (show 8 * src.len.toNat < 2 ^ 256 by unfold UInt256.size at h8; omega)]

/-- After `dst.copy_from(src)`, `dst` holds what `src` held. -/
theorem SliceAt.copy {src dst : MemSlice_u64} {ls ks : List Limb} {mem : ByteArray}
    (hs : SliceAt src ls mem) (hd : SliceAt dst ks mem) (hl : ks.length = ls.length) :
    SliceAt dst ls (mem.write src.ptr.toNat mem dst.ptr.toNat (8 * ls.length)) := by
  have hb := hd.limbs.1
  refine ⟨by rw [hd.len, hl], hs.limbs.write_same (by omega), ?_⟩
  rw [write_size_from _ _ _ _ _ hs.limbs.1 (by omega)]; exact hs.small

/-- **`a.zero()`**: `8 n` zero bytes over the array. -/
theorem zero_exec (a : MemArray_u64) (h8 : 8 * a.len.toNat < UInt256.size) (I : Env) (w : World) :
    (Lib.MemArray_zero_u64 a).exec I w =
      some (.ok (((), a),
        { w with memory := (zeros (8 * a.len.toNat)).write 0 w.memory a.ptr.toNat (8 * a.len.toNat) })) := by
  have hm : checkedMul a.len (UInt256.ofNat 8) = pure (UInt256.ofNat (8 * a.len.toNat)) := by
    have := a.len.val.isLt
    rw [← ofNat_toNat a.len, checkedMul_small (show a.len.toNat < 2 ^ 256 from this) (by norm_num)
      (by unfold UInt256.size at h8; omega), ofNat_toNat, Nat.mul_comm]
  simp [Lib.MemArray_zero_u64, as_slice_mut_eq, Lib.MemSlice_zero_u64, Lib.drop_in_place_n_u64,
    Lib.drop_range_u64, Lib.byte_ptr_u64, Lib.cast_u64_u8, Lib.MemSlice_byte_len_u64, hm,
    Lib.zero_bytes, zeroMem, Fe.M.exec_modify, zeros,
    toNat_lit (show 8 * a.len.toNat < 2 ^ 256 by unfold UInt256.size at h8; omega)]

/-- After `a.zero()`, the array holds zero limbs. -/
theorem ArrayAt.zero {a : MemArray_u64} {ls : List Limb} {mem : ByteArray} (h : ArrayAt a ls mem) :
    ArrayAt a (List.replicate ls.length 0)
      ((zeros (8 * ls.length)).write 0 mem a.ptr.toNat (8 * ls.length)) := by
  have hb := h.limbs.1
  have hz : LimbsAt (zeros (8 * ls.length)) 0 (List.replicate ls.length 0) := by
    have := limbsAt_zeros ByteArray.empty ls.length
    rwa [ByteArray.empty_append, ByteArray.size_empty] at this
  refine ⟨by rw [h.len, List.length_replicate], ?_, ?_⟩
  · have := hz.write_same (mem := mem) (d := a.ptr.toNat) (by rw [List.length_replicate]; exact hb)
    rwa [List.length_replicate] at this
  · rw [write_size_from _ _ _ _ _ (by simp) hb]; exact h.small

end FeProofs.Precompiles
