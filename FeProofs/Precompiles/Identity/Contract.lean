import FeProofs.Precompiles.Blake2F.Contract
import FeProofs.Precompiles.Exported.Identity

/-!
# Identity: the contract

The exported runtime entry of `Identity` against the IDENTITY precompile, `Ξ_ID`.

- `arm_exec`: the fallback arm copies the call data into the input buffer (`input_exec`,
  `input_holds`), and `copied` allocates the output buffer with `MemBuffer::try_new`
  (`tryNew_exec`), which succeeds because the allocation is not at address 0. Then `copied`
  copies eight bytes at a time (`lanes_exec`, `le8_lane`) and the bytes left one at a time
  (`bytes_exec`, `low_byte`), and the arm returns the output buffer: the call data.
- `feIdentityContractCorrect`: the same of the runtime entry, without call value. The entry
  reserves low memory, so the arm runs on memory that is not empty, and the output buffer is
  never at address 0, empty call data included. `precompile_eq`: with at least the gas the
  precompile charges, its output is what the contract stops with.

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`), and memory has room for
the input and the output.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Precompiles.Identity

open Lib (MemBuffer)
open Exported.Shared
open Exported.Identity

/-! ## Bytes -/

/-- Two byte arrays of one size with the same big-endian number are equal. -/
theorem eq_of_be {a b : ByteArray} (hs : a.size = b.size)
    (h : fromByteArrayBigEndian a = fromByteArrayBigEndian b) : a = b := by
  apply ByteArray.ext
  apply Array.ext'
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    exact hs
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian]
    exact h

/-- The big-endian number of `le8 x`: the bytes of `x` from the least significant. -/
theorem be_le8 (x : ℕ) : fromByteArrayBigEndian (le8 x) =
    (List.range 8).foldl (fun acc n => acc * 256 + x / 256 ^ n % 256) 0 := by
  rw [fromByteArrayBigEndian, byteArray_toList_eq]
  show fromBytesBigEndian (Array.ofFn _).toList = _
  rw [Array.toList_ofFn, fromBytesBigEndian_ofFn (fun n => x / 256 ^ n) 8]

/-- A lane read little-endian fits in a `u64`. -/
theorem lane_lt (d : ByteArray) (j : ℕ) :
    (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d j 8))).toNat < 2 ^ 64 := by
  have hlt := foldl_digits_lt (fun n => beAt d j 8 / 256 ^ n % 256)
    (fun n => Nat.mod_lt _ (by decide)) (List.range 8) 0 0 (by decide)
  simp only [List.length_range, Nat.zero_add] at hlt
  rw [swapBytes_u64_toNat (beAt_lt d j 8)]
  simpa using hlt

/-- **A lane read and written back**: the eight bytes at `j`, read little-endian
    (`MemBuffer_lane_at`) and written little-endian (`MemBuffer_write_le_u64`), are the bytes
    there. -/
theorem le8_lane (d : ByteArray) (j : ℕ) (hj : j + 8 ≤ d.size) :
    le8 (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d j 8))).toNat = d.extract j (j + 8) := by
  have hb : beAt d j 8 < 2 ^ 64 := beAt_lt d j 8
  have hs := lane_lt d j
  apply eq_of_be (by rw [le8_size, ByteArray.size_extract]; omega)
  rw [be_le8, ← swapBytes_u64_toNat hs, u256_ofNat_toNat, swap_swap_beAt, toNat_lit (by omega),
    fromByteArrayBigEndian_extract d j 8 hj]

/-- The low byte of a word, as `mstoreInt (.u 8)` writes it. -/
theorem fromByteArrayBigEndian_low1 (y : UInt256) :
    fromByteArrayBigEndian (y.toByteArray.extract 31 32) = y.toNat % 2 ^ 8 := by
  have hs := toByteArray_size (v := y)
  have hsplit : y.toByteArray = y.toByteArray.extract 0 31 ++ y.toByteArray.extract 31 32 := by
    rw [ByteArray.extract_append_extract, Nat.zero_min, Nat.max_eq_right (by omega), ← hs,
      ByteArray.extract_zero_size]
  have hlt : fromByteArrayBigEndian (y.toByteArray.extract 31 32) < 2 ^ 8 := by
    have := fromBytes'_le (bs := (y.toByteArray.extract 31 32).toList.reverse)
    rw [List.length_reverse, byteArray_toList_eq, Array.length_toList] at this
    have h1 : (y.toByteArray.extract 31 32).data.size = 1 := by
      show (y.toByteArray.extract 31 32).size = 1
      rw [ByteArray.size_extract, hs]; rfl
    rw [h1] at this
    rw [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp, byteArray_toList_eq]
    exact this
  have h := fromByteArrayBigEndian_toByteArray y
  rw [hsplit, fromByteArrayBigEndian_append, ByteArray.size_extract, hs] at h
  rw [← h]
  simp only [show min 32 32 - 31 = 1 from rfl]
  omega

/-- **A byte read and written back**: the byte at `j` (`MemBuffer_byte_at`), stored as a `u8`,
    is the byte there. -/
theorem low_byte (d : ByteArray) (j : ℕ) (hj : j < d.size) :
    (UInt256.ofNat (byteAt d j)).toByteArray.extract 31 32 = d.extract j (j + 1) := by
  have hb := byteAt_lt d j
  apply eq_of_be (by rw [ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]; omega)
  rw [fromByteArrayBigEndian_low1, toNat_lit (by omega),
    Nat.mod_eq_of_lt (by omega : byteAt d j < 2 ^ 8),
    fromByteArrayBigEndian_extract d j 1 (by omega)]
  simp [beAt]

/-! ## The output region -/

/-- The output buffer after its first `k` bytes are copied: those of `d`, then zeros. -/
def region (d : ByteArray) (k : ℕ) : ByteArray :=
  d.extract 0 k ++ ⟨Array.replicate (d.size - k) 0⟩

theorem region_size (d : ByteArray) {k : ℕ} (hk : k ≤ d.size) : (region d k).size = d.size := by
  simp only [region, ByteArray.size_append, ByteArray.size_extract, zeros_size]
  omega

theorem region_zero (d : ByteArray) : region d 0 = ⟨Array.replicate d.size 0⟩ := by
  rw [region, ByteArray.extract_same, ByteArray.empty_append, Nat.sub_zero]

theorem region_full (d : ByteArray) : region d d.size = d := by
  rw [region, Nat.sub_self, ByteArray.extract_zero_size]
  exact ByteArray.append_empty

/-- Writing the `m` bytes of `d` at `k` into the output buffer copies them. -/
theorem region_write (d M src : ByteArray) {k m : ℕ} (hm : 0 < m) (hk : k + m ≤ d.size)
    (hsrc : src.extract 0 m = d.extract k (k + m)) (hsz : m ≤ src.size) :
    src.write 0 (M ++ region d k) (M.size + k) m = M ++ region d (k + m) := by
  have hr := region_size d (show k ≤ d.size by omega)
  have hek : (d.extract 0 k).size = k := by rw [ByteArray.size_extract]; omega
  rw [write_tail src M (region d k) 0 k m rfl (by omega) (by omega) (by omega), Nat.zero_add,
    hsrc]
  congr 1
  have hlo : (region d k).extract 0 k = d.extract 0 k := ByteArray.extract_append_eq_left hek.symm
  have hhi : (region d k).extract (k + m) (region d k).size =
      ⟨Array.replicate (d.size - (k + m)) 0⟩ := by
    rw [hr, region, ByteArray.extract_append, hek,
      ByteArray.extract_eq_empty_iff.mpr (by rw [hek]; omega), ByteArray.empty_append,
      zeros_extract]
    congr 2
    omega
  rw [hlo, hhi, region, ByteArray.extract_append_extract, Nat.zero_min,
    Nat.max_eq_right (by omega)]

/-! ## The copy -/

/-- **`MemBuffer::try_new`** on memory that is not empty: the allocation is not at address 0, so
    it succeeds, with a zeroed buffer at the end of memory. -/
theorem tryNew_exec (I : Env) (v : World) (n : ℕ) (hpos : 0 < v.memory.size)
    (hn : n < 2 ^ 64) (hroom : v.memory.size + n < UInt256.size) :
    (Lib.MemBuffer_try_new (UInt256.ofNat n)).exec I v =
      some (.ok (.Some ⟨UInt256.ofNat v.memory.size, UInt256.ofNat n, UInt256.ofNat n⟩,
        { v with memory := v.memory ++ ⟨Array.replicate n 0⟩ })) := by
  have hn' : (UInt256.ofNat n).toNat = n := toNat_lit (by omega)
  have hp : (UInt256.ofNat v.memory.size).toNat = v.memory.size := toNat_lit (by
    unfold UInt256.size at hroom; omega)
  have hmax : ¬ 18446744073709551615 < n := by omega
  have hne : UInt256.ofNat v.memory.size ≠ UInt256.ofNat 0 := fun e => by
    have := congrArg UInt256.toNat e
    rw [hp, toNat0] at this
    omega
  simp [Lib.MemBuffer_try_new, Lib.try_alloc_bytes, Lib.Option_u8.Some_0, Lib.zero_bytes, alloc,
    zeroMem, toNatMax,
    toNatU64, hn', hmax, hroom, hne, show ¬ UInt256.size - 1 < 18446744073709551615 by
      unfold UInt256.size; norm_num]
  rw [hp, FeProofs.Blake2F.zeros_write]

theorem le8_extract (x : ℕ) : (le8 x).extract 0 8 = le8 x :=
  calc (le8 x).extract 0 8 = (le8 x).extract 0 (le8 x).size := by rw [le8_size]
    _ = le8 x := ByteArray.extract_zero_size

theorem checkedAdd_ofNat (I : Env) (v : World) {a b : ℕ} (h : a + b < UInt256.size) :
    (checkedAdd (UInt256.ofNat a) (UInt256.ofNat b)).exec I v =
      some (.ok (UInt256.ofNat (a + b), v)) := by
  rw [checkedAdd, ite_eq_right (by rw [ulit_toNat' a (by omega), ulit_toNat' b (by omega)]; omega),
    ofNat_add_ofNat h]
  rfl

/-- The output buffer at the end of `M`. -/
abbrev out (M : ByteArray) (n : ℕ) : MemBuffer :=
  ⟨UInt256.ofNat M.size, UInt256.ofNat n, UInt256.ofNat n⟩

section Copy

variable (I : Env) (d M : ByteArray) (b : MemBuffer) (hb : Holds b d M)
  (hroom : M.size + d.size < UInt256.size) (hfits : d.size < 2 ^ 64)
include hb hroom hfits

set_option maxHeartbeats 2000000 in
/-- **The byte loop**: from byte `k` on, with the first `k` bytes copied, it copies the rest. -/
theorem bytes_exec (t : ℕ) : ∀ (k : ℕ) (v : World), k + t = d.size →
    v.memory = M ++ region d k →
    (copied_MemBuffer.loop.loop_1 b (UInt256.ofNat 0) (UInt256.ofNat d.size) (out M d.size)
        (UInt256.ofNat k)).exec I v =
      some (.ok (⟨UInt256.ofNat 0, UInt256.ofNat 0, out M d.size⟩,
        { v with memory := M ++ d })) := by
  have hn : (UInt256.ofNat d.size).toNat = d.size := toNat_lit (by omega)
  have hp : (UInt256.ofNat M.size).toNat = M.size := toNat_lit (by
    unfold UInt256.size at hroom; omega)
  induction t with
  | zero =>
    intro k v hk hv
    obtain rfl : k = d.size := by omega
    rw [copied_MemBuffer.loop.loop_1.eq_1]
    simp [hn, SUCCESS]
    rw [region_full] at hv
    cases v; simp_all
  | succ t ih =>
    intro k v hk hv
    have hkn : (UInt256.ofNat k).toNat = k := toNat_lit (by omega)
    have hs : (M ++ region d k).size = M.size + d.size := by
      rw [ByteArray.size_append, region_size d (by omega)]
    have hh : Holds b d v.memory := hv ▸ hb.append _ (by rw [← ByteArray.size_append, hs]; exact hroom)
    have hbyte := byte_exec (I := I) hh (j := k) (by omega)
    have hk' : M.size + k < UInt256.size := by omega
    have hpk : (UInt256.ofNat M.size + UInt256.ofNat k).toNat = M.size + k := by
      rw [uadd_toNat, hp, hkn, Nat.mod_eq_of_lt hk']
    have hnext : UInt256.ofNat k + UInt256.ofNat 1 = UInt256.ofNat (k + 1) :=
      ofNat_add_ofNat (by omega)
    have hw : ((UInt256.ofNat (byteAt d k)).toByteArray.extract 31 32).write 0 v.memory
        (M.size + k) 1 = M ++ region d (k + 1) := by
      rw [hv, region_write d M _ (by omega) (by omega)
        (by simp only [ByteArray.extract_extract, Nat.add_zero, show min (31 + 1) 32 = 32 from rfl]
            exact low_byte d k (by omega))
        (by rw [ByteArray.size_extract, toByteArray_size]; omega)]
    rw [copied_MemBuffer.loop.loop_1.eq_1]
    simp only [hkn, hn, show k < d.size by omega, decide_true, ite_true, Fe.M.exec_bind, hbyte,
      Lib.MemBuffer_index_mut, out, show ¬ d.size ≤ k by omega, decide_false, Bool.false_eq_true,
      ite_false, Fe.M.exec_pure, mstoreInt, Fe.M.exec_modify, IntTy.bits, hpk]
    rw [show (32 - 8 / 8 : ℕ) = 31 from rfl, show (8 / 8 : ℕ) = 1 from rfl, hw,
      checkedAdd_ofNat I _ (by omega)]
    exact ih (k + 1) _ (by omega) rfl

set_option maxHeartbeats 2000000 in
/-- **The lane loop**: from byte `k` on, with the first `k` bytes copied, it copies eight bytes
    at a time while eight are left, then the rest one at a time. -/
theorem lanes_exec (t : ℕ) :
    ∀ (k : ℕ) (v : World), k ≤ d.size → d.size < k + 8 * (t + 1) → v.memory = M ++ region d k →
    (copied_MemBuffer.loop b (UInt256.ofNat 0) (UInt256.ofNat d.size) (out M d.size)
        (UInt256.ofNat k)).exec I v =
      some (.ok (⟨UInt256.ofNat 0, UInt256.ofNat 0, out M d.size⟩,
        { v with memory := M ++ d })) := by
  have hn : (UInt256.ofNat d.size).toNat = d.size := toNat_lit (by omega)
  have hp : (UInt256.ofNat M.size).toNat = M.size := toNat_lit (by
    unfold UInt256.size at hroom; omega)
  induction t with
  | zero =>
    intro k v hk hlt hv
    rw [copied_MemBuffer.loop.eq_1]
    simp only [Fe.M.exec_bind, checkedAdd_ofNat I v (show k + 8 < UInt256.size by
      unfold UInt256.size; omega), toNat_lit (show k + 8 < 2 ^ 256 by omega),
      hn, show ¬ k + 8 ≤ d.size by omega, decide_false, Bool.false_eq_true, ite_false]
    exact bytes_exec I d M b hb hroom hfits (d.size - k) k v (by omega) hv
  | succ t ih =>
    intro k v hk hlt hv
    rw [copied_MemBuffer.loop.eq_1]
    simp only [Fe.M.exec_bind, checkedAdd_ofNat I v (show k + 8 < UInt256.size by
      unfold UInt256.size; omega), toNat_lit (show k + 8 < 2 ^ 256 by omega), hn]
    by_cases h8 : k + 8 ≤ d.size
    swap
    · simp only [h8, decide_false, Bool.false_eq_true, ite_false]
      exact bytes_exec I d M b hb hroom hfits (d.size - k) k v (by omega) hv
    have hs : (M ++ region d k).size = M.size + d.size := by
      rw [ByteArray.size_append, region_size d (by omega)]
    have hh : Holds b d v.memory := hv ▸ hb.append _ (by rw [← ByteArray.size_append, hs]; exact hroom)
    have hlane := lane_exec (I := I) hh (j := k) h8
    have hwr := write_le_exec (b := out M d.size) (I := I) (w := v) (off := k)
      (x := (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d k 8))).toNat) rfl
      (by rw [hn]; exact h8) (by rw [hp, hn, hv, hs]) (by rw [hv, hs]; exact hroom)
      (lane_lt d k)
    rw [u256_ofNat_toNat, hp] at hwr
    have hw : (le8 (IntTy.swapBytes (.u 64) (UInt256.ofNat (beAt d k 8))).toNat).write 0
        v.memory (M.size + k) 8 = M ++ region d (k + 8) := by
      rw [hv, region_write d M _ (by omega) h8 ((le8_extract _).trans (le8_lane d k h8))
        (by rw [le8_size])]
    simp only [h8, decide_true, ite_true, Fe.M.exec_bind, hlane, hwr, hw,
      checkedAdd_ofNat I _ (show k + 8 < UInt256.size by unfold UInt256.size; omega)]
    exact ih (k + 8) _ (by omega) (by omega) rfl

end Copy

set_option maxHeartbeats 2000000 in
/-- **`copied`** on the input buffer: it allocates the output buffer after the input and copies
    the call data into it. -/
theorem copied_exec (I : Env) (d M0 : ByteArray) (v : World) (hv : v.memory = inputMemory M0 d)
    (hpos : 0 < M0.size) (hfits : d.size < 2 ^ 64)
    (hmem : M0.size + 2 * d.size < UInt256.size) :
    (copied_MemBuffer (inputBuffer M0 d) (UInt256.ofNat 0)).exec I v =
      some (.ok (⟨UInt256.ofNat 0, UInt256.ofNat 0, out (inputMemory M0 d) d.size⟩,
        { v with memory := inputMemory M0 d ++ d })) := by
  have hM1 := inputMemory_size M0 d
  have hh := input_holds M0 d (by omega)
  have ht := tryNew_exec I v d.size (by rw [hv, hM1]; omega) hfits (by rw [hv, hM1]; omega)
  rw [hv] at ht
  simp only [copied_MemBuffer, Fe.M.exec_bind, len_exec, inputBuffer, ht, Fe.M.exec_pure,
    Lib.Option_MemBuffer.Some_0]
  exact lanes_exec I d (inputMemory M0 d) _ hh (by rw [hM1]; omega) hfits (d.size / 8) 0 _
    (by omega) (by omega) (by rw [region_zero])

theorem input_eq : input_Evm_5 = copyInput := rfl

/-- The `n` bytes after `M` in `M ++ d`, `n` the size of `d`, are `d`. -/
theorem read_after (M d : ByteArray) : (M ++ d).readWithPadding M.size d.size = d := by
  by_cases h0 : d.size = 0
  · rw [h0, byteArray_readWithPadding_zero]
    exact (ByteArray.size_eq_zero_iff.mp h0).symm
  rw [readWithPadding_tail M d 0 d.size (by omega) (by omega) (by omega), Nat.zero_add]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 2000000 in
/-- **The arm**: on memory that is not empty, it stops with the call data. -/
theorem arm_exec (I : Env) (w : World) (hpos : 0 < w.memory.size)
    (hfits : I.calldata.size < 2 ^ 64) (hmem : w.memory.size + 2 * I.calldata.size < UInt256.size) :
    recv_fallback.exec I w = some (.error (.stop I.calldata
      { w with memory := inputMemory w.memory I.calldata ++ I.calldata })) := by
  have hM1 := inputMemory_size w.memory I.calldata
  have hin := input_exec I w hfits (by omega)
  have hc := copied_exec I I.calldata w.memory { w with memory := inputMemory w.memory I.calldata }
    rfl hpos hfits hmem
  have hp : (UInt256.ofNat (inputMemory w.memory I.calldata).size).toNat =
      (inputMemory w.memory I.calldata).size := toNat_lit
        (by rw [hM1]; unfold UInt256.size at hmem; omega)
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := toNat_lit (by omega)
  simp only [recv_fallback, Fe.M.exec_bind, input_eq, hin, hc, Fe.M.exec_pure, Lib.MemBuffer_drop,
    Lib.dealloc_u8, Lib.cast_u8_u8, SUCCESS, ne_eq, not_true_eq_false, decide_false,
    Bool.false_eq_true, ite_false, Lib.MemBuffer_span_ref, Lib.MemSlice_from_raw_parts_ref_u8,
    Lib.Evm_return_data, Lib.MemSlice_ptr_u8, Lib.MemSlice_len_u8, out, returnData, hp, hn,
    Fe.M.exec_get, Fe.M.exec_stop, read_after]

/-! ## The contract -/

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv_fallback_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv_fallback.exec I w.reserved = some (.error f)) :
    (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv_fallback_entry, Fe.M.exec_bind, exec_nonPayable, ite_eq_left hv, h]

/-- **The contract `Identity` is IDENTITY.**  On call data shorter than `2 ^ 64` bytes, with room
    in memory for the input and the output, and no call value, the exported runtime entry stops
    with the call data, changing memory only.  It always terminates.  Empty call data included:
    the entry reserves low memory, so the output buffer `MemBuffer::try_new` allocates is not at
    address 0. -/
theorem feIdentityContractCorrect (I : ExecutionEnv) (w : World) (hfits : CalldataFits I)
    (hmem : w.memory.size + 2 * I.calldata.size < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    ∃ memory, (entry runtime).exec I w =
      some (.error (.stop I.calldata { w with memory := memory })) := by
  have hr := w.reserved_size
  unfold CalldataFits at hfits
  exact ⟨_, entry_runtime_error I w hv (arm_exec I w.reserved (by omega) hfits (by
    unfold UInt256.size at hmem ⊢; omega))⟩

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv_fallback_entry, Fe.M.exec_bind, exec_nonPayable, ite_eq_right hv]

/-- **The contract and the precompile.**  With at least the gas IDENTITY charges, the precompile
    returns what the contract stops with and keeps the account map. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : 15 + 3 * ((I.calldata.size + 31) / 32) ≤ g.toNat)
    (hfits : CalldataFits I) (hmem : w.memory.size + 2 * I.calldata.size < UInt256.size)
    (hv : I.weiValue = ⟨0⟩) :
    ∃ memory, (entry runtime).exec I w =
        some (.error (.stop (Ξ_ID σ g A I).2.2.2 { w with memory := memory })) ∧
      (Ξ_ID σ g A I).1 = σ := by
  obtain ⟨memory, h⟩ := feIdentityContractCorrect I w hfits hmem hv
  simp only [Ξ_ID, ite_eq_right (Nat.not_lt.mpr hg)]
  exact ⟨memory, h, trivial⟩

end FeProofs.Precompiles.Identity
