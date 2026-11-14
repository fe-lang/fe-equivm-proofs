import FeProofs.Precompiles.Blake2F.Compress
import Ethereum.Theory.BLAKE2

/-!
# Blake2F: the contract

The exported runtime entry of `Blake2F` against `BLAKE2.compressInput` and the BLAKE2 F
precompile.

- `input_eq`: `input()` is `copyInput` (`Buffer.lean`), so the buffer holds the call data.
- `arm_exec`: the fallback arm reverts with no data unless the buffer has 213 bytes and byte 212
  (read through `MemBuffer_index_ref` and `mloadInt (.u 8)`, `index_exec` and `load_byte_exec`)
  is at most 1; then `compress` gives the eight output words (`compress_exec`), and the write
  loop (`loop_exec`, eight passes of `MemBuffer_write_le_u64`, `write_le_exec`) leaves them
  little-endian in a fresh 64-byte buffer (`outK`), which it returns: that is
  `compressInput` (`compressInput_out`).
- `feBlake2FContractCorrect`: the same of the runtime entry, without call value; with call value
  the entry reverts with no data (`runtime_value`).  Nothing diverges: `compress` and the write
  loop are total.  `precompile_eq`: with at least the gas of the rounds, the precompile's output
  is what the contract stops with, and it fails exactly where the contract reverts
  (`Ξ_BLAKE2_F_eq`).

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`), and memory has room for
the input and the 64-byte output.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Blake2F

open FeProofs.Precompiles
open Precompiles.Exported.Blake2F

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

theorem input_eq : input_Evm_1 = copyInput := rfl

/-! ## The output -/

/-- The first `8 * k` bytes of the output: the words `o 0, …, o (k - 1)`, each little-endian. -/
def outK (o : ℕ → UInt64) (k : ℕ) : ByteArray :=
  ⟨Array.ofFn fun i : Fin (8 * k) => UInt8.ofNat ((o (i.val / 8)).toNat / 256 ^ (i.val % 8))⟩

theorem outK_size (o : ℕ → UInt64) (k : ℕ) : (outK o k).size = 8 * k := Array.size_ofFn

theorem outK_succ (o : ℕ → UInt64) (k : ℕ) : outK o (k + 1) = outK o k ++ le8 (o k).toNat := by
  apply ByteArray.ext
  simp only [outK, le8, ByteArray.data_append]
  apply Array.ext
  · simp; ring
  · intro i h1 h2
    simp only [Array.getElem_append, Array.getElem_ofFn, Array.size_ofFn]
    split
    · rfl
    · rename_i h
      simp only [Array.size_append, Array.size_ofFn] at h1 h2
      rw [show i / 8 = k by omega, show i % 8 = i - 8 * k by omega]

/-- The output word `j`. -/
def outWord (d : ByteArray) (j : ℕ) : UInt64 := (outArr d)[j]!

/-- `compressInput` is the eight output words, each little-endian. -/
theorem compressInput_out (d : ByteArray) : BLAKE2.compressInput d = outK (outWord d) 8 := by
  rw [compressInput_eq]
  apply ByteArray.ext
  simp only [outK]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_ofFn, outWord]
    apply UInt8.toNat.inj
    rw [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show 8 * (i % 8) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * (i % 8) < 64 by omega), Nat.shiftRight_eq_div_pow, pow_mul]
    rfl

/-- **The write loop**: from pass `k` on, with the first `k` words written into the 64-byte
    buffer at the end of `M`, it writes the rest and returns the 64 bytes. -/
theorem loop_exec (o : ℕ → UInt64) (r1 : Lib.MemBuffer) (r3 : Lib.Range_Known_0_Known_8)
    (M : ByteArray) (hM : M.size + 64 < UInt256.size) (I : Env) (w : World) (k t : ℕ)
    (hkt : k + t = 8) (hw : w.memory = M ++ outK o k ++ ⟨Array.replicate (64 - 8 * k) 0⟩) :
    (recv0_arm0.b5 (Vector.ofFn fun j : Fin 8 => lw (o j.val)) r1
        ⟨UInt256.ofNat M.size, UInt256.ofNat 64, UInt256.ofNat 64⟩ r3 (UInt256.ofNat k)).exec I w =
      some (.error (.stop (outK o 8) { w with memory := M ++ outK o 8 })) := by
  have hm : (UInt256.ofNat M.size).toNat = M.size := ulit_toNat' _ (by omega)
  have t64 : (UInt256.ofNat 64).toNat = 64 := rfl
  induction t generalizing k w with
  | zero =>
    obtain rfl : k = 8 := by omega
    have hw' : w.memory = M ++ outK o 8 := by
      rw [hw]; exact ByteArray.append_empty
    rw [recv0_arm0.b5.eq_1]
    have hk : (UInt256.ofNat 8).toNat = 8 := rfl
    simp [Lib.Range_has_0_8, Lib.range_has, hk, toNat0, Lib.MemBuffer_span_ref,
      Lib.MemSlice_from_raw_parts_ref_u8, Lib.Evm_return_data, Lib.MemSlice_ptr_u8,
      Lib.MemSlice_len_u8, returnData, hw', hm, t64]
    refine ⟨?_, by cases w; simp_all⟩
    rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide)
        (by simp [ByteArray.size_append, outK_size]),
      ByteArray.extract_append_eq_right rfl (by simp [outK_size])]
  | succ t ih =>
    have hk : (UInt256.ofNat k).toNat = k := ulit_toNat' _ (by unfold UInt256.size; omega)
    have h8 : (UInt256.ofNat 8).toNat = 8 := rfl
    have hmul : UInt256.ofNat k * UInt256.ofNat 8 = UInt256.ofNat (8 * k) := by
      rw [ofNat_mul_ofNat (by unfold UInt256.size; omega) (by decide)
        (by unfold UInt256.size; omega), Nat.mul_comm]
    have hnext : UInt256.ofNat k + UInt256.ofNat 1 = UInt256.ofNat (k + 1) :=
      ofNat_add_ofNat (by unfold UInt256.size; omega)
    have hvk : (Vector.ofFn fun j : Fin 8 => lw (o j.val))[k]! = UInt256.ofNat (o k).toNat := by
      rw [getElem!_pos _ k (by omega)]; simp [lw]
    have hwr := write_le_exec (b := ⟨UInt256.ofNat M.size, UInt256.ofNat 64, UInt256.ofNat 64⟩)
      (I := I) (w := w) (off := 8 * k) (x := (o k).toNat) rfl (by simp only [t64]; omega)
      (by simp only [hm, t64, hw, ByteArray.size_append, outK_size, zeros_size]; omega)
      (by simp only [hw, ByteArray.size_append, outK_size, zeros_size]; omega) (o k).toNat_lt
    have hmem : (le8 (o k).toNat).write 0 w.memory (M.size + 8 * k) 8 =
        M ++ outK o (k + 1) ++ ⟨Array.replicate (64 - 8 * (k + 1)) 0⟩ := by
      rw [hw, show M.size + 8 * k = M.size + (outK o k).size by rw [outK_size],
        le8_write_append _ _ _ _ (by rw [zeros_size]; omega), outK_succ, zeros_extract,
        zeros_size]
      congr 3
      omega
    have := ih (k := k + 1) (w := { w with memory := M ++ outK o (k + 1) ++
      ⟨Array.replicate (64 - 8 * (k + 1)) 0⟩ }) (by omega) rfl
    rw [recv0_arm0.b5.eq_1]
    simp only [hm] at hwr
    have hc : ¬ UInt256.size ≤ k * 8 := by unfold UInt256.size; omega
    simp only [Lib.Range_has_0_8, Lib.range_has, hk, h8, toNat0, Lib.Range_at_0_8, checkedMul,
      hmul, checkIndex, show k < 8 by omega, hvk, hwr, hmem, Lib.Range_next_0_8,
      Lib.usize_wrapping_add, hnext, Fe.M.exec_bind, Fe.M.exec_pure, hc, if_false, if_true,
      show (0 ≤ k) = True by simp, decide_true]
    exact this

/-- A fresh zeroed buffer at the end of memory adds zeros. -/
theorem zeros_write (M : ByteArray) (n : ℕ) :
    (⟨Array.replicate n 0⟩ : ByteArray).write 0 (M ++ ⟨Array.replicate n 0⟩) M.size n =
      M ++ ⟨Array.replicate n 0⟩ := by
  by_cases h0 : n = 0
  · subst h0; exact byteArray_write_len_zero _ _ _ _
  rw [write_eq_gen _ _ _ _ h0 (by rw [zeros_size]) (by simp [ByteArray.size_append, zeros_size]),
    ByteArray.extract_append_eq_left rfl, zeros_extract, Nat.min_self, Nat.sub_zero,
    ByteArray.extract_eq_empty_iff.mpr (by simp [ByteArray.size_append, zeros_size]),
    ByteArray.append_empty]

/-! ## The arm -/

theorem outK_zero (o : ℕ → UInt64) : outK o 0 = ByteArray.empty :=
  ByteArray.size_eq_zero_iff.mp (outK_size o 0)

/-- **The arm**: on 213 bytes whose final byte is 0 or 1 it stops with `compressInput`, changing
    memory only; otherwise it reverts with no data. -/
theorem arm_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) :
    if I.calldata.size = 213 ∧ byteAt I.calldata 212 ≤ 1 then
      ∃ memory, recv0_arm0.exec I w =
        some (.error (.stop (BLAKE2.compressInput I.calldata) { w with memory := memory }))
    else recv0_arm0.exec I w = some (.error (.revert ByteArray.empty)) := by
  have hin : input_Evm_1.exec I w = _ := input_exec I w hfits (by omega)
  have hh := input_holds w.memory I.calldata (by omega)
  have hM := inputMemory_size w.memory I.calldata
  have hc : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    toNat_lit (by unfold UInt256.size at hmem; omega)
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have hroom : w.memory.size + I.calldata.size < UInt256.size := by omega
  have hroom64 : w.memory.size + I.calldata.size + 64 < UInt256.size := hmem
  by_cases hs : I.calldata.size = 213
  swap
  · rw [if_neg (fun h => hs h.1)]
    have hne : UInt256.ofNat I.calldata.size ≠ UInt256.ofNat 213 := fun e => hs (by
      have := congrArg UInt256.toNat e; rwa [hc] at this)
    simp [recv0_arm0, hin, inputBuffer, Lib.MemBuffer_len, INPUT_LEN, hne, alloc, toNatMax,
      toNatU64, toNat0, hmax, hM, hroom, revertData, byteArray_readWithPadding_zero]
  have hdec : decide ((inputBuffer w.memory I.calldata).len ≠ UInt256.ofNat 213) = false := by
    simp [inputBuffer, hs]
  have hi := index_exec (I := I) (w := { w with memory := inputMemory w.memory I.calldata })
    hh (j := 212) (by omega)
  have hl := load_byte_exec (I := I) (w := { w with memory := inputMemory w.memory I.calldata })
    hh (j := 212) (by omega)
  have hbt : (UInt256.ofNat (byteAt I.calldata 212)).toNat = byteAt I.calldata 212 :=
    toNat_lit (lt_trans (byteAt_lt _ _) (by norm_num))
  have t1 : (UInt256.ofNat 1).toNat = 1 := rfl
  by_cases hf : byteAt I.calldata 212 ≤ 1
  swap
  · rw [if_neg (fun h => hf h.2)]
    simp only [recv0_arm0, Fe.M.exec_bind, hin, Lib.MemBuffer_len, INPUT_LEN, hdec,
      Fe.M.exec_pure, Bool.false_eq_true, if_false, hi, hl]
    simp [hbt, t1, Nat.lt_of_not_le hf, alloc, toNatMax, toNatU64, toNat0, hmax, hM, hroom,
      revertData, byteArray_readWithPadding_zero]
  rw [if_pos ⟨hs, hf⟩]
  have hcomp := compress_exec (I := I) (w := { w with memory := inputMemory w.memory I.calldata })
    hh hs hf
  have hloop := loop_exec (outWord I.calldata) (inputBuffer w.memory I.calldata) ⟨(), ()⟩
    (inputMemory w.memory I.calldata) (by omega) I
    { w with memory := inputMemory w.memory I.calldata ++ ⟨Array.replicate 64 0⟩ } 0 8 rfl
    (by simp [outK_zero])
  have hp : (UInt256.ofNat (w.memory.size + I.calldata.size)).toNat =
      w.memory.size + I.calldata.size := toNat_lit (by unfold UInt256.size at hmem; omega)
  simp only [outWord] at hloop
  rw [compressInput_out]
  refine ⟨inputMemory w.memory I.calldata ++ outK (outWord I.calldata) 8, ?_⟩
  simp only [recv0_arm0, Fe.M.exec_bind, hin, Lib.MemBuffer_len, INPUT_LEN, hdec,
    Fe.M.exec_pure, Bool.false_eq_true, if_false, hi, hl]
  simp [hbt, t1, Nat.not_lt.mpr hf, hcomp, alloc, toNatMax, toNatU64, toNat0, toNat64, hmax, hM,
    hroom64, hp, zeroMem, Lib.Range_start_0_8]
  rw [← hM, zeros_write]
  exact hloop

/-! ## The contract -/

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv0_arm0_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv0_arm0.exec I w = some (.error f)) : (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv0_arm0_entry, Fe.M.exec_bind, exec_nonPayable, if_pos hv,
    h]

/-- The specification's test of the final byte. -/
theorem flag_iff (d : ByteArray) : d[212]! ≤ 1 ↔ byteAt d 212 ≤ 1 := by
  rw [UInt8.le_iff_toNat_le, byte_get]; rfl

/-- **The contract `Blake2F` is BLAKE2 F.**  On call data shorter than `2 ^ 64` bytes, with room in
    memory for the input and the 64-byte output, and no call value, the exported runtime entry
    stops with `compressInput` of the call data when it has 213 bytes and a final block flag of
    0 or 1, changing memory only, and reverts with no data otherwise.  It always terminates. -/
theorem feBlake2FContractCorrect (I : ExecutionEnv) (w : World) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    if I.calldata.size = 213 ∧ I.calldata[212]! ≤ 1 then
      ∃ memory, (entry runtime).exec I w =
        some (.error (.stop (BLAKE2.compressInput I.calldata) { w with memory := memory }))
    else (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  have h := arm_exec I w hfits hmem
  simp only [flag_iff]
  split
  · rw [if_pos (by assumption)] at h
    obtain ⟨memory, h⟩ := h
    exact ⟨memory, entry_runtime_error I w hv h⟩
  · rw [if_neg (by assumption)] at h
    exact entry_runtime_error I w hv h

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv0_arm0_entry, Fe.M.exec_bind, exec_nonPayable, if_neg hv]

/-- **The contract and the precompile.**  With at least the gas of the rounds the first four
    bytes give, the precompile returns what the contract stops with and keeps the account map,
    and it fails exactly where the contract reverts. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat)
    (hfits : CalldataFits I) (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size)
    (hv : I.weiValue = ⟨0⟩) :
    (∃ memory, (entry runtime).exec I w =
        some (.error (.stop (Ξ_BLAKE2_F σ g A I).2.2.2 { w with memory := memory })) ∧
      (Ξ_BLAKE2_F σ g A I).1 = σ) ∨
    ((entry runtime).exec I w = some (.error (.revert ByteArray.empty)) ∧
      Ξ_BLAKE2_F σ g A I = (∅, ⟨0⟩, A, .empty)) := by
  have h := feBlake2FContractCorrect I w hfits hmem hv
  rw [Ξ_BLAKE2_F_eq]
  simp only [if_neg (Nat.not_lt.mpr hg)]
  split
  · rename_i hc
    rw [if_pos hc] at h
    obtain ⟨memory, h⟩ := h
    exact Or.inl ⟨memory, h, rfl⟩
  · rename_i hc
    rw [if_neg hc] at h
    exact Or.inr ⟨h, rfl⟩

end FeProofs.Blake2F
