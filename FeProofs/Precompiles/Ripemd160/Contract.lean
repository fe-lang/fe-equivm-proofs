import FeProofs.Precompiles.Ripemd160.Ripemd
import FeProofs.Precompiles.Blake2F.Contract
import Ethereum.Theory.RIP160

/-!
# Ripemd160: the contract

The exported runtime entry of `Ripemd160` against `RIPEMD160.hash` and the RIPEMD-160 precompile.

- `arm_exec`: the fallback arm allocates the 32-byte output buffer, then the input buffer, which
  holds the call data (`input_eq`, `input_exec`, `input_holds`); `ripemd160` gives the digest word
  (`ripemd160_exec`), whose 32 big-endian bytes are twelve zeros and the 20-byte digest
  (`digest_bytes`); `write_word` stores it and the arm returns those 32 bytes.
- `feRipemd160ContractCorrect`: the same of the runtime entry, without call value; it always
  stops, since every loop is bounded.  `precompile_eq`: with at least the gas the precompile
  charges, its output is what the contract stops with (`Ξ_RIP160_eq`).

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`), and memory has room for
the output and the input.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Ripemd160

open FeProofs.Precompiles
open Precompiles.Exported.Ripemd160

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

theorem input_eq : input_Evm_2 = copyInput := rfl

theorem zeroes_be (n : ℕ) : fromByteArrayBigEndian (ByteArray.zeroes n) = 0 := by
  rw [fromByteArrayBigEndian, byteArray_toList_eq]
  simp only [ByteArray.zeroes, Array.toList_replicate, fromBytesBigEndian, Function.comp,
    List.reverse_replicate]
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, fromBytes', ih]; rfl

/-- The word `ripemd160` returns is the digest, left-padded to 32 bytes. -/
theorem digest_bytes (d : ByteArray) :
    (UInt256.ofNat (fromByteArrayBigEndian (RIPEMD160.hash d))).toByteArray =
      ByteArray.zeroes 12 ++ RIPEMD160.hash d := by
  have hs := RIPEMD160.hash_size d
  have hl : fromByteArrayBigEndian (RIPEMD160.hash d) < 2 ^ 256 := by
    have := fromBytes'_le (bs := (RIPEMD160.hash d).toList.reverse)
    have hlen : (RIPEMD160.hash d).toList.reverse.length = 20 := by
      rw [List.length_reverse, byteArray_toList_eq, Array.length_toList]; exact hs
    rw [hlen] at this
    unfold fromByteArrayBigEndian fromBytesBigEndian
    exact lt_trans this (by norm_num)
  apply ByteArray.ext
  apply Array.ext'
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    change (UInt256.ofNat _).toByteArray.size = (ByteArray.zeroes 12 ++ RIPEMD160.hash d).size
    rw [toByteArray_size, ByteArray.size_append, ByteArray_zeroes_size, hs]
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian, fromByteArrayBigEndian_toByteArray,
      toNat_lit hl, fromByteArrayBigEndian_append, zeroes_be, Nat.zero_mul, Nat.zero_add]

/-- **The arm**: it stops with the digest of the call data, left-padded to 32 bytes. -/
theorem arm_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + 32 + I.calldata.size < UInt256.size) :
    ∃ memory, recv0_arm0.exec I w =
      some (.error (.stop (ByteArray.zeroes 12 ++ RIPEMD160.hash I.calldata)
        { w with memory := memory })) := by
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have hms : w.memory.size + 32 < UInt256.size := by omega
  simp [recv0_arm0, Lib.MemBuffer_new, Lib.MemBuffer_new_uninit, alloc, zeroMem, toNatMax, toNatU64,
    toNat0, toNat32, hmax, hms]
  have hp0 : (UInt256.ofNat w.memory.size).toNat = w.memory.size := toNat_lit (by
    unfold UInt256.size at hms; omega)
  set M1 := w.memory ++ (⟨Array.replicate 32 0⟩ : ByteArray) with hM1
  have hM1s : M1.size = w.memory.size + 32 := by
    rw [hM1, ByteArray.size_append]; rfl
  have hin := input_exec I { w with memory := M1 } hfits (by simp only; omega)
  have hh := input_holds M1 I.calldata (by omega)
  have hr := ripemd160_exec (I := I) (w := { w with memory := inputMemory M1 I.calldata }) hh hfits
  rw [hp0, FeProofs.Blake2F.zeros_write, ← hM1, input_eq]
  have s32 : (UInt256.ofNat 32 - UInt256.ofNat 0).toNat = 32 := rfl
  have a32 : (UInt256.ofNat 0 + UInt256.ofNat 32).toNat = 32 := rfl
  have hIM := inputMemory_size M1 I.calldata
  simp only [hin, hr]
  simp [s32, a32, Fe.EVM.add_zero, mstore, returnData, hp0]
  rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
    toByteArray_write32_read_back _ _ _ (by rw [hIM, hM1s]; omega), digest_bytes]

/-! ## The contract -/

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv0_arm0_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv0_arm0.exec I w = some (.error f)) : (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv0_arm0_entry, Fe.M.exec_bind, exec_nonPayable, if_pos hv, h]

/-- **The contract `Ripemd160` is RIPEMD-160.**  On call data shorter than `2 ^ 64` bytes, with
    room in memory for the 32-byte output and the input, and no call value, the exported runtime
    entry stops with the RIPEMD-160 digest of the call data, left-padded to 32 bytes, changing
    memory only.  It always terminates. -/
theorem feRipemd160ContractCorrect (I : ExecutionEnv) (w : World) (hfits : CalldataFits I)
    (hmem : w.memory.size + 32 + I.calldata.size < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    ∃ memory, (entry runtime).exec I w =
      some (.error (.stop (ByteArray.zeroes 12 ++ RIPEMD160.hash I.calldata)
        { w with memory := memory })) := by
  obtain ⟨memory, h⟩ := arm_exec I w hfits hmem
  exact ⟨memory, entry_runtime_error I w hv h⟩

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv0_arm0_entry, Fe.M.exec_bind, exec_nonPayable, if_neg hv]

/-- **The contract and the precompile.**  With at least the gas RIPEMD-160 charges, the precompile
    returns what the contract stops with and keeps the account map. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : 600 + 120 * ((I.calldata.size + 31) / 32) ≤ g.toNat)
    (hfits : CalldataFits I) (hmem : w.memory.size + 32 + I.calldata.size < UInt256.size)
    (hv : I.weiValue = ⟨0⟩) :
    ∃ memory, (entry runtime).exec I w =
        some (.error (.stop (Ξ_RIP160 σ g A I).2.2.2 { w with memory := memory })) ∧
      (Ξ_RIP160 σ g A I).1 = σ := by
  obtain ⟨memory, h⟩ := feRipemd160ContractCorrect I w hfits hmem hv
  rw [Ξ_RIP160_eq]
  simp only [if_neg (Nat.not_lt.mpr hg)]
  exact ⟨memory, h, trivial⟩

end FeProofs.Ripemd160
