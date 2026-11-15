import FeProofs.Precompiles.Secp256k1.Precompile
import FeProofs.Precompiles.Bn254.Contract
import Ethereum.Theory.ECRecover

/-!
# EcrecoverPrecompile: the contract

The exported runtime entry of `EcrecoverPrecompile` against `Ethereum.Secp256k1.Spec.ecrecover`
and the ECRECOVER precompile.

- `ecrecOut_eq`: `ecrecOut` of the four words of the call data is `Spec.ecrecover`, the address
  word being the specification's last 20 bytes of `KEC (x ‖ y)` left-padded (`kec_two_words`,
  `toBytes32_mod160`).
- `arm_exec`: the fallback arm copies the call data into memory (`input_eq`), runs `ecrecover`,
  and diverges or stops with the bytes `Spec.ecrecover` gives.  `words`' allocation succeeds
  whenever it runs: it runs only for `v` in `{27, 28}`, which needs more than 32 bytes of call
  data (`word1_zero`), so the copied input has made memory nonempty.  Empty or short call data
  gives `v = 0` and returns nothing without allocating.
- `feEcrecoverPrecompileContractCorrect`: the same of the runtime entry, for every call data,
  without call value; with call value the entry reverts with no data (`runtime_value`).
  `precompile_eq`: with the 3000 gas ECRECOVER charges, the contract's output is the
  precompile's (`Ξ_ECREC_eq`).

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`), and memory has room for
the input and the 32-byte output.  Left open: divergence, the variable-time inversions of the key
recovery, whose termination is not proved; on the bytecode that is running out of gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.EcrecoverPrecompile

open FeProofs.Precompiles FeProofs.Keccak
open Precompiles.Exported.Shared Precompiles.Exported.EcrecoverPrecompile

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

/-! ## The address bytes -/

theorem byte_mod160 (a s : ℕ) (hs : s + 8 ≤ 160) : a % 2 ^ 160 / 2 ^ s % 256 = a / 2 ^ s % 256 := by
  rw [show (2 : ℕ) ^ 160 = 2 ^ s * 2 ^ (160 - s) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (show 256 ∣ 2 ^ (160 - s) from
      ⟨2 ^ (160 - s - 8), by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add]; congr 1; omega⟩)]

theorem toBytes32_mod160 (a : ℕ) :
    Weierstrass.toBytes32 (a % 2 ^ 160) =
      ByteArray.zeroes 12 ++ (Weierstrass.toBytes32 a).extract 12 32 := by
  apply ByteArray.ext
  rw [ByteArray.data_append]
  apply Array.ext
  · simp [Weierstrass.toBytes32, ByteArray.zeroes]
  · intro i h1 h2
    have hi : i < 32 := by simpa [Weierstrass.toBytes32] using h1
    simp only [Weierstrass.toBytes32, ByteArray.zeroes, Array.getElem_ofFn]
    by_cases h12 : i < 12
    · rw [Array.getElem_append_left (by simpa using h12)]
      simp only [Array.getElem_replicate]
      apply UInt8.toNat_inj.mp
      rw [toUInt8_toNat, Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide))
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      rfl
    · rw [Array.getElem_append_right (by simpa using h12)]
      simp [ByteArray.extract, Array.getElem_extract]
      rw [show 12 + (i - 12) = i by omega]
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
      exact byte_mod160 a _ (by omega)

/-- `ecrecOut` of the four words of the call data is `Spec.ecrecover`. -/
theorem ecrecOut_eq (d : ByteArray) :
    ecrecOut (BN254.Spec.word d 0) (BN254.Spec.word d 1) (BN254.Spec.word d 2)
      (BN254.Spec.word d 3) = Secp256k1.Spec.ecrecover d := by
  unfold ecrecOut Secp256k1.Spec.ecrecover BN254.Spec.word
  dsimp only
  split_ifs
  · rcases Secp256k1.Spec.recover _ _ _ _ with _ | ⟨x, y⟩
    · rfl
    · simp only [Secp256k1.Spec.publicKeyBytes, kec_two_words, toBytes32_mod160]
  · rfl

/-! ## The arm -/

theorem input_eq : input_Evm_4 = copyInput := rfl

/-- `v` in `{27, 28}` needs more than 32 bytes of call data. -/
theorem word1_zero {d : ByteArray} (h : d.size ≤ 32) : BN254.Spec.word d 1 = 0 := by
  rw [BN254.Spec.word, readBytes_be _ _ _ (by omega) (by omega)]
  have := beAt_tail (d := d) (off := 32) (m := 0) (by omega) 32
  simpa [beAt] using this

/-- **The arm**: it diverges, or returns the bytes `Spec.ecrecover` gives of the call data. -/
theorem arm_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + I.calldata.size + 32 < UInt256.size) :
    recv0_arm0.exec I w = none ∨
      ∃ memory, recv0_arm0.exec I w =
        some (.error (.stop (Secp256k1.Spec.ecrecover I.calldata) { w with memory := memory })) := by
  have hin : input_Evm_4.exec I w = _ := input_exec I w hfits (by omega)
  have hh := input_holds w.memory I.calldata (by omega)
  have hw := fun i hi =>
    FeProofs.Bn254Add.word_exec (I := I) (w := { w with memory := inputMemory w.memory I.calldata })
      hh i hi
  have hl := fun i hi => toNat_lit (FeProofs.Bn254Add.word_lt I.calldata i hi)
  have hM := inputMemory_size w.memory I.calldata
  have hpos : (UInt256.ofNat (BN254.Spec.word I.calldata 1)).toNat = 27 ∨
      (UInt256.ofNat (BN254.Spec.word I.calldata 1)).toNat = 28 →
      0 < ({ w with memory := inputMemory w.memory I.calldata } : World).memory.size := by
    intro h
    rw [hl 1 (by omega)] at h
    show 0 < (inputMemory w.memory I.calldata).size
    rw [hM]
    by_contra hc
    rw [word1_zero (by omega)] at h
    omega
  rcases ecrecover_spec (inputBuffer w.memory I.calldata) _ _ _ _ I
    { w with memory := inputMemory w.memory I.calldata } (hw 0 (by omega)) (hw 1 (by omega))
    (hw 2 (by omega)) (hw 3 (by omega)) hpos (by show (inputMemory _ _).size + 32 < _; omega)
    with he | ⟨o, mem, he, hrd⟩
  · left
    simp [recv0_arm0, hin, he]
  · right
    refine ⟨mem, ?_⟩
    rw [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega), ecrecOut_eq] at hrd
    simp [recv0_arm0, hin, he, MemBuffer_drop, Lib.dealloc_u8, Lib.cast_u8_u8, returnData, hrd]

/-! ## The contract -/

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv0_arm0_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

/-- Without call value the entry ends as the arm does. -/
theorem entry_runtime_none (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩)
    (h : recv0_arm0.exec I w.reserved = none) : (entry runtime).exec I w = none := by
  simp only [entry, M.exec_bind, exec_reserve, runtime_eq, recv0_arm0_entry, exec_nonPayable,
    ite_eq_left hv, h]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv0_arm0.exec I w.reserved = some (.error f)) :
    (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv0_arm0_entry, M.exec_bind, exec_nonPayable, ite_eq_left hv, h]

/-- **The contract `EcrecoverPrecompile` is ECRECOVER.**  On any call data `d` shorter than
    `2 ^ 64` bytes, with room in memory for the input and the 32-byte output, and no call value,
    the exported runtime entry diverges or stops with the bytes `Spec.ecrecover d` gives: the
    address of the recovered key as a word, or nothing; memory is all it changes. -/
theorem feEcrecoverPrecompileContractCorrect (I : ExecutionEnv) (w : World)
    (hfits : CalldataFits I) (hmem : w.memory.size + I.calldata.size + 32 < UInt256.size)
    (hv : I.weiValue = ⟨0⟩) :
    (entry runtime).exec I w = none ∨
      ∃ memory, (entry runtime).exec I w =
        some (.error (.stop (Secp256k1.Spec.ecrecover I.calldata) { w with memory := memory })) := by
  have hr : w.reserved.memory.size + I.calldata.size + 32 < UInt256.size := by
    have := w.reserved_size; unfold CalldataFits at hfits; unfold UInt256.size at hmem ⊢; omega
  rcases arm_exec I w.reserved hfits hr with h | ⟨memory, h⟩
  · exact Or.inl (entry_runtime_none I w hv h)
  · exact Or.inr ⟨memory, entry_runtime_error I w hv h⟩

/-- **The contract and the precompile.**  With the 3000 gas ECRECOVER charges, where the contract
    stops it returns the precompile's output, and the precompile keeps the account map. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : 3000 ≤ g.toNat) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 32 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    (entry runtime).exec I w = none ∨
      (∃ memory, (entry runtime).exec I w =
          some (.error (.stop (Ξ_ECREC σ g A I).2.2.2 { w with memory := memory })) ∧
        (Ξ_ECREC σ g A I).1 = σ) := by
  rw [Ξ_ECREC_eq, ite_eq_right (by omega)]
  rcases feEcrecoverPrecompileContractCorrect I w hfits hmem hv with h | ⟨memory, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨memory, h, rfl⟩

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv0_arm0_entry, M.exec_bind, exec_nonPayable, ite_eq_right hv]

end FeProofs.EcrecoverPrecompile
