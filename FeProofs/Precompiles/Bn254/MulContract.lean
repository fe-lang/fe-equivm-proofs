import FeProofs.Precompiles.Bn254.Mul
import FeProofs.Precompiles.Bn254.Contract

/-!
# Bn254Mul: the contract

The exported runtime entry of `Bn254Mul` against `Ethereum.BN254.Spec.mul` and the ECMUL
precompile, as `Bn254/Contract.lean` does for ECADD and with its lemmas: the three words `mul`
reads are `Spec.word d 0` to `Spec.word d 2` (`word_exec`), for input of any length; `input()`
is `copyInput` (`input_eq`).

- `arm_exec`: the fallback arm diverges, stops with the 64 bytes `Spec.mul` gives, or reverts
  with no data where it gives none.
- `feBn254MulContractCorrect`: the same of the runtime entry, without call value; with call
  value the entry reverts with no data (`runtime_value`).  `precompile_eq`: with the 6000 gas
  ECMUL charges, where the contract stops it returns the precompile's output (`Ξ_BN_MUL_eq`), and
  where it reverts the precompile fails.

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`), and memory has room for
the input and the 64-byte output.  Left open: divergence, the variable-time inversions in
`to_affine` (of the precomputed sum and of the result), whose termination is not proved; on the
bytecode that is running out of gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Bn254Mul

open FeProofs.Precompiles FeProofs.Bn254Add
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Mul

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

theorem input_eq : input_Evm_3 = copyInput := rfl

/-- **The arm**: it diverges, returns the 64 bytes `Spec.mul` gives of the input's three words,
    or reverts with no data where `Spec.mul` gives none. -/
theorem arm_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) :
    let d := I.calldata
    let r := BN254.Spec.mul (BN254.Spec.word d 0) (BN254.Spec.word d 1) (BN254.Spec.word d 2)
    recv_fallback.exec I w = none ∨
      (∃ o, r = some o ∧ ∃ memory,
        recv_fallback.exec I w = some (.error (.stop o { w with memory := memory }))) ∨
      (r = none ∧ recv_fallback.exec I w = some (.error (.revert ByteArray.empty))) := by
  intro d r
  have hin : input_Evm_3.exec I w = _ := input_exec I w hfits (by omega)
  have hh := input_holds w.memory I.calldata (by omega)
  have hw := fun i hi =>
    word_exec (I := I) (w := { w with memory := inputMemory w.memory I.calldata }) hh i hi
  have hl := fun i hi => toNat_lit (word_lt I.calldata i hi)
  have hM := inputMemory_size w.memory I.calldata
  have hp : (UInt256.ofNat (w.memory.size + I.calldata.size)).toNat =
      w.memory.size + I.calldata.size := toNat_lit (by unfold UInt256.size at hmem; omega)
  have t1 : (UInt256.ofNat 1).toNat = 1 := rfl
  have s64 : (UInt256.ofNat 64 - UInt256.ofNat 0).toNat = 64 := rfl
  have s64' : (UInt256.ofNat 64 - UInt256.ofNat 32).toNat = 32 := rfl
  have a32 : (UInt256.ofNat 0 + UInt256.ofNat 32).toNat = 32 := rfl
  have a64 : (UInt256.ofNat 32 + UInt256.ofNat 32).toNat = 64 := rfl
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have hroom : w.memory.size + I.calldata.size + 64 < UInt256.size := hmem
  have hroom0 : w.memory.size + I.calldata.size < UInt256.size := by omega
  rcases mul_MemBuffer_correct (inputBuffer w.memory I.calldata) _ _ _ I
    { w with memory := inputMemory w.memory I.calldata } (hw 0 (by omega)) (hw 1 (by omega))
    (hw 2 (by omega)) with ha | ⟨v, ha, hr⟩
  · left
    simp [recv_fallback, hin, ha]
  · rw [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega)] at hr
    rcases v with _ | v
    · right; right
      refine ⟨hr, ?_⟩
      simp [recv_fallback, hin, ha, alloc, toNatMax, toNatU64, toNat0, hmax, hM, hroom0, revertData,
        byteArray_readWithPadding_zero]
    · obtain ⟨a, b, rfl, hap, hbp, hspec⟩ := hr
      right; left
      refine ⟨_, hspec, ?_⟩
      simp [recv_fallback, hin, ha, checkIndex, alloc, zeroMem, mstore, returnData, toNatMax, toNatU64,
        toNat64, toNat0, toNat32, t1, s64, s64', a32, a64, hmax, hM, hroom, hp, Fe.EVM.add_zero]
      have hs32 : (UInt256.ofNat (w.memory.size + I.calldata.size) + UInt256.ofNat 32).toNat =
          w.memory.size + I.calldata.size + 32 := by
        rw [ofNat_add_ofNat (by omega), toNat_lit (by unfold UInt256.size at hmem; omega)]
      have hv0 : (Option_array_u256_2.Some #v[UInt256.ofNat a, UInt256.ofNat b]).Some_0[0] =
          UInt256.ofNat a := rfl
      have hv1 : (Option_array_u256_2.Some #v[UInt256.ofNat a, UInt256.ofNat b]).Some_0[1] =
          UInt256.ofNat b := rfl
      have hpa : a < 2 ^ 256 := lt_trans hap (by decide)
      have hpb : b < 2 ^ 256 := lt_trans hbp (by decide)
      rw [hs32, hv0, hv1, ← hM, returned2_read, toBytes32_eq hpa, toBytes32_eq hpb]

/-! ## The contract -/

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv_fallback_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

/-- Without call value the entry ends as the arm does. -/
theorem entry_runtime_none (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩)
    (h : recv_fallback.exec I w.reserved = none) : (entry runtime).exec I w = none := by
  simp only [entry, M.exec_bind, exec_reserve, runtime_eq, recv_fallback_entry, exec_nonPayable,
    if_pos hv, h]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv_fallback.exec I w.reserved = some (.error f)) :
    (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv_fallback_entry, M.exec_bind, exec_nonPayable, if_pos hv, h]

/-- **The contract `Bn254Mul` is ECMUL.**  On call data `d` shorter than `2 ^ 64` bytes, with
    room in memory for the input and the 64-byte output, and no call value, the exported runtime
    entry diverges, stops with the 64 bytes `Spec.mul` gives of the three words of `d`, or
    reverts with no data where `Spec.mul` gives none; memory is all a successful run changes. -/
theorem feBn254MulContractCorrect (I : ExecutionEnv) (w : World) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    let d := I.calldata
    let r := BN254.Spec.mul (BN254.Spec.word d 0) (BN254.Spec.word d 1) (BN254.Spec.word d 2)
    (entry runtime).exec I w = none ∨
      (∃ o, r = some o ∧ ∃ memory,
        (entry runtime).exec I w = some (.error (.stop o { w with memory := memory }))) ∨
      (r = none ∧ (entry runtime).exec I w = some (.error (.revert ByteArray.empty))) := by
  intro d r
  have hr : w.reserved.memory.size + I.calldata.size + 64 < UInt256.size := by
    have := w.reserved_size; unfold CalldataFits at hfits; unfold UInt256.size at hmem ⊢; omega
  rcases arm_exec I w.reserved hfits hr with h | ⟨o, ho, memory, h⟩ | ⟨ho, h⟩
  · exact Or.inl (entry_runtime_none I w hv h)
  · exact Or.inr (Or.inl ⟨o, ho, memory, entry_runtime_error I w hv h⟩)
  · exact Or.inr (Or.inr ⟨ho, entry_runtime_error I w hv h⟩)

/-- **The contract and the precompile.**  With the 6000 gas ECMUL charges, where the contract
    stops it returns the precompile's output and the precompile keeps the account map, and where
    it reverts the precompile fails. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : 6000 ≤ g.toNat) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    (entry runtime).exec I w = none ∨
      (∃ memory, (entry runtime).exec I w =
          some (.error (.stop (Ξ_BN_MUL σ g A I).2.2.2 { w with memory := memory })) ∧
        (Ξ_BN_MUL σ g A I).1 = σ) ∨
      ((entry runtime).exec I w = some (.error (.revert ByteArray.empty)) ∧
        Ξ_BN_MUL σ g A I = (∅, ⟨0⟩, A, .empty)) := by
  rw [Ξ_BN_MUL_eq, if_neg (by omega)]
  rcases feBn254MulContractCorrect I w hfits hmem hv with h | ⟨o, ho, memory, h⟩ | ⟨ho, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨memory, by simp only [ho]; exact h, by simp only [ho]⟩)
  · exact Or.inr (Or.inr ⟨h, by simp only [ho]⟩)

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv_fallback_entry, M.exec_bind, exec_nonPayable, if_neg hv]

end FeProofs.Bn254Mul
