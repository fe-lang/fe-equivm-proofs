import FeProofs.Precompiles.Bn254.Add
import FeProofs.Precompiles.Buffer
import Fe.EVM.Entry
import Ethereum.Theory.BN254

/-!
# Bn254Add: the contract

The exported runtime entry of `Bn254Add` against `Ethereum.BN254.Spec.add` and the ECADD
precompile.

- `word_at_exec`: fevm's `word_at`, on a buffer that holds bytes `d` (`Holds`,
  `FeProofs/Precompiles/Buffer.lean`), returns at any offset `off` (with `off + 32 < 2 ^ 256`)
  the big-endian number of the 32 bytes of `d` from `off`, zero past its end, the world
  unchanged: four lanes where the bytes are there (`word_at_full`), the byte loop otherwise
  (`word_at_loop`).  So the four words `add` reads are `Spec.word d 0` to `Spec.word d 3`
  (`word_exec`), for input of any length: empty, short, 128 bytes or longer.
- `input_eq`: `input()` is `copyInput`, which allocates a buffer of the call data's size at the
  end of memory and copies the call data in (`input_exec`, `input_holds` in `Buffer.lean`).
- `arm_exec`: the fallback arm diverges, stops with the 64 bytes `Spec.add` gives
  (`toBytes32 x ++ toBytes32 y`, written by two `write_word`s into a fresh buffer and returned),
  or reverts with no data where it gives none.
- `feBn254AddContractCorrect`: the same of the runtime entry, without call value; with call value
  the entry reverts with no data (`runtime_value`): the exported entry of the fallback starts with
  `nonPayable`, where the precompile accepts value.  `precompile_eq`: with the 150 gas ECADD charges, where the
  contract stops it returns the precompile's output (`Ξ_BN_ADD_eq`), and where it reverts the
  precompile fails.

Assumed: the call data is shorter than `2 ^ 64` bytes (`CalldataFits`, std reads lengths as
`u64`), and memory has room for the input and the 64-byte output.  Left open: divergence, the
variable-time inversion in `to_affine`, whose termination is not proved; on the bytecode that is
running out of gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

/-! ## `word_at` -/

/-- Four lanes, each the big-endian number of eight bytes, assemble into the number of the 32. -/
theorem lanes_eq (d : ByteArray) (off : ℕ) :
    UInt256.ofNat (beAt d off 8) <<< UInt256.ofNat 192 |||
        UInt256.ofNat (beAt d (off + 8) 8) <<< UInt256.ofNat 128 |||
        UInt256.ofNat (beAt d (off + 16) 8) <<< UInt256.ofNat 64 |||
        UInt256.ofNat (beAt d (off + 24) 8) =
      UInt256.ofNat (beAt d off 32) := by
  have h0 := beAt_lt d off 8; have h1 := beAt_lt d (off + 8) 8
  have h2 := beAt_lt d (off + 16) 8; have h3 := beAt_lt d (off + 24) 8
  simp only [show 8 * 8 = 64 from rfl] at h0 h1 h2 h3
  have e : beAt d off 32 = ((beAt d off 8 * 2 ^ 64 + beAt d (off + 8) 8) * 2 ^ 64 +
      beAt d (off + 16) 8) * 2 ^ 64 + beAt d (off + 24) 8 := by
    rw [show 32 = 8 + 8 + 8 + 8 from rfl, beAt_add, beAt_add, beAt_add]
  have l : ∀ {n : ℕ}, n < 2 ^ 64 → (UInt256.ofNat n).toNat = n := fun h =>
    toNat_lit (lt_trans h (by norm_num))
  apply word_eq_of_toNat
  change (UInt256.lor (UInt256.lor (UInt256.lor _ _) _) _).toNat = _
  rw [u256_lor_toNat_exact, u256_lor_toNat_exact, u256_lor_toNat_exact,
    shiftLeft_toNat _ (by decide) (by rw [l h0]; omega),
    shiftLeft_toNat _ (by decide) (by rw [l h1]; omega),
    shiftLeft_toNat _ (by decide) (by rw [l h2]; omega), l h0, l h1, l h2, l h3, e,
    toNat_lit (by omega)]
  generalize beAt d off 8 = a0 at h0 ⊢
  generalize beAt d (off + 8) 8 = a1 at h1 ⊢
  generalize beAt d (off + 16) 8 = a2 at h2 ⊢
  generalize beAt d (off + 24) 8 = a3 at h3 ⊢
  have e1 : 2 ^ 192 * a0 ||| 2 ^ 128 * a1 = 2 ^ 128 * (2 ^ 64 * a0 + a1) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (show 2 ^ 128 * a1 < 2 ^ 192 by omega)]; ring
  have e2 : 2 ^ 128 * (2 ^ 64 * a0 + a1) ||| 2 ^ 64 * a2 =
      2 ^ 64 * ((2 ^ 64 * a0 + a1) * 2 ^ 64 + a2) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (show 2 ^ 64 * a2 < 2 ^ 128 by omega)]; ring
  have e3 : 2 ^ 64 * ((2 ^ 64 * a0 + a1) * 2 ^ 64 + a2) ||| a3 =
      ((a0 * 2 ^ 64 + a1) * 2 ^ 64 + a2) * 2 ^ 64 + a3 := by
    rw [← Nat.two_pow_add_eq_or_of_lt h3]; ring
  rw [e1, e2, e3]

/-- `word_at` where the 32 bytes are there: four lanes. -/
theorem word_at_full {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) {off : ℕ} (hoff : off + 32 ≤ d.size) :
    (word_at_MemBuffer b (UInt256.ofNat off)).exec I w =
      some (.ok (UInt256.ofNat (beAt d off 32), w)) := by
  have hs := h.small; have hb := h.bound
  have hn : (UInt256.ofNat off).toNat = off := toNat_lit (by unfold UInt256.size at hs; omega)
  have ha : ∀ k, k ≤ 32 → UInt256.ofNat off + UInt256.ofNat k = UInt256.ofNat (off + k) :=
    fun k hk => ofNat_add_ofNat (by omega)
  have hl : ∀ k, k ≤ 32 → (UInt256.ofNat (off + k)).toNat = off + k := fun k hk =>
    toNat_lit (by unfold UInt256.size at hs; omega)
  have t8 : (UInt256.ofNat 8).toNat = 8 := rfl
  have t16 : (UInt256.ofNat 16).toNat = 16 := rfl
  have t24 : (UInt256.ofNat 24).toNat = 24 := rfl
  have hc : ∀ k, k ≤ 32 → ¬ UInt256.size ≤ off + k := fun k hk => by omega
  simp [word_at_MemBuffer, checkedAdd, hn, toNat32, t8, t16, t24, ha 32 le_rfl, ha 8 (by omega),
    ha 16 (by omega), ha 24 (by omega), hl 32 le_rfl, len_exec, h.len, hoff, hc 32 le_rfl,
    hc 8 (by omega), hc 16 (by omega), hc 24 (by omega),
    lane_exec h (show off + 8 ≤ d.size by omega), lane_exec h (j := off + 8) (by omega),
    lane_exec h (j := off + 16) (by omega), lane_exec h (j := off + 24) (by omega), swap_swap_beAt,
    lanes_eq]

/-- One byte more, big-endian. -/
theorem shift_or_byte {x y : ℕ} (hx : x < 2 ^ 248) (hy : y < 256) :
    UInt256.ofNat x <<< UInt256.ofNat 8 ||| UInt256.ofNat y = UInt256.ofNat (x * 256 + y) := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, shiftLeft_toNat _ (by decide) (by rw [toNat_lit (by omega)]; omega),
    toNat_lit (by omega), toNat_lit (by omega), toNat_lit (by omega),
    ← Nat.two_pow_add_eq_or_of_lt (show y < 2 ^ 8 by omega)]
  ring

/-- `word_at`'s byte loop, from the byte `t` on. -/
theorem word_at_loop {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) {off : ℕ} (hoff : off + 32 < UInt256.size) (k t : ℕ)
    (hkt : k + t = 32) :
    (word_at_MemBuffer.b4 b (UInt256.ofNat (beAt d off t))
        ⟨UInt256.ofNat off, UInt256.ofNat (off + 32)⟩ (UInt256.ofNat (off + t))).exec I w =
      some (.ok (UInt256.ofNat (beAt d off 32), w)) := by
  have hl : ∀ k, k ≤ 32 → (UInt256.ofNat (off + k)).toNat = off + k := fun k hk =>
    toNat_lit (by unfold UInt256.size at hoff; omega)
  have hn : (UInt256.ofNat off).toNat = off := by simpa using hl 0 (by omega)
  induction k generalizing t with
  | zero =>
    obtain rfl : t = 32 := by omega
    rw [word_at_MemBuffer.b4.eq_1]
    simp [Lib.Range_Unknown_Unknown_has, Lib.range_has, hl 32 le_rfl, hn]
  | succ k ih =>
    rw [word_at_MemBuffer.b4.eq_1]
    have hlt := beAt_lt d off t
    have hstep := shift_or_byte (x := beAt d off t) (y := byteAt d (off + t))
      (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))) (byteAt_lt _ _)
    have hnext : UInt256.ofNat (off + t) + UInt256.ofNat 1 = UInt256.ofNat (off + (t + 1)) :=
      ofNat_add_ofNat (by omega)
    have := ih (t + 1) (by omega)
    rw [show beAt d off (t + 1) = beAt d off t * 256 + byteAt d (off + t) from rfl] at this
    simp [Lib.Range_Unknown_Unknown_has, Lib.range_has, Lib.Range_Unknown_Unknown_at,
      Lib.Range_Unknown_Unknown_next, Lib.usize_wrapping_add, len_exec, h.len, hl t (by omega),
      hl 32 le_rfl, hn, show off + t < off + 32 by omega]
    rw [hnext]
    split
    · rw [M.exec_bind, byte_exec h (by assumption)]
      simp only [hstep]
      exact this
    · rw [byteAt_of_ge (by omega)] at hstep this
      rw [hstep]
      exact this

/-- **`word_at`** gives the big-endian number of the 32 bytes at `off`, zero-padded: four lanes
    where the bytes are there, the byte loop otherwise. -/
theorem word_at_exec {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) {off : ℕ} (hoff : off + 32 < UInt256.size) :
    (word_at_MemBuffer b (UInt256.ofNat off)).exec I w =
      some (.ok (UInt256.ofNat (beAt d off 32), w)) := by
  by_cases hf : off + 32 ≤ d.size
  · exact word_at_full h hf
  have hn : (UInt256.ofNat off).toNat = off := toNat_lit (by unfold UInt256.size at hoff; omega)
  have h32 : (UInt256.ofNat (off + 32)).toNat = off + 32 :=
    toNat_lit (by unfold UInt256.size at hoff; omega)
  have hloop := word_at_loop (I := I) h hoff 32 0 rfl
  simp only [show beAt d off 0 = 0 from rfl, Nat.add_zero] at hloop
  simp [word_at_MemBuffer, checkedAdd, hn, toNat32, ofNat_add_ofNat hoff, h32, len_exec, h.len,
    hf, Nat.not_le.mpr hoff, Lib.Range_Unknown_Unknown_start, hloop]

/-! ## The input -/

theorem input_eq : input_Evm = copyInput := rfl

/-! ## The arm -/

/-- The four words of the input are `Spec.word`. -/
theorem word_exec {I : Env} {w : World} {b : Lib.MemBuffer} {d : ByteArray}
    (h : Holds b d w.memory) (i : ℕ) (hi : i < 4) :
    (word_at_MemBuffer b (UInt256.ofNat (32 * i))).exec I w =
      some (.ok (UInt256.ofNat (BN254.Spec.word d i), w)) := by
  rw [word_at_exec h (by unfold UInt256.size; omega), BN254.Spec.word,
    readBytes_be _ _ _ (by omega) (by omega)]

theorem word_lt (d : ByteArray) (i : ℕ) (hi : i < 4) : BN254.Spec.word d i < 2 ^ 256 := by
  rw [BN254.Spec.word, readBytes_be _ _ _ (by omega) (by omega)]
  exact beAt_lt d _ 32

/-- Two words written into a fresh 64-byte buffer at the end of memory read back as their
    concatenation. -/
theorem returned2_read (memory : ByteArray) (x y : UInt256) :
    (y.toByteArray.write 0 (x.toByteArray.write 0
        ((⟨Array.replicate 64 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 64 0⟩)
          memory.size 64) memory.size 32) (memory.size + 32) 32).readWithPadding memory.size 64 =
      x.toByteArray ++ y.toByteArray := by
  have hz : (⟨Array.replicate 64 0⟩ : ByteArray).size = 64 := rfl
  set m := memory.size
  set B0 := (⟨Array.replicate 64 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 64 0⟩) m 64
  have h0 : B0.size = m + 64 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
      ByteArray.size_append, hz]
  have h1 : (x.toByteArray.write 0 B0 m 32).size = m + 64 := by
    rw [write32_size_of_end_le _ _ _ (by omega), h0]
  have hs := toByteArray_size
  rw [show (64 : ℕ) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ _ 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [write32_size_of_end_le _ _ _ (by omega), h1])]
  rw [write32_read_below _ _ _ _ (by rw [hs]) (by omega) (by omega),
    toByteArray_write32_read_back _ _ _ (by omega), toByteArray_write32_read_back _ _ _ (by omega)]

/-- **The arm**: it diverges, returns the 64 bytes `Spec.add` gives of the input's four words,
    or reverts with no data where `Spec.add` gives none. -/
theorem arm_exec (I : Env) (w : World) (hfits : I.calldata.size < 2 ^ 64)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) :
    let d := I.calldata
    let r := BN254.Spec.add (BN254.Spec.word d 0) (BN254.Spec.word d 1) (BN254.Spec.word d 2)
      (BN254.Spec.word d 3)
    recv0_arm0.exec I w = none ∨
      (∃ o, r = some o ∧ ∃ memory,
        recv0_arm0.exec I w = some (.error (.stop o { w with memory := memory }))) ∨
      (r = none ∧ recv0_arm0.exec I w = some (.error (.revert ByteArray.empty))) := by
  intro d r
  have hin : input_Evm.exec I w = _ := input_exec I w hfits (by omega)
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
  rcases add_MemBuffer_correct (inputBuffer w.memory I.calldata) _ _ _ _ I
    { w with memory := inputMemory w.memory I.calldata } (hw 0 (by omega)) (hw 1 (by omega))
    (hw 2 (by omega)) (hw 3 (by omega)) with ha | ⟨v, ha, hr⟩
  · left
    simp [recv0_arm0, hin, ha]
  · rw [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega)] at hr
    rcases v with _ | v
    · right; right
      refine ⟨hr, ?_⟩
      simp [recv0_arm0, hin, ha, alloc, toNatMax, toNatU64, toNat0, hmax, hM, hroom0, revertData,
        byteArray_readWithPadding_zero]
    · obtain ⟨a, b, rfl, hap, hbp, hspec⟩ := hr
      right; left
      refine ⟨_, hspec, ?_⟩
      simp [recv0_arm0, hin, ha, checkIndex, alloc, zeroMem, mstore, returnData, toNatMax, toNatU64,
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

theorem runtime_eq (I : Env) (w : World) : runtime.exec I w = recv0_arm0_entry.exec I w := by
  by_cases h : (UInt256.ofNat I.calldata.size).toNat < 4 <;> simp [runtime, h, selector_exec]

/-- Without call value the entry ends as the arm does. -/
theorem entry_runtime_none (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩)
    (h : recv0_arm0.exec I w.reserved = none) : (entry runtime).exec I w = none := by
  simp only [entry, M.exec_bind, exec_reserve, runtime_eq, recv0_arm0_entry, exec_nonPayable,
    if_pos hv, h]

theorem entry_runtime_error (I : Env) (w : World) (hv : I.weiValue = ⟨0⟩) {f : Exit World}
    (h : recv0_arm0.exec I w.reserved = some (.error f)) :
    (entry runtime).exec I w = some (.error f) := by
  apply entry_exec
  simp only [runtime_eq, recv0_arm0_entry, M.exec_bind, exec_nonPayable, if_pos hv, h]

/-- **The contract `Bn254Add` is ECADD.**  On call data `d` shorter than `2 ^ 64` bytes, with
    room in memory for the input and the 64-byte output, and no call value, the exported runtime
    entry diverges, stops with the 64 bytes `Spec.add` gives of the four words of `d`, or reverts
    with no data where `Spec.add` gives none; memory is all a successful run changes. -/
theorem feBn254AddContractCorrect (I : ExecutionEnv) (w : World) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    let d := I.calldata
    let r := BN254.Spec.add (BN254.Spec.word d 0) (BN254.Spec.word d 1) (BN254.Spec.word d 2)
      (BN254.Spec.word d 3)
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

/-- **The contract and the precompile.**  With the 150 gas ECADD charges, where the contract
    stops it returns the precompile's output and the precompile keeps the account map, and where
    it reverts the precompile fails. -/
theorem precompile_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (w : World) (hg : 150 ≤ g.toNat) (hfits : CalldataFits I)
    (hmem : w.memory.size + I.calldata.size + 64 < UInt256.size) (hv : I.weiValue = ⟨0⟩) :
    (entry runtime).exec I w = none ∨
      (∃ memory, (entry runtime).exec I w =
          some (.error (.stop (Ξ_BN_ADD σ g A I).2.2.2 { w with memory := memory })) ∧
        (Ξ_BN_ADD σ g A I).1 = σ) ∨
      ((entry runtime).exec I w = some (.error (.revert ByteArray.empty)) ∧
        Ξ_BN_ADD σ g A I = (∅, ⟨0⟩, A, .empty)) := by
  rw [Ξ_BN_ADD_eq, if_neg (by omega)]
  rcases feBn254AddContractCorrect I w hfits hmem hv with h | ⟨o, ho, memory, h⟩ | ⟨ho, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨memory, by simp only [ho]; exact h, by simp only [ho]⟩)
  · exact Or.inr (Or.inr ⟨h, by simp only [ho]⟩)

/-- With call value the entry reverts with no data: the fallback is not payable. -/
theorem runtime_value (I : ExecutionEnv) (w : World) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_eq, recv0_arm0_entry, M.exec_bind, exec_nonPayable, if_neg hv]

end FeProofs.Bn254Add
