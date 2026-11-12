import FeProofs.CodeScalar.Dispatch
import FeProofs.CodeScalar.CreationBlocks_001
import Reasoning.VyperDispatch

/-!
# FeCodeScalar constructor trace

The initcode stores the free-memory pointer `0x60` at `0x40`, rejects call value, requires at
least 162 bytes of code (the initcode alone), copies the argument bytes to `0x60` and requires
a word of them.  It moves the free pointer to `0x80`, stores the argument word at `0x60`, the
buffer of the immutable fields, and that address at `0`.  Then it copies the 55-byte runtime
code to `0x80` and the buffer after it, and returns the 87 bytes: the runtime code followed by
the argument word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls
  Reasoning.VyperDispatch

namespace FeProofs.CodeScalar

set_option maxRecDepth 2000000

theorem feCodeScalarCreation_size : feCodeScalarCreationBytecode.size = 162 := by native_decide

theorem ctorCode_size (w : UInt256) :
    (feCodeScalarCreationBytecode ++ w.toByteArray).size = 194 := by
  rw [ByteArray.size_append, feCodeScalarCreation_size, toByteArray_size]

/-- Memory after `MSTORE(0x40, 0x60)`. -/
abbrev ctorPtrMem : ByteArray :=
  (UInt256.ofNat 96).toByteArray.write 0 ByteArray.empty 64 32

theorem ctorPtrMem_size : ctorPtrMem.size = 96 :=
  toByteArray_write32_size_of_ge _ _ 64 0 96 rfl (Nat.zero_le _)
    (Nat.lt_of_lt_of_le (by decide) USize.le_size) rfl

/-- Memory after the argument bytes are copied to `0x60`. -/
abbrev ctorArgMem (w : UInt256) : ByteArray :=
  (feCodeScalarCreationBytecode ++ w.toByteArray).write 162 ctorPtrMem 96
    ((UInt256.ofNat 194).sub (UInt256.ofNat 162)).toNat

theorem ctorArgMem_eq (w : UInt256) :
    ctorArgMem w = ctorPtrMem ++ ByteArray.zeroes 0 ++ w.toByteArray := by
  unfold ctorArgMem
  rw [show ((UInt256.ofNat 194).sub (UInt256.ofNat 162)).toNat = 32 by decide,
    write_from_gap_eq _ _ 162 96 32 (by decide) (by have := ctorCode_size w; omega)
      (by rw [ctorPtrMem_size])
      (by rw [ctorPtrMem_size]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size),
    extract_append_right' _ _ 162 (162 + 32) feCodeScalarCreation_size.symm
      (by rw [feCodeScalarCreation_size, toByteArray_size]), ctorPtrMem_size]

theorem ctorArgMem_size (w : UInt256) : (ctorArgMem w).size = 128 := by
  rw [ctorArgMem_eq, ByteArray.size_append, ByteArray.size_append, ctorPtrMem_size,
    ByteArray_zeroes_size, toByteArray_size]

theorem ctorArgMem_load (w : UInt256) : memLoad (UInt256.ofNat 96) (ctorArgMem w) = w := by
  have hpre : (ctorPtrMem ++ ByteArray.zeroes 0).size = 96 := by
    rw [ByteArray.size_append, ctorPtrMem_size, ByteArray_zeroes_size]
  have hsz := ctorArgMem_size w
  refine memLoad_of_read _ 96 w (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 96 (by omega), ctorArgMem_eq,
    extract_append_right' _ _ 96 (96 + 32) hpre.symm (by rw [hpre, toByteArray_size])]

/-- Memory after `MSTORE(0x40, 0x80)`. -/
abbrev ctorFreeMem (w : UInt256) : ByteArray :=
  (UInt256.ofNat 128).toByteArray.write 0 (ctorArgMem w) 64 32

theorem ctorFreeMem_size (w : UInt256) : (ctorFreeMem w).size = 128 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by have := ctorArgMem_size w; omega), ctorArgMem_size]

/-- Memory after the argument word is stored in the buffer at `0x60`. -/
abbrev ctorWordMem (w : UInt256) : ByteArray :=
  w.toByteArray.write 0 (ctorFreeMem w) 96 32

theorem ctorWordMem_size (w : UInt256) : (ctorWordMem w).size = 128 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by have := ctorFreeMem_size w; omega), ctorFreeMem_size]

/-- Memory after the buffer's address is stored at `0`: what the copies of the returned code
    start from. -/
abbrev ctorMem (w : UInt256) : ByteArray :=
  (UInt256.ofNat 96).toByteArray.write 0 (ctorWordMem w) 0 32

theorem ctorMem_size (w : UInt256) : (ctorMem w).size = 128 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by have := ctorWordMem_size w; omega), ctorWordMem_size]

/-- The free pointer is `0x80`. -/
theorem ctorMem_ptr (w : UInt256) : memLoad (UInt256.ofNat 64) (ctorMem w) = UInt256.ofNat 128 := by
  rw [memLoad_above_write _ _ 0 64 (by rw [toByteArray_size]) (Nat.zero_le _) (by decide)
      (by have := ctorWordMem_size w; omega) (by decide),
    memLoad_below_write _ _ 96 64 (by have := ctorFreeMem_size w; omega) (by decide)
      (by rw [ctorFreeMem_size]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size) (by decide),
    memLoad_write_back _ _ 64 (by decide)
      (by rw [ctorArgMem_size]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size)]

/-- The buffer holds the argument word. -/
theorem ctorMem_word (w : UInt256) : (ctorMem w).extract 96 (96 + 32) = w.toByteArray := by
  rw [← readWithPadding_eq_extract _ 96 (by have := ctorMem_size w; omega),
    write32_read_above _ _ 0 96 (by rw [toByteArray_size]) (Nat.zero_le _) (by decide)
      (by have := ctorWordMem_size w; omega),
    toByteArray_write32_read_back _ _ 96 (by have := ctorFreeMem_size w; omega)]

/-- The runtime code as the initcode holds it. -/
theorem ctorRuntime (w : UInt256) :
    (feCodeScalarCreationBytecode ++ w.toByteArray).extract 107 (107 + 55) = feCodeScalarBytecode := by
  rw [extract_append_left _ _ _ _ (by rw [feCodeScalarCreation_size])]
  native_decide

/-- The returned bytes: the runtime code, then the argument word. -/
theorem ctorOut (w : UInt256) :
    (((feCodeScalarCreationBytecode ++ w.toByteArray).write 107 (ctorMem w) 128 55).write 96
        ((feCodeScalarCreationBytecode ++ w.toByteArray).write 107 (ctorMem w) 128 55)
        183 32).readWithPadding 128 87
      = feCodeScalarBytecode ++ w.toByteArray := by
  have hcopy : (feCodeScalarCreationBytecode ++ w.toByteArray).write 107 (ctorMem w) 128 55
      = ctorMem w ++ feCodeScalarBytecode := by
    have h := write_at_end_eq_from (feCodeScalarCreationBytecode ++ w.toByteArray) (ctorMem w)
      107 55 (by decide) (by have := ctorCode_size w; omega)
    rwa [ctorMem_size, ctorRuntime] at h
  have hsize : (ctorMem w ++ feCodeScalarBytecode).size = 183 := by
    rw [ByteArray.size_append, ctorMem_size, feCodeScalarBytecode_size]
  rw [hcopy]
  have hword : (ctorMem w ++ feCodeScalarBytecode).write 96 (ctorMem w ++ feCodeScalarBytecode)
      183 32 = ctorMem w ++ feCodeScalarBytecode ++ w.toByteArray := by
    have h := write_at_end_eq_from (ctorMem w ++ feCodeScalarBytecode)
      (ctorMem w ++ feCodeScalarBytecode) 96 32 (by decide) (by omega)
    rwa [hsize, extract_append_left _ _ _ _ (by have := ctorMem_size w; omega), ctorMem_word] at h
  rw [hword, readWithPadding_eq_extract' _ 128 87 (by decide) (by decide)
      (by rw [ByteArray.size_append, hsize, toByteArray_size]),
    ByteArray.append_assoc,
    extract_append_right' _ _ 128 (128 + 87) (ctorMem_size w).symm
      (by rw [ctorMem_size, ByteArray.size_append, feCodeScalarBytecode_size, toByteArray_size])]

/-- Deployment with the argument word `w` and no call value returns the runtime code followed
    by `w`, and changes no account. -/
theorem feCodeScalarCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (w : UInt256) (hcode : I.code = feCodeScalarCreationBytecode ++ w.toByteArray)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (feCodeScalarCreationBytecode ++ w.toByteArray) g (initState σ σ₀ g A I) σ
      (feCodeScalarBytecode ++ w.toByteArray) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 using [hwv, ctorCode_size w, (by native_decide)]
  simp only [ctorCode_size] at rd0
  u256_lits at rd0
  rw [ctorArgMem_load, ctorMem_ptr] at rd0
  u256_lits at rd0
  rwa [ctorOut] at rd0

theorem feCodeScalarCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {tail : ByteArray} (hcode : I.code = feCodeScalarCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (feCodeScalarCreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 using [isZero_eq_zero_of_ne hwv]
  exact rd0

end FeProofs.CodeScalar
