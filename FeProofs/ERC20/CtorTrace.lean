import FeProofs.ERC20.Common
import FeProofs.ERC20.CreationBlocks_001
import FeProofs.ERC20.CreationBlocks_002
import FeProofs.Common.CtorUInt256
import FeProofs.Common.Storage
import Reasoning.VyperCalls

/-!
# FeERC20 constructor trace

The initcode stores the free-memory pointer `0xa0` at `0x40`, rejects call value, requires at least
987 bytes of code (the initcode alone), copies the argument bytes to `0xa0` and requires at least
one word of them.  It then writes the caller and slot 0 at `0x60`/`0x80`, stores the argument at
their `KECCAK256` (`balanceOf[msg.sender]`) and in slot 2, emits the `Transfer` log and returns
the 863-byte runtime.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs.ERC20

/-- The ABI-encoded constructor argument. -/
abbrev ctorTail (w : UInt256) : ByteArray := (EVM.Word.toBytesBE w).toByteArray

theorem feERC20Creation_size : feERC20CreationBytecode.size = 987 := by native_decide

theorem ctorCode_size (w : UInt256) : (feERC20CreationBytecode ++ ctorTail w).size = 1019 := by
  rw [ByteArray.size_append, feERC20Creation_size, word_toBytesBE_toByteArray_size]

/-- Memory after `MSTORE(0x40, 0xa0)`. -/
abbrev ctorPtrMem : ByteArray :=
  (UInt256.ofNat 160).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32

theorem ctorPtrMem_size : ctorPtrMem.size = 96 :=
  toByteArray_write32_size_of_ge _ _ 64 0 96 rfl (Nat.zero_le _)
    (Nat.lt_of_lt_of_le (by decide) USize.le_size) rfl

/-- Memory after `MSTORE(0x40, 0xa0)` and `CODECOPY(0xa0, 987, 32)`. -/
abbrev ctorArgMem (w : UInt256) : ByteArray :=
  (feERC20CreationBytecode ++ ctorTail w).write (UInt256.ofNat 987).toNat ctorPtrMem
    (UInt256.ofNat 160).toNat (UInt256.sub (UInt256.ofNat 1019) (UInt256.ofNat 987)).toNat

theorem ctorArgMem_eq (w : UInt256) :
    ctorArgMem w = ctorPtrMem ++ ByteArray.zeroes 64 ++ ctorTail w := by
  unfold ctorArgMem
  rw [show (UInt256.ofNat 987).toNat = 987 from rfl, show (UInt256.ofNat 160).toNat = 160 from rfl,
    show (UInt256.sub (UInt256.ofNat 1019) (UInt256.ofNat 987)).toNat = 32 by decide,
    write_from_gap_eq _ _ 987 160 32 (by decide) (by have := ctorCode_size w; omega)
      (by rw [ctorPtrMem_size]; omega)
      (by rw [ctorPtrMem_size]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size),
    extract_append_right' _ _ 987 (987 + 32) feERC20Creation_size.symm
      (by rw [feERC20Creation_size, word_toBytesBE_toByteArray_size]), ctorPtrMem_size]

theorem ctorArgMem_load (w : UInt256) : memLoad (UInt256.ofNat 160) (ctorArgMem w) = w := by
  have hpre : (ctorPtrMem ++ ByteArray.zeroes 64).size = 160 := by
    rw [ByteArray.size_append, ctorPtrMem_size, ByteArray_zeroes_size]
  have hsz : (ctorArgMem w).size = 192 := by
    rw [ctorArgMem_eq, ByteArray.size_append, hpre, word_toBytesBE_toByteArray_size]
  refine memLoad_of_read _ 160 w (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 160 (by omega), ctorArgMem_eq,
    extract_append_right' _ _ 160 (160 + 32) hpre.symm
      (by rw [hpre, word_toBytesBE_toByteArray_size]),
    ctorTail, word_toBytesBE_toByteArray_eq_toByteArray]

/-- The `KECCAK256(0x60, 0x40)` input memory: the caller word at `0x60`, slot 0 at `0x80`. -/
abbrev ctorKeyMem (w : UInt256) (caller : AccountAddress) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.ofNat caller.val).toByteArray.write 0 (ctorArgMem w)
    (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32

/-- The constructor's store slot is `balanceOf[caller]` under the Solidity layout. -/
theorem ctorKey_slot (w : UInt256) (c : AccountAddress) :
    keccakWord (UInt256.ofNat 96) (UInt256.ofNat 64) (ctorKeyMem w c) =
      solcMappingSlot ⟨0⟩ (UInt256.ofNat c.val) :=
  keccakWord_mapSlotAtWord _ _ _ 96 128 rfl (by norm_num)

theorem ctorRuntime_read (w : UInt256) (mem : ByteArray) :
    ((feERC20CreationBytecode ++ ctorTail w).write (UInt256.ofNat 124).toNat mem
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 863).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 863).toNat = feERC20Bytecode := by
  rw [show (UInt256.ofNat 124).toNat = 124 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 863).toNat = 863 from rfl,
    write0_read_back_from_gen _ _ 124 863 (by decide) (by have := ctorCode_size w; omega) (by decide),
    extract_append_left _ _ _ _ (by rw [feERC20Creation_size])]
  native_decide

/-- Zero call value: the initcode stores the argument at `balanceOf[caller]` and in slot 2 and
    returns the runtime. -/
theorem feERC20CtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (w : UInt256) (hcode : I.code = feERC20CreationBytecode ++ ctorTail w)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    RDret (feERC20CreationBytecode ++ ctorTail w) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ
        (keccakWord (UInt256.ofNat 96) (UInt256.ofNat 64) (ctorKeyMem w I.source)) w)
        (UInt256.ofNat 2) w) feERC20Bytecode := by
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd using [hwv, ctorCode_size w, (by native_decide)]
  simp only [ctorCode_size] at rd
  rw [ctorArgMem_load, ctorRuntime_read] at rd
  exact rd

theorem feERC20CtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {tail : ByteArray} (hcode : I.code = feERC20CreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (feERC20CreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd using [isZero_eq_zero_of_ne hwv]
  exact rd

end FeProofs.ERC20
