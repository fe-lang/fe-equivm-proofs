import FeProofs.ERC20.Common
import FeProofs.ERC20.CreationBlocks_001
import FeProofs.ERC20.CreationBlocks_002
import FeProofs.Common.CtorUInt256
import Reasoning.VyperCalls

/-!
# FeERC20 constructor trace

The initcode rejects call value, requires at least 969 bytes of code (the initcode alone), takes
`max(mload(0x40), 0x60) = 0x60` as its scratch pointer, copies the argument bytes there and
requires at least one word of them.  It then writes the caller and slot 0 at `0x60`/`0x80`,
stores the argument at their `KECCAK256` (`balanceOf[msg.sender]`) and in slot 2, emits the
`Transfer` log and returns the 838-byte runtime.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs.ERC20

/-- The ABI-encoded constructor argument. -/
abbrev ctorTail (w : UInt256) : ByteArray := (EVM.Word.toBytesBE w).toByteArray

theorem feERC20Creation_size : feERC20CreationBytecode.size = 969 := by native_decide

theorem ctorCode_size (w : UInt256) : (feERC20CreationBytecode ++ ctorTail w).size = 1001 := by
  rw [ByteArray.size_append, feERC20Creation_size, word_toBytesBE_toByteArray_size]

/-- Memory after `CODECOPY(0x60, 969, 32)` into empty memory. -/
abbrev ctorArgMem (w : UInt256) : ByteArray :=
  (feERC20CreationBytecode ++ ctorTail w).write (UInt256.ofNat 969).toNat ByteArray.empty
    (UInt256.ofNat 96).toNat (UInt256.sub (UInt256.ofNat 1001) (UInt256.ofNat 969)).toNat

theorem ctorArgMem_eq (w : UInt256) :
    ctorArgMem w = ByteArray.zeroes 96 ++ ctorTail w := by
  unfold ctorArgMem
  rw [show (UInt256.ofNat 969).toNat = 969 from rfl, show (UInt256.ofNat 96).toNat = 96 from rfl,
    show (UInt256.sub (UInt256.ofNat 1001) (UInt256.ofNat 969)).toNat = 32 by decide,
    write_from_gap_eq _ _ 969 96 32 (by decide) (by have := ctorCode_size w; omega)
      (by simp) (by simp only [ByteArray.size_empty]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size),
    extract_append_right' _ _ 969 (969 + 32) feERC20Creation_size.symm
      (by rw [feERC20Creation_size, word_toBytesBE_toByteArray_size])]
  simp [ByteArray.empty_append]

theorem ctorArgMem_load (w : UInt256) : memLoad (UInt256.ofNat 96) (ctorArgMem w) = w := by
  have hsz : (ctorArgMem w).size = 128 := by
    rw [ctorArgMem_eq, ByteArray.size_append, ByteArray_zeroes_size, word_toBytesBE_toByteArray_size]
  refine memLoad_of_read _ 96 w (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 96 (by omega), ctorArgMem_eq,
    extract_append_right' _ _ 96 (96 + 32) (by rw [ByteArray_zeroes_size])
      (by rw [ByteArray_zeroes_size, word_toBytesBE_toByteArray_size]),
    ctorTail, word_toBytesBE_toByteArray_eq_toByteArray]

/-- The `KECCAK256(0x60, 0x40)` input memory: the caller word at `0x60`, slot 0 at `0x80`. -/
abbrev ctorKeyMem (w : UInt256) (caller : AccountAddress) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 ((UInt256.ofNat caller.val).toByteArray.write 0 (ctorArgMem w)
    (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32

theorem ctorKeyMem_read (w : UInt256) (c : AccountAddress) :
    (ctorKeyMem w c).readWithPadding 96 64 =
      (UInt256.ofNat c.val).toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
  have hA : (ctorArgMem w).size = 128 := by
    rw [ctorArgMem_eq, ByteArray.size_append, ByteArray_zeroes_size, word_toBytesBE_toByteArray_size]
  have hk := toByteArray_size (UInt256.ofNat c.val)
  have hz := toByteArray_size (⟨0⟩ : UInt256)
  have h1 : (UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32 =
      (ctorArgMem w).extract 0 96 ++ (UInt256.ofNat c.val).toByteArray ++
        (ctorArgMem w).extract 128 (ctorArgMem w).size := by
    rw [write32_eq _ _ 96 (by omega) (by omega), toByteArray_extract_all]
  have h1s : ((UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32).size = 128 := by
    rw [h1]; simp only [ByteArray.size_append, ByteArray.size_extract, hA, hk]; omega
  have e : ((UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32).extract 0 128 =
      (UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32 := by
    rw [← h1s, ByteArray.extract_zero_size]
  have h2 : (⟨0⟩ : UInt256).toByteArray.write 0
      ((UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32) 128 32 =
      (UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32 ++ (⟨0⟩ : UInt256).toByteArray ++
        ((UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32).extract (128 + 32)
          ((UInt256.ofNat c.val).toByteArray.write 0 (ctorArgMem w) 96 32).size := by
    rw [write32_eq _ _ 128 (by omega) (by omega), toByteArray_extract_all, e]
  unfold ctorKeyMem
  rw [show (UInt256.ofNat 96).toNat = 96 from rfl, show (UInt256.ofNat 128).toNat = 128 from rfl, h2,
    readWithPadding_eq_extract' _ 96 64 (by decide) (by decide)
      (by simp only [ByteArray.size_append, ByteArray.size_extract, h1s, hz]; omega),
    extract_append_left _ _ _ _ (by simp only [ByteArray.size_append, h1s, hz]; omega),
    extract_append_span _ _ 96 160 (by omega) (by omega), h1s,
    show 160 - 128 = 32 from rfl, toByteArray_extract_all, h1,
    extract_append_left _ _ _ _ (by simp only [ByteArray.size_append, ByteArray.size_extract, hA, hk]; omega),
    extract_append_right' _ _ 96 128 (by simp only [ByteArray.size_extract, hA]; omega)
      (by simp only [ByteArray.size_extract, hA, hk]; omega)]

/-- The constructor's store slot is `balanceOf[caller]` under the Solidity layout. -/
theorem ctorKey_slot (w : UInt256) (c : AccountAddress) :
    keccakWord (UInt256.ofNat 96) (UInt256.ofNat 64) (ctorKeyMem w c) =
      solcMappingSlot ⟨0⟩ (UInt256.ofNat c.val) := by
  unfold keccakWord solcMappingSlot
  rw [show (UInt256.ofNat 96).toNat = 96 from rfl, show (UInt256.ofNat 64).toNat = 64 from rfl,
    ctorKeyMem_read]
  exact mappingSlot_single _ _

theorem ctorRuntime_read (w : UInt256) (mem : ByteArray) :
    ((feERC20CreationBytecode ++ ctorTail w).write (UInt256.ofNat 131).toNat mem
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 838).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 838).toNat = feERC20Bytecode := by
  rw [show (UInt256.ofNat 131).toNat = 131 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 838).toNat = 838 from rfl,
    write0_read_back_from_gen _ _ 131 838 (by decide) (by have := ctorCode_size w; omega) (by decide),
    extract_append_left _ _ _ _ (by rw [feERC20Creation_size])]
  native_decide

set_option maxHeartbeats 1000000 in
/-- Zero call value: the initcode stores the argument at `balanceOf[caller]` and in slot 2 and
    returns the runtime. -/
theorem feERC20CtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (w : UInt256) (hcode : I.code = feERC20CreationBytecode ++ ctorTail w)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    RDret (feERC20CreationBytecode ++ ctorTail w) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ
        (keccakWord (UInt256.ofNat 96) (UInt256.ofNat 64) (ctorKeyMem w I.source)) w)
        (UInt256.ofNat 2) w) feERC20Bytecode := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := feERC20CreationBlocks.feERC20Creation_block_0_taken (by simp)
    (by rw [hwv]; decide) (by jump_dest) rd0
  have rd2 := feERC20CreationBlocks.feERC20Creation_block_9_fallthrough (by simp)
    (by rw [ctorCode_size]; decide) rd1
  have rd3 := feERC20CreationBlocks.feERC20Creation_block_20_fallthrough (by simp)
    (by native_decide) rd2
  have rd4 := feERC20CreationBlocks.feERC20Creation_block_33 (by simp) rd3
  have rd5 := feERC20CreationBlocks.feERC20Creation_block_36_fallthrough (by simp)
    (by rw [ctorCode_size]; decide) rd4
  have rret := feERC20CreationBlocks.feERC20Creation_block_48 (by simp) hperm rd5
  simp only [feERC20CreationBlocks.feERC20Creation_block_36_fallthrough_memory,
    ctorCode_size] at rret
  rw [ctorArgMem_load, ctorRuntime_read] at rret
  exact rret

theorem feERC20CtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {tail : ByteArray} (hcode : I.code = feERC20CreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (feERC20CreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := feERC20CreationBlocks.feERC20Creation_block_0_fallthrough (by simp)
    (isZero_eq_zero_of_ne hwv) rd0
  exact feERC20CreationBlocks.feERC20Creation_block_5 (by simp) rd1

end FeProofs.ERC20
