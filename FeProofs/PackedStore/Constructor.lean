import FeProofs.PackedStore.Common
import FeProofs.PackedStore.CreationBlocks_001
import FeProofs.Common.Constructor

/-!
# FePackedStore constructor correctness

Creation-code equivalence: the non-payable guard, then `CODECOPY` of the 489-byte runtime and its
`RETURN`, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.PackedStore

/-- The initcode's `CODECOPY(0, 20, 489)` into empty memory reads back as the runtime code. -/
theorem fePackedStoreCreation_runtime_copy :
    (fePackedStoreCreationBytecode.write (UInt256.ofNat 20).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 489).toNat).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 489).toNat = fePackedStoreBytecode := by
  native_decide

theorem fePackedStoreCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = fePackedStoreCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret fePackedStoreCreationBytecode g (initState σ σ₀ g A I) σ fePackedStoreBytecode := by
  have hcode' : I.code = fePackedStoreCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := fePackedStoreCreationBlocks.fePackedStoreCreation_block_0_taken (by simp)
    (by rw [hwv]; decide) (by jump_dest) rd0
  have rret := fePackedStoreCreationBlocks.fePackedStoreCreation_block_8 (by simp) rd1
  rw [ByteArray.append_empty, fePackedStoreCreation_runtime_copy] at rret
  exact rret

theorem fePackedStoreCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = fePackedStoreCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev fePackedStoreCreationBytecode g (initState σ σ₀ g A I) := by
  have hcode' : I.code = fePackedStoreCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := fePackedStoreCreationBlocks.fePackedStoreCreation_block_0_fallthrough (by simp)
    (isZero_eq_zero_of_ne hwv) rd0
  have rrev := fePackedStoreCreationBlocks.fePackedStoreCreation_block_5 (by simp) rd1
  rw [ByteArray.append_empty] at rrev
  exact rrev

theorem fePackedStoreConstructorCorrect :
    typedConstructorRefinement config fePackedStoreCreationBytecode contract
      (fun _ => fePackedStoreBytecode) :=
  FeProofs.nonpayableEmptyConstructorCorrect rfl rfl rfl
    fePackedStoreCtorRet fePackedStoreCtorRev

end FeProofs.PackedStore
