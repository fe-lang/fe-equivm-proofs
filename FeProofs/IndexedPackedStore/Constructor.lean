import FeProofs.IndexedPackedStore.Common
import FeProofs.IndexedPackedStore.CreationBlocks_001
import FeProofs.Common.Constructor

/-!
# FeIndexedPackedStore constructor correctness

Creation-code equivalence: the non-payable guard, then `CODECOPY` of the 422-byte runtime and its
`RETURN`, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

/-- The initcode's `CODECOPY(0, 20, 422)` into empty memory reads back as the runtime code. -/
theorem feIndexedPackedStoreCreation_runtime_copy :
    (feIndexedPackedStoreCreationBytecode.write (UInt256.ofNat 20).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 422).toNat).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 422).toNat = feIndexedPackedStoreBytecode := by
  native_decide

theorem feIndexedPackedStoreCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feIndexedPackedStoreCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret feIndexedPackedStoreCreationBytecode g (initState σ σ₀ g A I) σ feIndexedPackedStoreBytecode := by
  have hcode' : I.code = feIndexedPackedStoreCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feIndexedPackedStoreCreationBlocks.feIndexedPackedStoreCreation_block_0_taken (by simp)
    (by rw [hwv]; decide) (by jump_dest) rd0
  have rret := feIndexedPackedStoreCreationBlocks.feIndexedPackedStoreCreation_block_8 (by simp) rd1
  rw [ByteArray.append_empty, feIndexedPackedStoreCreation_runtime_copy] at rret
  exact rret

theorem feIndexedPackedStoreCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feIndexedPackedStoreCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feIndexedPackedStoreCreationBytecode g (initState σ σ₀ g A I) := by
  have hcode' : I.code = feIndexedPackedStoreCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feIndexedPackedStoreCreationBlocks.feIndexedPackedStoreCreation_block_0_fallthrough (by simp)
    (isZero_eq_zero_of_ne hwv) rd0
  have rrev := feIndexedPackedStoreCreationBlocks.feIndexedPackedStoreCreation_block_5 (by simp) rd1
  rw [ByteArray.append_empty] at rrev
  exact rrev

theorem feIndexedPackedStoreConstructorCorrect :
    typedConstructorRefinement config feIndexedPackedStoreCreationBytecode contract
      (fun _ => feIndexedPackedStoreBytecode) :=
  FeProofs.nonpayableEmptyConstructorCorrect rfl rfl rfl
    feIndexedPackedStoreCtorRet feIndexedPackedStoreCtorRev

end FeProofs.IndexedPackedStore
