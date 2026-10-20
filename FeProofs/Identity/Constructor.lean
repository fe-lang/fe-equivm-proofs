import FeProofs.Identity.Common
import FeProofs.Identity.CreationBlocks_001
import FeProofs.Common.Constructor

/-!
# FeIdentity constructor correctness

Creation-code equivalence: the non-payable guard, then `CODECOPY` of the 58-byte runtime and its
`RETURN`, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Identity

/-- The initcode's `CODECOPY(0, 19, 58)` into empty memory reads back as the runtime code. -/
theorem feIdentityCreation_runtime_copy :
    (feIdentityCreationBytecode.write (UInt256.ofNat 19).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 58).toNat).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 58).toNat = feIdentityBytecode := by
  native_decide

theorem feIdentityCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feIdentityCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret feIdentityCreationBytecode g (initState σ σ₀ g A I) σ feIdentityBytecode := by
  have hcode' : I.code = feIdentityCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feIdentityCreationBlocks.feIdentityCreation_block_0_taken (by simp)
    (by rw [hwv]; decide) (by jump_dest) rd0
  have rret := feIdentityCreationBlocks.feIdentityCreation_block_8 (by simp) rd1
  rw [ByteArray.append_empty, feIdentityCreation_runtime_copy] at rret
  exact rret

theorem feIdentityCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feIdentityCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feIdentityCreationBytecode g (initState σ σ₀ g A I) := by
  have hcode' : I.code = feIdentityCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feIdentityCreationBlocks.feIdentityCreation_block_0_fallthrough (by simp)
    (isZero_eq_zero_of_ne hwv) rd0
  have rrev := feIdentityCreationBlocks.feIdentityCreation_block_5 (by simp) rd1
  rw [ByteArray.append_empty] at rrev
  exact rrev

theorem feIdentityConstructorCorrect :
    typedConstructorRefinement config feIdentityCreationBytecode contract
      (fun _ => feIdentityBytecode) :=
  FeProofs.Common.nonpayableEmptyConstructorCorrect rfl rfl rfl
    feIdentityCtorRet feIdentityCtorRev

end FeProofs.Identity
