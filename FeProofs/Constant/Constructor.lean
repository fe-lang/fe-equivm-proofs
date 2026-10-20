import FeProofs.Constant.Common
import FeProofs.Constant.CreationBlocks_001
import FeProofs.Common.Constructor

/-!
# FeConstant constructor correctness

Creation-code equivalence: the non-payable guard, then `CODECOPY` of the 45-byte runtime and its
`RETURN`, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Constant

/-- The initcode's `CODECOPY(0, 19, 45)` into empty memory reads back as the runtime code. -/
theorem feConstantCreation_runtime_copy :
    (feConstantCreationBytecode.write (UInt256.ofNat 19).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 45).toNat).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 45).toNat = feConstantBytecode := by
  native_decide

theorem feConstantCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feConstantCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret feConstantCreationBytecode g (initState σ σ₀ g A I) σ feConstantBytecode := by
  have hcode' : I.code = feConstantCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feConstantCreationBlocks.feConstantCreation_block_0_taken (by simp)
    (by rw [hwv]; decide) (by jump_dest) rd0
  have rret := feConstantCreationBlocks.feConstantCreation_block_8 (by simp) rd1
  rw [ByteArray.append_empty, feConstantCreation_runtime_copy] at rret
  exact rret

theorem feConstantCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feConstantCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feConstantCreationBytecode g (initState σ σ₀ g A I) := by
  have hcode' : I.code = feConstantCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  have rd1 := feConstantCreationBlocks.feConstantCreation_block_0_fallthrough (by simp)
    (isZero_eq_zero_of_ne hwv) rd0
  have rrev := feConstantCreationBlocks.feConstantCreation_block_5 (by simp) rd1
  rw [ByteArray.append_empty] at rrev
  exact rrev

theorem feConstantConstructorCorrect :
    typedConstructorRefinement config feConstantCreationBytecode contract
      (fun _ => feConstantBytecode) :=
  FeProofs.Common.nonpayableEmptyConstructorCorrect rfl rfl rfl
    feConstantCtorRet feConstantCtorRev

end FeProofs.Constant
