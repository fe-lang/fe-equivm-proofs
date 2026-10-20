import FeProofs.NarrowAbi.Common
import FeProofs.NarrowAbi.CreationBlocks_001
import FeProofs.Common.Constructor

/-!
# FeNarrowAbi constructor correctness

Creation-code equivalence: the non-payable guard, then `CODECOPY` of the 276-byte runtime and its
`RETURN`, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

/-- The initcode's `CODECOPY(0, 20, 276)` into empty memory reads back as the runtime code. -/
theorem feNarrowAbiCreation_runtime_copy :
    (feNarrowAbiCreationBytecode.write (UInt256.ofNat 20).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 276).toNat).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 276).toNat = feNarrowAbiBytecode := by
  native_decide

theorem feNarrowAbiCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feNarrowAbiCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret feNarrowAbiCreationBytecode g (initState σ σ₀ g A I) σ feNarrowAbiBytecode := by
  have hcode' : I.code = feNarrowAbiCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  rd_run rd using [hwv]
  rwa [ByteArray.append_empty, feNarrowAbiCreation_runtime_copy] at rd

theorem feNarrowAbiCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = feNarrowAbiCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feNarrowAbiCreationBytecode g (initState σ σ₀ g A I) := by
  have hcode' : I.code = feNarrowAbiCreationBytecode ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact hcode
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  rd_run rd using [isZero_eq_zero_of_ne hwv]
  rwa [ByteArray.append_empty] at rd

theorem feNarrowAbiConstructorCorrect :
    typedConstructorRefinement config feNarrowAbiCreationBytecode contract
      (fun _ => feNarrowAbiBytecode) :=
  FeProofs.nonpayableEmptyConstructorCorrect rfl rfl rfl
    feNarrowAbiCtorRet feNarrowAbiCtorRev

end FeProofs.NarrowAbi
