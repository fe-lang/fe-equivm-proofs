import FeProofs.ScalarStore.Dispatch
import FeProofs.ScalarStore.Storage
import FeProofs.Common.Basic

/-!
# FeScalarStore `get()`

Arm entry pc 67: the call-value check, then `MSTORE(0, SLOAD(0))` and a 32-byte `RETURN`
at pc 72.  There are no arguments, so no head check.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ScalarStore

set_option maxRecDepth 2000000

theorem feScalarStoreGetDecode {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (getTransition.params.map Param.name)
      (transitionSignature getTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `get()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem feScalarStoreGetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 1) rfl hsel
  have h0 : ¬ selIs I (feScalarStoreSelBytes 0) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd := feScalarStoreDispatch_get h0 hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachGetBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feScalarStoreBlocks.feScalarStore_block_67_fallthrough (by simp) hwv rd
    have rret := feScalarStoreBlocks.feScalarStore_block_72 (by simp) rd1
    have hout : ((σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0
          ByteArray.empty (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat
          (UInt256.ofNat 32).toNat = (solcSlotWordAt ⟨0⟩ σ I).toByteArray :=
      toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)
    rw [hout] at rret
    have hread := stored_read (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (by simp)
    rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
    exact rret.reEquivExecution hcode hd (feScalarStoreGetDecode hsz)
      (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
      (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWordAt ⟨0⟩ σ I)))
  · have rd1 := feScalarStoreBlocks.feScalarStore_block_67_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode (feScalarStoreBlocks.feScalarStore_block_42 (by simp) rd1)
      hd fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ScalarStore
