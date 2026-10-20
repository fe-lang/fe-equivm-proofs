import FeProofs.ScalarStore.Common

/-!
# FeScalarStore storage facts

`stored` is a full-word `uint256` in slot 0 under the generated Solidity layout.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ScalarStore

abbrev storedRef : StorageRef := { base := "stored" }

theorem storedRef_eval {stele : Frame} {evm : EVM.State} :
    evalStorageRef config stele evm storedRef = .ok { base := "stored", steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem stored_read {L : Store} {evm : EVM.State} (hL : L.get? "stored" = none) :
    evalExpr? config { contract := contract, locals := L } evm (.storage storedRef) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) :=
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩)) (loc := uint256Loc ⟨0⟩) hL storedRef_eval
    (by show storageTypeAt? contract.storage _ = _; decide) rfl rfl (storageLocLoad_uint256 evm ⟨0⟩)

theorem stored_write {L : Store} {evm : EVM.State} (hL : L.get? "stored" = none) (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage storedRef
        (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ w) :=
  assignStorageRef_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := uint256Loc ⟨0⟩) hL storedRef_eval
    (by show storageTypeAt? contract.storage _ = _; decide) rfl rfl (Or.inl ⟨_, rfl⟩)
    (storageLocStore_uint256 evm ⟨0⟩ w)

end FeProofs.ScalarStore
