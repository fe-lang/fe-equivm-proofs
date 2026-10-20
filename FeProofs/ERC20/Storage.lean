import FeProofs.ERC20.Common

/-!
# FeERC20 storage facts

`totalSupply` is a full-word `uint256` in slot 2 under the generated Solidity layout.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

abbrev totalSupplyRef : StorageRef := { base := "totalSupply" }

theorem totalSupplyRef_eval {stele : Frame} {evm : EVM.State} :
    evalStorageRef config stele evm totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem totalSupply_read {L : Store} {evm : EVM.State} (hL : L.get? "totalSupply" = none) :
    evalExpr? config { contract := contract, locals := L } evm (.storage totalSupplyRef) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) :=
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩)) (loc := uint256Loc ⟨2⟩) hL totalSupplyRef_eval
    (by show storageTypeAt? contract.storage _ = _; decide) rfl rfl (storageLocLoad_uint256 evm ⟨2⟩)

end FeProofs.ERC20
