import FeProofs.ERC20.Common
import FeProofs.Common.Glue
import FeProofs.Common.Storage

/-!
# FeERC20 mapping facts

`Common/Storage.lean`'s mapping lemmas for `balanceOf` (slot 0) and the map of maps `allowance`
(slot 1), for key expressions that evaluate to addresses.  FeERC20 hashes the 64-byte preimage in
scratch memory at `0x00` (`keccakWord_mapSlot`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The word at `balanceOf[key]` in the account map `σ`. -/
abbrev balanceWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : UInt256 :=
  solcSlotWord σ I (mapSlot key ⟨0⟩)

/-- `balanceOf[to]`. -/
abbrev balanceOfTo : StorageRef := { base := "balanceOf", steps := [.mindex (.var "to")] }

section
variable {L : Store} {evm : EVM.State} {e f : Expr} {a b : AccountAddress}

/-- `balanceOf[e]`, for a key `e` evaluating to the address `a`, reads the word at
`mapSlot a 0`. -/
theorem balanceOf_read (hL : L.get? "balanceOf" = none)
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.address a)) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "balanceOf", steps := [.mindex e] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address a)) ⟨0⟩)).toNat)) :=
  map_read (layout := solidityLayout! [contract.structs] [contract.storage]) rfl
    (fun _ => rfl) (fun _ => rfl) hL he

/-- Writing `w` to `balanceOf[e]` stores it at `mapSlot a 0`. -/
theorem balanceOf_assign (hL : L.get? "balanceOf" = none)
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.address a))
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage
        { base := "balanceOf", steps := [.mindex e] } (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner (mapSlot (keyValueToWord (.address a)) ⟨0⟩) w) :=
  map_assign (layout := solidityLayout! [contract.structs] [contract.storage]) rfl
    (fun _ => rfl) (fun _ => rfl) hL he w

/-- `allowance[e][f]`, for keys evaluating to the addresses `a` and `b`, reads the word at
`mapSlot b (mapSlot a 1)`. -/
theorem allowance_read (hL : L.get? "allowance" = none)
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.address a))
    (hf : evalExpr? config { contract := contract, locals := L } evm f = .ok (.address b)) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "allowance", steps := [.mindex e, .mindex f] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address b))
          (mapSlot (keyValueToWord (.address a)) ⟨1⟩))).toNat)) :=
  map2_read (layout := solidityLayout! [contract.structs] [contract.storage]) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hL he hf

/-- Writing `w` to `allowance[e][f]` stores it at `mapSlot b (mapSlot a 1)`. -/
theorem allowance_assign (hL : L.get? "allowance" = none)
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.address a))
    (hf : evalExpr? config { contract := contract, locals := L } evm f = .ok (.address b))
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage
        { base := "allowance", steps := [.mindex e, .mindex f] } (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address b)) (mapSlot (keyValueToWord (.address a)) ⟨1⟩)) w) :=
  map2_assign (layout := solidityLayout! [contract.structs] [contract.storage]) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hL he hf w

end

end FeProofs.ERC20
