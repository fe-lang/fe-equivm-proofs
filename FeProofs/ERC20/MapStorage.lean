import FeProofs.ERC20.Common
import FeProofs.Common.Glue

/-!
# FeERC20 mapping facts

Fe's `StorageMap` derives an entry's slot as `keccak256(key ‖ slot)` with the key as a 32-byte
word, like a Solidity mapping; the map of maps `allowance` nests that derivation.  The EVM side
hashes the 64-byte scratch preimage at `0x00`; the Stele side locates `balanceOf[k]` and
`allowance[o][s]` through the generated Solidity layout, for key expressions that evaluate to
addresses.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The slot of entry `key` of a mapping at slot `base`. -/
abbrev mapSlot (key base : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ base.toByteArray))

/-- The word at `balanceOf[key]` in the account map `σ`. -/
abbrev balanceWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : UInt256 :=
  solcSlotWord σ I (mapSlot key ⟨0⟩)

/-- `balanceOf[to]`. -/
abbrev balanceOfTo : StorageRef := { base := "balanceOf", steps := [.mindex (.var "to")] }

/-- `KECCAK256(0, 64)` over `MSTORE(0, key); MSTORE(32, base)`. -/
theorem keccakWord_mapSlot (key base : UInt256) (mem : ByteArray) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
        (base.toByteArray.write 0 (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = mapSlot key base := by
  show UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem key base mem).readWithPadding 0 64))) = _
  rw [twoWordHashMem_read0_64_any]
  exact mappingSlot_single key base

/-- A branch-condition hint for `rd_run` whose words are read from slots hashed in scratch memory:
rewrites the hashes to `mapSlot`, then closes the condition with `h`. -/
macro "slot_hint " h:term:max : term => `(by simp only [keccakWord_mapSlot]; exact $h)

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
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩)) (er := { base := "balanceOf", steps := [.mindex (.address a)] })
    hL (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he])
    rfl rfl rfl (storageLocLoad_uint256 evm _)

/-- Writing `w` to `balanceOf[e]` stores it at `mapSlot a 0`. -/
theorem balanceOf_assign (hL : L.get? "balanceOf" = none)
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.address a))
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage
        { base := "balanceOf", steps := [.mindex e] } (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner (mapSlot (keyValueToWord (.address a)) ⟨0⟩) w) :=
  assignStorageRef_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (er := { base := "balanceOf", steps := [.mindex (.address a)] })
    (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (loc := uint256Loc (mapSlot (keyValueToWord (.address a)) ⟨0⟩)) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ w)

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
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩))
    (er := { base := "allowance", steps := [.mindex (.address a), .mindex (.address b)] })
    hL (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he, hf])
    rfl rfl rfl (storageLocLoad_uint256 evm _)

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
  assignStorageRef_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (er := { base := "allowance", steps := [.mindex (.address a), .mindex (.address b)] })
    (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (loc := uint256Loc (mapSlot (keyValueToWord (.address b))
      (mapSlot (keyValueToWord (.address a)) ⟨1⟩))) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he, hf])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ w)

end

end FeProofs.ERC20
