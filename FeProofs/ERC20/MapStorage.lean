import FeProofs.ERC20.Common
import FeProofs.Common.Glue

/-!
# FeERC20 mapping facts

Fe's `StorageMap` derives an entry's slot as `keccak256(key ‖ slot)` with the key as a 32-byte
word, like a Solidity mapping; the map of maps `allowance` nests that derivation.  The EVM side
hashes the 64-byte scratch preimage at `0x00`; the Stele side locates `balanceOf[owner]` through
the generated Solidity layout.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The slot of entry `key` of a mapping at slot `base`. -/
abbrev mapSlot (key base : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ base.toByteArray))

/-- `KECCAK256(0, 64)` over `MSTORE(0, key); MSTORE(32, base)`. -/
theorem keccakWord_mapSlot (key base : UInt256) (mem : ByteArray) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
        (base.toByteArray.write 0 (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = mapSlot key base := by
  show UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem key base mem).readWithPadding 0 64))) = _
  rw [twoWordHashMem_read0_64_any]
  exact mappingSlot_single key base

-- LIBRARY CANDIDATE: duplicates `FeProofs.NarrowAbi.shiftRight160_*` (the canonical-address check).
/-- `balanceOf[owner]` reads the word at `mapSlot owner 0`. -/
theorem balanceOf_read {L : Store} {evm : EVM.State} {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hL : L.get? "balanceOf" = none)
    (hown : L.get? "owner" = some (.address (AccountAddress.ofNat w.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "balanceOf", steps := [.mindex (.var "owner")] }) =
      .ok (.int (Int.ofNat
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot w ⟨0⟩)).toNat)) := by
  have hown' : L["owner"]? = some (.address (AccountAddress.ofNat w.toNat)) := by simpa using hown
  have h := evalExpr_storage_scalar_value (cfg := config)
    (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩))
    (loc := uint256Loc (mapSlot (keyValueToWord (.address (AccountAddress.ofNat w.toNat))) ⟨0⟩))
    (er := { base := "balanceOf", steps := [.mindex (.address (AccountAddress.ofNat w.toNat))] })
    (slot := { base := "balanceOf", steps := [.mindex (.var "owner")] })
    (stele := { contract := contract, locals := L }) (evm := evm) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hown'])
    rfl rfl rfl (storageLocLoad_uint256 evm _)
  rw [keyValueToWord_address_of_canonical w hcanon] at h
  exact h

/-- `allowance[owner][spender]` reads the word at `mapSlot spender (mapSlot owner 1)`. -/
theorem allowance_read {L : Store} {evm : EVM.State} {w v : UInt256}
    (hcanon0 : w.toNat < EVM.addressModulus) (hcanon1 : v.toNat < EVM.addressModulus)
    (hL : L.get? "allowance" = none)
    (hown : L.get? "owner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hsp : L.get? "spender" = some (.address (AccountAddress.ofNat v.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "allowance", steps := [.mindex (.var "owner"), .mindex (.var "spender")] }) =
      .ok (.int (Int.ofNat
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
          (mapSlot v (mapSlot w (UInt256.ofNat 1)))).toNat)) := by
  have hown' : L["owner"]? = some (.address (AccountAddress.ofNat w.toNat)) := by simpa using hown
  have hsp' : L["spender"]? = some (.address (AccountAddress.ofNat v.toNat)) := by simpa using hsp
  have h := evalExpr_storage_scalar_value (cfg := config)
    (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int (.uint ⟨256, by decide⟩))
    (loc := uint256Loc (mapSlot (keyValueToWord (.address (AccountAddress.ofNat v.toNat)))
      (mapSlot (keyValueToWord (.address (AccountAddress.ofNat w.toNat))) ⟨1⟩)))
    (er := { base := "allowance", steps := [.mindex (.address (AccountAddress.ofNat w.toNat)),
      .mindex (.address (AccountAddress.ofNat v.toNat))] })
    (slot := { base := "allowance", steps := [.mindex (.var "owner"), .mindex (.var "spender")] })
    (stele := { contract := contract, locals := L }) (evm := evm) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hown', hsp'])
    rfl rfl rfl (storageLocLoad_uint256 evm _)
  rw [keyValueToWord_address_of_canonical w hcanon0,
    keyValueToWord_address_of_canonical v hcanon1] at h
  exact h

end FeProofs.ERC20
