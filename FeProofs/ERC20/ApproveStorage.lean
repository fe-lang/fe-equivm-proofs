import FeProofs.ERC20.Common

/-!
# FeERC20 `allowance` slot facts

The generated Solidity layout puts `allowance[owner][spender]` at
`keccak256(spender ‖ keccak256(owner ‖ 1))`.  Fe hashes the same preimages in scratch memory at
`0x00..0x40`: owner then slot 1, then spender then the inner hash.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The generated Solidity layout of the contract's storage. -/
def approveLayout : StorageLayout := storageBackend.locate?

theorem approveConfig_storageBackend : config.storageBackend = solidityStorageBackend approveLayout :=
  rfl

/-- Solidity's mapping slot `keccak256(key ‖ base)`. -/
def approveMapSlot (key base : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ base.toByteArray))

theorem approveAllowanceLoc (o s : KeyValue) :
    approveLayout { base := "allowance", steps := [.mindex o, .mindex s] } =
      some (.leaf (uint256Loc (approveMapSlot (keyValueToWord s)
        (approveMapSlot (keyValueToWord o) (UInt256.ofNat 1))))) :=
  rfl

/-- `KECCAK256(0, 64)` over the two scratch words is the mapping slot of `a` at base `b`. -/
theorem approvePair_keccak (mem : ByteArray) (a b : UInt256) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
        (b.toByteArray.write 0 (a.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = approveMapSlot a b := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (UInt256.ofNat 64).toNat = 64 from rfl, twoWordWrite_read0_64_any]
  exact mappingSlot_single a b

end FeProofs.ERC20
