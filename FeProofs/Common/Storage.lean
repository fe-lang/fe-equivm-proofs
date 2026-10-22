import Reasoning.SteleBody
import Reasoning.Storage
import Reasoning.MemCascade
import FeProofs.Common.Memory

/-!
# Mapping slots

Fe's `StorageMap` derives an entry's slot as `keccak256(key ‖ slot)` with the key as a 32-byte
word, like a Solidity mapping; a map of maps nests that derivation.  The EVM side hashes a 64-byte
preimage of two adjacent words in memory (`keccakWord_mapSlot`, `keccakWord_mapSlotAt`).  The Stele
side reads and writes `m[k]` and `m[k][k']` through a Solidity layout (`map_read`, `map_assign`,
`map2_read`, `map2_assign`); a contract instantiates them for its own mappings, discharging the
layout hypotheses by `rfl`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs

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

/-- `KECCAK256(s, 64)` over `MSTORE(s, key); MSTORE(s + 32, base)`, for a preimage below `2^32`. -/
theorem keccakWord_mapSlotAt (key base : UInt256) (mem : ByteArray) (s t : Nat) (ht : t = s + 32)
    (hs : s + 32 < 2 ^ 32) :
    keccakWord (UInt256.ofNat s) (UInt256.ofNat 64)
        (base.toByteArray.write 0 (key.toByteArray.write 0 mem s 32) t 32) = mapSlot key base := by
  have hs' : (UInt256.ofNat s).toNat = s := by
    simp only [UInt256.toNat, UInt256.ofNat]; exact Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  unfold keccakWord
  rw [hs', show (UInt256.ofNat 64).toNat = 64 from rfl, pairWords_read mem key base s t 64 ht rfl hs]
  exact mappingSlot_single key base

/-- A branch-condition hint for `rd_run` whose words are read from slots hashed in memory: rewrites
the hashes to `mapSlot`, then closes the condition with `h`. -/
macro "slot_hint " h:term:max : term =>
  `(by simp (disch := (first | rfl | decide | omega)) only [keccakWord_mapSlot,
    keccakWord_mapSlotAt]; exact $h)

/-- The element type of a `uint256` value. -/
abbrev uint256Elem : ABI.ElemType := .int (.uint ⟨256, by decide⟩)

section
variable {cfg : Config} {c : ContractDecl} {layout : StorageLayout} {name : Ident} {base : UInt256}
  {L : Store} {evm : EVM.State} {e f : Expr} {a b : AccountAddress}

/-- `m[e]` of a `mapping(address => uint256)` named `name` at slot `base`, for a key `e`
evaluating to the address `a`, reads the word at `mapSlot a base`. -/
theorem map_read (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a)] } = some (.elem uint256Elem))
    (hloc : ∀ a : AccountAddress, layout { base := name, steps := [.mindex (.address a)] } =
      some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address a)) base))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a)) :
    evalExpr? cfg { contract := c, locals := L } evm (.storage { base := name, steps := [.mindex e] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address a)) base)).toNat)) :=
  evalExpr_storage_scalar_value (layout := layout) (t := uint256Elem)
    (er := { base := name, steps := [.mindex (.address a)] })
    hL (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he])
    (hty a) hbackend (hloc a) (storageLocLoad_uint256 evm _)

/-- Writing the integer `n` to `m[e]` stores its wrapped word at `mapSlot a base`. -/
theorem map_assign_int (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a)] } = some (.elem uint256Elem))
    (hloc : ∀ a : AccountAddress, layout { base := name, steps := [.mindex (.address a)] } =
      some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address a)) base))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a)) (n : Int) :
    assignStorageRef? cfg { contract := c, locals := L } evm .storage
        { base := name, steps := [.mindex e] } (.int n) =
      .ok ({ contract := c, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner (mapSlot (keyValueToWord (.address a)) base) (EVM.wordOfInt n)) :=
  assignStorageRef_storage_scalar_value (layout := layout)
    (er := { base := name, steps := [.mindex (.address a)] }) (ty := .elem uint256Elem)
    (loc := uint256Loc (mapSlot (keyValueToWord (.address a)) base)) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he])
    (hty a) hbackend (hloc a) (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256_int evm _ n)

/-- Writing `w` to `m[e]` stores it at `mapSlot a base`. -/
theorem map_assign (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a)] } = some (.elem uint256Elem))
    (hloc : ∀ a : AccountAddress, layout { base := name, steps := [.mindex (.address a)] } =
      some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address a)) base))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a)) (w : UInt256) :
    assignStorageRef? cfg { contract := c, locals := L } evm .storage
        { base := name, steps := [.mindex e] } (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := c, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner (mapSlot (keyValueToWord (.address a)) base) w) := by
  rw [map_assign_int hbackend hty hloc hL he, wordOfInt_ofNat_toNat]

/-- `m[e][f]` of a `mapping(address => mapping(address => uint256))` named `name` at slot `base`,
for keys evaluating to the addresses `a` and `b`, reads the word at
`mapSlot b (mapSlot a base)`. -/
theorem map2_read (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a b : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.elem uint256Elem))
    (hloc : ∀ a b : AccountAddress,
      layout { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address b))
          (mapSlot (keyValueToWord (.address a)) base)))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a))
    (hf : evalExpr? cfg { contract := c, locals := L } evm f = .ok (.address b)) :
    evalExpr? cfg { contract := c, locals := L } evm
        (.storage { base := name, steps := [.mindex e, .mindex f] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address b))
          (mapSlot (keyValueToWord (.address a)) base))).toNat)) :=
  evalExpr_storage_scalar_value (layout := layout) (t := uint256Elem)
    (er := { base := name, steps := [.mindex (.address a), .mindex (.address b)] })
    hL (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he, hf])
    (hty a b) hbackend (hloc a b) (storageLocLoad_uint256 evm _)

/-- Writing the integer `n` to `m[e][f]` stores its wrapped word at
`mapSlot b (mapSlot a base)`. -/
theorem map2_assign_int (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a b : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.elem uint256Elem))
    (hloc : ∀ a b : AccountAddress,
      layout { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address b))
          (mapSlot (keyValueToWord (.address a)) base)))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a))
    (hf : evalExpr? cfg { contract := c, locals := L } evm f = .ok (.address b)) (n : Int) :
    assignStorageRef? cfg { contract := c, locals := L } evm .storage
        { base := name, steps := [.mindex e, .mindex f] } (.int n) =
      .ok ({ contract := c, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address b)) (mapSlot (keyValueToWord (.address a)) base))
        (EVM.wordOfInt n)) :=
  assignStorageRef_storage_scalar_value (layout := layout)
    (er := { base := name, steps := [.mindex (.address a), .mindex (.address b)] })
    (ty := .elem uint256Elem)
    (loc := uint256Loc (mapSlot (keyValueToWord (.address b))
      (mapSlot (keyValueToWord (.address a)) base))) hL
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, he, hf])
    (hty a b) hbackend (hloc a b) (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256_int evm _ n)

/-- Writing `w` to `m[e][f]` stores it at `mapSlot b (mapSlot a base)`. -/
theorem map2_assign (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : ∀ a b : AccountAddress, storageTypeAt? c.storage
      { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.elem uint256Elem))
    (hloc : ∀ a b : AccountAddress,
      layout { base := name, steps := [.mindex (.address a), .mindex (.address b)] } =
        some (.leaf (uint256Loc (mapSlot (keyValueToWord (.address b))
          (mapSlot (keyValueToWord (.address a)) base)))))
    (hL : L.get? name = none)
    (he : evalExpr? cfg { contract := c, locals := L } evm e = .ok (.address a))
    (hf : evalExpr? cfg { contract := c, locals := L } evm f = .ok (.address b)) (w : UInt256) :
    assignStorageRef? cfg { contract := c, locals := L } evm .storage
        { base := name, steps := [.mindex e, .mindex f] } (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := c, locals := L }, Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner
        (mapSlot (keyValueToWord (.address b)) (mapSlot (keyValueToWord (.address a)) base)) w) := by
  rw [map2_assign_int hbackend hty hloc hL he hf, wordOfInt_ofNat_toNat]

end

end FeProofs
