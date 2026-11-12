import FeProofs.IndexedPackedStore.Common
import FeProofs.Common.PackedByte
import FeProofs.Common.Glue

/-!
# FeIndexedPackedStore element facts

For an index `i < 64`, the bytecode's word `KECCAK256` over `MSTORE(0, i >> 5); MSTORE(32, 0)` and
bit offset `(i & 31) << 3` are the layout's word `mapSlot (i / 32) 0` and byte `i % 32`; the Stele
read and write of `pack[i]` are the packed-byte read and read-modify-write of that word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev elemByte (i : Nat) : Fin 32 := ⟨i % 32, Nat.mod_lt _ (by decide)⟩

abbrev elemSlot (i : Nat) : UInt256 := mapSlot (UInt256.ofNat (i / 32)) ⟨0⟩

theorem shr5_eq (x : UInt256) : UInt256.shiftRight x (UInt256.ofNat 5) = UInt256.ofNat (x.toNat / 32) := by
  apply u256_inj
  have hlt : x.toNat / 32 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (show x.toNat < UInt256.size from x.val.isLt)
  rw [shiftRight_toNat_of_lt x 5 (by decide), ulit_toNat' (x.toNat / 32) hlt]
  norm_num

theorem bitOffset_eq (x : UInt256) :
    UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 31)) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * (elemByte x.toNat).val) := by
  have hland : (UInt256.land x (UInt256.ofNat 31)).toNat = x.toNat % 32 := by
    rw [uland_toNat, ulit_toNat' 31 (by decide)]
    change Nat.land x.toNat (2 ^ 5 - 1) = x.toNat % 2 ^ 5
    exact nat_land_mask_eq_mod _ 5
  apply u256_inj
  rw [shiftLeft_toNat_of_lt _ 3 (by decide) (by
      rw [hland]; have := Nat.mod_lt x.toNat (show 0 < 32 by decide)
      have h2 : x.toNat % 32 * 2 ^ 3 < 256 := by omega
      exact lt_of_lt_of_le h2 (by decide)),
    hland, ulit_toNat' _ (by
      have := Nat.mod_lt x.toNat (show 0 < 32 by decide)
      have hs : (256 : Nat) ≤ UInt256.size := by decide
      simp only; omega)]
  simp only
  omega

/-- The bytecode's lane read is `packedByte`. -/
theorem laneRead_eq (w x : UInt256) :
    UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight w
      (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 31)) (UInt256.ofNat 3))) =
      packedByte w (elemByte x.toNat) := by
  rw [bitOffset_eq, u256_land_comm]
  rfl

abbrev uint8Ty : StorageType := .elem (.int (.uint ⟨8, by decide⟩))
abbrev uint256Ty : StorageType := .elem (.int (.uint ⟨256, by decide⟩))

abbrev elemRef (x : Ident) : StorageRef := { base := "pack", steps := [.aindex (.var x)] }

theorem elemRef_eval {L : Store} {evm : EVM.State} {x : Ident} {i : Nat} (hi : i < 64)
    (hx : L.get? x = some (.int (Int.ofNat i))) :
    evalStorageRef config { contract := contract, locals := L } evm (elemRef x) =
      .ok { base := "pack", steps := [.aindex (.int (Int.ofNat i))] } := by
  have hidx : evalExpr? config { contract := contract, locals := L } evm (.var x) =
      .ok (.int (Int.ofNat i)) := evalLocalVar hx
  have hty : storageTypeAt? contract.storage { base := "pack", steps := [] } =
      some (.array uint8Ty 64) := rfl
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
    arrayIndexInBounds?, hty, bind, EvalResult.bind, pure, EvalResult.ofOption, hi]

theorem elemLayout {i : Nat} (hi : i < 64) :
    storageLayout { base := "pack", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (packedByteLoc (elemSlot i) (elemByte i))) := by
  simp [storageLayout, hi, elemLoc]

/-- `uint256(pack[x])` for an in-bounds `x`. -/
theorem evalElemCast {L : Store} {evm : EVM.State} {x : Ident} {i : Nat} (hi : i < 64)
    (hx : L.get? x = some (.int (Int.ofNat i))) (hbase : L.get? "pack" = none) :
    evalExpr? config { contract := contract, locals := L } evm (.cast (.storage (elemRef x)) uint256Ty) =
      .ok (.int (Int.ofNat (packedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (elemSlot i)) (elemByte i)).toNat)) := by
  rw [evalExpr_cast_int (evalExpr_storage_scalar_value (layout := storageLayout) hbase
    (elemRef_eval hi hx) rfl rfl (elemLayout hi)
    (storageLocLoad_packedByte evm (elemSlot i) (elemByte i)))]
  congr 2
  refine normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) ?_
  exact Int.ofNat_lt.mpr (packedByte _ _).val.isLt

/-- `pack[x] = uint8(v)` for an in-bounds `x`. -/
theorem assignElem {L : Store} {evm : EVM.State} {x : Ident} {i : Nat} (hi : i < 64)
    (hx : L.get? x = some (.int (Int.ofNat i))) (hbase : L.get? "pack" = none) (v : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage (elemRef x)
        (.int (Int.ofNat (packedByte0 v).toNat)) =
      .ok ({ contract := contract, locals := L }, Stele.EVM.storageStore evm evm.executionEnv.codeOwner
        (elemSlot i) (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (elemSlot i))
          v (elemByte i))) := by
  refine assignStorageRef_storage_scalar (layout := storageLayout) hbase (elemRef_eval hi hx) rfl rfl
    (elemLayout hi) (Or.inl ⟨_, rfl⟩) ?_
  rw [storageLocStore_packedByte, setPackedByte_truncate]

/-- The bytecode's lane write is `setPackedByte`. -/
theorem laneWrite_eq (W v x : UInt256) :
    UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) v)
        (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 31)) (UInt256.ofNat 3)))
      (UInt256.land W (UInt256.xor (UInt256.lnot (⟨0⟩ : UInt256))
        (UInt256.shiftLeft (UInt256.ofNat 255)
          (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 31)) (UInt256.ofNat 3))))) =
      setPackedByte W v (elemByte x.toNat) := by
  rw [bitOffset_eq]
  unfold setPackedByte packedByte0
  dsimp only
  rw [u256_lor_comm, u256_land_comm (UInt256.ofNat 255) v]
  rfl

theorem evalCastU8 {L : Store} {evm : EVM.State} {x : Ident} {v : UInt256}
    (h : L.get? x = some (.int (Int.ofNat v.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm (.cast (.var x) uint8Ty) =
      .ok (.int (Int.ofNat (packedByte0 v).toNat)) := by
  rw [evalExpr_cast_int (evalLocalVar h)]
  congr 2
  rw [packedByte0_toNat]
  change Int.ofNat v.toNat % Int.ofNat 256 = Int.ofNat (v.toNat % 256)
  simp only [Int.ofNat_eq_natCast]
  omega

-- LIBRARY CANDIDATE: copied from FeProofs.PackedStore (two static uint256 arguments).
/-! ## Calldata of `setBoth(uint256,uint256)` -/


theorem evalIndexLt {L : Store} {evm : EVM.State} {x : Ident} {i : Nat}
    (hx : L.get? x = some (.int (Int.ofNat i))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .lt (.var x) (.intLit 64)) = .ok (.bool (decide (i < 64))) := by
  simp only [evalExpr?, hx, bind, EvalResult.bind, pure, EvalResult.ofOption, evalBinaryOp?]
  congr 2
  simp only [Int.ofNat_eq_natCast, decide_eq_decide]
  omega

end FeProofs.IndexedPackedStore
