import FeProofs.IndexedPackedStore.Common
import FeProofs.Common.PackedByte
import FeProofs.Common.Glue

/-!
# FeIndexedPackedStore element facts

For an index `i < 64`, the bytecode's word `keccak256(0) + (i >> 5)` and bit offset
`(i & 31) << 3` are the layout's word `packedSlot + i / 32` and byte `i % 32`; the Stele read and
write of `pack[i]` are the packed-byte read and read-modify-write of that word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev elemByte (i : Nat) : Fin 32 := ⟨i % 32, Nat.mod_lt _ (by decide)⟩

abbrev elemSlot (i : Nat) : UInt256 := packedSlot + UInt256.ofNat (i / 32)

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

theorem decodeCalldata_four_uint256_ok {cd : ByteArray} {a b c d : Ident}
    (hsz : 132 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [a, b, c, d] [abiUInt256, abiUInt256, abiUInt256, abiUInt256] cd =
      some (((((∅ : Store).insert a (.int (Int.ofNat (calldataWord cd 4).toNat))).insert b
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert c
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert d
        (.int (Int.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have ht36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have ht68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have ht100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hw4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hw36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hw68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hw100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hd1 : (cd.toList.drop 4).drop 32 = cd.toList.drop 36 := by rw [List.drop_drop]
  have hd2 : (cd.toList.drop 4).drop 64 = cd.toList.drop 68 := by rw [List.drop_drop]
  have hd3 : (cd.toList.drop 4).drop 96 = cd.toList.drop 100 := by rw [List.drop_drop]
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?, Nat.zero_add, Nat.reduceAdd]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa only [List.drop_zero] using ht4)]
  simp only [bind, Option.bind]
  rw [decodeScalarWord_uint256_ok (start := 32) (by simpa only [hd1] using ht36),
    decodeScalarWord_uint256_ok (start := 64) (by simpa only [hd2] using ht68),
    decodeScalarWord_uint256_ok (start := 96) (by simpa only [hd3] using ht100)]
  simp only [List.drop_zero, hd1, hd2, hd3, hw4, hw36, hw68, hw100]
  rfl

theorem decodeCalldata_four_uint256_none_short {cd : ByteArray} {a b c d : Ident}
    (hshort : cd.size < 132) :
    decodeCalldata [a, b, c, d] [abiUInt256, abiUInt256, abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_short (by decide) (by simpa using hshort)

theorem decodeCalldata_four_uint256_none_huge {cd : ByteArray} {a b c d : Ident}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [a, b, c, d] [abiUInt256, abiUInt256, abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_huge (by decide) rfl hhuge

end FeProofs.IndexedPackedStore
