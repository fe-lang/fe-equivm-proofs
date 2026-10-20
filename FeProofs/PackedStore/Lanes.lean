import FeProofs.PackedStore.Common
import FeProofs.Common.PackedByte
import FeProofs.Common.Glue

/-!
# FePackedStore lane facts

The compiled mask/shift expressions are the byte-lane operations of `FeCommon.PackedByte`, and
the Stele reads/writes of `lane0`/`lane1` are byte loads/stores of word `packedSlot`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach FeProofs.Common

namespace FeProofs.PackedStore

set_option maxRecDepth 2000000

/-! ## Word algebra -/

theorem packedByte_lane0 (w : UInt256) :
    UInt256.land (UInt256.ofNat 255) w = packedByte w 0 := by
  apply u256_inj
  rw [packedByte_toNat, uland_toNat]
  change Nat.land 255 w.toNat = w.toNat / 256 ^ 0 % 256
  rw [nat_land_comm, show (255 : Nat) = 2 ^ 8 - 1 by norm_num, nat_land_mask_eq_mod]
  simp

theorem packedByte_lane1 (w : UInt256) :
    UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight w (UInt256.ofNat 8)) = packedByte w 1 :=
  u256_land_comm _ _

theorem lane0Mask :
    UInt256.xor (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft ⟨255⟩ (UInt256.ofNat (8 * (0 : Fin 32).val))) =
      UInt256.lnot (UInt256.ofNat 255) := by
  native_decide

theorem lane1Mask :
    UInt256.xor (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft ⟨255⟩ (UInt256.ofNat (8 * (1 : Fin 32).val))) =
      UInt256.lnot (UInt256.ofNat 65280) := by
  native_decide

theorem shiftLeft_lane0 (x : UInt256) :
    UInt256.shiftLeft x (UInt256.ofNat (8 * (0 : Fin 32).val)) = x := by
  apply u256_inj
  change (x.shiftLeft (UInt256.ofNat 0)).toNat = x.toNat
  rw [shiftLeft_toNat_of_lt x 0 (by decide) (by rw [Nat.pow_zero, Nat.mul_one]; exact x.val.isLt)]
  simp

theorem setPackedByte_lane0 (old v : UInt256) :
    setPackedByte old v 0 =
      UInt256.lor (UInt256.land (UInt256.ofNat 255) v) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) old) := by
  unfold setPackedByte packedByte0
  dsimp only
  rw [lane0Mask, shiftLeft_lane0]
  exact (u256_lor_comm _ _).trans (congrArg₂ UInt256.lor (u256_land_comm _ _) (u256_land_comm _ _))

theorem setPackedByte_lane1 (old v : UInt256) :
    setPackedByte old v 1 =
      UInt256.lor (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 255) v) (UInt256.ofNat 8))
        (UInt256.land (UInt256.lnot (UInt256.ofNat 65280)) old) := by
  unfold setPackedByte packedByte0
  dsimp only
  rw [lane1Mask]
  exact (u256_lor_comm _ _).trans (congrArg₂ UInt256.lor
    (congrArg₂ UInt256.shiftLeft (u256_land_comm _ _) rfl) (u256_land_comm _ _))

/-! ## Stele reads and writes of the lanes -/

abbrev uint8Ty : StorageType := .elem (.int (.uint ⟨8, by decide⟩))
abbrev uint256Ty : StorageType := .elem (.int (.uint ⟨256, by decide⟩))

theorem evalLaneCast {stele : Frame} {evm : EVM.State} (name : Ident) (offset : Fin 32)
    (hbase : stele.locals.get? name = none)
    (hty : storageTypeAt? stele.contract.storage { base := name, steps := [] } = some uint8Ty)
    (hloc : storageLayout { base := name, steps := [] } =
      some (.leaf (packedByteLoc packedSlot offset))) :
    evalExpr? config stele evm (.cast (.storage { base := name, steps := [] }) uint256Ty) =
      .ok (.int (Int.ofNat (packedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        packedSlot) offset).toNat)) := by
  rw [evalExpr_cast_int (evalExpr_storage_scalar_value (layout := storageLayout) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps]; rfl) hty rfl
    hloc (storageLocLoad_packedByte evm packedSlot offset))]
  congr 2
  refine normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) ?_
  exact Int.ofNat_lt.mpr (packedByte _ offset).val.isLt

theorem evalCast8 {stele : Frame} {evm : EVM.State} {x : Ident} {v : UInt256}
    (h : stele.locals.get? x = some (.int (Int.ofNat v.toNat))) :
    evalExpr? config stele evm (.cast (.var x) uint8Ty) =
      .ok (.int (Int.ofNat (packedByte0 v).toNat)) := by
  have hvar : evalExpr? config stele evm (.var x) = .ok (.int (Int.ofNat v.toNat)) := by
    rw [evalExpr?]
    rw [h]
    rfl
  rw [evalExpr_cast_int hvar]
  congr 2
  rw [packedByte0_toNat]
  change Int.ofNat v.toNat % Int.ofNat 256 = Int.ofNat (v.toNat % 256)
  simp only [Int.ofNat_eq_natCast]
  omega

theorem assignLane {stele : Frame} {evm : EVM.State} (name : Ident) (offset : Fin 32)
    (v : UInt256)
    (hbase : stele.locals.get? name = none)
    (hty : storageTypeAt? stele.contract.storage { base := name, steps := [] } = some uint8Ty)
    (hloc : storageLayout { base := name, steps := [] } =
      some (.leaf (packedByteLoc packedSlot offset))) :
    assignStorageRef? config stele evm .storage { base := name, steps := [] }
        (.int (Int.ofNat (packedByte0 v).toNat)) =
      .ok (stele, Stele.EVM.storageStore evm evm.executionEnv.codeOwner packedSlot
        (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner packedSlot) v offset)) := by
  refine assignStorageRef_storage_scalar (layout := storageLayout) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps]; rfl) hty rfl hloc
    (Or.inl ⟨_, rfl⟩) ?_
  rw [storageLocStore_packedByte, setPackedByte_truncate]


/-! ## Calldata of `setBoth(uint256,uint256)` -/

theorem decodeCalldata_uint256_uint256_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hdrop : (cd.toList.drop 4).drop 32 = cd.toList.drop 36 := by
    rw [List.drop_drop]
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, List.drop_zero,
    Nat.zero_add, hdrop, htake4, htake36, ↓reduceIte, hword4, hword36, bind, Option.bind]
  have hb4 : ((calldataWord cd 4).val : Nat) < EVM.twoPow 256 := (calldataWord cd 4).val.isLt
  have hb36 : ((calldataWord cd 36).val : Nat) < EVM.twoPow 256 := (calldataWord cd 36).val.isLt
  simp [decodeABIWord?, decodeCalldata.insertValues, abiUInt256, hb4, hb36]
  rfl

theorem decodeCalldata_uint256_uint256_none_short {cd : ByteArray} {x y : Ident}
    (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_short (by decide) (by simpa using hshort)

theorem decodeCalldata_uint256_uint256_none_huge {cd : ByteArray} {x y : Ident}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_huge (by decide) rfl hhuge

/-! ## Account maps after one or two lane writes -/

theorem storeLane_accountMap {σ σ₀ A I} {g : Sat256} (v : UInt256) (offset : Fin 32) :
    (Stele.EVM.storageStore (initState σ σ₀ g A I) (initState σ σ₀ g A I).executionEnv.codeOwner
      packedSlot (setPackedByte (Stele.EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner packedSlot) v offset)).accountMap =
      sstoreAccountMap I.codeOwner σ packedSlot
        (setPackedByte (codeOwnerStorageWord I σ packedSlot) v offset) := by
  rw [storageStore_accountMap]
  exact congrArg (sstoreAccountMap I.codeOwner σ packedSlot)
    (congrArg (setPackedByte · v offset) (codeOwnerStorageWord_initState packedSlot))

/-- Two Stele lane writes leave the account map of the compiled single `SSTORE`. -/
theorem storeLanes_accountMap {evm : EVM.State} (first second : UInt256) :
    let evm₁ := Stele.EVM.storageStore evm evm.executionEnv.codeOwner packedSlot
      (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner packedSlot) first 0)
    (Stele.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner packedSlot
      (setPackedByte (Stele.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner packedSlot)
        second 1)).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap packedSlot
        (setPackedByte (setPackedByte
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner packedSlot) first 0) second 1) := by
  intro evm₁
  have henv : evm₁.executionEnv = evm.executionEnv := storageStore_executionEnv _ _ _ _
  rw [henv]
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
      have h₁ : evm₁ = evm := storageStore_absent _ _ hacc _ _
      rw [h₁, storageStore_absent _ _ hacc, sstoreAccountMap_absent_same hacc]
  | some acc =>
      rw [storageLoad_storageStore_same_present evm _ hacc, storageStore_accountMap,
        storageStore_accountMap]
      exact (sstoreAccountMap_self_update _ _ _ _ _).symm

/-- The decoded argument store of the one-argument setters. -/
abbrev valueStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "value" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

/-- The decoded argument store of `setBoth`. -/
abbrev bothStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "first" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert "second"
    (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

end FeProofs.PackedStore
