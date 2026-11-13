import FeProofs.Lib.ExportedCorrect
import FeProofs.PackedStore.Exported
import FeProofs.Common.PackedByte

/-!
# FePackedStore: what the exported arms do

Lanes 0 and 1 of the array are bytes 0 and 1 of the word at `wordSlot`, read and written as
`packedByte` and `setPackedByte`.  Each arm looks the word up through std's `StorageMap`, which
leaves the hashed key in a fresh buffer.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM
open FeProofs.Lib (locateU256_exec)

namespace FeProofs.PackedStore.Exported

/-! ## The constants -/

theorem lanesPerSlot : StoragePackedArray_LANES_PER_SLOT_8 = pure ⟨32⟩ := by
  simp [StoragePackedArray_LANES_PER_SLOT_8, checkedDiv]
  rfl

theorem laneMask : StoragePackedArray_LANE_MASK_8 = pure ⟨255⟩ := by
  simp [StoragePackedArray_LANE_MASK_8, checkedSub]
  rfl

theorem u256Mask : U256_MASK = pure (UInt256.lnot ⟨0⟩) := by
  simp [U256_MASK]
  rfl

/-! ## The arms -/

/-- The slot of word 0 of the array in the contract field `pack`: entry 0 of the map `words`
    at slot 0. -/
def wordSlot : UInt256 := mapSlot ⟨0⟩ ⟨0⟩

variable (I : ExecutionEnv) (w : World)

/-- `w` with the buffer a lookup of word 0 of the array leaves: its key and the map's root, both
    zero. -/
def afterLookup (w : World) : World := { w with memory := keyed w.memory ⟨0⟩ ⟨0⟩ }

theorem afterLookup_size : (afterLookup w).memory.size = w.memory.size + 64 := keyed_size _ _ _

theorem get0_exec (hmem : w.memory.size + 64 < UInt256.size) :
    recv0_arm0.exec I w =
      some (.ok (packedByte (slotWord I w.accounts wordSlot) 0, afterLookup w)) := by
  simp [recv0_arm0, StoragePackedArray_get_8, lanesPerSlot, laneMask, Field.pack, Layout.StoragePackedArray_8,
    checkedRem, checkedDiv, locateU256_exec _ _ _ _ _ hmem, afterLookup]
  exact ⟨rfl, rfl⟩

theorem get1_exec (hmem : w.memory.size + 64 < UInt256.size) :
    recv0_arm1.exec I w =
      some (.ok (packedByte (slotWord I w.accounts wordSlot) 1, afterLookup w)) := by
  simp [recv0_arm1, StoragePackedArray_get_8, lanesPerSlot, laneMask, Field.pack, Layout.StoragePackedArray_8,
    checkedRem, checkedDiv, locateU256_exec _ _ _ _ _ hmem, afterLookup]
  exact ⟨rfl, rfl⟩

/-- The accounts after lane `lane` of the word at `wordSlot` is set to the low byte of
    `value`. -/
def setLane (I : ExecutionEnv) (σ : AccountMap) (lane : Fin 32) (value : UInt256) : AccountMap :=
  storeWord I.codeOwner σ wordSlot (setPackedByte (slotWord I σ wordSlot) value lane)

theorem set0_exec (value : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm2 value).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup w with accounts := setLane I w.accounts 0 value }))
      else some (.error .static) := by
  simp [recv0_arm2, StoragePackedArray_set_8, lanesPerSlot, laneMask, u256Mask, Field.pack,
    Layout.StoragePackedArray_8, checkedRem, checkedDiv, exec_sstore,
    locateU256_exec _ _ _ _ _ hmem, afterLookup]
  rfl

theorem set1_exec (value : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    (recv0_arm3 value).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup w with accounts := setLane I w.accounts 1 value }))
      else some (.error .static) := by
  simp [recv0_arm3, StoragePackedArray_set_8, lanesPerSlot, laneMask, u256Mask, Field.pack,
    Layout.StoragePackedArray_8, checkedRem, checkedDiv, exec_sstore,
    locateU256_exec _ _ _ _ _ hmem, afterLookup]
  rfl

theorem setBoth_exec (first second : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    (recv0_arm4 first second).exec I w =
      if I.perm then
        some (.ok ((), { afterLookup (afterLookup w) with
          accounts := setLane I (setLane I w.accounts 0 first) 1 second }))
      else some (.error .static) := by
  cases hperm : I.perm <;>
    simp (disch := (try simp only [keyed_size]); omega) [recv0_arm4, StoragePackedArray_set_8, lanesPerSlot,
      laneMask, u256Mask, Field.pack, Layout.StoragePackedArray_8, checkedRem, checkedDiv,
      exec_sstore, hperm, locateU256_exec, afterLookup]
  exact ⟨rfl, rfl⟩

end FeProofs.PackedStore.Exported
