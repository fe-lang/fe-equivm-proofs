import FeProofs.ScalarStore.Model

/-!
# FeScalarStore: exported arms

The three definitions below are the output of `fe-lean-export` on `FeScalarStore.fe`, pasted
unchanged (Fe branch `lean-export`, test `scalar_store_arms_export`).  The theorems show each
equals the hand-written model arm, so the certificate for the model covers the exported code.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ScalarStore.Exported

def init (v0 : UInt256) : FeM Unit := do
  let v1 ← pure v0
  sstore (UInt256.ofNat 0) v1
  let v2 ← pure ()
  return ()

def recv0_arm0 : FeM UInt256 := do
  let v0 ← sload (UInt256.ofNat 0)
  return v0

def recv0_arm1 (v0 : UInt256) : FeM Unit := do
  sstore (UInt256.ofNat 0) v0
  let v1 ← pure ()
  return ()

theorem init_eq (initial : UInt256) : init initial = Model.initBody initial := by
  simp [init, Model.initBody, Model.storedSlot]
  rfl

theorem recv0_arm0_eq : recv0_arm0 = Model.get := by
  simp [recv0_arm0, Model.get, Model.storedSlot]
  rfl

theorem recv0_arm1_eq (value : UInt256) : recv0_arm1 value = Model.set value := by
  simp [recv0_arm1, Model.set, Model.storedSlot]
  rfl

end FeProofs.ScalarStore.Exported
