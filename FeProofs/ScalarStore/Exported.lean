import FeProofs.ScalarStore.Model

/-!
# FeScalarStore: exported arms

The definitions below are the output of `fe-lean-export` on `FeScalarStore.fe` (Fe branch
`lean-export`, golden file `tests/golden/scalar_store.lean`), copied in by
`scripts/sync_exported.py`.  The theorems show each
equals the hand-written model arm, so the certificate for the model covers the exported code.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ScalarStore.Exported

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: scalar_store

def Field.stored : Place :=
  .storage (UInt256.ofNat 0)

def init (v0 : UInt256) : FeM Unit := do
  let v1 := v0
  store Field.stored v1
  let v2 := ()
  return ()

def recv0_arm0 : FeM UInt256 := do
  let v0 ← load Field.stored
  return v0

def recv0_arm1 (v0 : UInt256) : FeM Unit := do
  store Field.stored v0
  let v1 := ()
  return ()

-- END fe-lean-export

end

theorem init_eq (initial : UInt256) : init initial = Model.initBody initial := by
  simp [init, Field.stored, Model.initBody, Model.storedSlot]
  rfl

theorem recv0_arm0_eq : recv0_arm0 = Model.get := by
  simp [recv0_arm0, Field.stored, Model.get, Model.storedSlot]
  rfl

theorem recv0_arm1_eq (value : UInt256) : recv0_arm1 value = Model.set value := by
  simp [recv0_arm1, Field.stored, Model.set, Model.storedSlot]
  rfl

end FeProofs.ScalarStore.Exported
