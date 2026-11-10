import Fe.EVM.World

/-!
# Exporter fixtures

Output of `fe-lean-export` on fixtures that have no bytecode proof (Fe branch `lean-export`,
`crates/lean-export/tests/golden/`), copied in by `scripts/sync_exported.py`.  This file checks
that the output elaborates, and that the control flow it prints means what the source says.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

/-! ## `helper_call`: a helper that takes contract state through `uses` -/

namespace FeProofs.Fixtures.HelperCall

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: helper_call

def Field.store : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Store : Layout :=
  { storage := [0, 1] }

def init : FeM Unit := do
  return ()

def add_Store (v0 : UInt256) : FeM UInt256 := do
  let v1 ← load (Field.store.field Layout.Store 0)
  let v2 := v0
  let v3 ← checkedAdd v1 v2
  let v4 := v3
  store (Field.store.field Layout.Store 0) v4
  let v5 := ()
  let v6 := (UInt256.ofNat 1)
  let v7 := v0
  let v8 ← load ((Field.store.field Layout.Store 1).entry v7)
  let v9 ← checkedAdd v8 v6
  store ((Field.store.field Layout.Store 1).entry v7) v9
  let v10 := ()
  return v4

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← add_Store v0
  return v1

-- END fe-lean-export

end

end FeProofs.Fixtures.HelperCall

/-! ## `join`: an `if` expression whose branches merge -/

namespace FeProofs.Fixtures.Join

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: join

def Field.store : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Store : Layout :=
  { storage := [0, 1] }

def init : FeM Unit := do
  return ()

def add_Store (v0 : UInt256) : FeM UInt256 := do
  let v2 := v0
  let v3 := (UInt256.ofNat 10)
  let v4 := decide (v3.toNat < v2.toNat)
  let b3 : UInt256 → FeM UInt256 := fun v1 => do
    let v13 := v1
    store (Field.store.field Layout.Store 0) v13
    let v14 := ()
    let v15 := (UInt256.ofNat 1)
    let v16 := v0
    let v17 ← load ((Field.store.field Layout.Store 1).entry v16)
    let v18 ← checkedAdd v17 v15
    store ((Field.store.field Layout.Store 1).entry v16) v18
    let v19 := ()
    return v13
  if v4 then
    let v5 ← load (Field.store.field Layout.Store 0)
    let v6 := (UInt256.ofNat 10)
    let v7 ← checkedAdd v5 v6
    let v8 := v7
    b3 v8
  else
    let v9 ← load (Field.store.field Layout.Store 0)
    let v10 := v0
    let v11 ← checkedAdd v9 v10
    let v12 := v11
    b3 v12

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← add_Store v0
  return v1

-- END fe-lean-export

end

/-- `add` of the fixture, written with the `if` as an expression:

```fe
let next = if by > 10 { store.total + 10 } else { store.total + by }
store.total = next
store.hits[by] += 1
next
```
-/
def addSpec (amount : UInt256) : FeM UInt256 := do
  let total ← load (Field.store.field Layout.Store 0)
  let next ← checkedAdd total (if 10 < amount.toNat then UInt256.ofNat 10 else amount)
  store (Field.store.field Layout.Store 0) next
  let hits ← load ((Field.store.field Layout.Store 1).entry amount)
  let hits ← checkedAdd hits (UInt256.ofNat 1)
  store ((Field.store.field Layout.Store 1).entry amount) hits
  return next

/-- The exported join block runs after either branch, with that branch's value. -/
theorem add_exec (amount : UInt256) (I : ExecutionEnv) (w : World) :
    (add_Store amount).exec I w = (addSpec amount).exec I w := by
  have h10 : (UInt256.ofNat 10).toNat = 10 := rfl
  by_cases h : 10 < amount.toNat <;> simp [add_Store, addSpec, h, h10]

end FeProofs.Fixtures.Join
