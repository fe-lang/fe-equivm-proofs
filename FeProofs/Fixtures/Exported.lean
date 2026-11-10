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

/-! ## `local_struct`: struct values in mutable locals, passed by `mut` -/

namespace FeProofs.Fixtures.LocalStruct

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: local_struct

structure Cursor where
  pos : UInt256
  base : UInt256
deriving Inhabited

structure Span where
  start : Cursor
  len : UInt256
deriving Inhabited

def Field.saved : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Cursor : Layout :=
  { storage := [0, 1] }

def init : FeM Unit := do
  return ()

def advance (v0 : Cursor) (v1 : UInt256) : FeM (UInt256 × Cursor) := do
  let mut v0 := v0
  let v2 := v0.pos
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  v0 := { v0 with pos := v5 }
  let v6 := ()
  return (v3, v0)

def skip (v0 : Cursor) (v1 : UInt256) : FeM (Unit × Cursor) := do
  let mut v0 := v0
  let v2 := v1
  let v3 := (UInt256.ofNat 32)
  let v4 := decide (v3.toNat < v2.toNat)
  let b3 : Cursor → FeM (Unit × Cursor) := fun v0 => do
    let mut v0 := v0
    let v10 := v0.pos
    v0 := { v0 with base := v10 }
    let v11 := ()
    return ((), v0)
  if v4 then
    let v5 := (UInt256.ofNat 32)
    let (v6, v6_0) ← advance v0 v5
    v0 := v6_0
    let v7 := v6
    b3 v0
  else
    let (v8, v8_0) ← advance v0 v1
    v0 := v8_0
    let v9 := v8
    b3 v0

def «end» (v0 : Cursor) : FeM UInt256 := do
  let v1 := v0.pos
  let v2 := v0.base
  let v3 ← checkedAdd v1 v2
  return v3

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : Cursor := default
  let mut r1 : Span := default
  let v1 := (UInt256.ofNat 0)
  let v2 := (UInt256.ofNat 4)
  let v4 := (Cursor.mk v1 v2)
  r0 := v4
  let (v6, v6_0) ← advance r0 v0
  r0 := v6_0
  let v7 := v6
  let (v9, v9_0) ← skip r0 v0
  r0 := v9_0
  let v10 := r0
  let v11 := v10
  let v13 := (Span.mk v11 v0)
  r1 := v13
  let v14 := r1.len
  let (v16, v16_0) ← advance r1.start v14
  r1 := { r1 with start := v16_0 }
  let v17 := v16
  let v18 ← checkedAdd v7 v17
  let v21 ← «end» r1.start
  let v22 ← checkedAdd v18 v21
  return v22

def advance_1 (v0 : Place) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← load (v0.field Layout.Cursor 0)
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  store (v0.field Layout.Cursor 0) v5
  let v6 := ()
  return v3

def recv0_arm1 (v0 : UInt256) : FeM UInt256 := do
  let v1 := Field.saved
  let v2 ← advance_1 v1 v0
  return v2

-- END fe-lean-export

end

/-- A `mut self` method on a local takes the struct and returns it updated. -/
theorem advance_exec (c : Cursor) (amount : UInt256) (I : ExecutionEnv) (w : World) :
    (advance c amount).exec I w =
      (do let pos ← checkedAdd c.pos amount
          pure (c.pos, { c with pos := pos })).exec I w := by
  simp [advance]

/-- The `Sum` arm of the fixture, with each call replaced by what it does to the cursor:

```fe
var c = Cursor { pos: 0, base: 4 }
let a = c.advance(by: step)
c.skip(by: step)
var s = Span { start: c, len: step }
let b = s.start.advance(by: s.len)
a + b + s.start.end()
```
-/
def sumSpec (step : UInt256) : FeM UInt256 := do
  let first ← checkedAdd (UInt256.ofNat 0) step
  let skipped ← checkedAdd first (if 32 < step.toNat then UInt256.ofNat 32 else step)
  let last ← checkedAdd skipped step
  let ab ← checkedAdd (UInt256.ofNat 0) skipped
  let «end» ← checkedAdd last skipped
  checkedAdd ab «end»

/-- Writes through `mut` accesses to a local, to a field of a local, and across a join reach
    the reads after them. -/
theorem sum_exec (step : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm0 step).exec I w = (sumSpec step).exec I w := by
  have h32 : (UInt256.ofNat 32).toNat = 32 := rfl
  by_cases h : 32 < step.toNat <;> simp [recv0_arm0, advance, skip, «end», sumSpec, h, h32]

end FeProofs.Fixtures.LocalStruct

/-! ## `tuple`: tuple values, projections and a write to one field -/

namespace FeProofs.Fixtures.Tuple

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: tuple

def init : FeM Unit := do
  return ()

def swap (v0 : (UInt256 × UInt256 × Bool)) : FeM (UInt256 × UInt256 × Bool) := do
  let v1 := v0.snd.fst
  let v2 := v0.fst
  let v3 := v0.snd.snd
  return (v1, v2, v3)

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : (UInt256 × UInt256 × Bool) := default
  let mut r1 : (UInt256 × UInt256 × Bool) := default
  let v3 := true
  r1 := (v0, v1, v3)
  let v6 ← swap r1
  let v7 := v6
  r0 := v7
  let v8 := r0.snd.fst
  let v9 := (UInt256.ofNat 1)
  let v10 ← checkedAdd v8 v9
  r0 := { r0 with snd := { r0.snd with fst := v10 } }
  let v11 := ()
  let v12 := r0.snd.snd
  let b3 : (UInt256 × UInt256 × Bool) → (UInt256 × UInt256 × Bool) → UInt256 → FeM UInt256 := fun r0 r1 v2 => do
    let mut r0 := r0
    let mut r1 := r1
    return v2
  if v12 then
    let v13 := r0.fst
    let v14 := r0.snd.fst
    let v15 ← checkedSub v13 v14
    let v16 := v15
    b3 r0 r1 v16
  else
    let v17 := (UInt256.ofNat 0)
    let v18 := v17
    b3 r0 r1 v18

-- END fe-lean-export

end

/-- A tuple is a right-nested product: field 1 of three is `.snd.fst`. -/
theorem swap_eq (a b : UInt256) (flag : Bool) : swap (a, b, flag) = pure (b, a, flag) := rfl

/-- `var pair = swap((a, b, true)); pair.1 = pair.1 + 1; pair.0 - pair.1` -/
theorem swap_arm_exec (a b : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm0 a b).exec I w =
      (do let next ← checkedAdd a (UInt256.ofNat 1)
          checkedSub b next).exec I w := by
  simp [recv0_arm0, swap]

end FeProofs.Fixtures.Tuple

/-! ## `param_slot`: owned parameters the body assigns or borrows -/

namespace FeProofs.Fixtures.ParamSlot

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: param_slot

structure Cursor where
  pos : UInt256
  base : UInt256
deriving Inhabited

def init : FeM Unit := do
  return ()

def make (v0 : UInt256) : FeM Cursor := do
  let v1 := v0
  let v2 := (UInt256.ofNat 4)
  return (Cursor.mk v1 v2)

def «end» (v0 : Cursor) : FeM UInt256 := do
  let v1 := v0.pos
  let v2 := v0.base
  let v3 ← checkedAdd v1 v2
  return v3

def advance (v0 : Cursor) (v1 : UInt256) : FeM (UInt256 × Cursor) := do
  let mut v0 := v0
  let v2 := v0.pos
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  v0 := { v0 with pos := v5 }
  let v6 := ()
  return (v3, v0)

def c_end (v0 : Cursor) : FeM UInt256 := do
  let v1 ← «end» v0
  return v1

def consume (r0 : Cursor) (v0 : UInt256) : FeM UInt256 := do
  let mut r0 := r0
  let mut r1 : Cursor := default
  let (v2, v2_0) ← advance r0 v0
  r0 := v2_0
  let v3 ← make v0
  r1 := v3
  let v5 ← c_end r1
  let v6 ← checkedAdd v2 v5
  return v6

def bump (r0 : UInt256) : FeM UInt256 := do
  let mut r0 := r0
  let v0 := (UInt256.ofNat 1)
  let v1 := r0
  let v2 ← checkedAdd v1 v0
  let v3 := v2
  r0 := v3
  let v4 := ()
  let v5 := r0
  return v5

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : Cursor := default
  let v1 ← make v0
  r0 := v1
  let v3 ← «end» r0
  let v4 := (UInt256.ofNat 1)
  let v5 ← make v4
  let v6 ← consume v5 v0
  let v7 ← checkedAdd v3 v6
  let v8 ← bump v0
  let v9 ← checkedAdd v7 v8
  return v9

-- END fe-lean-export

end

/-- A `var` parameter is a slot that starts out holding the argument:
    `fn bump(var by: own u256) -> u256 { by += 1; by }`. -/
theorem bump_exec (amount : UInt256) (I : ExecutionEnv) (w : World) :
    (bump amount).exec I w = (checkedAdd amount (UInt256.ofNat 1)).exec I w := by
  simp [bump]

/-- `c.advance(by) + c_end(c: make(pos: by))` on an owned `c`. -/
theorem consume_exec (c : Cursor) (amount : UInt256) (I : ExecutionEnv) (w : World) :
    (consume c amount).exec I w =
      (do let _ ← checkedAdd c.pos amount
          let «end» ← checkedAdd amount (UInt256.ofNat 4)
          checkedAdd c.pos «end»).exec I w := by
  simp [consume, advance, make, c_end, «end»]

end FeProofs.Fixtures.ParamSlot

