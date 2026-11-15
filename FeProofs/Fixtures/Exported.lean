import FeProofs.Lib.Exported

/-!
# Exporter fixtures

Output of `fe-lean-export` on fixtures that have no bytecode proof (Fe branch `lean-export`,
`crates/lean-export/tests/golden/`), copied in by `scripts/sync_exported.py`.  The core and std
definitions the fixtures call are in `FeProofs/Lib/Exported.lean`.  This file checks that the
output elaborates, and that the control flow it prints means what the source says.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

/-! ## `helper_call`: a helper that takes contract state through `uses` -/

namespace FeProofs.Fixtures.HelperCall

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: helper_call

export Lib (StorageMap_locate_u256_u256)

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
  let l0 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v7
  let v8 ← load (Place.mk .storage l0.slot)
  let v9 ← checkedAdd v8 v6
  let l1 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v7
  store (Place.mk .storage l1.slot) v9
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

export Lib (StorageMap_locate_u256_u256)

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
    let l0 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v16
    let v17 ← load (Place.mk .storage l0.slot)
    let v18 ← checkedAdd v17 v15
    let l1 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v16
    store (Place.mk .storage l1.slot) v18
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

/-- `add` of the fixture, written with the `if` as an expression.  The entry of `hits` is
    where std's exported `locate` puts it:

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
  let hits := Field.store.field Layout.Store 1
  let entry ← StorageMap_locate_u256_u256 hits hits.slot amount
  let count ← checkedAdd (← load ⟨.storage, entry.slot⟩) (UInt256.ofNat 1)
  let entry ← StorageMap_locate_u256_u256 hits hits.slot amount
  store ⟨.storage, entry.slot⟩ count
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

def Cursor_advance (v0 : Cursor) (v1 : UInt256) : FeM (UInt256 × Cursor) := do
  let mut v0 := v0
  let v2 := v0.pos
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  v0 := { v0 with pos := v5 }
  let v6 := ()
  return (v3, v0)

def Cursor_skip (v0 : Cursor) (v1 : UInt256) : FeM (Unit × Cursor) := do
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
    let (v6, v6_0) ← Cursor_advance v0 v5
    v0 := v6_0
    let v7 := v6
    b3 v0
  else
    let (v8, v8_0) ← Cursor_advance v0 v1
    v0 := v8_0
    let v9 := v8
    b3 v0

def Cursor_end (v0 : Cursor) : FeM UInt256 := do
  let v1 := v0.pos
  let v2 := v0.base
  let v3 ← checkedAdd v1 v2
  return v3

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : Cursor := default
  let mut r1 : Span := default
  let v1 := (UInt256.ofNat 0)
  let v2 := (UInt256.ofNat 4)
  let v3 := (Cursor.mk v1 v2)
  let v4 := v3
  r0 := v4
  let (v6, v6_0) ← Cursor_advance r0 v0
  r0 := v6_0
  let v7 := v6
  let (v9, v9_0) ← Cursor_skip r0 v0
  r0 := v9_0
  let v10 := r0
  let v11 := v10
  let v12 := (Span.mk v11 v0)
  let v13 := v12
  r1 := v13
  let v14 := r1.len
  let (v16, v16_0) ← Cursor_advance r1.start v14
  r1 := { r1 with start := v16_0 }
  let v17 := v16
  let v18 ← checkedAdd v7 v17
  let v21 ← Cursor_end r1.start
  let v22 ← checkedAdd v18 v21
  return v22

def Cursor_advance_1 (v0 : Place) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← load (v0.field Layout.Cursor 0)
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  store (v0.field Layout.Cursor 0) v5
  let v6 := ()
  return v3

def recv0_arm1 (v0 : UInt256) : FeM UInt256 := do
  let v1 := Field.saved
  let v2 ← Cursor_advance_1 v1 v0
  return v2

-- END fe-lean-export

end

/-- A `mut self` method on a local takes the struct and returns it updated. -/
theorem advance_exec (c : Cursor) (amount : UInt256) (I : ExecutionEnv) (w : World) :
    (Cursor_advance c amount).exec I w =
      (do let pos ← checkedAdd c.pos amount
          pure (c.pos, { c with pos := pos })).exec I w := by
  simp [Cursor_advance]

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
  by_cases h : 32 < step.toNat <;> simp [recv0_arm0, Cursor_advance, Cursor_skip, Cursor_end, sumSpec, h, h32]

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
  let v4 := (v1, v2, v3)
  return v4

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : (UInt256 × UInt256 × Bool) := default
  let mut r1 : (UInt256 × UInt256 × Bool) := default
  let v3 := true
  let v4 := (v0, v1, v3)
  r1 := v4
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
  let v3 := (Cursor.mk v1 v2)
  return v3

def Cursor_end (v0 : Cursor) : FeM UInt256 := do
  let v1 := v0.pos
  let v2 := v0.base
  let v3 ← checkedAdd v1 v2
  return v3

def Cursor_advance (v0 : Cursor) (v1 : UInt256) : FeM (UInt256 × Cursor) := do
  let mut v0 := v0
  let v2 := v0.pos
  let v3 := v2
  let v4 := v1
  let v5 ← checkedAdd v3 v4
  v0 := { v0 with pos := v5 }
  let v6 := ()
  return (v3, v0)

def c_end (v0 : Cursor) : FeM UInt256 := do
  let v1 ← Cursor_end v0
  return v1

def consume (r0 : Cursor) (v0 : UInt256) : FeM UInt256 := do
  let mut r0 := r0
  let mut r1 : Cursor := default
  let (v2, v2_0) ← Cursor_advance r0 v0
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
  let v3 ← Cursor_end r0
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
  simp [consume, Cursor_advance, make, c_end, Cursor_end]

end FeProofs.Fixtures.ParamSlot

/-! ## `decode`: the std calldata decoder, `evm.decode_args<(u256, u256)>()` -/

namespace FeProofs.Fixtures.Decode

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: decode

export Lib (Evm_decode_args_tuple_u256_u256)

def init : FeM Unit := do
  return ()

def recv0_arm0 : FeM UInt256 := do
  let v1 ← Evm_decode_args_tuple_u256_u256
  let v2 := v1
  let v3 := v2.fst
  let v4 := v2.snd
  let v5 ← checkedAdd v3 v4
  return v5

-- END fe-lean-export

end

end FeProofs.Fixtures.Decode

/-! ## `encode`: the std ABI encoder, `revert(value: u256)` -/

namespace FeProofs.Fixtures.Encode

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: encode

export Lib (revert_u256)

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← revert_u256 v0
  let v1 : UInt256 := nomatch v1
  return v1

-- END fe-lean-export

end

end FeProofs.Fixtures.Encode

/-! ## `ints`: integers of every width, and the call's context -/

namespace FeProofs.Fixtures.Ints

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: ints

export Lib (Address_word Evm_address Evm_block_number Evm_origin Evm_value Wei Wei_as_wei downcast_truncate_i256_i8 downcast_unchecked_u256_i256)

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← IntTy.add (.u 8) v0 v1
  let v3 := v2
  let v4 := (UInt256.ofNat 1)
  let v5 := v3 >>> v4
  let v6 := (UInt256.ofNat 15)
  let v7 := v5 &&& v6
  let v8 := v7
  let v9 ← IntTy.sub (.u 8) v3 v8
  let v10 := (UInt256.ofNat 2)
  let v11 ← IntTy.mul (.u 8) v9 v10
  let v12 ← checkedDiv v11 v1
  let v13 := (UInt256.ofNat 7)
  let v14 ← checkedRem v12 v13
  return v14

def wrapping (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 := v0
  let v3 := v1
  let v4 := IntTy.mulW (.i 32) v2 v3
  let v5 := (UInt256.ofNat 3)
  let v6 := IntTy.shl (.i 32) v4 v5
  return v6

def recv0_arm1 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 := UInt256.sltBool v0 v1
  if v2 then
    let v3 ← IntTy.neg (.i 32) v0
    return v3
  else
    let v4 := ()
    let v5 := v4
    let v6 ← wrapping v0 v1
    let v7 ← IntTy.div (.i 32) v0 v1
    let v8 ← IntTy.add (.i 32) v6 v7
    let v9 ← IntTy.rem (.i 32) v0 v1
    let v10 ← IntTy.sub (.i 32) v8 v9
    let v11 := (IntTy.wrap (.i 256) (-5))
    let v12 ← IntTy.add (.i 32) v10 v11
    return v12

def recv0_arm2 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 := v1
  let v3 := v2
  let v4 ← downcast_truncate_i256_i8 v0
  let v5 := v4
  let v6 ← downcast_unchecked_u256_i256 v3
  let v7 := v6
  let v8 := (UInt256.ofNat 2)
  let v9 := IntTy.shr (.i 256) v0 v8
  let v10 := (UInt256.ofNat 2)
  let v11 ← IntTy.pow (.i 256) v9 v10
  let v12 := v5
  let v13 ← IntTy.add (.i 256) v11 v12
  let v14 ← IntTy.add (.i 256) v13 v7
  let v15 := IntTy.not (.i 256) v0
  let v16 ← IntTy.add (.i 256) v14 v15
  return v16

def recv0_arm3 : FeM UInt256 := do
  let mut r1 : UInt256 := default
  let mut r2 : Wei := default
  let mut r3 : UInt256 := default
  let v1 ← Evm_address
  r1 := v1
  let v2 := r1
  let v3 ← Address_word v2
  let v5 ← Evm_value
  r2 := v5
  let v6 := r2
  let v7 ← Wei_as_wei v6
  let v8 := v3 ^^^ v7
  let v10 ← Evm_origin
  r3 := v10
  let v11 := r3
  let v12 ← Address_word v11
  let v13 := v8 ^^^ v12
  let v15 ← Evm_block_number
  let v16 := v13 ^^^ v15
  return v16

-- END fe-lean-export

end

end FeProofs.Fixtures.Ints

/-! ## `enums`: enum values, `match`, and a write through a variant's field -/

namespace FeProofs.Fixtures.Enums

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: enums

export Lib (Option_u256 Option_u256.None Option_u256.Some)

inductive Shape where
  | Empty
  | Square (f0 : UInt256)
  | Rect (f0 : UInt256) (f1 : UInt256)
deriving Inhabited

def Shape.tag : Shape → UInt256
  | .Empty => UInt256.ofNat 0
  | .Square .. => UInt256.ofNat 1
  | .Rect .. => UInt256.ofNat 2

def Shape.Square_0 : Shape → UInt256
  | .Square f0 => f0
  | _ => default

def Shape.set_Square_0 (x : Shape) (v : UInt256) : Shape :=
  match x with
  | .Square f0 => .Square v
  | x => x

def Shape.Rect_0 : Shape → UInt256
  | .Rect f0 f1 => f0
  | _ => default

def Shape.set_Rect_0 (x : Shape) (v : UInt256) : Shape :=
  match x with
  | .Rect f0 f1 => .Rect v f1
  | x => x

def Shape.Rect_1 : Shape → UInt256
  | .Rect f0 f1 => f1
  | _ => default

def Shape.set_Rect_1 (x : Shape) (v : UInt256) : Shape :=
  match x with
  | .Rect f0 f1 => .Rect f0 v
  | x => x

def init : FeM Unit := do
  return ()

def shape (v0 : UInt256) (v1 : UInt256) : FeM Shape := do
  let v4 := v0
  let v5 := (UInt256.ofNat 0)
  let v6 := decide (v4 = v5)
  let b3 : Shape → FeM Shape := fun v2 => do
    return v2
  if v6 then
    let v7 := Shape.Empty
    let v8 := v7
    b3 v8
  else
    let v9 := v0
    let v10 := v1
    let v11 := decide (v9 = v10)
    let b6 : Shape → FeM Shape := fun v3 => do
      let v19 := v3
      b3 v19
    if v11 then
      let v12 := v0
      let v13 := Shape.Square v12
      let v14 := v13
      b6 v14
    else
      let v15 := v0
      let v16 := v1
      let v17 := Shape.Rect v15 v16
      let v18 := v17
      b6 v18

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v3 ← shape v0 v1
  let b1 : UInt256 → FeM UInt256 := fun v2 => do
    return v2
  match v3 with
  | .Empty =>
    let v4 := (UInt256.ofNat 0)
    let v5 := v4
    b1 v5
  | .Square .. =>
    let v6 := v3.Square_0
    let v7 := v6
    let v8 ← checkedMul v7 v7
    let v9 := v8
    b1 v9
  | .Rect .. =>
    let v10 := v3.Rect_0
    let v11 := v10
    let v12 := v3.Rect_1
    let v13 := v12
    let v14 ← checkedMul v11 v13
    let v15 := v14
    b1 v15

def halve (v0 : UInt256) : FeM Option_u256 := do
  let v2 := v0
  let v3 := (UInt256.ofNat 2)
  let v4 ← checkedRem v2 v3
  let v5 := (UInt256.ofNat 0)
  let v6 := decide (v4 = v5)
  let b3 : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  if v6 then
    let v7 := v0
    let v8 := (UInt256.ofNat 2)
    let v9 ← checkedDiv v7 v8
    let v10 := Option_u256.Some v9
    let v11 := v10
    b3 v11
  else
    let v12 := Option_u256.None
    let v13 := v12
    b3 v13

def recv0_arm1 (v0 : UInt256) : FeM UInt256 := do
  let v2 ← halve v0
  let b1 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v2 with
  | .Some .. =>
    let v3 := v2.Some_0
    let v4 := v3
    let v5 := v4
    b1 v5
  | _ =>
    let v6 := v0
    b1 v6

def recv0_arm2 (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : Shape := default
  let v2 := Shape.Square v0
  let v3 := v2
  r0 := v3
  let b3 : Shape → FeM UInt256 := fun r0 => do
    let mut r0 := r0
    let v13 := r0
    let b6 : Shape → UInt256 → FeM UInt256 := fun r0 v1 => do
      let mut r0 := r0
      return v1
    match v13 with
    | .Square .. =>
      let v14 := r0.Square_0
      let v15 := v14
      b6 r0 v15
    | _ =>
      let v16 := (UInt256.ofNat 0)
      let v17 := v16
      b6 r0 v17
  match r0 with
  | .Square .. =>
    let v6 := (UInt256.ofNat 1)
    let v7 := r0.Square_0
    let v8 ← checkedAdd v7 v6
    r0 := (r0.set_Square_0 v8)
    let v9 := ()
    let v10 := v9
    b3 r0
  | _ =>
    let v11 := ()
    let v12 := v11
    b3 r0

-- END fe-lean-export

end

/-- `area` multiplies the sides of whichever shape the arguments make. -/
theorem area_exec (width height : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm0 width height).exec I w =
      if width = UInt256.ofNat 0 then some (.ok (UInt256.ofNat 0, w))
      else (checkedMul width height).exec I w := by
  by_cases h0 : width = UInt256.ofNat 0
  · simp [recv0_arm0, shape, h0]
  · by_cases hs : width = height
    · subst hs
      simp [recv0_arm0, shape, Shape.Square_0, h0]
    · simp [recv0_arm0, shape, Shape.Rect_0, Shape.Rect_1, h0, hs]

/-- `grow` adds one to the side through the variant's field. -/
theorem grow_exec (side : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm2 side).exec I w = (checkedAdd side (UInt256.ofNat 1)).exec I w := by
  simp [recv0_arm2, Shape.Square_0, Shape.set_Square_0, checkedAdd]
  rfl

end FeProofs.Fixtures.Enums

/-! ## `loops`: a loop is a recursive local function, the least fixed point of its body -/

namespace FeProofs.Fixtures.Loops

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: loops

export Lib (Option_u256 Option_u256.None Option_u256.Some)

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let v1 := (UInt256.ofNat 0)
  let v2 := v1
  r0 := v2
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r1 := v4
  let rec b1 (r0 : UInt256) (r1 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let v5 := r1
    let v6 := v5
    let v7 := decide (v6.toNat < v0.toNat)
    if v7 then
      let v8 := (UInt256.ofNat 1)
      let v9 := r1
      let v10 ← checkedAdd v9 v8
      let v11 := v10
      r1 := v11
      let v12 := ()
      let v13 := r1
      let v14 := v13
      let v15 := r0
      let v16 ← checkedAdd v15 v14
      let v17 := v16
      r0 := v17
      let v18 := ()
      b1 r0 r1
    else
      let v19 := r0
      return v19
  partial_fixpoint
  b1 r0 r1

def step (v0 : UInt256) : FeM Option_u256 := do
  let v3 := v0
  let v4 := (UInt256.ofNat 1)
  let v5 := decide (v3 = v4)
  let b3 : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  if v5 then
    let v6 := Option_u256.None
    let v7 := v6
    b3 v7
  else
    let v8 := v0
    let v9 := (UInt256.ofNat 2)
    let v10 ← checkedRem v8 v9
    let v11 := (UInt256.ofNat 0)
    let v12 := decide (v10 = v11)
    let b6 : Option_u256 → FeM Option_u256 := fun v2 => do
      let v25 := v2
      b3 v25
    if v12 then
      let v13 := v0
      let v14 := (UInt256.ofNat 2)
      let v15 ← checkedDiv v13 v14
      let v16 := Option_u256.Some v15
      let v17 := v16
      b6 v17
    else
      let v18 := (UInt256.ofNat 3)
      let v19 := v0
      let v20 ← checkedMul v18 v19
      let v21 := (UInt256.ofNat 1)
      let v22 ← checkedAdd v20 v21
      let v23 := Option_u256.Some v22
      let v24 := v23
      b6 v24

def recv0_arm1 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let v2 := v0
  r0 := v2
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r1 := v4
  let rec b1 (r0 : UInt256) (r1 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let v5 := r1
    let v6 := v5
    let v7 := decide (v6 = v1)
    if v7 then
      return v1
    else
      let v8 := ()
      let v9 := v8
      let v10 := r0
      let v11 := v10
      let v12 ← step v11
      match (← pure v12) with
      | .Some .. =>
        let v13 := v12.Some_0
        let v14 := v13
        let v15 := v14
        r0 := v15
        let v16 := ()
        let v17 := (UInt256.ofNat 1)
        let v18 := r1
        let v19 ← checkedAdd v18 v17
        let v20 := v19
        r1 := v20
        let v21 := ()
        let v22 := v21
        b1 r0 r1
      | .None =>
        let v23 := r1
        return v23
  partial_fixpoint
  b1 r0 r1

-- END fe-lean-export

end

/-- `triangle(3)` runs the loop body three times and returns `1 + 2 + 3`. -/
theorem triangle_three (I : ExecutionEnv) (w : World) :
    (recv0_arm0 (UInt256.ofNat 3)).exec I w = some (.ok (UInt256.ofNat 6, w)) := by
  simp [recv0_arm0]
  iterate 4 (rw [recv0_arm0.b1]; simp +decide [checkedAdd])

end FeProofs.Fixtures.Loops

/-! ## `nested_loops`: loops in loops, and joins on the recursion of a loop

A join that an inner loop's exit enters from outside the inner loop, and that leads back to the
outer loop's head (`windows`: the shape of `small_power` in fevm's `modexp.fe`), is a recursive
local function of its own.  The values below are the source's, worked by hand; the export audit
compares the model with the bytecode on generated calls. -/

namespace FeProofs.Fixtures.NestedLoops

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: nested_loops

export Lib (Range_Known_0_Unknown Range_Known_0_Unknown.mk Range_Unknown_Unknown Range_Unknown_Unknown.mk Range_Unknown_Unknown_at Range_Unknown_Unknown_has Range_Unknown_Unknown_next Range_Unknown_Unknown_start Range_at_0 Range_has_0 Range_next_0 Range_start_0 downcast_truncate_u256_usize)

def init : FeM Unit := do
  return ()

def windows (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let mut r2 : Bool := default
  let mut r3 : Range_Unknown_Unknown := default
  let v4 := (UInt256.ofNat 1)
  let v5 := v4
  r0 := v5
  let v6 := (UInt256.ofNat 0)
  let v7 := v6
  r1 := v7
  let v8 := false
  let v9 := v8
  r2 := v9
  let rec b1 (r0 : UInt256) (r1 : UInt256) (r2 : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let mut r2 := r2
    let mut r3 := r3
    let v10 := r1
    let v11 := v10
    let v12 := v0
    let v13 := decide (v11.toNat < v12.toNat)
    if v13 then
      let v14 := r1
      let v15 := v14
      let v16 := v1
      let v17 ← checkedAdd v15 v16
      let v18 := (UInt256.ofNat 1)
      let v19 ← checkedAdd v17 v18
      let v20 := v0
      let v21 := decide (v19.toNat < v20.toNat)
      let b6 : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → UInt256 → FeM UInt256 := fun r0 r1 r2 r3 v2 => do
        let mut r0 := r0
        let mut r1 := r1
        let mut r2 := r2
        let mut r3 := r3
        let v31 := v2
        let v32 := r2
        let rec b9 (r0 : UInt256) (r1 : UInt256) (r2 : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
          let mut r0 := r0
          let mut r1 := r1
          let mut r2 := r2
          let mut r3 := r3
          let v59 := (UInt256.ofNat 2)
          let v60 ← checkedRem v31 v59
          let v61 := (UInt256.ofNat 1)
          let v62 := decide (v60 = v61)
          let b16 : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → FeM UInt256 := fun r0 r1 r2 r3 => do
            let mut r0 := r0
            let mut r1 := r1
            let mut r2 := r2
            let mut r3 := r3
            let v75 := v31
            r1 := v75
            let v76 := ()
            b1 r0 r1 r2 r3
          if v62 then
            let v63 := r0
            let v64 := v63
            let v65 := v31
            let v66 ← checkedAdd v64 v65
            let v67 := v66
            r0 := v67
            let v68 := ()
            let v69 := true
            let v70 := v69
            r2 := v70
            let v71 := ()
            let v72 := v71
            b16 r0 r1 r2 r3
          else
            let v73 := ()
            let v74 := v73
            b16 r0 r1 r2 r3
        partial_fixpoint
        if v32 then
          let v33 := r1
          let v34 := v33
          let v35 := ()
          let v36 := (Range_Unknown_Unknown.mk v34 v31)
          r3 := v36
          let v38 ← Range_Unknown_Unknown_start r3
          let v39 := v38
          let rec b10 (r0 : UInt256) (r1 : UInt256) (r2 : Bool) (r3 : Range_Unknown_Unknown) (v3 : UInt256) : FeM UInt256 := do
            let mut r0 := r0
            let mut r1 := r1
            let mut r2 := r2
            let mut r3 := r3
            let v41 ← Range_Unknown_Unknown_has r3 v3
            if v41 then
              let v43 ← Range_Unknown_Unknown_at r3 v3
              let v44 := r0
              let v45 := v44
              let v46 := (UInt256.ofNat 2)
              let v47 ← checkedMul v45 v46
              let v48 := (UInt256.ofNat 1000003)
              let v49 ← checkedRem v47 v48
              let v50 := v49
              r0 := v50
              let v51 := ()
              let v53 ← Range_Unknown_Unknown_next r3 v3
              let v54 := v53
              b10 r0 r1 r2 r3 v54
            else
              let v55 := ()
              let v56 := v55
              b9 r0 r1 r2 r3
          partial_fixpoint
          b10 r0 r1 r2 r3 v39
        else
          let v57 := ()
          let v58 := v57
          b9 r0 r1 r2 r3
      if v21 then
        let v22 := r1
        let v23 := v22
        let v24 := v1
        let v25 ← checkedAdd v23 v24
        let v26 := (UInt256.ofNat 1)
        let v27 ← checkedAdd v25 v26
        let v28 := v27
        b6 r0 r1 r2 r3 v28
      else
        let v29 := v0
        let v30 := v29
        b6 r0 r1 r2 r3 v30
    else
      let v77 := r0
      return v77
  partial_fixpoint
  b1 r0 r1 r2 r3

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← downcast_truncate_u256_usize v0
  let v3 ← downcast_truncate_u256_usize v1
  let v4 ← windows v2 v3
  return v4

def break_both (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let mut r2 : Bool := default
  let mut r3 : UInt256 := default
  let v1 := (UInt256.ofNat 0)
  let v2 := v1
  r0 := v2
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r1 := v4
  let v5 := false
  let v6 := v5
  r2 := v6
  let rec b1 (r0 : UInt256) (r1 : UInt256) (r2 : Bool) (r3 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let mut r2 := r2
    let mut r3 := r3
    let v7 := r0
    let v8 := v7
    let v9 := v0
    let v10 := decide (v8.toNat < v9.toNat)
    let b3 : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun r0 r1 r2 r3 => do
      let mut r0 := r0
      let mut r1 := r1
      let mut r2 := r2
      let mut r3 := r3
      let v49 := r1
      return v49
    if v10 then
      let v11 := (UInt256.ofNat 0)
      let v12 := v11
      r3 := v12
      let rec b4 (r0 : UInt256) (r1 : UInt256) (r2 : Bool) (r3 : UInt256) : FeM UInt256 := do
        let mut r0 := r0
        let mut r1 := r1
        let mut r2 := r2
        let mut r3 := r3
        let v13 := r3
        let v14 := v13
        let v15 := r0
        let v16 := decide (v14.toNat < v15.toNat)
        let b6 : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun r0 r1 r2 r3 => do
          let mut r0 := r0
          let mut r1 := r1
          let mut r2 := r2
          let mut r3 := r3
          let v41 := r2
          if v41 then
            b3 r0 r1 r2 r3
          else
            let v42 := ()
            let v43 := v42
            let v44 := (UInt256.ofNat 1)
            let v45 := r0
            let v46 ← checkedAdd v45 v44
            let v47 := v46
            r0 := v47
            let v48 := ()
            b1 r0 r1 r2 r3
        if v16 then
          let v17 := r0
          let v18 := v17
          let v19 := r3
          let v20 ← checkedMul v18 v19
          let v21 := (UInt256.ofNat 12)
          let v22 := decide (v20 = v21)
          if v22 then
            let v23 := r0
            let v24 := v23
            let v25 := (UInt256.ofNat 100)
            let v26 ← checkedMul v24 v25
            let v27 := r3
            let v28 ← checkedAdd v26 v27
            let v29 := v28
            r1 := v29
            let v30 := ()
            let v31 := true
            let v32 := v31
            r2 := v32
            let v33 := ()
            b6 r0 r1 r2 r3
          else
            let v34 := ()
            let v35 := v34
            let v36 := (UInt256.ofNat 1)
            let v37 := r3
            let v38 ← checkedAdd v37 v36
            let v39 := v38
            r3 := v39
            let v40 := ()
            b4 r0 r1 r2 r3
        else
          b6 r0 r1 r2 r3
      partial_fixpoint
      b4 r0 r1 r2 r3
    else
      b3 r0 r1 r2 r3
  partial_fixpoint
  b1 r0 r1 r2 r3

def recv0_arm1 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← break_both v0
  return v1

def continue_outer (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let mut r2 : UInt256 := default
  let mut r3 : Bool := default
  let v1 := (UInt256.ofNat 0)
  let v2 := v1
  r0 := v2
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r1 := v4
  let rec b1 (r0 : UInt256) (r1 : UInt256) (r2 : UInt256) (r3 : Bool) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let mut r2 := r2
    let mut r3 := r3
    let v5 := r0
    let v6 := v5
    let v7 := v0
    let v8 := decide (v6.toNat < v7.toNat)
    if v8 then
      let v9 := (UInt256.ofNat 1)
      let v10 := r0
      let v11 ← checkedAdd v10 v9
      let v12 := v11
      r0 := v12
      let v13 := ()
      let v14 := (UInt256.ofNat 0)
      let v15 := v14
      r2 := v15
      let v16 := false
      let v17 := v16
      r3 := v17
      let rec b4 (r0 : UInt256) (r1 : UInt256) (r2 : UInt256) (r3 : Bool) : FeM UInt256 := do
        let mut r0 := r0
        let mut r1 := r1
        let mut r2 := r2
        let mut r3 := r3
        let v18 := r2
        let v19 := v18
        let v20 := r0
        let v21 := decide (v19.toNat < v20.toNat)
        let b6 : UInt256 → UInt256 → UInt256 → Bool → FeM UInt256 := fun r0 r1 r2 r3 => do
          let mut r0 := r0
          let mut r1 := r1
          let mut r2 := r2
          let mut r3 := r3
          let v36 := r3
          if v36 then
            b1 r0 r1 r2 r3
          else
            let v37 := ()
            let v38 := v37
            let v39 := r0
            let v40 := v39
            let v41 := r1
            let v42 ← checkedAdd v41 v40
            let v43 := v42
            r1 := v43
            let v44 := ()
            b1 r0 r1 r2 r3
        if v21 then
          let v22 := r2
          let v23 := v22
          let v24 := (UInt256.ofNat 3)
          let v25 := decide (v23 = v24)
          if v25 then
            let v26 := true
            let v27 := v26
            r3 := v27
            let v28 := ()
            b6 r0 r1 r2 r3
          else
            let v29 := ()
            let v30 := v29
            let v31 := (UInt256.ofNat 1)
            let v32 := r2
            let v33 ← checkedAdd v32 v31
            let v34 := v33
            r2 := v34
            let v35 := ()
            b4 r0 r1 r2 r3
        else
          b6 r0 r1 r2 r3
      partial_fixpoint
      b4 r0 r1 r2 r3
    else
      let v45 := r1
      return v45
  partial_fixpoint
  b1 r0 r1 r2 r3

def recv0_arm2 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← continue_outer v0
  return v1

def return_inner (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let v1 := (UInt256.ofNat 0)
  let v2 := v1
  r0 := v2
  let rec b1 (r0 : UInt256) (r1 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let v3 := r0
    let v4 := v3
    let v5 := v0
    let v6 := decide (v4.toNat < v5.toNat)
    if v6 then
      let v7 := (UInt256.ofNat 0)
      let v8 := v7
      r1 := v8
      let rec b4 (r0 : UInt256) (r1 : UInt256) : FeM UInt256 := do
        let mut r0 := r0
        let mut r1 := r1
        let v9 := r1
        let v10 := v9
        let v11 := v0
        let v12 := decide (v10.toNat < v11.toNat)
        if v12 then
          let v13 := r0
          let v14 := v13
          let v15 := r1
          let v16 ← checkedAdd v14 v15
          let v17 := (UInt256.ofNat 7)
          let v18 := decide (v16 = v17)
          if v18 then
            let v19 := r0
            let v20 := v19
            let v21 := (UInt256.ofNat 10)
            let v22 ← checkedMul v20 v21
            let v23 := r1
            let v24 ← checkedAdd v22 v23
            return v24
          else
            let v25 := ()
            let v26 := v25
            let v27 := (UInt256.ofNat 1)
            let v28 := r1
            let v29 ← checkedAdd v28 v27
            let v30 := v29
            r1 := v30
            let v31 := ()
            b4 r0 r1
        else
          let v32 := (UInt256.ofNat 1)
          let v33 := r0
          let v34 ← checkedAdd v33 v32
          let v35 := v34
          r0 := v35
          let v36 := ()
          b1 r0 r1
      partial_fixpoint
      b4 r0 r1
    else
      let v37 := (UInt256.ofNat 0)
      return v37
  partial_fixpoint
  b1 r0 r1

def recv0_arm3 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← return_inner v0
  return v1

def three_levels (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let mut r2 : Range_Known_0_Unknown := default
  let mut r3 : Range_Known_0_Unknown := default
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r0 := v4
  let v5 := (UInt256.ofNat 0)
  let v6 := v0
  let v7 := ()
  let v8 := (Range_Known_0_Unknown.mk v7 v6)
  r2 := v8
  let v10 ← Range_start_0 r2
  let v11 := v10
  let rec b1 (r0 : UInt256) (r1 : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v1 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let mut r2 := r2
    let mut r3 := r3
    let v13 ← Range_has_0 r2 v1
    if v13 then
      let v15 ← Range_at_0 r2 v1
      let v16 := v15
      let v17 := (UInt256.ofNat 0)
      let v18 := ()
      let v19 := (Range_Known_0_Unknown.mk v18 v16)
      r3 := v19
      let v21 ← Range_start_0 r3
      let v22 := v21
      let rec b5 (r0 : UInt256) (r1 : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v2 : UInt256) : FeM UInt256 := do
        let mut r0 := r0
        let mut r1 := r1
        let mut r2 := r2
        let mut r3 := r3
        let v24 ← Range_has_0 r3 v2
        if v24 then
          let v26 ← Range_at_0 r3 v2
          let v27 := v26
          let v28 := (UInt256.ofNat 0)
          let v29 := v28
          r1 := v29
          let rec b9 (r0 : UInt256) (r1 : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) : FeM UInt256 := do
            let mut r0 := r0
            let mut r1 := r1
            let mut r2 := r2
            let mut r3 := r3
            let v30 := r1
            let v31 := v30
            let v32 := decide (v31.toNat < v27.toNat)
            if v32 then
              let v33 ← checkedAdd v16 v27
              let v34 := r1
              let v35 ← checkedAdd v33 v34
              let v36 := (UInt256.ofNat 3)
              let v37 ← checkedRem v35 v36
              let v38 := (UInt256.ofNat 0)
              let v39 := decide (v37 = v38)
              let b14 : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun r0 r1 r2 r3 => do
                let mut r0 := r0
                let mut r1 := r1
                let mut r2 := r2
                let mut r3 := r3
                let v52 := (UInt256.ofNat 1)
                let v53 := r1
                let v54 ← checkedAdd v53 v52
                let v55 := v54
                r1 := v55
                let v56 := ()
                b9 r0 r1 r2 r3
              if v39 then
                let v40 := (UInt256.ofNat 1)
                let v41 := r0
                let v42 ← checkedAdd v41 v40
                let v43 := v42
                r0 := v43
                let v44 := ()
                let v45 := v44
                b14 r0 r1 r2 r3
              else
                let v46 := (UInt256.ofNat 2)
                let v47 := r0
                let v48 ← checkedAdd v47 v46
                let v49 := v48
                r0 := v49
                let v50 := ()
                let v51 := v50
                b14 r0 r1 r2 r3
            else
              let v57 := (UInt256.ofNat 2)
              let v58 ← checkedRem v27 v57
              let v59 := (UInt256.ofNat 0)
              let v60 := decide (v58 = v59)
              let b17 : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun r0 r1 r2 r3 => do
                let mut r0 := r0
                let mut r1 := r1
                let mut r2 := r2
                let mut r3 := r3
                let v70 ← Range_next_0 r3 v2
                let v71 := v70
                b5 r0 r1 r2 r3 v71
              if v60 then
                let v61 := (UInt256.ofNat 10)
                let v62 := r0
                let v63 ← checkedAdd v62 v61
                let v64 := v63
                r0 := v64
                let v65 := ()
                let v66 := v65
                b17 r0 r1 r2 r3
              else
                let v67 := ()
                let v68 := v67
                b17 r0 r1 r2 r3
          partial_fixpoint
          b9 r0 r1 r2 r3
        else
          let v72 := ()
          let v74 ← Range_next_0 r2 v1
          let v75 := v74
          b1 r0 r1 r2 r3 v75
      partial_fixpoint
      b5 r0 r1 r2 r3 v22
    else
      let v76 := r0
      return v76
  partial_fixpoint
  b1 r0 r1 r2 r3 v11

def recv0_arm4 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← downcast_truncate_u256_usize v0
  let v2 ← three_levels v1
  return v2

-- END fe-lean-export

end

/-- The value a function returns from an empty world, if it returns. -/
def value (m : FeM UInt256) : Option Nat :=
  match m.exec default (World.init ∅ default) with
  | some (.ok (v, _)) => some v.toNat
  | _ => none

def w (n : Nat) : UInt256 := UInt256.ofNat n

#guard [(0, 1), (1, 0), (5, 1), (10, 2), (9, 0), (20, 3)].map (fun (n, k) =>
    value (windows (w n) (w k))) == [some 1, some 2, some 6, some 530, some 821, some 1]
#guard [0, 4, 5, 10].map (value ∘ break_both ∘ w) == [some 0, some 0, some 403, some 403]
#guard [0, 3, 4, 6].map (value ∘ continue_outer ∘ w) == [some 0, some 6, some 6, some 6]
#guard [0, 4, 8, 10].map (value ∘ return_inner ∘ w) == [some 0, some 0, some 7, some 7]
#guard [0, 3, 5].map (value ∘ three_levels ∘ w) == [some 0, some 21, some 76]

end FeProofs.Fixtures.NestedLoops

/-! ## `arrays`: array values, element reads and writes, and the index check -/

namespace FeProofs.Fixtures.Arrays

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: arrays

def init : FeM Unit := do
  return ()

def bump (v0 : (Vector UInt256 4)) (v1 : UInt256) (v2 : UInt256) : FeM (Unit × (Vector UInt256 4)) := do
  let mut v0 := v0
  let v3 := v2
  let v4 := v1
  checkIndex v4 4
  let v5 := v0[v4.toNat]!
  let v6 ← checkedAdd v5 v3
  checkIndex v4 4
  v0 := (v0.set! v4.toNat v6)
  let v7 := ()
  return ((), v0)

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : (Vector UInt256 4) := default
  let v2 := Vector.replicate 4 v1
  let v3 := v2
  r0 := v3
  let v4 := (UInt256.ofNat 7)
  let v5 := (UInt256.ofNat 0)
  checkIndex v5 4
  r0 := (r0.set! v5.toNat v4)
  let v6 := ()
  let v8 := (UInt256.ofNat 1)
  let (v9, v9_0) ← bump r0 v0 v8
  r0 := v9_0
  checkIndex v0 4
  let v10 := r0[v0.toNat]!
  let v11 := (UInt256.ofNat 3)
  checkIndex v11 4
  let v12 := r0[v11.toNat]!
  let v13 ← checkedAdd v10 v12
  return v13

def WEIGHTS : FeM (Vector UInt256 3) := do
  let v0 := (UInt256.ofNat 1)
  let v1 := (UInt256.ofNat 10)
  let v2 := (UInt256.ofNat 100)
  let v3 := #v[v0, v1, v2]
  return v3

def recv0_arm1 (v0 : (Vector UInt256 3)) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let mut r1 : UInt256 := default
  let v1 := (UInt256.ofNat 0)
  let v2 := v1
  r0 := v2
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  r1 := v4
  let rec b1 (r0 : UInt256) (r1 : UInt256) : FeM UInt256 := do
    let mut r0 := r0
    let mut r1 := r1
    let v5 := r1
    let v6 := v5
    let v7 := (UInt256.ofNat 3)
    let v8 := decide (v6.toNat < v7.toNat)
    if v8 then
      let v9 := r1
      checkIndex v9 3
      let v10 := v0[v9.toNat]!
      let v11 ← WEIGHTS
      let v12 := r1
      checkIndex v12 3
      let v13 := v11[v12.toNat]!
      let v14 ← checkedMul v10 v13
      let v15 := r0
      let v16 ← checkedAdd v15 v14
      let v17 := v16
      r0 := v17
      let v18 := ()
      let v19 := (UInt256.ofNat 1)
      let v20 := r1
      let v21 ← checkedAdd v20 v19
      let v22 := v21
      r1 := v22
      let v23 := ()
      b1 r0 r1
    else
      let v24 := r0
      return v24
  partial_fixpoint
  b1 r0 r1

-- END fe-lean-export

end

/- The constants the compiler folded: each is the value the exporter printed in its place. -/
-- BEGIN fe-lean-export: arrays.checks

set_option maxRecDepth 10000 in
example : WEIGHTS = pure #v[(UInt256.ofNat 1), (UInt256.ofNat 10), (UInt256.ofNat 100)] := rfl
-- END fe-lean-export

/-- `pick` with an index past the array panics with `Panic(0x32)` at the helper's check. -/
theorem pick_out_of_bounds (value : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm0 (UInt256.ofNat 4) value).exec I w = some (.error (.panic 0x32)) := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h4 : (UInt256.ofNat 4).toNat = 4 := rfl
  simp [recv0_arm0, bump, checkIndex, h0, h4]

/-- `pick(3, value)` bumps element 3 and reads it twice. -/
theorem pick_last (value : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm0 (UInt256.ofNat 3) value).exec I w =
      (do let bumped ← checkedAdd value (UInt256.ofNat 1)
          checkedAdd bumped bumped : FeM UInt256).exec I w := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h3 : (UInt256.ofNat 3).toNat = 3 := rfl
  have hread : ((Vector.replicate 4 value).set! 0 (UInt256.ofNat 7))[3] = value := rfl
  have hset (a : UInt256) :
      (((Vector.replicate 4 value).set! 0 (UInt256.ofNat 7)).set! 3 a)[3] = a := rfl
  simp [recv0_arm0, bump, checkIndex, h0, h3, hread, hset]

end FeProofs.Fixtures.Arrays

/-! ## `state`: packed fields, enums, arrays and transient storage in contract state -/

namespace FeProofs.Fixtures.State

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: state

export Lib (Layout.TSlot_bool)

def Field.packed : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Packed : Layout :=
  { storage := [0, 0, 0, 0, 1] }

structure Packed where
  flag : Bool
  small : UInt256
  delta : UInt256
  owner : UInt256
  total : UInt256
deriving Inhabited

def load_Packed (p : Place) : FeM Packed := do
  let f0 ← loadBoolAt (p.offset 0) ⟨0, 1, true⟩
  let f1 ← loadIntAt (.u 8) (p.offset 0) ⟨1, 1, true⟩
  let f2 ← loadIntAt (.i 16) (p.offset 0) ⟨2, 2, true⟩
  let f3 ← loadIntAt (.u 256) (p.offset 0) ⟨4, 20, true⟩
  let f4 ← load (p.offset 1)
  return (Packed.mk f0 f1 f2 f3 f4)

def store_Packed (p : Place) (v : Packed) : FeM Unit := do
  let b0 ← Lane.pack ⟨0, 1, true⟩ (.u 8) (Bool.toUInt256 v.flag)
  let b1 ← Lane.pack ⟨1, 1, true⟩ (.u 8) v.small
  let b2 ← Lane.pack ⟨2, 2, true⟩ (.i 16) v.delta
  let b3 ← Lane.pack ⟨4, 20, true⟩ (.u 256) v.owner
  store (p.offset 0) (packed [(0, b0), (1, b1), (2, b2), (4, b3)])
  store (p.offset 1) v.total

def Field.phase : Place :=
  .storage (UInt256.ofNat 2)

inductive Phase where
  | Idle
  | Running (f0 : UInt256) (f1 : UInt256)
  | Done (f0 : Bool)
deriving Inhabited

def Phase.tag : Phase → UInt256
  | .Idle => UInt256.ofNat 0
  | .Running .. => UInt256.ofNat 1
  | .Done .. => UInt256.ofNat 2

def Phase.Running_0 : Phase → UInt256
  | .Running f0 f1 => f0
  | _ => default

def Phase.set_Running_0 (x : Phase) (v : UInt256) : Phase :=
  match x with
  | .Running f0 f1 => .Running v f1
  | x => x

def Phase.Running_1 : Phase → UInt256
  | .Running f0 f1 => f1
  | _ => default

def Phase.set_Running_1 (x : Phase) (v : UInt256) : Phase :=
  match x with
  | .Running f0 f1 => .Running f0 v
  | x => x

def Phase.Done_0 : Phase → Bool
  | .Done f0 => f0
  | _ => default

def Phase.set_Done_0 (x : Phase) (v : Bool) : Phase :=
  match x with
  | .Done f0 => .Done v
  | x => x

def load_Phase (p : Place) : FeM Phase := do
  match (← loadTag 8 3 p) with
  | 0 => do
    return .Idle
  | 1 => do
    let f0 ← loadInt (.u 64) (p.offset 1)
    let f1 ← load (p.offset 2)
    return .Running f0 f1
  | _ => do
    let f0 ← loadBool (p.offset 1)
    return .Done f0

def store_Phase (p : Place) (v : Phase) : FeM Unit := do
  match v with
  | .Idle => do
    store p (UInt256.ofNat 0)
  | .Running f0 f1 => do
    store p (UInt256.ofNat 1)
    storeInt (.u 64) (p.offset 1) f0
    store (p.offset 2) f1
  | .Done f0 => do
    store p (UInt256.ofNat 2)
    storeBool (p.offset 1) f0

def Field.levels : Place :=
  .storage (UInt256.ofNat 5)

def Field.narrow : Place :=
  .storage (UInt256.ofNat 8)

def Field.lock : Place :=
  .storage (UInt256.ofNat 0)

def Field.alone : Place :=
  .storage (UInt256.ofNat 8)

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← loadIntAt (.i 16) (Field.packed.field Layout.Packed 2) ⟨2, 2, true⟩
  let v2 := v1
  storeIntAt (.i 16) (Field.packed.field Layout.Packed 2) ⟨2, 2, true⟩ v0
  let v3 := ()
  return v2

def recv0_arm1 (v0 : Bool) (v1 : UInt256) (v2 : UInt256) (v3 : UInt256) (v4 : UInt256) : FeM UInt256 := do
  let v5 ← load_Packed Field.packed
  let v6 := v5
  let v7 := (Packed.mk v0 v1 v2 v3 v4)
  store_Packed Field.packed v7
  let v8 := ()
  let v9 := v6.total
  return v9

def recv0_arm2 (v0 : UInt256) : FeM UInt256 := do
  let v3 ← load_Phase Field.phase
  let b1 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v3 with
  | .Idle =>
    let v4 := (UInt256.ofNat 1)
    let v5 := Phase.Running v4 v0
    store_Phase Field.phase v5
    let v6 := ()
    let v7 := (UInt256.ofNat 0)
    let v8 := v7
    b1 v8
  | .Running .. =>
    let v9 ← loadInt (.u 64) (Field.phase.offset 1)
    let v10 ← load (Field.phase.offset 2)
    let v11 := decide (v0.toNat < v10.toNat)
    let v12 := Phase.Done v11
    store_Phase Field.phase v12
    let v13 := ()
    let v14 := v10
    b1 v14
  | .Done .. =>
    let v15 ← loadBool (Field.phase.offset 1)
    let b7 : UInt256 → FeM UInt256 := fun v2 => do
      let v20 := v2
      b1 v20
    if v15 then
      let v16 := (UInt256.ofNat 1)
      let v17 := v16
      b7 v17
    else
      let v18 := (UInt256.ofNat 2)
      let v19 := v18
      b7 v19

def recv0_arm3 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  checkIndex v0 3
  let v2 ← loadInt (.u 8) (Field.levels.index 1 v0)
  let v3 := v2
  checkIndex v0 3
  storeInt (.u 8) (Field.levels.index 1 v0) v1
  let v4 := ()
  storeIntAt (.u 8) Field.narrow ⟨1, 1, true⟩ v3
  let v5 := ()
  let v6 ← loadIntAt (.u 8) Field.narrow ⟨1, 1, true⟩
  return v6

def recv0_arm4 : FeM Bool := do
  let v0 ← loadBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩
  let v1 := v0
  let v2 := true
  storeBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩ v2
  let v3 := ()
  storeBoolAt Field.alone ⟨0, 1, true⟩ v1
  let v4 := ()
  let v5 ← loadBoolAt Field.alone ⟨0, 1, true⟩
  return v5

-- END fe-lean-export

end

end FeProofs.Fixtures.State

/-! ## `entries`: map entries located by std's `StateIndex::locate`, as exported -/

namespace FeProofs.Fixtures.Entries

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: entries

export Lib (StorageMap_locate_bool_u256 StorageMap_locate_tuple_u256_u256_bool)

def Field.store : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Store : Layout :=
  { storage := [0, 1] }

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) : FeM Bool := do
  let v2 := (v0, v1)
  let l0 ← StorageMap_locate_tuple_u256_u256_bool (Field.store.field Layout.Store 0) (Field.store.field Layout.Store 0).slot v2
  let v3 ← loadBool (Place.mk .storage l0.slot)
  let v4 := v3
  let v5 := true
  let v6 := (v0, v1)
  let l1 ← StorageMap_locate_tuple_u256_u256_bool (Field.store.field Layout.Store 0) (Field.store.field Layout.Store 0).slot v6
  storeBool (Place.mk .storage l1.slot) v5
  let v7 := ()
  return v4

def recv0_arm1 (v0 : Bool) : FeM UInt256 := do
  let v1 := (UInt256.ofNat 1)
  let l0 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v0
  let v2 ← load (Place.mk .storage l0.slot)
  let v3 ← checkedAdd v2 v1
  let l1 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v0
  store (Place.mk .storage l1.slot) v3
  let v4 := ()
  let l2 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot v0
  let v5 ← load (Place.mk .storage l2.slot)
  return v5

-- END fe-lean-export

end

end FeProofs.Fixtures.Entries

/-! ## `wide`: a long definition cut into pieces that call one another -/

namespace FeProofs.Fixtures.Wide

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: wide

export Lib (CallData Evm_input Evm_return_value_Sol_u256 Sol_SELECTOR_SIZE Sol_validate_runtime_head abi_field_head_size_u256 decode_msg_field_from_Sol_u256_CallData len_CallData)

structure Sum where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256
  f : UInt256
  g : UInt256
  h : UInt256
  i : UInt256
  j : UInt256
deriving Inhabited

def init : FeM Unit := do
  return ()

def recv0_arm0 (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) (v3 : UInt256) (v4 : UInt256) (v5 : UInt256) (v6 : UInt256) (v7 : UInt256) (v8 : UInt256) (v9 : UInt256) : FeM UInt256 := do
  let v10 ← checkedAdd v0 v1
  let v11 ← checkedAdd v10 v2
  let v12 ← checkedAdd v11 v3
  let v13 ← checkedAdd v12 v4
  let v14 ← checkedAdd v13 v5
  let v15 ← checkedAdd v14 v6
  let v16 ← checkedAdd v15 v7
  let v17 ← checkedAdd v16 v8
  let v18 ← checkedAdd v17 v9
  return v18

def Sum_HEAD_SIZE : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd v0 v1
  let v3 ← abi_field_head_size_u256
  let v4 ← checkedAdd v2 v3
  let v5 ← abi_field_head_size_u256
  let v6 ← checkedAdd v4 v5
  let v7 ← abi_field_head_size_u256
  let v8 ← checkedAdd v6 v7
  let v9 ← abi_field_head_size_u256
  let v10 ← checkedAdd v8 v9
  let v11 ← abi_field_head_size_u256
  let v12 ← checkedAdd v10 v11
  let v13 ← abi_field_head_size_u256
  let v14 ← checkedAdd v12 v13
  let v15 ← abi_field_head_size_u256
  let v16 ← checkedAdd v14 v15
  let v17 ← abi_field_head_size_u256
  let v18 ← checkedAdd v16 v17
  let v19 ← abi_field_head_size_u256
  let v20 ← checkedAdd v18 v19
  return v20

def Sum_decode_from_CallData_k5 (v5 : UInt256) (v10 : UInt256) (v17 : UInt256) (v26 : UInt256) (v37 : UInt256) (v50 : UInt256) (v65 : UInt256) (v82 : UInt256) (v101 : UInt256) (v121 : UInt256) : FeM Sum := do
  let v122 := v121
  let v123 := (Sum.mk v5 v10 v17 v26 v37 v50 v65 v82 v101 v122)
  return v123

def Sum_decode_from_CallData_k4 (v0 : CallData) (v1 : UInt256) (v3 : UInt256) (v5 : UInt256) (v10 : UInt256) (v17 : UInt256) (v26 : UInt256) (v37 : UInt256) (v50 : UInt256) (v65 : UInt256) (v82 : UInt256) (v97 : UInt256) : FeM Sum := do
  let v98 ← abi_field_head_size_u256
  let v99 ← checkedAdd v97 v98
  let v100 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v99 v3
  let v101 := v100
  let v102 := v1
  let v103 ← abi_field_head_size_u256
  let v104 ← checkedAdd v102 v103
  let v105 ← abi_field_head_size_u256
  let v106 ← checkedAdd v104 v105
  let v107 ← abi_field_head_size_u256
  let v108 ← checkedAdd v106 v107
  let v109 ← abi_field_head_size_u256
  let v110 ← checkedAdd v108 v109
  let v111 ← abi_field_head_size_u256
  let v112 ← checkedAdd v110 v111
  let v113 ← abi_field_head_size_u256
  let v114 ← checkedAdd v112 v113
  let v115 ← abi_field_head_size_u256
  let v116 ← checkedAdd v114 v115
  let v117 ← abi_field_head_size_u256
  let v118 ← checkedAdd v116 v117
  let v119 ← abi_field_head_size_u256
  let v120 ← checkedAdd v118 v119
  let v121 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v120 v3
  Sum_decode_from_CallData_k5 v5 v10 v17 v26 v37 v50 v65 v82 v101 v121

def Sum_decode_from_CallData_k3 (v0 : CallData) (v1 : UInt256) (v3 : UInt256) (v5 : UInt256) (v10 : UInt256) (v17 : UInt256) (v26 : UInt256) (v37 : UInt256) (v50 : UInt256) (v65 : UInt256) (v72 : UInt256) (v73 : UInt256) : FeM Sum := do
  let v74 ← checkedAdd v72 v73
  let v75 ← abi_field_head_size_u256
  let v76 ← checkedAdd v74 v75
  let v77 ← abi_field_head_size_u256
  let v78 ← checkedAdd v76 v77
  let v79 ← abi_field_head_size_u256
  let v80 ← checkedAdd v78 v79
  let v81 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v80 v3
  let v82 := v81
  let v83 := v1
  let v84 ← abi_field_head_size_u256
  let v85 ← checkedAdd v83 v84
  let v86 ← abi_field_head_size_u256
  let v87 ← checkedAdd v85 v86
  let v88 ← abi_field_head_size_u256
  let v89 ← checkedAdd v87 v88
  let v90 ← abi_field_head_size_u256
  let v91 ← checkedAdd v89 v90
  let v92 ← abi_field_head_size_u256
  let v93 ← checkedAdd v91 v92
  let v94 ← abi_field_head_size_u256
  let v95 ← checkedAdd v93 v94
  let v96 ← abi_field_head_size_u256
  let v97 ← checkedAdd v95 v96
  Sum_decode_from_CallData_k4 v0 v1 v3 v5 v10 v17 v26 v37 v50 v65 v82 v97

def Sum_decode_from_CallData_k2 (v0 : CallData) (v1 : UInt256) (v3 : UInt256) (v5 : UInt256) (v10 : UInt256) (v17 : UInt256) (v26 : UInt256) (v37 : UInt256) (v49 : UInt256) : FeM Sum := do
  let v50 := v49
  let v51 := v1
  let v52 ← abi_field_head_size_u256
  let v53 ← checkedAdd v51 v52
  let v54 ← abi_field_head_size_u256
  let v55 ← checkedAdd v53 v54
  let v56 ← abi_field_head_size_u256
  let v57 ← checkedAdd v55 v56
  let v58 ← abi_field_head_size_u256
  let v59 ← checkedAdd v57 v58
  let v60 ← abi_field_head_size_u256
  let v61 ← checkedAdd v59 v60
  let v62 ← abi_field_head_size_u256
  let v63 ← checkedAdd v61 v62
  let v64 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v63 v3
  let v65 := v64
  let v66 := v1
  let v67 ← abi_field_head_size_u256
  let v68 ← checkedAdd v66 v67
  let v69 ← abi_field_head_size_u256
  let v70 ← checkedAdd v68 v69
  let v71 ← abi_field_head_size_u256
  let v72 ← checkedAdd v70 v71
  let v73 ← abi_field_head_size_u256
  Sum_decode_from_CallData_k3 v0 v1 v3 v5 v10 v17 v26 v37 v50 v65 v72 v73

def Sum_decode_from_CallData_k1 (v0 : CallData) (v1 : UInt256) (v3 : UInt256) (v5 : UInt256) (v10 : UInt256) (v17 : UInt256) (v25 : UInt256) : FeM Sum := do
  let v26 := v25
  let v27 := v1
  let v28 ← abi_field_head_size_u256
  let v29 ← checkedAdd v27 v28
  let v30 ← abi_field_head_size_u256
  let v31 ← checkedAdd v29 v30
  let v32 ← abi_field_head_size_u256
  let v33 ← checkedAdd v31 v32
  let v34 ← abi_field_head_size_u256
  let v35 ← checkedAdd v33 v34
  let v36 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v35 v3
  let v37 := v36
  let v38 := v1
  let v39 ← abi_field_head_size_u256
  let v40 ← checkedAdd v38 v39
  let v41 ← abi_field_head_size_u256
  let v42 ← checkedAdd v40 v41
  let v43 ← abi_field_head_size_u256
  let v44 ← checkedAdd v42 v43
  let v45 ← abi_field_head_size_u256
  let v46 ← checkedAdd v44 v45
  let v47 ← abi_field_head_size_u256
  let v48 ← checkedAdd v46 v47
  let v49 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v48 v3
  Sum_decode_from_CallData_k2 v0 v1 v3 v5 v10 v17 v26 v37 v49

def Sum_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Sum := do
  let v2 ← len_CallData v0
  let v3 := v2
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v3
  let v5 := v4
  let v6 := v1
  let v7 ← abi_field_head_size_u256
  let v8 ← checkedAdd v6 v7
  let v9 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v8 v3
  let v10 := v9
  let v11 := v1
  let v12 ← abi_field_head_size_u256
  let v13 ← checkedAdd v11 v12
  let v14 ← abi_field_head_size_u256
  let v15 ← checkedAdd v13 v14
  let v16 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v15 v3
  let v17 := v16
  let v18 := v1
  let v19 ← abi_field_head_size_u256
  let v20 ← checkedAdd v18 v19
  let v21 ← abi_field_head_size_u256
  let v22 ← checkedAdd v20 v21
  let v23 ← abi_field_head_size_u256
  let v24 ← checkedAdd v22 v23
  let v25 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v24 v3
  Sum_decode_from_CallData_k1 v0 v1 v3 v5 v10 v17 v25

def decode_from_prechecked_head_Sum_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM Sum := do
  let v3 ← Sum_decode_from_CallData v0 v1
  return v3

def decode_runtime_args_Evm_Sol_Sum : FeM Sum := do
  let mut r0 : CallData := default
  let v2 ← Evm_input
  let v3 := v2
  r0 := v3
  let v4 ← Sol_SELECTOR_SIZE
  let v5 := v4
  let v6 := r0
  let v7 ← len_CallData v6
  let v8 := v7
  let v9 ← Sum_HEAD_SIZE
  let v10 ← Sol_validate_runtime_head v8 v5 v9
  let v11 := r0
  let v12 ← decode_from_prechecked_head_Sum_Sol_CallData v11 v5 v8
  return v12

def recv0_arm0_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Sum
  let result ← recv0_arm0 message.a message.b message.c message.d message.e message.f message.g message.h message.i message.j
  Evm_return_value_Sol_u256 result

def runtime : FeM Empty := do
  let size ← calldatasize
  if size.toNat < 4 then
    revertEmpty
  else
    let selector ← calldataSelector
    if selector = UInt256.ofNat 0x460e9674 then
      recv0_arm0_entry
    else
      revertEmpty

def init_entry (args : ByteArray) : FeM ByteArray := do
  nonPayable
  let _ ← init
  return ByteArray.empty

-- END fe-lean-export

end

/- The constants the compiler folded: each is the value the exporter printed in its place. -/
-- BEGIN fe-lean-export: wide.checks

set_option maxRecDepth 10000 in
example : Sum_HEAD_SIZE = pure (UInt256.ofNat 320) := rfl
-- END fe-lean-export

end FeProofs.Fixtures.Wide

/-! ## `projections`: a granted place, a grant with a slide, and a grant into a local -/

namespace FeProofs.Fixtures.Projections

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: projections

def Field.cell : Place :=
  .storage (UInt256.ofNat 0)

def Layout.Cell : Layout :=
  { storage := [0] }

def init : FeM Unit := do
  return ()

def Cell_slot (v0 : Place) : FeM Place := do
  let v1 := (v0.field Layout.Cell 0)
  return v1

def recv0_arm0 (v0 : UInt256) : FeM UInt256 := do
  let v1 := Field.cell
  let v2 ← Cell_slot v1
  let v3 ← load v2
  let v4 ← checkedAdd v3 v0
  store v2 v4
  let v5 := ()
  let v6 ← load (Field.cell.field Layout.Cell 0)
  return v6

def Cell_get (v0 : Place) : FeM UInt256 := do
  let v1 ← load (v0.field Layout.Cell 0)
  return v1

def Cell_set (v0 : Place) (v1 : UInt256) : FeM Unit := do
  let v2 := v1
  store (v0.field Layout.Cell 0) v2
  let v3 := ()
  return ()

def Cell_cached (v0 : Place) : FeM (UInt256 × (UInt256 → FeM Unit)) := do
  let mut r0 : UInt256 := default
  let v1 := v0
  let v2 ← Cell_get v1
  let v3 := v2
  r0 := v3
  let slide : UInt256 → FeM Unit := fun g => do
    let mut r0 := r0
    r0 := g
    let v5 := r0
    let v6 := v5
    let v7 ← Cell_set v0 v6
    return ()
  return (r0, slide)

def recv0_arm1 (v0 : UInt256) : FeM UInt256 := do
  let mut v2 : UInt256 := default
  let v1 := Field.cell
  let (v2_g, v2_k) ← Cell_cached v1
  v2 := v2_g
  let v3 := v2
  let v4 ← checkedAdd v3 v0
  v2 := v4
  let _ ← v2_k v2
  let v5 := ()
  let v6 ← load (Field.cell.field Layout.Cell 0)
  return v6

def first (v0 : (UInt256 × UInt256)) : FeM (UInt256 × (UInt256 → FeM (UInt256 × UInt256))) := do
  let mut v0 := v0
  let slide : UInt256 → FeM (UInt256 × UInt256) := fun g => do
    let mut v0 := v0
    v0 := { v0 with fst := g }
    return v0
  return (v0.fst, slide)

def recv0_arm2 (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let mut r0 : (UInt256 × UInt256) := default
  let mut v5 : UInt256 := default
  let v2 := (v0, v1)
  let v3 := v2
  r0 := v3
  let (v5_g, v5_k) ← first r0
  v5 := v5_g
  let v6 := v5
  let v7 ← checkedAdd v6 v1
  v5 := v7
  let v5_0 ← v5_k v5
  r0 := v5_0
  let v8 := ()
  let v9 := r0.fst
  return v9

-- END fe-lean-export

end

/-- Writing through a grant of a local whose slide stores it does what writing through the place
    itself does. -/
theorem slide_exec (by_ : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm1 by_).exec I w = (recv0_arm0 by_).exec I w := by
  simp [recv0_arm0, recv0_arm1, Cell_slot, Cell_cached, Cell_get, Cell_set]

/-- A write through a grant into the caller's local comes back when the session ends. -/
theorem local_exec (a b : UInt256) (I : ExecutionEnv) (w : World) :
    (recv0_arm2 a b).exec I w = (checkedAdd a b).exec I w := by
  simp [recv0_arm2, first]

end FeProofs.Fixtures.Projections
