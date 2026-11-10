import Fe.EVM.Int

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
  let v3 := Cursor.mk v1 v2
  let v4 := v3
  r0 := v4
  let (v6, v6_0) ← advance r0 v0
  r0 := v6_0
  let v7 := v6
  let (v9, v9_0) ← skip r0 v0
  r0 := v9_0
  let v10 := r0
  let v11 := v10
  let v12 := Span.mk v11 v0
  let v13 := v12
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
  let v3 := Cursor.mk v1 v2
  return v3

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

/-! ## `decode`: the std calldata decoder, `evm.decode_args<(u256, u256)>()` -/

namespace FeProofs.Fixtures.Decode

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: decode

structure CallData where
  base : UInt256
deriving Inhabited

def init : FeM Unit := do
  return ()

def new : FeM CallData := do
  let v0 := (UInt256.ofNat 0)
  let v1 := CallData.mk v0
  return v1

def input : FeM CallData := do
  let v1 ← new
  return v1

def to_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def IS_SIGNED : FeM Bool := do
  let v0 := false
  return v0

def U64_MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 18446744073709551615)
  return v0

def MASK : FeM UInt256 := do
  let v0 ← U64_MASK
  return v0

def SIGN_BIT : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  return v0

def U256_MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)
  return v0

def sign_extend (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) : FeM UInt256 := do
  let v4 := v0
  let v5 := v1
  let v6 := v4 &&& v5
  let v7 := v6
  let v8 := v2
  let v9 := v7 &&& v8
  let v10 := (UInt256.ofNat 0)
  let v11 := decide (v9 ≠ v10)
  let b3 : UInt256 → FeM UInt256 := fun v3 => do
    return v3
  if v11 then
    let v12 ← U256_MASK
    let v13 := v1
    let v14 := v12 ^^^ v13
    let v15 := v7 ||| v14
    let v16 := v15
    b3 v16
  else
    let v17 := v7
    b3 v17

def from_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := truncate 64 v0
  return v1

def downcast_truncate_u256_u64 (v0 : UInt256) : FeM UInt256 := do
  let v2 ← to_word v0
  let v3 := v2
  let v4 ← IS_SIGNED
  let b3 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  if v4 then
    let v5 ← MASK
    let v6 ← SIGN_BIT
    let v7 ← sign_extend v3 v5 v6
    let v8 ← from_word v7
    let v9 := v8
    b3 v9
  else
    let v10 ← MASK
    let v11 := v3 &&& v10
    let v12 ← from_word v11
    let v13 := v12
    b3 v13

def size (v0 : CallData) : FeM UInt256 := do
  let v2 ← calldatasize
  let v3 := v2
  let v4 := v0.base
  let v5 := decide (v3.toNat < v4.toNat)
  let b3 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  if v5 then
    let v6 := (UInt256.ofNat 0)
    let v7 := v6
    b3 v7
  else
    let v8 := v0.base
    let v9 ← checkedSub v3 v8
    let v10 ← downcast_truncate_u256_u64 v9
    let v11 := v10
    b3 v11

def len_CallData (v0 : CallData) : FeM UInt256 := do
  let v1 ← size v0
  let v2 := v1
  return v2

def IS_DYNAMIC : FeM Bool := do
  let v0 := false
  return v0

def HEAD_SIZE : FeM UInt256 := do
  let v0 := (UInt256.ofNat 32)
  return v0

def abi_field_head_size_u256 : FeM UInt256 := do
  let v0 ← IS_DYNAMIC
  if v0 then
    let v1 := (UInt256.ofNat 32)
    return v1
  else
    let v2 := ()
    let v3 := v2
    let v4 ← HEAD_SIZE
    return v4

def HEAD_SIZE_u256_u256 : FeM UInt256 := do
  let v0 ← abi_field_head_size_u256
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd v0 v1
  return v2

def decode_error : FeM Empty := do
  let v0 ← revertEmpty
  nomatch v0

def checked_frame_end_Sol (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) : FeM UInt256 := do
  let v3 := v0
  let v4 := v2
  let v5 := decide (v4.toNat < v3.toNat)
  let b1 : FeM UInt256 := do
    let v16 ← decode_error
    nomatch v16
  if v5 then
    b1
  else
    let v6 := v1
    let v7 := v2
    let v8 := v0
    let v9 := v7 - v8
    let v10 := decide (v9.toNat < v6.toNat)
    if v10 then
      b1
    else
      let v11 := ()
      let v12 := v11
      let v13 := v0
      let v14 := v1
      let v15 := v13 + v14
      return v15

def word_at (v0 : CallData) (v1 : UInt256) : FeM UInt256 := do
  let v2 := v0.base
  let v3 := v1
  let v4 := v2 + v3
  let v5 ← calldataload v4
  return v5

def checked_tail_Sol (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 := v1
  let v3 := (UInt256.ofNat 0)
  let v4 := v3
  let v5 := ~~~v4
  let v6 := v0
  let v7 := v5 - v6
  let v8 := decide (v7.toNat < v2.toNat)
  if v8 then
    let v9 ← decode_error
    nomatch v9
  else
    let v10 := ()
    let v11 := v10
    let v12 := v0
    let v13 := v1
    let v14 := v12 + v13
    return v14

def decode_from_Sol_CallData (v0 : CallData) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← word_at v0 v1
  return v2

def decode_from_bounded_u256_Sol_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM UInt256 := do
  let v3 ← HEAD_SIZE
  let v4 ← checked_frame_end_Sol v1 v3 v2
  let v5 ← decode_from_Sol_CallData v0 v1
  return v5

def decode_field_from_prechecked_head_Sol_u256_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) (v3 : UInt256) : FeM UInt256 := do
  let v4 ← IS_DYNAMIC
  if v4 then
    let v5 ← word_at v0 v2
    let v6 := v5
    let v7 ← checked_tail_Sol v1 v6
    let v8 := v7
    let v9 ← decode_from_bounded_u256_Sol_CallData v0 v8 v3
    return v9
  else
    let v10 := ()
    let v11 := v10
    let v12 ← decode_from_Sol_CallData v0 v2
    return v12

def decode_from_prechecked_head_Sol_u256_u256_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM (UInt256 × UInt256) := do
  let mut r0 : UInt256 := default
  let v3 := v1
  let v4 := v3
  r0 := v4
  let v5 := r0
  let v6 := v5
  let v7 ← decode_field_from_prechecked_head_Sol_u256_CallData v0 v1 v6 v2
  let v8 := v7
  let v9 ← abi_field_head_size_u256
  let v10 := r0
  let v11 ← checkedAdd v10 v9
  let v12 := v11
  r0 := v12
  let v13 := ()
  let v14 := r0
  let v15 := v14
  let v16 ← decode_field_from_prechecked_head_Sol_u256_CallData v0 v1 v15 v2
  let v17 := v16
  let v18 := (v8, v17)
  return v18

def decode_frame_from_Sol_u256_u256_CallData (v0 : CallData) (v1 : UInt256) (v2 : UInt256) : FeM (UInt256 × UInt256) := do
  let v3 ← HEAD_SIZE_u256_u256
  let v4 ← checked_frame_end_Sol v1 v3 v2
  let v5 ← decode_from_prechecked_head_Sol_u256_u256_CallData v0 v1 v2
  return v5

def decode_input_at_u256_u256_CallData (v0 : CallData) (v1 : UInt256) : FeM (UInt256 × UInt256) := do
  let v2 ← len_CallData v0
  let v3 := v2
  let v4 ← decode_frame_from_Sol_u256_u256_CallData v0 v1 v3
  return v4

def decode_args_u256_u256 : FeM (UInt256 × UInt256) := do
  let mut r0 : CallData := default
  let v1 ← input
  r0 := v1
  let v2 := (UInt256.ofNat 4)
  let v3 := v2
  let v4 := r0
  let v5 ← decode_input_at_u256_u256_CallData v4 v3
  return v5

def recv0_arm0 : FeM UInt256 := do
  let v1 ← decode_args_u256_u256
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

structure MemBuffer where
  ptr : UInt256
  len : UInt256
  capacity : UInt256
deriving Inhabited

structure AbiFrame where
  ptr : UInt256
  len : UInt256
deriving Inhabited

def init : FeM Unit := do
  return ()

def HEAD_SIZE : FeM UInt256 := do
  let v0 := (UInt256.ofNat 32)
  return v0

def payload_size_u256 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← HEAD_SIZE
  return v1

def IS_DYNAMIC : FeM Bool := do
  let v0 := false
  return v0

def abi_field_size_u256 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← payload_size_u256 v0
  let v2 := v1
  let v3 ← IS_DYNAMIC
  if v3 then
    let v4 := (UInt256.ofNat 32)
    let v5 ← checkedAdd v4 v2
    return v5
  else
    let v6 := ()
    let v7 := v6
    return v2

def abi_single_root_size_u256 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← abi_field_size_u256 v0
  return v1

def max : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 := ~~~v0
  return v1

def PANIC_OUT_OF_MEMORY : FeM UInt256 := do
  let v0 := (UInt256.ofNat 65)
  return v0

def word_to_usize (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def allocation_len (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  let v2 ← max
  let v3 := v2
  let v4 := decide (v3.toNat < v1.toNat)
  if v4 then
    let v5 ← PANIC_OUT_OF_MEMORY
    let v6 ← panicCode v5
    nomatch v6
  else
    let v7 := ()
    let v8 := v7
    let v9 ← word_to_usize v0
    return v9

def max_1 : FeM UInt256 := do
  let v0 := (UInt256.ofNat 18446744073709551615)
  return v0

def to_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  let v2 := v1
  return v2

def IS_SIGNED : FeM Bool := do
  let v0 := false
  return v0

def MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  let v1 := ~~~v0
  let v2 := v1
  return v2

def from_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def I256_SIGN_BIT : FeM UInt256 := do
  let v0 := (UInt256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968)
  return v0

def SIGN_BIT : FeM UInt256 := do
  let v0 := (UInt256.ofNat 0)
  return v0

def U256_MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)
  return v0

def sign_extend (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) : FeM UInt256 := do
  let v4 := v0
  let v5 := v1
  let v6 := v4 &&& v5
  let v7 := v6
  let v8 := v2
  let v9 := v7 &&& v8
  let v10 := (UInt256.ofNat 0)
  let v11 := decide (v9 ≠ v10)
  let b3 : UInt256 → FeM UInt256 := fun v3 => do
    return v3
  if v11 then
    let v12 ← U256_MASK
    let v13 := v1
    let v14 := v12 ^^^ v13
    let v15 := v7 ||| v14
    let v16 := v15
    b3 v16
  else
    let v17 := v7
    b3 v17

def downcast_saturate_u64_usize (v0 : UInt256) : FeM UInt256 := do
  let mut r0 : UInt256 := default
  let v8 ← to_word v0
  let v9 := v8
  let v10 ← IS_SIGNED
  let v11 := !v10
  let b3 : UInt256 → UInt256 → FeM UInt256 := fun r0 v1 => do
    let mut r0 := r0
    return v1
  if v11 then
    let v12 := v9
    r0 := v12
    let v13 ← IS_SIGNED
    let b6 : UInt256 → FeM UInt256 := fun r0 => do
      let mut r0 := r0
      let v24 := r0
      let v25 := v24
      let v26 ← MASK
      let v27 := decide (v26.toNat < v25.toNat)
      let b10 : UInt256 → UInt256 → FeM UInt256 := fun r0 v2 => do
        let mut r0 := r0
        let v35 := v2
        b3 r0 v35
      if v27 then
        let v28 ← MASK
        let v29 ← from_word v28
        let v30 := v29
        b10 r0 v30
      else
        let v31 := r0
        let v32 := v31
        let v33 ← from_word v32
        let v34 := v33
        b10 r0 v34
    let b5 : UInt256 → FeM UInt256 := fun r0 => do
      let mut r0 := r0
      let v22 := ()
      let v23 := v22
      b6 r0
    if v13 then
      let v14 ← I256_SIGN_BIT
      let v15 := v9 &&& v14
      let v16 := (UInt256.ofNat 0)
      let v17 := decide (v15 ≠ v16)
      if v17 then
        let v18 := (UInt256.ofNat 0)
        let v19 := v18
        r0 := v19
        let v20 := ()
        let v21 := v20
        b6 r0
      else
        b5 r0
    else
      b5 r0
  else
    let v36 ← SIGN_BIT
    let v37 ← MASK
    let v38 ← SIGN_BIT
    let v39 ← sign_extend v36 v37 v38
    let v40 := v39
    let v41 ← SIGN_BIT
    let v42 := (UInt256.ofNat 1)
    let v43 ← checkedSub v41 v42
    let v44 := v43
    let v45 := v40
    let v46 := v45
    let v47 := v44
    let v48 := v47
    let v49 ← IS_SIGNED
    let b13 : UInt256 → UInt256 → FeM UInt256 := fun r0 v3 => do
      let mut r0 := r0
      let v77 := v3
      b3 r0 v77
    if v49 then
      let v50 := v9
      let v51 := v50
      let v52 := UInt256.sltBool v51 v46
      let b16 : UInt256 → UInt256 → FeM UInt256 := fun r0 v4 => do
        let mut r0 := r0
        let v61 := v4
        b13 r0 v61
      if v52 then
        let v53 ← from_word v40
        let v54 := v53
        b16 r0 v54
      else
        let v55 := UInt256.sgtBool v51 v48
        let b19 : UInt256 → UInt256 → FeM UInt256 := fun r0 v5 => do
          let mut r0 := r0
          let v60 := v5
          b16 r0 v60
        if v55 then
          let v56 ← from_word v44
          let v57 := v56
          b19 r0 v57
        else
          let v58 ← from_word v9
          let v59 := v58
          b19 r0 v59
    else
      let v62 ← I256_SIGN_BIT
      let v63 := v9 &&& v62
      let v64 := (UInt256.ofNat 0)
      let v65 := decide (v63 ≠ v64)
      let b22 : UInt256 → UInt256 → FeM UInt256 := fun r0 v6 => do
        let mut r0 := r0
        let v76 := v6
        b13 r0 v76
      if v65 then
        let v66 ← from_word v44
        let v67 := v66
        b22 r0 v67
      else
        let v68 := v9
        let v69 := v68
        let v70 := UInt256.sgtBool v69 v48
        let b25 : UInt256 → UInt256 → FeM UInt256 := fun r0 v7 => do
          let mut r0 := r0
          let v75 := v7
          b22 r0 v75
        if v70 then
          let v71 ← from_word v44
          let v72 := v71
          b25 r0 v72
        else
          let v73 ← from_word v9
          let v74 := v73
          b25 r0 v74

def MAX_ALLOCATION : FeM UInt256 := do
  let v0 ← max_1
  let v1 ← downcast_saturate_u64_usize v0
  return v1

def alloc_bytes (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  let v2 ← MAX_ALLOCATION
  let v3 := decide (v2.toNat < v1.toNat)
  if v3 then
    let v4 ← PANIC_OUT_OF_MEMORY
    let v5 ← panicCode v4
    nomatch v5
  else
    let v6 := ()
    let v7 := v6
    let v8 ← alloc v0
    return v8

def new_uninit (v0 : UInt256) : FeM MemBuffer := do
  let v1 ← alloc_bytes v0
  let v2 := v0
  let v3 := v0
  let v4 := MemBuffer.mk v1 v2 v3
  return v4

def zero_bytes (v0 : UInt256) (v1 : UInt256) : FeM Unit := do
  let v2 ← zeroMem v0 v1
  return ()

def new (v0 : UInt256) : FeM MemBuffer := do
  let v1 ← new_uninit v0
  let v2 := v1
  let v3 := v2.ptr
  let v4 ← zero_bytes v3 v0
  return v2

def ptr (v0 : MemBuffer) : FeM UInt256 := do
  let v1 := v0.ptr
  return v1

def from_raw_parts (v0 : UInt256) (v1 : UInt256) : FeM AbiFrame := do
  let v2 := v0
  let v3 := v1
  let v4 := AbiFrame.mk v2 v3
  return v4

def abi_field_head_size_u256 : FeM UInt256 := do
  let v0 ← IS_DYNAMIC
  if v0 then
    let v1 := (UInt256.ofNat 32)
    return v1
  else
    let v2 := ()
    let v3 := v2
    let v4 ← HEAD_SIZE
    return v4

def abi_single_root_head_size_u256 : FeM UInt256 := do
  let v0 ← abi_field_head_size_u256
  return v0

def PANIC_INDEX_OUT_OF_BOUNDS : FeM UInt256 := do
  let v0 := (UInt256.ofNat 50)
  return v0

def index_out_of_bounds : FeM Empty := do
  let v0 ← PANIC_INDEX_OUT_OF_BOUNDS
  let v1 ← panicCode v0
  nomatch v1

def ptr_offset (v0 : UInt256) (v1 : UInt256) : FeM UInt256 := do
  let v2 ← word_to_usize v1
  let v3 := v0 + v2
  return v3

def tail (v0 : AbiFrame) (v1 : UInt256) : FeM AbiFrame := do
  let v2 := v1
  let v3 := v0.len
  let v4 := decide (v3.toNat < v2.toNat)
  if v4 then
    let v5 ← index_out_of_bounds
    nomatch v5
  else
    let v6 := ()
    let v7 := v6
    let v8 := v0.ptr
    let v9 ← ptr_offset v8 v1
    let v10 := v0.len
    let v11 := v1
    let v12 := v10 - v11
    let v13 := AbiFrame.mk v9 v12
    return v13

def len (v0 : AbiFrame) : FeM UInt256 := do
  let v1 := v0.len
  return v1

def slice (v0 : AbiFrame) (v1 : UInt256) (v2 : UInt256) : FeM AbiFrame := do
  let v3 := v1
  let v4 := v0.len
  let v5 := decide (v4.toNat < v3.toNat)
  let b1 : FeM AbiFrame := do
    let v17 ← index_out_of_bounds
    nomatch v17
  if v5 then
    b1
  else
    let v6 := v2
    let v7 := v0.len
    let v8 := v1
    let v9 := v7 - v8
    let v10 := decide (v9.toNat < v6.toNat)
    if v10 then
      b1
    else
      let v11 := ()
      let v12 := v11
      let v13 := v0.ptr
      let v14 ← ptr_offset v13 v1
      let v15 := v2
      let v16 := AbiFrame.mk v14 v15
      return v16

def cast_u8_u256 (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  let v2 := v1
  return v2

def store_word (v0 : UInt256) (v1 : UInt256) : FeM Unit := do
  let v2 := v1
  let v3 ← cast_u8_u256 v0
  mstore v3 v2
  let v4 := ()
  return ()

def store_word_1 (v0 : AbiFrame) (v1 : UInt256) (v2 : UInt256) : FeM Unit := do
  let v3 := (UInt256.ofNat 32)
  let v4 ← slice v0 v1 v3
  let v5 := v4
  let v6 := v5.ptr
  let v7 ← store_word v6 v2
  return ()

def encode_Sol (v0 : UInt256) (v1 : AbiFrame) : FeM Unit := do
  let v2 := (UInt256.ofNat 0)
  let v3 ← store_word_1 v1 v2 v0
  return ()

def encode_field_Sol_u256 (v0 : UInt256) (v1 : AbiFrame) (v2 : UInt256) (r0 : AbiFrame) : FeM AbiFrame := do
  let mut r0 := r0
  let mut r1 : AbiFrame := default
  let mut r2 : AbiFrame := default
  let v3 ← IS_DYNAMIC
  if v3 then
    let v4 ← payload_size_u256 v0
    let v5 := v4
    let v6 ← len v1
    let v8 ← len r0
    let v9 := v6 - v8
    let v10 ← store_word_1 v1 v2 v9
    let v11 := (UInt256.ofNat 0)
    let v13 ← slice r0 v11 v5
    r1 := v13
    let v15 ← encode_Sol v0 r1
    let v17 ← tail r0 v5
    return v17
  else
    let v18 := ()
    let v19 := v18
    let v20 ← HEAD_SIZE
    let v21 ← slice v1 v2 v20
    r2 := v21
    let v23 ← encode_Sol v0 r2
    let v24 := r0
    return v24

def encode_single_root_alloc_Sol_u256 (v0 : UInt256) : FeM MemBuffer := do
  let mut r0 : MemBuffer := default
  let mut r1 : AbiFrame := default
  let v1 ← abi_single_root_size_u256 v0
  let v2 := v1
  let v3 ← allocation_len v2
  let v4 ← new v3
  let v5 := v4
  r0 := v5
  let v7 ← ptr r0
  let v8 ← from_raw_parts v7 v2
  let v9 := v8
  r1 := v9
  let v10 := (UInt256.ofNat 0)
  let v11 ← abi_single_root_head_size_u256
  let v13 ← tail r1 v11
  let v15 ← encode_field_Sol_u256 v0 r1 v10 v13
  let v16 := r0
  return v16

def len_1 (v0 : MemBuffer) : FeM UInt256 := do
  let v1 := v0.len
  return v1

def revert_u256 (v0 : UInt256) : FeM Empty := do
  let mut r0 : MemBuffer := default
  let v1 ← encode_single_root_alloc_Sol_u256 v0
  let v2 := v1
  r0 := v2
  let v4 ← ptr r0
  let v6 ← len_1 r0
  let v7 := v6
  let v8 ← revertData v4 v7
  nomatch v8

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

structure Wei where
  amount : UInt256
deriving Inhabited

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

def to_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def IS_SIGNED : FeM Bool := do
  let v0 := true
  return v0

def U8_MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 255)
  return v0

def MASK : FeM UInt256 := do
  let v0 ← U8_MASK
  return v0

def I8_SIGN_BIT : FeM UInt256 := do
  let v0 := (UInt256.ofNat 128)
  return v0

def SIGN_BIT : FeM UInt256 := do
  let v0 ← I8_SIGN_BIT
  return v0

def U256_MASK : FeM UInt256 := do
  let v0 := (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)
  return v0

def sign_extend (v0 : UInt256) (v1 : UInt256) (v2 : UInt256) : FeM UInt256 := do
  let v4 := v0
  let v5 := v1
  let v6 := v4 &&& v5
  let v7 := v6
  let v8 := v2
  let v9 := v7 &&& v8
  let v10 := (UInt256.ofNat 0)
  let v11 := decide (v9 ≠ v10)
  let b3 : UInt256 → FeM UInt256 := fun v3 => do
    return v3
  if v11 then
    let v12 ← U256_MASK
    let v13 := v1
    let v14 := v12 ^^^ v13
    let v15 := v7 ||| v14
    let v16 := v15
    b3 v16
  else
    let v17 := v7
    b3 v17

def from_word (v0 : UInt256) : FeM UInt256 := do
  let v1 := IntTy.cast (.u 256) (.i 8) v0
  return v1

def downcast_truncate_i256_i8 (v0 : UInt256) : FeM UInt256 := do
  let v2 ← to_word v0
  let v3 := v2
  let v4 ← IS_SIGNED
  let b3 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  if v4 then
    let v5 ← MASK
    let v6 ← SIGN_BIT
    let v7 ← sign_extend v3 v5 v6
    let v8 ← from_word v7
    let v9 := v8
    b3 v9
  else
    let v10 ← MASK
    let v11 := v3 &&& v10
    let v12 ← from_word v11
    let v13 := v12
    b3 v13

def from_word_1 (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def downcast_unchecked_u256_i256 (v0 : UInt256) : FeM UInt256 := do
  let v1 ← to_word v0
  let v2 := v1
  let v3 ← from_word_1 v2
  return v3

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

def address : FeM UInt256 := do
  let v1 ← selfAddress
  let v2 := v1
  return v2

def word (v0 : UInt256) : FeM UInt256 := do
  let v1 := v0
  return v1

def wei (v0 : UInt256) : FeM Wei := do
  let v1 := v0
  let v2 := Wei.mk v1
  return v2

def value : FeM Wei := do
  let v1 ← callvalue
  let v2 ← wei v1
  return v2

def as_wei (v0 : Wei) : FeM UInt256 := do
  let v1 := v0.amount
  return v1

def origin_1 : FeM UInt256 := do
  let v1 ← origin
  let v2 := v1
  return v2

def block_number : FeM UInt256 := do
  let v1 ← blockNumber
  return v1

def recv0_arm3 : FeM UInt256 := do
  let mut r1 : UInt256 := default
  let mut r2 : Wei := default
  let mut r3 : UInt256 := default
  let v1 ← address
  r1 := v1
  let v2 := r1
  let v3 ← word v2
  let v5 ← value
  r2 := v5
  let v6 := r2
  let v7 ← as_wei v6
  let v8 := v3 ^^^ v7
  let v10 ← origin_1
  r3 := v10
  let v11 := r3
  let v12 ← word v11
  let v13 := v8 ^^^ v12
  let v15 ← block_number
  let v16 := v13 ^^^ v15
  return v16

-- END fe-lean-export

end

end FeProofs.Fixtures.Ints
