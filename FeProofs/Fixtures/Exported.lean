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

/-- The `init` of contract `Counter`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `helper_call::add<Store>` -/
def add_Store («by» : UInt256) : FeM UInt256 := do
  let v1 ← load (Field.store.field Layout.Store 0)
  let next ← checkedAdd v1 «by»
  store (Field.store.field Layout.Store 0) next
  let l0 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot «by»
  let v8 ← load (Place.mk .storage l0.slot)
  let v9 ← checkedAdd v8 (UInt256.ofNat 1)
  let l1 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot «by»
  store (Place.mk .storage l1.slot) v9
  return next

/-- `Bump { by } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump («by» : UInt256) : FeM UInt256 := do
  let v1 ← add_Store «by»
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

/-- The `init` of contract `Counter`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `join::add<Store>` -/
def add_Store («by» : UInt256) : FeM UInt256 := do
  let v4 := decide ((UInt256.ofNat 10).toNat < «by».toNat)
  let b3 : UInt256 → FeM UInt256 := fun next => do
    store (Field.store.field Layout.Store 0) next
    let l0 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot «by»
    let v17 ← load (Place.mk .storage l0.slot)
    let v18 ← checkedAdd v17 (UInt256.ofNat 1)
    let l1 ← StorageMap_locate_u256_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot «by»
    store (Place.mk .storage l1.slot) v18
    return next
  if v4 then
    let v5 ← load (Field.store.field Layout.Store 0)
    let v7 ← checkedAdd v5 (UInt256.ofNat 10)
    b3 v7
  else
    let v9 ← load (Field.store.field Layout.Store 0)
    let v11 ← checkedAdd v9 «by»
    b3 v11

/-- `Bump { by } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump («by» : UInt256) : FeM UInt256 := do
  let v1 ← add_Store «by»
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

/-- The `init` of contract `Walker`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Cursor::advance` -/
def Cursor_advance (self : Cursor) («by» : UInt256) : FeM (UInt256 × Cursor) := do
  let mut self := self
  let «at» := self.pos
  let v5 ← checkedAdd «at» «by»
  self := { self with pos := v5 }
  return («at», self)

/-- `Cursor::skip` -/
def Cursor_skip (self : Cursor) («by» : UInt256) : FeM (Unit × Cursor) := do
  let mut self := self
  let v4 := decide ((UInt256.ofNat 32).toNat < «by».toNat)
  let b3 : Cursor → FeM (Unit × Cursor) := fun self => do
    let mut self := self
    let v10 := self.pos
    self := { self with base := v10 }
    return ((), self)
  if v4 then
    let (v6, v6_0) ← Cursor_advance self (UInt256.ofNat 32)
    self := v6_0
    b3 self
  else
    let (v8, v8_0) ← Cursor_advance self «by»
    self := v8_0
    b3 self

/-- `Cursor::end` -/
def Cursor_end (self : Cursor) : FeM UInt256 := do
  let v1 := self.pos
  let v2 := self.base
  let v3 ← checkedAdd v1 v2
  return v3

/-- `Sum { step } -> u256`, selector `0x188b85b4` (`sum(uint256)`) -/
def recv_Sum (step : UInt256) : FeM UInt256 := do
  let mut c : Cursor := default
  let mut s : Span := default
  let c_3 := (Cursor.mk (UInt256.ofNat 0) (UInt256.ofNat 4))
  c := c_3
  let (a, a_0) ← Cursor_advance c step
  c := a_0
  let (v9, v9_0) ← Cursor_skip c step
  c := v9_0
  let c_10 := c
  let s_12 := (Span.mk c_10 step)
  s := s_12
  let v14 := s.len
  let (b, b_0) ← Cursor_advance s.start v14
  s := { s with start := b_0 }
  let v18 ← checkedAdd a b
  let v21 ← Cursor_end s.start
  let v22 ← checkedAdd v18 v21
  return v22

/-- `Cursor::advance` -/
def Cursor_advance_1 (self : Place) («by» : UInt256) : FeM UInt256 := do
  let «at» ← load (self.field Layout.Cursor 0)
  let v5 ← checkedAdd «at» «by»
  store (self.field Layout.Cursor 0) v5
  return «at»

/-- `Bump { step } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump (step : UInt256) : FeM UInt256 := do
  let v1 := Field.saved
  let v2 ← Cursor_advance_1 v1 step
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
    (recv_Sum step).exec I w = (sumSpec step).exec I w := by
  have h32 : (UInt256.ofNat 32).toNat = 32 := rfl
  by_cases h : 32 < step.toNat <;> simp [recv_Sum, Cursor_advance, Cursor_skip, Cursor_end, sumSpec, h, h32]

end FeProofs.Fixtures.LocalStruct

/-! ## `tuple`: tuple values, projections and a write to one field -/

namespace FeProofs.Fixtures.Tuple

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: tuple

/-- The `init` of contract `Pairs`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `tuple::swap` -/
def swap (pair : (UInt256 × UInt256 × Bool)) : FeM (UInt256 × UInt256 × Bool) := do
  let v1 := pair.snd.fst
  let v2 := pair.fst
  let v3 := pair.snd.snd
  let v4 := (v1, v2, v3)
  return v4

/-- `Swap { a, b } -> u256`, selector `0xd96073cf` (`swap(uint256,uint256)`) -/
def recv_Swap (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let mut pair : (UInt256 × UInt256 × Bool) := default
  let mut r1 : (UInt256 × UInt256 × Bool) := default
  let v4 := (a, b, true)
  r1 := v4
  let pair_6 ← swap r1
  pair := pair_6
  let v8 := pair.snd.fst
  let v10 ← checkedAdd v8 (UInt256.ofNat 1)
  pair := { pair with snd := { pair.snd with fst := v10 } }
  let v12 := pair.snd.snd
  let b3 : (UInt256 × UInt256 × Bool) → (UInt256 × UInt256 × Bool) → UInt256 → FeM UInt256 := fun pair r1 v2 => do
    let mut pair := pair
    let mut r1 := r1
    return v2
  if v12 then
    let v13 := pair.fst
    let v14 := pair.snd.fst
    let v15 ← checkedSub v13 v14
    b3 pair r1 v15
  else
    b3 pair r1 (UInt256.ofNat 0)

-- END fe-lean-export

end

/-- A tuple is a right-nested product: field 1 of three is `.snd.fst`. -/
theorem swap_eq (a b : UInt256) (flag : Bool) : swap (a, b, flag) = pure (b, a, flag) := rfl

/-- `var pair = swap((a, b, true)); pair.1 = pair.1 + 1; pair.0 - pair.1` -/
theorem swap_arm_exec (a b : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Swap a b).exec I w =
      (do let next ← checkedAdd a (UInt256.ofNat 1)
          checkedSub b next).exec I w := by
  simp [recv_Swap, swap]

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

/-- The `init` of contract `Walker`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `param_slot::make` -/
def make (pos : UInt256) : FeM Cursor := do
  let v3 := (Cursor.mk pos (UInt256.ofNat 4))
  return v3

/-- `Cursor::end` -/
def Cursor_end (self : Cursor) : FeM UInt256 := do
  let v1 := self.pos
  let v2 := self.base
  let v3 ← checkedAdd v1 v2
  return v3

/-- `Cursor::advance` -/
def Cursor_advance (self : Cursor) («by» : UInt256) : FeM (UInt256 × Cursor) := do
  let mut self := self
  let «at» := self.pos
  let v5 ← checkedAdd «at» «by»
  self := { self with pos := v5 }
  return («at», self)

/-- `param_slot::c_end` -/
def c_end (c : Cursor) : FeM UInt256 := do
  let v1 ← Cursor_end c
  return v1

/-- `param_slot::consume` -/
def consume (c : Cursor) («by» : UInt256) : FeM UInt256 := do
  let mut c := c
  let mut r1 : Cursor := default
  let (v2, v2_0) ← Cursor_advance c «by»
  c := v2_0
  let v3 ← make «by»
  r1 := v3
  let v5 ← c_end r1
  let v6 ← checkedAdd v2 v5
  return v6

/-- `param_slot::bump` -/
def bump («by» : UInt256) : FeM UInt256 := do
  let mut «by» := «by»
  let by_1 := «by»
  let by_2 ← checkedAdd by_1 (UInt256.ofNat 1)
  «by» := by_2
  let by_5 := «by»
  return by_5

/-- `Sum { step } -> u256`, selector `0x188b85b4` (`sum(uint256)`) -/
def recv_Sum (step : UInt256) : FeM UInt256 := do
  let mut r0 : Cursor := default
  let v1 ← make step
  r0 := v1
  let v3 ← Cursor_end r0
  let v5 ← make (UInt256.ofNat 1)
  let v6 ← consume v5 step
  let v7 ← checkedAdd v3 v6
  let v8 ← bump step
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

/-- The `init` of contract `Decoder`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Probe -> u256`, selector `0xb74af5a9` (`probe()`) -/
def recv_Probe : FeM UInt256 := do
  let args ← Evm_decode_args_tuple_u256_u256
  let v3 := args.fst
  let v4 := args.snd
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

/-- The `init` of contract `Encoder`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Probe { value } -> u256`, selector `0xdb082440` (`probe(uint256)`) -/
def recv_Probe (value : UInt256) : FeM UInt256 := do
  let v1 ← revert_u256 value
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

/-- The `init` of contract `Ints`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Narrow { a, b } -> u8`, selector `0x741ef9d5` (`narrow(uint8,uint8)`) -/
def recv_Narrow (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let sum ← IntTy.add (.u 8) a b
  let v5 := sum >>> (UInt256.ofNat 1)
  let low := v5 &&& (UInt256.ofNat 15)
  let v9 ← IntTy.sub (.u 8) sum low
  let v11 ← IntTy.mul (.u 8) v9 (UInt256.ofNat 2)
  let v12 ← checkedDiv v11 b
  let v14 ← checkedRem v12 (UInt256.ofNat 7)
  return v14

/-- `ints::wrapping` -/
def wrapping (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let v4 := IntTy.mulW (.i 32) a b
  let v6 := IntTy.shl (.i 32) v4 (UInt256.ofNat 3)
  return v6

/-- `Signed { a, b } -> i32`, selector `0x6effafad` (`signed(int32,int32)`) -/
def recv_Signed (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let v2 := UInt256.sltBool a b
  if v2 then
    let v3 ← IntTy.neg (.i 32) a
    return v3
  else
    let v6 ← wrapping a b
    let v7 ← IntTy.div (.i 32) a b
    let v8 ← IntTy.add (.i 32) v6 v7
    let v9 ← IntTy.rem (.i 32) a b
    let v10 ← IntTy.sub (.i 32) v8 v9
    let v12 ← IntTy.add (.i 32) v10 (IntTy.wrap (.i 256) (-5))
    return v12

/-- `Mixed { a, b } -> i256`, selector `0x728ac8e2` (`mixed(int256,uint16)`) -/
def recv_Mixed (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let wide := b
  let small ← downcast_truncate_i256_i8 a
  let bits ← downcast_unchecked_u256_i256 wide
  let v9 := IntTy.shr (.i 256) a (UInt256.ofNat 2)
  let v11 ← IntTy.pow (.i 256) v9 (UInt256.ofNat 2)
  let v12 := small
  let v13 ← IntTy.add (.i 256) v11 v12
  let v14 ← IntTy.add (.i 256) v13 bits
  let v15 := IntTy.not (.i 256) a
  let v16 ← IntTy.add (.i 256) v14 v15
  return v16

/-- `Context -> u256`, selector `0xd0496d6a` (`context()`) -/
def recv_Context : FeM UInt256 := do
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

/-- The `init` of contract `Enums`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `enums::shape` -/
def shape (width : UInt256) (height : UInt256) : FeM Shape := do
  let v6 := decide (width = (UInt256.ofNat 0))
  let b3 : Shape → FeM Shape := fun v2 => do
    return v2
  if v6 then
    let v7 := Shape.Empty
    b3 v7
  else
    let v11 := decide (width = height)
    let b6 : Shape → FeM Shape := fun v3 => do
      b3 v3
    if v11 then
      let v13 := Shape.Square width
      b6 v13
    else
      let v17 := Shape.Rect width height
      b6 v17

/-- `Area { width, height } -> u256`, selector `0x15529a52` (`area(uint256,uint256)`) -/
def recv_Area (width_0 : UInt256) (height_1 : UInt256) : FeM UInt256 := do
  let v3 ← shape width_0 height_1
  let b1 : UInt256 → FeM UInt256 := fun v2 => do
    return v2
  match v3 with
  | .Empty =>
    b1 (UInt256.ofNat 0)
  | .Square .. =>
    let side := v3.Square_0
    let v8 ← checkedMul side side
    b1 v8
  | .Rect .. =>
    let width_10 := v3.Rect_0
    let height_12 := v3.Rect_1
    let v14 ← checkedMul width_10 height_12
    b1 v14

/-- `enums::halve` -/
def halve (value : UInt256) : FeM Option_u256 := do
  let v4 ← checkedRem value (UInt256.ofNat 2)
  let v6 := decide (v4 = (UInt256.ofNat 0))
  let b3 : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  if v6 then
    let v9 ← checkedDiv value (UInt256.ofNat 2)
    let v10 := Option_u256.Some v9
    b3 v10
  else
    let v12 := Option_u256.None
    b3 v12

/-- `Half { value } -> u256`, selector `0xdee6088b` (`half(uint256)`) -/
def recv_Half (value : UInt256) : FeM UInt256 := do
  let v2 ← halve value
  let b1 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v2 with
  | .Some .. =>
    let half := v2.Some_0
    b1 half
  | _ =>
    b1 value

/-- `Grow { side } -> u256`, selector `0x28531f06` (`grow(uint256)`) -/
def recv_Grow (side_0 : UInt256) : FeM UInt256 := do
  let mut current : Shape := default
  let current_2 := Shape.Square side_0
  current := current_2
  let b3 : Shape → FeM UInt256 := fun current => do
    let mut current := current
    let v13 := current
    let b6 : Shape → UInt256 → FeM UInt256 := fun current v1 => do
      let mut current := current
      return v1
    match v13 with
    | .Square .. =>
      let side_14 := current.Square_0
      b6 current side_14
    | _ =>
      b6 current (UInt256.ofNat 0)
  match current with
  | .Square .. =>
    let v7 := current.Square_0
    let v8 ← checkedAdd v7 (UInt256.ofNat 1)
    current := (current.set_Square_0 v8)
    b3 current
  | _ =>
    b3 current

-- END fe-lean-export

end

/-- `area` multiplies the sides of whichever shape the arguments make. -/
theorem area_exec (width height : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Area width height).exec I w =
      if width = UInt256.ofNat 0 then some (.ok (UInt256.ofNat 0, w))
      else (checkedMul width height).exec I w := by
  by_cases h0 : width = UInt256.ofNat 0
  · simp [recv_Area, shape, h0]
  · by_cases hs : width = height
    · subst hs
      simp [recv_Area, shape, Shape.Square_0, h0]
    · simp [recv_Area, shape, Shape.Rect_0, Shape.Rect_1, h0, hs]

/-- `grow` adds one to the side through the variant's field. -/
theorem grow_exec (side : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Grow side).exec I w = (checkedAdd side (UInt256.ofNat 1)).exec I w := by
  simp [recv_Grow, Shape.Square_0, Shape.set_Square_0, checkedAdd]

end FeProofs.Fixtures.Enums

/-! ## `loops`: a loop is a recursive local function, the least fixed point of its body -/

namespace FeProofs.Fixtures.Loops

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: loops

export Lib (Option_u256 Option_u256.None Option_u256.Some)

/-- The `init` of contract `Loops`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Triangle { n } -> u256`, selector `0x50c2698d` (`triangle(uint256)`) -/
def recv_Triangle (n : UInt256) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut i : UInt256 := default
  total := (UInt256.ofNat 0)
  i := (UInt256.ofNat 0)
  let rec b1 (total : UInt256) (i : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut i := i
    let i_5 := i
    let v7 := decide (i_5.toNat < n.toNat)
    if v7 then
      let i_9 := i
      let i_10 ← checkedAdd i_9 (UInt256.ofNat 1)
      i := i_10
      let i_13 := i
      let total_15 := total
      let total_16 ← checkedAdd total_15 i_13
      total := total_16
      b1 total i
    else
      let total_19 := total
      return total_19
  partial_fixpoint
  b1 total i

/-- `loops::step` -/
def step (value : UInt256) : FeM Option_u256 := do
  let v5 := decide (value = (UInt256.ofNat 1))
  let b3 : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  if v5 then
    let v6 := Option_u256.None
    b3 v6
  else
    let v10 ← checkedRem value (UInt256.ofNat 2)
    let v12 := decide (v10 = (UInt256.ofNat 0))
    let b6 : Option_u256 → FeM Option_u256 := fun v2 => do
      b3 v2
    if v12 then
      let v15 ← checkedDiv value (UInt256.ofNat 2)
      let v16 := Option_u256.Some v15
      b6 v16
    else
      let v20 ← checkedMul (UInt256.ofNat 3) value
      let v22 ← checkedAdd v20 (UInt256.ofNat 1)
      let v23 := Option_u256.Some v22
      b6 v23

/-- `Collatz { start, limit } -> u256`, selector `0xea732925` (`collatz(uint256,uint256)`) -/
def recv_Collatz (start : UInt256) (limit : UInt256) : FeM UInt256 := do
  let mut value : UInt256 := default
  let mut steps : UInt256 := default
  value := start
  steps := (UInt256.ofNat 0)
  let rec b1 (value : UInt256) (steps : UInt256) : FeM UInt256 := do
    let mut value := value
    let mut steps := steps
    let steps_5 := steps
    let v7 := decide (steps_5 = limit)
    if v7 then
      return limit
    else
      let value_10 := value
      let v12 ← step value_10
      match (← pure v12) with
      | .Some .. =>
        let next := v12.Some_0
        value := next
        let steps_18 := steps
        let steps_19 ← checkedAdd steps_18 (UInt256.ofNat 1)
        steps := steps_19
        b1 value steps
      | .None =>
        let steps_23 := steps
        return steps_23
  partial_fixpoint
  b1 value steps

-- END fe-lean-export

end

/-- `triangle(3)` runs the loop body three times and returns `1 + 2 + 3`. -/
theorem triangle_three (I : ExecutionEnv) (w : World) :
    (recv_Triangle (UInt256.ofNat 3)).exec I w = some (.ok (UInt256.ofNat 6, w)) := by
  simp [recv_Triangle]
  iterate 4 (rw [recv_Triangle.b1]; simp +decide [checkedAdd])

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

/-- The `init` of contract `NestedLoops`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `nested_loops::windows` -/
def windows (n : UInt256) (width : UInt256) : FeM UInt256 := do
  let mut acc : UInt256 := default
  let mut index : UInt256 := default
  let mut started : Bool := default
  let mut r3 : Range_Unknown_Unknown := default
  acc := (UInt256.ofNat 1)
  index := (UInt256.ofNat 0)
  started := false
  let rec b1 (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
    let mut acc := acc
    let mut index := index
    let mut started := started
    let mut r3 := r3
    let index_10 := index
    let v13 := decide (index_10.toNat < n.toNat)
    if v13 then
      let index_14 := index
      let v17 ← checkedAdd index_14 width
      let v19 ← checkedAdd v17 (UInt256.ofNat 1)
      let v21 := decide (v19.toNat < n.toNat)
      let b6 : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → UInt256 → FeM UInt256 := fun acc index started r3 «end» => do
        let mut acc := acc
        let mut index := index
        let mut started := started
        let mut r3 := r3
        let started_32 := started
        let rec b9 (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
          let mut acc := acc
          let mut index := index
          let mut started := started
          let mut r3 := r3
          let v60 ← checkedRem «end» (UInt256.ofNat 2)
          let v62 := decide (v60 = (UInt256.ofNat 1))
          let b16 : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → FeM UInt256 := fun acc index started r3 => do
            let mut acc := acc
            let mut index := index
            let mut started := started
            let mut r3 := r3
            index := «end»
            b1 acc index started r3
          if v62 then
            let acc_63 := acc
            let v65 := «end»
            let acc_66 ← checkedAdd acc_63 v65
            acc := acc_66
            started := true
            b16 acc index started r3
          else
            b16 acc index started r3
        partial_fixpoint
        if started_32 then
          let index_33 := index
          let v36 := (Range_Unknown_Unknown.mk index_33 «end»)
          r3 := v36
          let v38 ← Range_Unknown_Unknown_start r3
          let rec b10 (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) (v3 : UInt256) : FeM UInt256 := do
            let mut acc := acc
            let mut index := index
            let mut started := started
            let mut r3 := r3
            let v41 ← Range_Unknown_Unknown_has r3 v3
            if v41 then
              let _ ← Range_Unknown_Unknown_at r3 v3
              let acc_44 := acc
              let v47 ← checkedMul acc_44 (UInt256.ofNat 2)
              let acc_49 ← checkedRem v47 (UInt256.ofNat 1000003)
              acc := acc_49
              let v53 ← Range_Unknown_Unknown_next r3 v3
              b10 acc index started r3 v53
            else
              b9 acc index started r3
          partial_fixpoint
          b10 acc index started r3 v38
        else
          b9 acc index started r3
      if v21 then
        let index_22 := index
        let v25 ← checkedAdd index_22 width
        let v27 ← checkedAdd v25 (UInt256.ofNat 1)
        b6 acc index started r3 v27
      else
        b6 acc index started r3 n
    else
      let acc_77 := acc
      return acc_77
  partial_fixpoint
  b1 acc index started r3

/-- `Windows { n, width } -> u256`, selector `0x6a39ed49` (`windows(uint256,uint256)`) -/
def recv_Windows (n : UInt256) (width : UInt256) : FeM UInt256 := do
  let v2 ← downcast_truncate_u256_usize n
  let v3 ← downcast_truncate_u256_usize width
  let v4 ← windows v2 v3
  return v4

/-- `nested_loops::break_both` -/
def break_both (n : UInt256) : FeM UInt256 := do
  let mut i : UInt256 := default
  let mut found : UInt256 := default
  let mut done : Bool := default
  let mut j : UInt256 := default
  i := (UInt256.ofNat 0)
  found := (UInt256.ofNat 0)
  done := false
  let rec b1 (i : UInt256) (found : UInt256) (done : Bool) (j : UInt256) : FeM UInt256 := do
    let mut i := i
    let mut found := found
    let mut done := done
    let mut j := j
    let i_7 := i
    let v10 := decide (i_7.toNat < n.toNat)
    let b3 : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun i found done j => do
      let mut i := i
      let mut found := found
      let mut done := done
      let mut j := j
      let found_49 := found
      return found_49
    if v10 then
      j := (UInt256.ofNat 0)
      let rec b4 (i : UInt256) (found : UInt256) (done : Bool) (j : UInt256) : FeM UInt256 := do
        let mut i := i
        let mut found := found
        let mut done := done
        let mut j := j
        let j_13 := j
        let i_15 := i
        let v16 := decide (j_13.toNat < i_15.toNat)
        let b6 : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun i found done j => do
          let mut i := i
          let mut found := found
          let mut done := done
          let mut j := j
          let done_41 := done
          if done_41 then
            b3 i found done j
          else
            let i_45 := i
            let i_46 ← checkedAdd i_45 (UInt256.ofNat 1)
            i := i_46
            b1 i found done j
        if v16 then
          let i_17 := i
          let j_19 := j
          let v20 ← checkedMul i_17 j_19
          let v22 := decide (v20 = (UInt256.ofNat 12))
          if v22 then
            let i_23 := i
            let v26 ← checkedMul i_23 (UInt256.ofNat 100)
            let j_27 := j
            let found_28 ← checkedAdd v26 j_27
            found := found_28
            done := true
            b6 i found done j
          else
            let j_37 := j
            let j_38 ← checkedAdd j_37 (UInt256.ofNat 1)
            j := j_38
            b4 i found done j
        else
          b6 i found done j
      partial_fixpoint
      b4 i found done j
    else
      b3 i found done j
  partial_fixpoint
  b1 i found done j

/-- `BreakBoth { n } -> u256`, selector `0x17ea0cd5` (`breakBoth(uint256)`) -/
def recv_BreakBoth (n : UInt256) : FeM UInt256 := do
  let v1 ← break_both n
  return v1

/-- `nested_loops::continue_outer` -/
def continue_outer (n : UInt256) : FeM UInt256 := do
  let mut i : UInt256 := default
  let mut total : UInt256 := default
  let mut j : UInt256 := default
  let mut skip : Bool := default
  i := (UInt256.ofNat 0)
  total := (UInt256.ofNat 0)
  let rec b1 (i : UInt256) (total : UInt256) (j : UInt256) (skip : Bool) : FeM UInt256 := do
    let mut i := i
    let mut total := total
    let mut j := j
    let mut skip := skip
    let i_5 := i
    let v8 := decide (i_5.toNat < n.toNat)
    if v8 then
      let i_10 := i
      let i_11 ← checkedAdd i_10 (UInt256.ofNat 1)
      i := i_11
      j := (UInt256.ofNat 0)
      skip := false
      let rec b4 (i : UInt256) (total : UInt256) (j : UInt256) (skip : Bool) : FeM UInt256 := do
        let mut i := i
        let mut total := total
        let mut j := j
        let mut skip := skip
        let j_18 := j
        let i_20 := i
        let v21 := decide (j_18.toNat < i_20.toNat)
        let b6 : UInt256 → UInt256 → UInt256 → Bool → FeM UInt256 := fun i total j skip => do
          let mut i := i
          let mut total := total
          let mut j := j
          let mut skip := skip
          let skip_36 := skip
          if skip_36 then
            b1 i total j skip
          else
            let i_39 := i
            let total_41 := total
            let total_42 ← checkedAdd total_41 i_39
            total := total_42
            b1 i total j skip
        if v21 then
          let j_22 := j
          let v25 := decide (j_22 = (UInt256.ofNat 3))
          if v25 then
            skip := true
            b6 i total j skip
          else
            let j_32 := j
            let j_33 ← checkedAdd j_32 (UInt256.ofNat 1)
            j := j_33
            b4 i total j skip
        else
          b6 i total j skip
      partial_fixpoint
      b4 i total j skip
    else
      let total_45 := total
      return total_45
  partial_fixpoint
  b1 i total j skip

/-- `ContinueOuter { n } -> u256`, selector `0x0dec9eef` (`continueOuter(uint256)`) -/
def recv_ContinueOuter (n : UInt256) : FeM UInt256 := do
  let v1 ← continue_outer n
  return v1

/-- `nested_loops::return_inner` -/
def return_inner (n : UInt256) : FeM UInt256 := do
  let mut i : UInt256 := default
  let mut j : UInt256 := default
  i := (UInt256.ofNat 0)
  let rec b1 (i : UInt256) (j : UInt256) : FeM UInt256 := do
    let mut i := i
    let mut j := j
    let i_3 := i
    let v6 := decide (i_3.toNat < n.toNat)
    if v6 then
      j := (UInt256.ofNat 0)
      let rec b4 (i : UInt256) (j : UInt256) : FeM UInt256 := do
        let mut i := i
        let mut j := j
        let j_9 := j
        let v12 := decide (j_9.toNat < n.toNat)
        if v12 then
          let i_13 := i
          let j_15 := j
          let v16 ← checkedAdd i_13 j_15
          let v18 := decide (v16 = (UInt256.ofNat 7))
          if v18 then
            let i_19 := i
            let v22 ← checkedMul i_19 (UInt256.ofNat 10)
            let j_23 := j
            let v24 ← checkedAdd v22 j_23
            return v24
          else
            let j_28 := j
            let j_29 ← checkedAdd j_28 (UInt256.ofNat 1)
            j := j_29
            b4 i j
        else
          let i_33 := i
          let i_34 ← checkedAdd i_33 (UInt256.ofNat 1)
          i := i_34
          b1 i j
      partial_fixpoint
      b4 i j
    else
      return (UInt256.ofNat 0)
  partial_fixpoint
  b1 i j

/-- `ReturnInner { n } -> u256`, selector `0x92ba46ad` (`returnInner(uint256)`) -/
def recv_ReturnInner (n : UInt256) : FeM UInt256 := do
  let v1 ← return_inner n
  return v1

/-- `nested_loops::three_levels` -/
def three_levels (n : UInt256) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut k : UInt256 := default
  let mut r2 : Range_Known_0_Unknown := default
  let mut r3 : Range_Known_0_Unknown := default
  total := (UInt256.ofNat 0)
  let v8 := (Range_Known_0_Unknown.mk () n)
  r2 := v8
  let v10 ← Range_start_0 r2
  let rec b1 (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v1 : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut k := k
    let mut r2 := r2
    let mut r3 := r3
    let v13 ← Range_has_0 r2 v1
    if v13 then
      let v15 ← Range_at_0 r2 v1
      let i := v15
      let v19 := (Range_Known_0_Unknown.mk () i)
      r3 := v19
      let v21 ← Range_start_0 r3
      let rec b5 (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v2 : UInt256) : FeM UInt256 := do
        let mut total := total
        let mut k := k
        let mut r2 := r2
        let mut r3 := r3
        let v24 ← Range_has_0 r3 v2
        if v24 then
          let v26 ← Range_at_0 r3 v2
          let j := v26
          k := (UInt256.ofNat 0)
          let rec b9 (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) : FeM UInt256 := do
            let mut total := total
            let mut k := k
            let mut r2 := r2
            let mut r3 := r3
            let k_30 := k
            let v32 := decide (k_30.toNat < j.toNat)
            if v32 then
              let v33 ← checkedAdd i j
              let k_34 := k
              let v35 ← checkedAdd v33 k_34
              let v37 ← checkedRem v35 (UInt256.ofNat 3)
              let v39 := decide (v37 = (UInt256.ofNat 0))
              let b14 : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun total k r2 r3 => do
                let mut total := total
                let mut k := k
                let mut r2 := r2
                let mut r3 := r3
                let k_53 := k
                let k_54 ← checkedAdd k_53 (UInt256.ofNat 1)
                k := k_54
                b9 total k r2 r3
              if v39 then
                let total_41 := total
                let total_42 ← checkedAdd total_41 (UInt256.ofNat 1)
                total := total_42
                b14 total k r2 r3
              else
                let total_47 := total
                let total_48 ← checkedAdd total_47 (UInt256.ofNat 2)
                total := total_48
                b14 total k r2 r3
            else
              let v58 ← checkedRem j (UInt256.ofNat 2)
              let v60 := decide (v58 = (UInt256.ofNat 0))
              let b17 : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun total k r2 r3 => do
                let mut total := total
                let mut k := k
                let mut r2 := r2
                let mut r3 := r3
                let v70 ← Range_next_0 r3 v2
                b5 total k r2 r3 v70
              if v60 then
                let total_62 := total
                let total_63 ← checkedAdd total_62 (UInt256.ofNat 10)
                total := total_63
                b17 total k r2 r3
              else
                b17 total k r2 r3
          partial_fixpoint
          b9 total k r2 r3
        else
          let v74 ← Range_next_0 r2 v1
          b1 total k r2 r3 v74
      partial_fixpoint
      b5 total k r2 r3 v21
    else
      let total_76 := total
      return total_76
  partial_fixpoint
  b1 total k r2 r3 v10

/-- `ThreeLevels { n } -> u256`, selector `0x81037424` (`threeLevels(uint256)`) -/
def recv_ThreeLevels (n : UInt256) : FeM UInt256 := do
  let v1 ← downcast_truncate_u256_usize n
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

/-- The `init` of contract `Arrays`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `arrays::bump` -/
def bump (items : (Vector UInt256 4)) («at» : UInt256) («by» : UInt256) : FeM (Unit × (Vector UInt256 4)) := do
  let mut items := items
  checkIndex «at» 4
  let v5 := items[«at».toNat]!
  let v6 ← checkedAdd v5 «by»
  checkIndex «at» 4
  items := (items.set! «at».toNat v6)
  return ((), items)

/-- `Pick { index, value } -> u256`, selector `0xa62f4550` (`pick(uint256,uint256)`) -/
def recv_Pick (index : UInt256) (value : UInt256) : FeM UInt256 := do
  let mut items : (Vector UInt256 4) := default
  let items_2 := Vector.replicate 4 value
  items := items_2
  let v5 := (UInt256.ofNat 0)
  checkIndex v5 4
  items := (items.set! v5.toNat (UInt256.ofNat 7))
  let (v9, v9_0) ← bump items index (UInt256.ofNat 1)
  items := v9_0
  checkIndex index 4
  let v10 := items[index.toNat]!
  let v11 := (UInt256.ofNat 3)
  checkIndex v11 4
  let v12 := items[v11.toNat]!
  let v13 ← checkedAdd v10 v12
  return v13

/-- `arrays::WEIGHTS` -/
def WEIGHTS : FeM (Vector UInt256 3) := do
  let v3 := #v[(UInt256.ofNat 1), (UInt256.ofNat 10), (UInt256.ofNat 100)]
  return v3

/-- `Weigh { values } -> u256`, selector `0x2f57374e` (`weigh(uint256[3])`) -/
def recv_Weigh (values : (Vector UInt256 3)) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut i : UInt256 := default
  total := (UInt256.ofNat 0)
  i := (UInt256.ofNat 0)
  let rec b1 (total : UInt256) (i : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut i := i
    let i_5 := i
    let v8 := decide (i_5.toNat < (UInt256.ofNat 3).toNat)
    if v8 then
      let i_9 := i
      checkIndex i_9 3
      let v10 := values[i_9.toNat]!
      let v11 ← WEIGHTS
      let i_12 := i
      checkIndex i_12 3
      let v13 := v11[i_12.toNat]!
      let v14 ← checkedMul v10 v13
      let total_15 := total
      let total_16 ← checkedAdd total_15 v14
      total := total_16
      let i_20 := i
      let i_21 ← checkedAdd i_20 (UInt256.ofNat 1)
      i := i_21
      b1 total i
    else
      let total_24 := total
      return total_24
  partial_fixpoint
  b1 total i

-- END fe-lean-export

end

/- The constants the compiler folded: each is the value the exporter printed in its place. -/
-- BEGIN fe-lean-export: arrays.checks

set_option maxRecDepth 10000 in
example : WEIGHTS = pure #v[(UInt256.ofNat 1), (UInt256.ofNat 10), (UInt256.ofNat 100)] := rfl
-- END fe-lean-export

/-- `pick` with an index past the array panics with `Panic(0x32)` at the helper's check. -/
theorem pick_out_of_bounds (value : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Pick (UInt256.ofNat 4) value).exec I w = some (.error (.panic 0x32)) := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h4 : (UInt256.ofNat 4).toNat = 4 := rfl
  simp [recv_Pick, bump, checkIndex, h0, h4]

/-- `pick(3, value)` bumps element 3 and reads it twice. -/
theorem pick_last (value : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Pick (UInt256.ofNat 3) value).exec I w =
      (do let bumped ← checkedAdd value (UInt256.ofNat 1)
          checkedAdd bumped bumped : FeM UInt256).exec I w := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h3 : (UInt256.ofNat 3).toNat = 3 := rfl
  have hread : ((Vector.replicate 4 value).set! 0 (UInt256.ofNat 7))[3] = value := rfl
  have hset (a : UInt256) :
      (((Vector.replicate 4 value).set! 0 (UInt256.ofNat 7)).set! 3 a)[3] = a := rfl
  simp [recv_Pick, bump, checkIndex, h0, h3, hread, hset]

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

/-- The `init` of contract `State`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `SetDelta { delta } -> i16`, selector `0x36899e92` (`setDelta(int16)`) -/
def recv_SetDelta (delta : UInt256) : FeM UInt256 := do
  let old ← loadIntAt (.i 16) (Field.packed.field Layout.Packed 2) ⟨2, 2, true⟩
  storeIntAt (.i 16) (Field.packed.field Layout.Packed 2) ⟨2, 2, true⟩ delta
  return old

/-- `Replace { flag, small, delta, owner, total } -> u256`, selector `0x1e84534a` (`replace(bool,uint8,int16,address,uint256)`) -/
def recv_Replace (flag : Bool) (small : UInt256) (delta : UInt256) (owner : UInt256) (total : UInt256) : FeM UInt256 := do
  let packed_1 ← load_Packed Field.packed
  let v7 := (Packed.mk flag small delta owner total)
  store_Packed Field.packed v7
  let v9 := packed_1.total
  return v9

/-- `Advance { by } -> u256`, selector `0x71d6ddd6` (`advance(uint256)`) -/
def recv_Advance («by» : UInt256) : FeM UInt256 := do
  let v3 ← load_Phase Field.phase
  let b1 : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v3 with
  | .Idle =>
    let v5 := Phase.Running (UInt256.ofNat 1) «by»
    store_Phase Field.phase v5
    b1 (UInt256.ofNat 0)
  | .Running .. =>
    let count ← loadInt (.u 64) (Field.phase.offset 1)
    let sum ← load (Field.phase.offset 2)
    let v11 := decide («by».toNat < sum.toNat)
    let v12 := Phase.Done v11
    store_Phase Field.phase v12
    b1 sum
  | .Done .. =>
    let ok ← loadBool (Field.phase.offset 1)
    let b7 : UInt256 → FeM UInt256 := fun v2 => do
      b1 v2
    if ok then
      b7 (UInt256.ofNat 1)
    else
      b7 (UInt256.ofNat 2)

/-- `Mark { at, level } -> u8`, selector `0x0a774e1e` (`mark(uint256,uint8)`) -/
def recv_Mark («at» : UInt256) (level : UInt256) : FeM UInt256 := do
  checkIndex «at» 3
  let old ← loadInt (.u 8) (Field.levels.index 1 «at»)
  checkIndex «at» 3
  storeInt (.u 8) (Field.levels.index 1 «at») level
  storeIntAt (.u 8) Field.narrow ⟨1, 1, true⟩ old
  let narrow ← loadIntAt (.u 8) Field.narrow ⟨1, 1, true⟩
  return narrow

/-- `Lock -> bool`, selector `0xf83d08ba` (`lock()`) -/
def recv_Lock : FeM Bool := do
  let was ← loadBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩
  storeBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩ true
  storeBoolAt Field.alone ⟨0, 1, true⟩ was
  let alone ← loadBoolAt Field.alone ⟨0, 1, true⟩
  return alone

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

/-- The `init` of contract `Entries`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Vote { voter, proposal } -> bool`, selector `0xb384abef` (`vote(uint256,uint256)`) -/
def recv_Vote (voter : UInt256) (proposal : UInt256) : FeM Bool := do
  let v2 := (voter, proposal)
  let l0 ← StorageMap_locate_tuple_u256_u256_bool (Field.store.field Layout.Store 0) (Field.store.field Layout.Store 0).slot v2
  let before ← loadBool (Place.mk .storage l0.slot)
  let v6 := (voter, proposal)
  let l1 ← StorageMap_locate_tuple_u256_u256_bool (Field.store.field Layout.Store 0) (Field.store.field Layout.Store 0).slot v6
  storeBool (Place.mk .storage l1.slot) true
  return before

/-- `Flag { on } -> u256`, selector `0xa92a4c3b` (`flag(bool)`) -/
def recv_Flag (on : Bool) : FeM UInt256 := do
  let l0 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot on
  let v2 ← load (Place.mk .storage l0.slot)
  let v3 ← checkedAdd v2 (UInt256.ofNat 1)
  let l1 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot on
  store (Place.mk .storage l1.slot) v3
  let l2 ← StorageMap_locate_bool_u256 (Field.store.field Layout.Store 1) (Field.store.field Layout.Store 1).slot on
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

/-- The `init` of contract `Wide`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Sum { a, b, c, d, e, f, g, h, i, j } -> u256`, selector `0x460e9674` (`sum(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256)`) -/
def recv_Sum (a : UInt256) (b : UInt256) (c : UInt256) (d : UInt256) (e : UInt256) (f : UInt256) (g : UInt256) (h : UInt256) (i : UInt256) (j : UInt256) : FeM UInt256 := do
  let v10 ← checkedAdd a b
  let v11 ← checkedAdd v10 c
  let v12 ← checkedAdd v11 d
  let v13 ← checkedAdd v12 e
  let v14 ← checkedAdd v13 f
  let v15 ← checkedAdd v14 g
  let v16 ← checkedAdd v15 h
  let v17 ← checkedAdd v16 i
  let v18 ← checkedAdd v17 j
  return v18

/-- `<Sum as AbiSize>::HEAD_SIZE` -/
def Sum_HEAD_SIZE : FeM UInt256 := do
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd (UInt256.ofNat 0) v1
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

def Sum_decode_from_CallData_k5 (__fe_field_0 : UInt256) (__fe_field_1 : UInt256) (__fe_field_2 : UInt256) (__fe_field_3 : UInt256) (__fe_field_4 : UInt256) (__fe_field_5 : UInt256) (__fe_field_6 : UInt256) (__fe_field_7 : UInt256) (__fe_field_8 : UInt256) (__fe_field_9 : UInt256) : FeM Sum := do
  let v123 := (Sum.mk __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3 __fe_field_4 __fe_field_5 __fe_field_6 __fe_field_7 __fe_field_8 __fe_field_9)
  return v123

def Sum_decode_from_CallData_k4 (__fe_msg_decode_input : CallData) (__fe_msg_decode_base : UInt256) (__fe_msg_decode_input_len : UInt256) (__fe_field_0 : UInt256) (__fe_field_1 : UInt256) (__fe_field_2 : UInt256) (__fe_field_3 : UInt256) (__fe_field_4 : UInt256) (__fe_field_5 : UInt256) (__fe_field_6 : UInt256) (__fe_field_7 : UInt256) (v97 : UInt256) : FeM Sum := do
  let v98 ← abi_field_head_size_u256
  let v99 ← checkedAdd v97 v98
  let __fe_field_8 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v99 __fe_msg_decode_input_len
  let v103 ← abi_field_head_size_u256
  let v104 ← checkedAdd __fe_msg_decode_base v103
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
  let __fe_field_9 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v120 __fe_msg_decode_input_len
  Sum_decode_from_CallData_k5 __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3 __fe_field_4 __fe_field_5 __fe_field_6 __fe_field_7 __fe_field_8 __fe_field_9

def Sum_decode_from_CallData_k3 (__fe_msg_decode_input : CallData) (__fe_msg_decode_base : UInt256) (__fe_msg_decode_input_len : UInt256) (__fe_field_0 : UInt256) (__fe_field_1 : UInt256) (__fe_field_2 : UInt256) (__fe_field_3 : UInt256) (__fe_field_4 : UInt256) (__fe_field_5 : UInt256) (__fe_field_6 : UInt256) (v72 : UInt256) (v73 : UInt256) : FeM Sum := do
  let v74 ← checkedAdd v72 v73
  let v75 ← abi_field_head_size_u256
  let v76 ← checkedAdd v74 v75
  let v77 ← abi_field_head_size_u256
  let v78 ← checkedAdd v76 v77
  let v79 ← abi_field_head_size_u256
  let v80 ← checkedAdd v78 v79
  let __fe_field_7 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v80 __fe_msg_decode_input_len
  let v84 ← abi_field_head_size_u256
  let v85 ← checkedAdd __fe_msg_decode_base v84
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
  Sum_decode_from_CallData_k4 __fe_msg_decode_input __fe_msg_decode_base __fe_msg_decode_input_len __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3 __fe_field_4 __fe_field_5 __fe_field_6 __fe_field_7 v97

def Sum_decode_from_CallData_k2 (__fe_msg_decode_input : CallData) (__fe_msg_decode_base : UInt256) (__fe_msg_decode_input_len : UInt256) (__fe_field_0 : UInt256) (__fe_field_1 : UInt256) (__fe_field_2 : UInt256) (__fe_field_3 : UInt256) (__fe_field_4 : UInt256) (__fe_field_5 : UInt256) : FeM Sum := do
  let v52 ← abi_field_head_size_u256
  let v53 ← checkedAdd __fe_msg_decode_base v52
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
  let __fe_field_6 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v63 __fe_msg_decode_input_len
  let v67 ← abi_field_head_size_u256
  let v68 ← checkedAdd __fe_msg_decode_base v67
  let v69 ← abi_field_head_size_u256
  let v70 ← checkedAdd v68 v69
  let v71 ← abi_field_head_size_u256
  let v72 ← checkedAdd v70 v71
  let v73 ← abi_field_head_size_u256
  Sum_decode_from_CallData_k3 __fe_msg_decode_input __fe_msg_decode_base __fe_msg_decode_input_len __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3 __fe_field_4 __fe_field_5 __fe_field_6 v72 v73

def Sum_decode_from_CallData_k1 (__fe_msg_decode_input : CallData) (__fe_msg_decode_base : UInt256) (__fe_msg_decode_input_len : UInt256) (__fe_field_0 : UInt256) (__fe_field_1 : UInt256) (__fe_field_2 : UInt256) (__fe_field_3 : UInt256) : FeM Sum := do
  let v28 ← abi_field_head_size_u256
  let v29 ← checkedAdd __fe_msg_decode_base v28
  let v30 ← abi_field_head_size_u256
  let v31 ← checkedAdd v29 v30
  let v32 ← abi_field_head_size_u256
  let v33 ← checkedAdd v31 v32
  let v34 ← abi_field_head_size_u256
  let v35 ← checkedAdd v33 v34
  let __fe_field_4 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v35 __fe_msg_decode_input_len
  let v39 ← abi_field_head_size_u256
  let v40 ← checkedAdd __fe_msg_decode_base v39
  let v41 ← abi_field_head_size_u256
  let v42 ← checkedAdd v40 v41
  let v43 ← abi_field_head_size_u256
  let v44 ← checkedAdd v42 v43
  let v45 ← abi_field_head_size_u256
  let v46 ← checkedAdd v44 v45
  let v47 ← abi_field_head_size_u256
  let v48 ← checkedAdd v46 v47
  let __fe_field_5 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v48 __fe_msg_decode_input_len
  Sum_decode_from_CallData_k2 __fe_msg_decode_input __fe_msg_decode_base __fe_msg_decode_input_len __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3 __fe_field_4 __fe_field_5

/-- `<Sum as Decode>::decode_from<CallData>` -/
def Sum_decode_from_CallData (__fe_msg_decode_input : CallData) (__fe_msg_decode_base : UInt256) : FeM Sum := do
  let __fe_msg_decode_input_len ← len_CallData __fe_msg_decode_input
  let __fe_field_0 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base __fe_msg_decode_base __fe_msg_decode_input_len
  let v7 ← abi_field_head_size_u256
  let v8 ← checkedAdd __fe_msg_decode_base v7
  let __fe_field_1 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v8 __fe_msg_decode_input_len
  let v12 ← abi_field_head_size_u256
  let v13 ← checkedAdd __fe_msg_decode_base v12
  let v14 ← abi_field_head_size_u256
  let v15 ← checkedAdd v13 v14
  let __fe_field_2 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v15 __fe_msg_decode_input_len
  let v19 ← abi_field_head_size_u256
  let v20 ← checkedAdd __fe_msg_decode_base v19
  let v21 ← abi_field_head_size_u256
  let v22 ← checkedAdd v20 v21
  let v23 ← abi_field_head_size_u256
  let v24 ← checkedAdd v22 v23
  let __fe_field_3 ← decode_msg_field_from_Sol_u256_CallData __fe_msg_decode_input __fe_msg_decode_base v24 __fe_msg_decode_input_len
  Sum_decode_from_CallData_k1 __fe_msg_decode_input __fe_msg_decode_base __fe_msg_decode_input_len __fe_field_0 __fe_field_1 __fe_field_2 __fe_field_3

/-- `core::abi::Decode::decode_from_prechecked_head<Sum, Sol, CallData>` -/
def decode_from_prechecked_head_Sum_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Sum := do
  let v3 ← Sum_decode_from_CallData input pos
  return v3

/-- `core::contracts::decode_runtime_args<Evm, Sol, Sum>` -/
def decode_runtime_args_Evm_Sol_Sum : FeM Sum := do
  let mut input : CallData := default
  let input_2 ← Evm_input
  input := input_2
  let base ← Sol_SELECTOR_SIZE
  let input_6 := input
  let len ← len_CallData input_6
  let v9 ← Sum_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  let input_11 := input
  let v12 ← decode_from_prechecked_head_Sum_Sol_CallData input_11 base len
  return v12

/-- The entry of `recv_Sum`, for `wide::WideMsg::Sum` -/
def recv_Sum_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Sum
  let result ← recv_Sum message.a message.b message.c message.d message.e message.f message.g message.h message.i message.j
  Evm_return_value_Sol_u256 result

/-- The runtime entry of contract `Wide`: the entry of the arm the call's selector picks -/
def runtime : FeM Empty := do
  let size ← calldatasize
  if size.toNat < 4 then
    revertEmpty
  else
    let selector ← calldataSelector
    if selector = UInt256.ofNat 0x460e9674 then
      recv_Sum_entry
    else
      revertEmpty

/-- The deployment entry of contract `Wide`: `init` on the arguments after the creation code -/
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

/-- The `init` of contract `Projections`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Cell::slot` -/
def Cell_slot (self : Place) : FeM Place := do
  let v1 := (self.field Layout.Cell 0)
  return v1

/-- `Direct { by } -> u256`, selector `0x9bbc59f9` (`direct(uint256)`) -/
def recv_Direct («by» : UInt256) : FeM UInt256 := do
  let v1 := Field.cell
  let v2 ← Cell_slot v1
  let v3 ← load v2
  let v4 ← checkedAdd v3 «by»
  store v2 v4
  let v6 ← load (Field.cell.field Layout.Cell 0)
  return v6

/-- `Cell::get` -/
def Cell_get (self : Place) : FeM UInt256 := do
  let v1 ← load (self.field Layout.Cell 0)
  return v1

/-- `Cell::set` -/
def Cell_set (self : Place) (v : UInt256) : FeM Unit := do
  store (self.field Layout.Cell 0) v
  return ()

/-- `Cell::cached` -/
def Cell_cached (self_0 : Place) : FeM (UInt256 × (UInt256 → FeM Unit)) := do
  let mut tmp : UInt256 := default
  let self_1 := self_0
  let tmp_2 ← Cell_get self_1
  tmp := tmp_2
  let slide : UInt256 → FeM Unit := fun g => do
    let mut tmp := tmp
    tmp := g
    let tmp_5 := tmp
    let _ ← Cell_set self_0 tmp_5
    return ()
  return (tmp, slide)

/-- `Slide { by } -> u256`, selector `0x235361d9` (`slide(uint256)`) -/
def recv_Slide («by» : UInt256) : FeM UInt256 := do
  let mut v2 : UInt256 := default
  let v1 := Field.cell
  let (v2_g, v2_k) ← Cell_cached v1
  v2 := v2_g
  let v3 := v2
  let v4 ← checkedAdd v3 «by»
  v2 := v4
  let _ ← v2_k v2
  let v6 ← load (Field.cell.field Layout.Cell 0)
  return v6

/-- `projections::first` -/
def first (pair : (UInt256 × UInt256)) : FeM (UInt256 × (UInt256 → FeM (UInt256 × UInt256))) := do
  let mut pair := pair
  let slide : UInt256 → FeM (UInt256 × UInt256) := fun g => do
    let mut pair := pair
    pair := { pair with fst := g }
    return pair
  return (pair.fst, slide)

/-- `Local { a, b } -> u256`, selector `0xa60eff5e` (`local(uint256,uint256)`) -/
def recv_Local (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let mut pair : (UInt256 × UInt256) := default
  let mut v5 : UInt256 := default
  let pair_2 := (a, b)
  pair := pair_2
  let (v5_g, v5_k) ← first pair
  v5 := v5_g
  let v6 := v5
  let v7 ← checkedAdd v6 b
  v5 := v7
  let v5_0 ← v5_k v5
  pair := v5_0
  let v9 := pair.fst
  return v9

-- END fe-lean-export

end

/-- Writing through a grant of a local whose slide stores it does what writing through the place
    itself does. -/
theorem slide_exec (by_ : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Slide by_).exec I w = (recv_Direct by_).exec I w := by
  simp [recv_Direct, recv_Slide, Cell_slot, Cell_cached, Cell_get, Cell_set]

/-- A write through a grant into the caller's local comes back when the session ends. -/
theorem local_exec (a b : UInt256) (I : ExecutionEnv) (w : World) :
    (recv_Local a b).exec I w = (checkedAdd a b).exec I w := by
  simp [recv_Local, first]

end FeProofs.Fixtures.Projections
