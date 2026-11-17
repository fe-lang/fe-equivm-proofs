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

/-- `store.total` -/
abbrev Field.store.total : Place :=
  Field.store.field Layout.Store 0

/-- `store.hits` -/
abbrev Field.store.hits : Place :=
  Field.store.field Layout.Store 1

/-- The `init` of contract `Counter`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `helper_call::add` -/
def add («by» : UInt256) : FeM UInt256 := do
  -- let next = store.total + by
  let v1 ← load Field.store.total
  let next ← checkedAdd v1 «by»
  -- store.total = next
  store Field.store.total next
  -- store.hits[by] += 1
  let hits_by ← StorageMap_locate_u256_u256 Field.store.hits Field.store.hits.slot «by»
  let v8 ← load (Place.mk .storage hits_by.slot)
  let v9 ← checkedAdd v8 (UInt256.ofNat 1)
  let hits_by_1 ← StorageMap_locate_u256_u256 Field.store.hits Field.store.hits.slot «by»
  store (Place.mk .storage hits_by_1.slot) v9
  return next

/-- `Bump { by } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump («by» : UInt256) : FeM UInt256 := do
  -- add(by)
  let v1 ← add «by»
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

/-- `store.total` -/
abbrev Field.store.total : Place :=
  Field.store.field Layout.Store 0

/-- `store.hits` -/
abbrev Field.store.hits : Place :=
  Field.store.field Layout.Store 1

/-- The `init` of contract `Counter`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `join::add` -/
def add («by» : UInt256) : FeM UInt256 := do
  let join : UInt256 → FeM UInt256 := fun next => do
    -- store.total = next
    store Field.store.total next
    -- store.hits[by] += 1
    let hits_by ← StorageMap_locate_u256_u256 Field.store.hits Field.store.hits.slot «by»
    let v17 ← load (Place.mk .storage hits_by.slot)
    let v18 ← checkedAdd v17 (UInt256.ofNat 1)
    let hits_by_1 ← StorageMap_locate_u256_u256 Field.store.hits Field.store.hits.slot «by»
    store (Place.mk .storage hits_by_1.slot) v18
    return next
  -- let next = if by > 10 { store.total + 10 } else { store.total + by }
  if decide ((UInt256.ofNat 10).toNat < «by».toNat) then
    -- store.total + 10
    let v5 ← load Field.store.total
    let v7 ← checkedAdd v5 (UInt256.ofNat 10)
    join v7
  else
    -- store.total + by
    let v9 ← load Field.store.total
    let v11 ← checkedAdd v9 «by»
    join v11

/-- `Bump { by } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump («by» : UInt256) : FeM UInt256 := do
  -- add(by)
  let v1 ← add «by»
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
  -- let at = self.pos
  let «at» := self.pos
  -- self.pos = at + by
  let v5 ← checkedAdd «at» «by»
  self := { self with pos := v5 }
  return («at», self)

/-- `Cursor::skip` -/
def Cursor_skip (self : Cursor) («by» : UInt256) : FeM (Unit × Cursor) := do
  let mut self := self
  let join : Cursor → FeM (Unit × Cursor) := fun self => do
    let mut self := self
    -- self.base = self.pos
    self := { self with base := self.pos }
    return ((), self)
  -- if by > 32 {
  if decide ((UInt256.ofNat 32).toNat < «by».toNat) then
    -- self.advance(by: 32)
    let (v6, v6_0) ← Cursor_advance self (UInt256.ofNat 32)
    self := v6_0
    join self
  else
    -- self.advance(by)
    let (v8, v8_0) ← Cursor_advance self «by»
    self := v8_0
    join self

/-- `Cursor::end` -/
def Cursor_end (self : Cursor) : FeM UInt256 := do
  -- self.pos + self.base
  let v3 ← checkedAdd self.pos self.base
  return v3

/-- `Sum { step } -> u256`, selector `0x188b85b4` (`sum(uint256)`) -/
def recv_Sum (step : UInt256) : FeM UInt256 := do
  let mut c : Cursor := default
  let mut s : Span := default
  -- var c = Cursor { pos: 0, base: 4 }
  c := (Cursor.mk (UInt256.ofNat 0) (UInt256.ofNat 4))
  -- let a = c.advance(by: step)
  let (a, a_0) ← Cursor_advance c step
  c := a_0
  -- c.skip(by: step)
  let (v9, v9_0) ← Cursor_skip c step
  c := v9_0
  -- var s = Span { start: c, len: step }
  s := (Span.mk c step)
  -- let b = s.start.advance(by: s.len)
  let v14 := s.len
  let (b, b_0) ← Cursor_advance s.start v14
  s := { s with start := b_0 }
  -- a + b + s.start.end()
  let v18 ← checkedAdd a b
  let v21 ← Cursor_end s.start
  let v22 ← checkedAdd v18 v21
  return v22

/-- `Cursor::advance` -/
def Cursor_advance_1 (self : Place) («by» : UInt256) : FeM UInt256 := do
  -- let at = self.pos
  let «at» ← load (self.field Layout.Cursor 0)
  -- self.pos = at + by
  let v5 ← checkedAdd «at» «by»
  store (self.field Layout.Cursor 0) v5
  return «at»

/-- `Bump { step } -> u256`, selector `0xb20eb4c4` (`bump(uint256)`) -/
def recv_Bump (step : UInt256) : FeM UInt256 := do
  -- saved.advance(by: step)
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
  return (pair.snd.fst, pair.fst, pair.snd.snd)

/-- `Swap { a, b } -> u256`, selector `0xd96073cf` (`swap(uint256,uint256)`) -/
def recv_Swap (a : UInt256) (b : UInt256) : FeM UInt256 := do
  let mut pair : (UInt256 × UInt256 × Bool) := default
  let mut r1 : (UInt256 × UInt256 × Bool) := default
  -- var pair = swap(pair: (a, b, true))
  r1 := (a, b, true)
  let pair_6 ← swap r1
  pair := pair_6
  -- pair.1 = pair.1 + 1
  let v10 ← checkedAdd pair.snd.fst (UInt256.ofNat 1)
  pair := { pair with snd := { pair.snd with fst := v10 } }
  let join : (UInt256 × UInt256 × Bool) → (UInt256 × UInt256 × Bool) → UInt256 → FeM UInt256 := fun pair r1 v2 => do
    let mut pair := pair
    let mut r1 := r1
    return v2
  -- if pair.2 {
  if pair.snd.snd then
    -- pair.0 - pair.1
    let v15 ← checkedSub pair.fst pair.snd.fst
    join pair r1 v15
  else
    join pair r1 (UInt256.ofNat 0)

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
  return Cursor.mk pos (UInt256.ofNat 4)

/-- `Cursor::end` -/
def Cursor_end (self : Cursor) : FeM UInt256 := do
  -- self.pos + self.base
  let v3 ← checkedAdd self.pos self.base
  return v3

/-- `Cursor::advance` -/
def Cursor_advance (self : Cursor) («by» : UInt256) : FeM (UInt256 × Cursor) := do
  let mut self := self
  -- let at = self.pos
  let «at» := self.pos
  -- self.pos = at + by
  let v5 ← checkedAdd «at» «by»
  self := { self with pos := v5 }
  return («at», self)

/-- `param_slot::c_end` -/
def c_end (c : Cursor) : FeM UInt256 := do
  -- c.end()
  let v1 ← Cursor_end c
  return v1

/-- `param_slot::consume` -/
def consume (c : Cursor) («by» : UInt256) : FeM UInt256 := do
  let mut c := c
  let mut r1 : Cursor := default
  -- c.advance(by) + c_end(c: make(pos: by))
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
  -- by += 1
  let by_2 ← checkedAdd «by» (UInt256.ofNat 1)
  «by» := by_2
  return «by»

/-- `Sum { step } -> u256`, selector `0x188b85b4` (`sum(uint256)`) -/
def recv_Sum (step : UInt256) : FeM UInt256 := do
  let mut r0 : Cursor := default
  -- make(pos: step).end() + consume(make(pos: 1), by: step) + bump(by: step)
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
  -- let args: (u256, u256) = evm.decode_args()
  let args ← Evm_decode_args_tuple_u256_u256
  -- args.0 + args.1
  let v5 ← checkedAdd args.fst args.snd
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
  -- revert(value)
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
  -- let sum = a + b
  let sum ← IntTy.add (.u 8) a b
  -- (sum - low) * 2 / b % 7
  let v9 ← IntTy.sub (.u 8) sum ((sum >>> (UInt256.ofNat 1)) &&& (UInt256.ofNat 15))
  let v11 ← IntTy.mul (.u 8) v9 (UInt256.ofNat 2)
  let v12 ← checkedDiv v11 b
  let v14 ← checkedRem v12 (UInt256.ofNat 7)
  return v14

/-- `ints::wrapping` -/
def wrapping (a : UInt256) (b : UInt256) : FeM UInt256 := do
  -- (a * b) << 3
  let v6 := IntTy.shl (.i 32) (IntTy.mulW (.i 32) a b) (UInt256.ofNat 3)
  return v6

/-- `Signed { a, b } -> i32`, selector `0x6effafad` (`signed(int32,int32)`) -/
def recv_Signed (a : UInt256) (b : UInt256) : FeM UInt256 := do
  -- if a < b {
  if UInt256.sltBool a b then
    -- return -a
    let v3 ← IntTy.neg (.i 32) a
    return v3
  else
    -- wrapping(a, b) + (a / b) - (a % b) + -5
    let v6 ← wrapping a b
    let v7 ← IntTy.div (.i 32) a b
    let v8 ← IntTy.add (.i 32) v6 v7
    let v9 ← IntTy.rem (.i 32) a b
    let v10 ← IntTy.sub (.i 32) v8 v9
    let v12 ← IntTy.add (.i 32) v10 (IntTy.wrap (.i 256) (-5))
    return v12

/-- `Mixed { a, b } -> i256`, selector `0x728ac8e2` (`mixed(int256,uint16)`) -/
def recv_Mixed (a : UInt256) (b : UInt256) : FeM UInt256 := do
  -- let small: i8 = a.downcast_truncate()
  let small ← downcast_truncate_i256_i8 a
  -- let bits: i256 = wide.downcast_unchecked()
  let bits ← downcast_unchecked_u256_i256 b
  -- (a >> 2) ** 2 + (small as i256) + bits + (!a)
  let v11 ← IntTy.pow (.i 256) (IntTy.shr (.i 256) a (UInt256.ofNat 2)) (UInt256.ofNat 2)
  let v13 ← IntTy.add (.i 256) v11 small
  let v14 ← IntTy.add (.i 256) v13 bits
  let v16 ← IntTy.add (.i 256) v14 (IntTy.not (.i 256) a)
  return v16

/-- `Context -> u256`, selector `0xd0496d6a` (`context()`) -/
def recv_Context : FeM UInt256 := do
  let mut r1 : UInt256 := default
  let mut r2 : Wei := default
  let mut r3 : UInt256 := default
  -- evm.address().word() ^ evm.value().as_wei() ^ evm.origin().word() ^ evm.block_number()
  let v1 ← Evm_address
  r1 := v1
  let v3 ← Address_word r1
  let v5 ← Evm_value
  r2 := v5
  let v7 ← Wei_as_wei r2
  let v10 ← Evm_origin
  r3 := v10
  let v12 ← Address_word r3
  let v15 ← Evm_block_number
  return ((v3 ^^^ v7) ^^^ v12) ^^^ v15

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
  let join : Shape → FeM Shape := fun v2 => do
    return v2
  -- if width == 0 {
  if decide (width = (UInt256.ofNat 0)) then
    join Shape.Empty
  else
    let join_1 : Shape → FeM Shape := fun v3 => do
      join v3
    if decide (width = height) then
      join_1 (Shape.Square width)
    else
      join_1 (Shape.Rect width height)

/-- `Area { width, height } -> u256`, selector `0x15529a52` (`area(uint256,uint256)`) -/
def recv_Area (width_0 : UInt256) (height_1 : UInt256) : FeM UInt256 := do
  -- match shape(width, height) {
  let v3 ← shape width_0 height_1
  let join : UInt256 → FeM UInt256 := fun v2 => do
    return v2
  match v3 with
  | .Empty =>
    join (UInt256.ofNat 0)
  | .Square .. =>
    let side := v3.Square_0
    let v8 ← checkedMul side side
    join v8
  | .Rect .. =>
    let v14 ← checkedMul v3.Rect_0 v3.Rect_1
    join v14

/-- `enums::halve` -/
def halve (value : UInt256) : FeM Option_u256 := do
  -- if value % 2 == 0 {
  let v4 ← checkedRem value (UInt256.ofNat 2)
  let join : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  if decide (v4 = (UInt256.ofNat 0)) then
    -- Option::Some(value / 2)
    let v9 ← checkedDiv value (UInt256.ofNat 2)
    join (Option_u256.Some v9)
  else
    join Option_u256.None

/-- `Half { value } -> u256`, selector `0xdee6088b` (`half(uint256)`) -/
def recv_Half (value : UInt256) : FeM UInt256 := do
  -- match halve(value) {
  let v2 ← halve value
  let join : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v2 with
  | .Some .. =>
    join v2.Some_0
  | _ =>
    join value

/-- `Grow { side } -> u256`, selector `0x28531f06` (`grow(uint256)`) -/
def recv_Grow (side_0 : UInt256) : FeM UInt256 := do
  let mut current : Shape := default
  -- var current = Shape::Square(side)
  current := (Shape.Square side_0)
  let join : Shape → FeM UInt256 := fun current => do
    let mut current := current
    let join_1 : Shape → UInt256 → FeM UInt256 := fun current v1 => do
      let mut current := current
      return v1
    -- match current {
    match current with
    | .Square .. =>
      join_1 current current.Square_0
    | _ =>
      join_1 current (UInt256.ofNat 0)
  -- if let Shape::Square(mut inner) = current {
  match current with
  | .Square .. =>
    -- inner += 1
    let v8 ← checkedAdd current.Square_0 (UInt256.ofNat 1)
    current := (current.set_Square_0 v8)
    join current
  | _ =>
    join current

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
  rfl

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
  -- var total: u256 = 0
  total := (UInt256.ofNat 0)
  -- var i: u256 = 0
  i := (UInt256.ofNat 0)
  let rec loop (total : UInt256) (i : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut i := i
    -- while i < n {
    if decide (i.toNat < n.toNat) then
      -- i += 1
      let i_10 ← checkedAdd i (UInt256.ofNat 1)
      i := i_10
      -- total += i
      let total_16 ← checkedAdd total i
      total := total_16
      loop total i
    else
      return total
  partial_fixpoint
  loop total i

/-- `loops::step` -/
def step (value : UInt256) : FeM Option_u256 := do
  let join : Option_u256 → FeM Option_u256 := fun v1 => do
    return v1
  -- if value == 1 {
  if decide (value = (UInt256.ofNat 1)) then
    join Option_u256.None
  else
    let v10 ← checkedRem value (UInt256.ofNat 2)
    let join_1 : Option_u256 → FeM Option_u256 := fun v2 => do
      join v2
    if decide (v10 = (UInt256.ofNat 0)) then
      -- Option::Some(value / 2)
      let v15 ← checkedDiv value (UInt256.ofNat 2)
      join_1 (Option_u256.Some v15)
    else
      -- Option::Some(3 * value + 1)
      let v20 ← checkedMul (UInt256.ofNat 3) value
      let v22 ← checkedAdd v20 (UInt256.ofNat 1)
      join_1 (Option_u256.Some v22)

/-- `Collatz { start, limit } -> u256`, selector `0xea732925` (`collatz(uint256,uint256)`) -/
def recv_Collatz (start : UInt256) (limit : UInt256) : FeM UInt256 := do
  let mut value : UInt256 := default
  let mut steps : UInt256 := default
  -- var value = start
  value := start
  -- var steps: u256 = 0
  steps := (UInt256.ofNat 0)
  let rec loop (value : UInt256) (steps : UInt256) : FeM UInt256 := do
    let mut value := value
    let mut steps := steps
    -- if steps == limit {
    if decide (steps = limit) then
      return limit
    else
      -- match step(value) {
      let v12 ← step value
      match (← pure v12) with
      | .Some .. =>
        -- value = next
        value := v12.Some_0
        -- steps += 1
        let steps_19 ← checkedAdd steps (UInt256.ofNat 1)
        steps := steps_19
        loop value steps
      | .None =>
        return steps
  partial_fixpoint
  loop value steps

-- END fe-lean-export

end

/-- `triangle(3)` runs the loop body three times and returns `1 + 2 + 3`. -/
theorem triangle_three (I : ExecutionEnv) (w : World) :
    (recv_Triangle (UInt256.ofNat 3)).exec I w = some (.ok (UInt256.ofNat 6, w)) := by
  simp [recv_Triangle]
  iterate 4 (rw [recv_Triangle.loop]; simp +decide [checkedAdd])

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
  -- var acc: u256 = 1
  acc := (UInt256.ofNat 1)
  -- var index: usize = 0
  index := (UInt256.ofNat 0)
  -- var started = false
  started := false
  let rec loop (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
    let mut acc := acc
    let mut index := index
    let mut started := started
    let mut r3 := r3
    -- while index < n {
    if decide (index.toNat < n.toNat) then
      -- let end = if index + width + 1 < n { index + width + 1 } else { n }
      let v17 ← checkedAdd index width
      let v19 ← checkedAdd v17 (UInt256.ofNat 1)
      let join : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → UInt256 → FeM UInt256 := fun acc index started r3 «end» => do
        let mut acc := acc
        let mut index := index
        let mut started := started
        let mut r3 := r3
        let rec loop_1 (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) : FeM UInt256 := do
          let mut acc := acc
          let mut index := index
          let mut started := started
          let mut r3 := r3
          -- if end % 2 == 1 {
          let v60 ← checkedRem «end» (UInt256.ofNat 2)
          let join_1 : UInt256 → UInt256 → Bool → Range_Unknown_Unknown → FeM UInt256 := fun acc index started r3 => do
            let mut acc := acc
            let mut index := index
            let mut started := started
            let mut r3 := r3
            -- index = end
            index := «end»
            loop acc index started r3
          if decide (v60 = (UInt256.ofNat 1)) then
            -- acc = acc + end as u256
            let acc_66 ← checkedAdd acc «end»
            acc := acc_66
            -- started = true
            started := true
            join_1 acc index started r3
          else
            join_1 acc index started r3
        partial_fixpoint
        -- if started {
        if started then
          -- for _ in index..end { acc = acc * 2 % 1000003 }
          r3 := (Range_Unknown_Unknown.mk index «end»)
          let v38 ← Range_Unknown_Unknown_start r3
          let rec loop_2 (acc : UInt256) (index : UInt256) (started : Bool) (r3 : Range_Unknown_Unknown) (v3 : UInt256) : FeM UInt256 := do
            let mut acc := acc
            let mut index := index
            let mut started := started
            let mut r3 := r3
            -- for _ in index..end { acc = acc * 2 % 1000003 }
            let v41 ← Range_Unknown_Unknown_has r3 v3
            if v41 then
              let _ ← Range_Unknown_Unknown_at r3 v3
              -- acc = acc * 2 % 1000003
              let v47 ← checkedMul acc (UInt256.ofNat 2)
              let acc_49 ← checkedRem v47 (UInt256.ofNat 1000003)
              acc := acc_49
              -- for _ in index..end { acc = acc * 2 % 1000003 }
              let v53 ← Range_Unknown_Unknown_next r3 v3
              loop_2 acc index started r3 v53
            else
              loop_1 acc index started r3
          partial_fixpoint
          loop_2 acc index started r3 v38
        else
          loop_1 acc index started r3
      if decide (v19.toNat < n.toNat) then
        -- index + width + 1
        let v25 ← checkedAdd index width
        let v27 ← checkedAdd v25 (UInt256.ofNat 1)
        join acc index started r3 v27
      else
        join acc index started r3 n
    else
      return acc
  partial_fixpoint
  loop acc index started r3

/-- `Windows { n, width } -> u256`, selector `0x6a39ed49` (`windows(uint256,uint256)`) -/
def recv_Windows (n : UInt256) (width : UInt256) : FeM UInt256 := do
  -- windows(n.downcast_truncate(), width.downcast_truncate())
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
  -- var i: u256 = 0
  i := (UInt256.ofNat 0)
  -- var found: u256 = 0
  found := (UInt256.ofNat 0)
  -- var done = false
  done := false
  let rec loop (i : UInt256) (found : UInt256) (done : Bool) (j : UInt256) : FeM UInt256 := do
    let mut i := i
    let mut found := found
    let mut done := done
    let mut j := j
    let join : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun i found done j => do
      let mut i := i
      let mut found := found
      let mut done := done
      let mut j := j
      return found
    -- while i < n {
    if decide (i.toNat < n.toNat) then
      -- var j: u256 = 0
      j := (UInt256.ofNat 0)
      let rec loop_1 (i : UInt256) (found : UInt256) (done : Bool) (j : UInt256) : FeM UInt256 := do
        let mut i := i
        let mut found := found
        let mut done := done
        let mut j := j
        let join_1 : UInt256 → UInt256 → Bool → UInt256 → FeM UInt256 := fun i found done j => do
          let mut i := i
          let mut found := found
          let mut done := done
          let mut j := j
          -- if done { break }
          if done then
            join i found done j
          else
            -- i += 1
            let i_46 ← checkedAdd i (UInt256.ofNat 1)
            i := i_46
            loop i found done j
        -- while j < i {
        if decide (j.toNat < i.toNat) then
          -- if i * j == 12 {
          let v20 ← checkedMul i j
          if decide (v20 = (UInt256.ofNat 12)) then
            -- found = i * 100 + j
            let v26 ← checkedMul i (UInt256.ofNat 100)
            let found_28 ← checkedAdd v26 j
            found := found_28
            -- done = true
            done := true
            join_1 i found done j
          else
            -- j += 1
            let j_38 ← checkedAdd j (UInt256.ofNat 1)
            j := j_38
            loop_1 i found done j
        else
          join_1 i found done j
      partial_fixpoint
      loop_1 i found done j
    else
      join i found done j
  partial_fixpoint
  loop i found done j

/-- `BreakBoth { n } -> u256`, selector `0x17ea0cd5` (`breakBoth(uint256)`) -/
def recv_BreakBoth (n : UInt256) : FeM UInt256 := do
  -- break_both(n)
  let v1 ← break_both n
  return v1

/-- `nested_loops::continue_outer` -/
def continue_outer (n : UInt256) : FeM UInt256 := do
  let mut i : UInt256 := default
  let mut total : UInt256 := default
  let mut j : UInt256 := default
  let mut skip : Bool := default
  -- var i: u256 = 0
  i := (UInt256.ofNat 0)
  -- var total: u256 = 0
  total := (UInt256.ofNat 0)
  let rec loop (i : UInt256) (total : UInt256) (j : UInt256) (skip : Bool) : FeM UInt256 := do
    let mut i := i
    let mut total := total
    let mut j := j
    let mut skip := skip
    -- while i < n {
    if decide (i.toNat < n.toNat) then
      -- i += 1
      let i_11 ← checkedAdd i (UInt256.ofNat 1)
      i := i_11
      -- var j: u256 = 0
      j := (UInt256.ofNat 0)
      -- var skip = false
      skip := false
      let rec loop_1 (i : UInt256) (total : UInt256) (j : UInt256) (skip : Bool) : FeM UInt256 := do
        let mut i := i
        let mut total := total
        let mut j := j
        let mut skip := skip
        let join : UInt256 → UInt256 → UInt256 → Bool → FeM UInt256 := fun i total j skip => do
          let mut i := i
          let mut total := total
          let mut j := j
          let mut skip := skip
          -- if skip { continue }
          if skip then
            loop i total j skip
          else
            -- total += i
            let total_42 ← checkedAdd total i
            total := total_42
            loop i total j skip
        -- while j < i {
        if decide (j.toNat < i.toNat) then
          -- if j == 3 {
          if decide (j = (UInt256.ofNat 3)) then
            -- skip = true
            skip := true
            join i total j skip
          else
            -- j += 1
            let j_33 ← checkedAdd j (UInt256.ofNat 1)
            j := j_33
            loop_1 i total j skip
        else
          join i total j skip
      partial_fixpoint
      loop_1 i total j skip
    else
      return total
  partial_fixpoint
  loop i total j skip

/-- `ContinueOuter { n } -> u256`, selector `0x0dec9eef` (`continueOuter(uint256)`) -/
def recv_ContinueOuter (n : UInt256) : FeM UInt256 := do
  -- continue_outer(n)
  let v1 ← continue_outer n
  return v1

/-- `nested_loops::return_inner` -/
def return_inner (n : UInt256) : FeM UInt256 := do
  let mut i : UInt256 := default
  let mut j : UInt256 := default
  -- var i: u256 = 0
  i := (UInt256.ofNat 0)
  let rec loop (i : UInt256) (j : UInt256) : FeM UInt256 := do
    let mut i := i
    let mut j := j
    -- while i < n {
    if decide (i.toNat < n.toNat) then
      -- var j: u256 = 0
      j := (UInt256.ofNat 0)
      let rec loop_1 (i : UInt256) (j : UInt256) : FeM UInt256 := do
        let mut i := i
        let mut j := j
        -- while j < n {
        if decide (j.toNat < n.toNat) then
          -- if i + j == 7 { return i * 10 + j }
          let v16 ← checkedAdd i j
          if decide (v16 = (UInt256.ofNat 7)) then
            -- return i * 10 + j
            let v22 ← checkedMul i (UInt256.ofNat 10)
            let v24 ← checkedAdd v22 j
            return v24
          else
            -- j += 1
            let j_29 ← checkedAdd j (UInt256.ofNat 1)
            j := j_29
            loop_1 i j
        else
          -- i += 1
          let i_34 ← checkedAdd i (UInt256.ofNat 1)
          i := i_34
          loop i j
      partial_fixpoint
      loop_1 i j
    else
      return UInt256.ofNat 0
  partial_fixpoint
  loop i j

/-- `ReturnInner { n } -> u256`, selector `0x92ba46ad` (`returnInner(uint256)`) -/
def recv_ReturnInner (n : UInt256) : FeM UInt256 := do
  -- return_inner(n)
  let v1 ← return_inner n
  return v1

/-- `nested_loops::three_levels` -/
def three_levels (n : UInt256) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut k : UInt256 := default
  let mut r2 : Range_Known_0_Unknown := default
  let mut r3 : Range_Known_0_Unknown := default
  -- var total: u256 = 0
  total := (UInt256.ofNat 0)
  -- for i in 0..n {
  r2 := (Range_Known_0_Unknown.mk () n)
  let v10 ← Range_start_0 r2
  let rec loop (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v1 : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut k := k
    let mut r2 := r2
    let mut r3 := r3
    -- for i in 0..n {
    let v13 ← Range_has_0 r2 v1
    if v13 then
      let v15 ← Range_at_0 r2 v1
      let i := v15
      -- for j in 0..i {
      r3 := (Range_Known_0_Unknown.mk () i)
      let v21 ← Range_start_0 r3
      let rec loop_1 (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) (v2 : UInt256) : FeM UInt256 := do
        let mut total := total
        let mut k := k
        let mut r2 := r2
        let mut r3 := r3
        -- for j in 0..i {
        let v24 ← Range_has_0 r3 v2
        if v24 then
          let v26 ← Range_at_0 r3 v2
          let j := v26
          -- var k: usize = 0
          k := (UInt256.ofNat 0)
          let rec loop_2 (total : UInt256) (k : UInt256) (r2 : Range_Known_0_Unknown) (r3 : Range_Known_0_Unknown) : FeM UInt256 := do
            let mut total := total
            let mut k := k
            let mut r2 := r2
            let mut r3 := r3
            -- while k < j {
            if decide (k.toNat < j.toNat) then
              -- if (i + j + k) % 3 == 0 { total += 1 } else { total += 2 }
              let v33 ← checkedAdd i j
              let v35 ← checkedAdd v33 k
              let v37 ← checkedRem v35 (UInt256.ofNat 3)
              let join : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun total k r2 r3 => do
                let mut total := total
                let mut k := k
                let mut r2 := r2
                let mut r3 := r3
                -- k += 1
                let k_54 ← checkedAdd k (UInt256.ofNat 1)
                k := k_54
                loop_2 total k r2 r3
              if decide (v37 = (UInt256.ofNat 0)) then
                -- total += 1
                let total_42 ← checkedAdd total (UInt256.ofNat 1)
                total := total_42
                join total k r2 r3
              else
                -- total += 2
                let total_48 ← checkedAdd total (UInt256.ofNat 2)
                total := total_48
                join total k r2 r3
            else
              -- if j % 2 == 0 { total += 10 }
              let v58 ← checkedRem j (UInt256.ofNat 2)
              let join_1 : UInt256 → UInt256 → Range_Known_0_Unknown → Range_Known_0_Unknown → FeM UInt256 := fun total k r2 r3 => do
                let mut total := total
                let mut k := k
                let mut r2 := r2
                let mut r3 := r3
                -- for j in 0..i {
                let v70 ← Range_next_0 r3 v2
                loop_1 total k r2 r3 v70
              if decide (v58 = (UInt256.ofNat 0)) then
                -- total += 10
                let total_63 ← checkedAdd total (UInt256.ofNat 10)
                total := total_63
                join_1 total k r2 r3
              else
                join_1 total k r2 r3
          partial_fixpoint
          loop_2 total k r2 r3
        else
          -- for i in 0..n {
          let v74 ← Range_next_0 r2 v1
          loop total k r2 r3 v74
      partial_fixpoint
      loop_1 total k r2 r3 v21
    else
      return total
  partial_fixpoint
  loop total k r2 r3 v10

/-- `ThreeLevels { n } -> u256`, selector `0x81037424` (`threeLevels(uint256)`) -/
def recv_ThreeLevels (n : UInt256) : FeM UInt256 := do
  -- three_levels(n.downcast_truncate())
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
  -- items[at] += by
  checkIndex «at» 4
  let v6 ← checkedAdd items[«at».toNat]! «by»
  checkIndex «at» 4
  items := (items.set! «at».toNat v6)
  return ((), items)

/-- `Pick { index, value } -> u256`, selector `0xa62f4550` (`pick(uint256,uint256)`) -/
def recv_Pick (index : UInt256) (value : UInt256) : FeM UInt256 := do
  let mut items : (Vector UInt256 4) := default
  -- var items: [u256; 4] = [value; 4]
  items := (Vector.replicate 4 value)
  -- items[0] = 7
  let v5 := (UInt256.ofNat 0)
  checkIndex v5 4
  items := (items.set! v5.toNat (UInt256.ofNat 7))
  -- bump(mut items, at: index, by: 1)
  let (v9, v9_0) ← bump items index (UInt256.ofNat 1)
  items := v9_0
  -- items[index] + items[3]
  checkIndex index 4
  let v11 := (UInt256.ofNat 3)
  checkIndex v11 4
  let v13 ← checkedAdd items[index.toNat]! items[v11.toNat]!
  return v13

/-- `arrays::WEIGHTS` -/
def WEIGHTS : FeM (Vector UInt256 3) := do
  let v3 := #v[(UInt256.ofNat 1), (UInt256.ofNat 10), (UInt256.ofNat 100)]
  return v3

/-- `Weigh { values } -> u256`, selector `0x2f57374e` (`weigh(uint256[3])`) -/
def recv_Weigh (values : (Vector UInt256 3)) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut i : UInt256 := default
  -- var total: u256 = 0
  total := (UInt256.ofNat 0)
  -- var i: usize = 0
  i := (UInt256.ofNat 0)
  let rec loop (total : UInt256) (i : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut i := i
    -- while i < 3 {
    if decide (i.toNat < (UInt256.ofNat 3).toNat) then
      -- total += values[i] * WEIGHTS[i]
      let i_9 := i
      checkIndex i_9 3
      let v11 ← WEIGHTS
      let i_12 := i
      checkIndex i_12 3
      let v14 ← checkedMul values[i_9.toNat]! v11[i_12.toNat]!
      let total_16 ← checkedAdd total v14
      total := total_16
      -- i += 1
      let i_21 ← checkedAdd i (UInt256.ofNat 1)
      i := i_21
      loop total i
    else
      return total
  partial_fixpoint
  loop total i

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

/-- `packed.delta` -/
abbrev Field.packed.delta : Place :=
  Field.packed.field Layout.Packed 2

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
  -- let old = packed.delta
  let old ← loadIntAt (.i 16) Field.packed.delta ⟨2, 2, true⟩
  -- packed.delta = delta
  storeIntAt (.i 16) Field.packed.delta ⟨2, 2, true⟩ delta
  return old

/-- `Replace { flag, small, delta, owner, total } -> u256`, selector `0x1e84534a` (`replace(bool,uint8,int16,address,uint256)`) -/
def recv_Replace (flag : Bool) (small : UInt256) (delta : UInt256) (owner : UInt256) (total : UInt256) : FeM UInt256 := do
  -- let old = packed
  let packed_1 ← load_Packed Field.packed
  -- packed = Packed { flag, small, delta, owner, total }
  store_Packed Field.packed (Packed.mk flag small delta owner total)
  return packed_1.total

/-- `Advance { by } -> u256`, selector `0x71d6ddd6` (`advance(uint256)`) -/
def recv_Advance («by» : UInt256) : FeM UInt256 := do
  -- match phase {
  let v3 ← load_Phase Field.phase
  let join : UInt256 → FeM UInt256 := fun v1 => do
    return v1
  match v3 with
  | .Idle =>
    -- phase = Phase::Running(1, by)
    store_Phase Field.phase (Phase.Running (UInt256.ofNat 1) «by»)
    join (UInt256.ofNat 0)
  | .Running .. =>
    let count ← loadInt (.u 64) (Field.phase.offset 1)
    let sum ← load (Field.phase.offset 2)
    -- phase = Phase::Done { ok: sum > by }
    store_Phase Field.phase (Phase.Done (decide («by».toNat < sum.toNat)))
    join sum
  | .Done .. =>
    let ok ← loadBool (Field.phase.offset 1)
    let join_1 : UInt256 → FeM UInt256 := fun v2 => do
      join v2
    -- if ok { 1 } else { 2 }
    if ok then
      join_1 (UInt256.ofNat 1)
    else
      join_1 (UInt256.ofNat 2)

/-- `Mark { at, level } -> u8`, selector `0x0a774e1e` (`mark(uint256,uint8)`) -/
def recv_Mark («at» : UInt256) (level : UInt256) : FeM UInt256 := do
  -- let old = levels[at]
  checkIndex «at» 3
  let old ← loadInt (.u 8) (Field.levels.index 1 «at»)
  -- levels[at] = level
  checkIndex «at» 3
  storeInt (.u 8) (Field.levels.index 1 «at») level
  -- narrow = old
  storeIntAt (.u 8) Field.narrow ⟨1, 1, true⟩ old
  let narrow ← loadIntAt (.u 8) Field.narrow ⟨1, 1, true⟩
  return narrow

/-- `Lock -> bool`, selector `0xf83d08ba` (`lock()`) -/
def recv_Lock : FeM Bool := do
  -- let was = lock.value
  let was ← loadBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩
  -- lock.value = true
  storeBoolAt ((Field.lock.pin .transient).field Layout.TSlot_bool 0) ⟨0, 1, false⟩ true
  -- alone = was
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

/-- `store.voted` -/
abbrev Field.store.voted : Place :=
  Field.store.field Layout.Store 0

/-- `store.flags` -/
abbrev Field.store.flags : Place :=
  Field.store.field Layout.Store 1

/-- The `init` of contract `Entries`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Vote { voter, proposal } -> bool`, selector `0xb384abef` (`vote(uint256,uint256)`) -/
def recv_Vote (voter : UInt256) (proposal : UInt256) : FeM Bool := do
  -- let before = store.voted[(voter, proposal)]
  let voted_entry ← StorageMap_locate_tuple_u256_u256_bool Field.store.voted Field.store.voted.slot (voter, proposal)
  let before ← loadBool (Place.mk .storage voted_entry.slot)
  -- store.voted[(voter, proposal)] = true
  let voted_entry_1 ← StorageMap_locate_tuple_u256_u256_bool Field.store.voted Field.store.voted.slot (voter, proposal)
  storeBool (Place.mk .storage voted_entry_1.slot) true
  return before

/-- `Flag { on } -> u256`, selector `0xa92a4c3b` (`flag(bool)`) -/
def recv_Flag (on : Bool) : FeM UInt256 := do
  -- store.flags[on] += 1
  let flags_on ← StorageMap_locate_bool_u256 Field.store.flags Field.store.flags.slot on
  let v2 ← load (Place.mk .storage flags_on.slot)
  let v3 ← checkedAdd v2 (UInt256.ofNat 1)
  let flags_on_1 ← StorageMap_locate_bool_u256 Field.store.flags Field.store.flags.slot on
  store (Place.mk .storage flags_on_1.slot) v3
  -- store.flags[on]
  let flags_on_2 ← StorageMap_locate_bool_u256 Field.store.flags Field.store.flags.slot on
  let v5 ← load (Place.mk .storage flags_on_2.slot)
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
  -- a + b + c + d + e + f + g + h + i + j
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

def Sum_decode_from_CallData_k5 (v4 : UInt256) (v9 : UInt256) (v16 : UInt256) (v25 : UInt256) (v36 : UInt256) (v49 : UInt256) (v64 : UInt256) (v81 : UInt256) (v100 : UInt256) (v121 : UInt256) : FeM Sum := do
  return Sum.mk v4 v9 v16 v25 v36 v49 v64 v81 v100 v121

def Sum_decode_from_CallData_k4 (v0 : CallData) (v1 : UInt256) (v2 : UInt256) (v4 : UInt256) (v9 : UInt256) (v16 : UInt256) (v25 : UInt256) (v36 : UInt256) (v49 : UInt256) (v64 : UInt256) (v81 : UInt256) (v97 : UInt256) : FeM Sum := do
  let v98 ← abi_field_head_size_u256
  let v99 ← checkedAdd v97 v98
  let v100 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v99 v2
  let v103 ← abi_field_head_size_u256
  let v104 ← checkedAdd v1 v103
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
  let v121 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v120 v2
  Sum_decode_from_CallData_k5 v4 v9 v16 v25 v36 v49 v64 v81 v100 v121

def Sum_decode_from_CallData_k3 (v0 : CallData) (v1 : UInt256) (v2 : UInt256) (v4 : UInt256) (v9 : UInt256) (v16 : UInt256) (v25 : UInt256) (v36 : UInt256) (v49 : UInt256) (v64 : UInt256) (v72 : UInt256) (v73 : UInt256) : FeM Sum := do
  let v74 ← checkedAdd v72 v73
  let v75 ← abi_field_head_size_u256
  let v76 ← checkedAdd v74 v75
  let v77 ← abi_field_head_size_u256
  let v78 ← checkedAdd v76 v77
  let v79 ← abi_field_head_size_u256
  let v80 ← checkedAdd v78 v79
  let v81 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v80 v2
  let v84 ← abi_field_head_size_u256
  let v85 ← checkedAdd v1 v84
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
  Sum_decode_from_CallData_k4 v0 v1 v2 v4 v9 v16 v25 v36 v49 v64 v81 v97

def Sum_decode_from_CallData_k2 (v0 : CallData) (v1 : UInt256) (v2 : UInt256) (v4 : UInt256) (v9 : UInt256) (v16 : UInt256) (v25 : UInt256) (v36 : UInt256) (v49 : UInt256) : FeM Sum := do
  let v52 ← abi_field_head_size_u256
  let v53 ← checkedAdd v1 v52
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
  let v64 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v63 v2
  let v67 ← abi_field_head_size_u256
  let v68 ← checkedAdd v1 v67
  let v69 ← abi_field_head_size_u256
  let v70 ← checkedAdd v68 v69
  let v71 ← abi_field_head_size_u256
  let v72 ← checkedAdd v70 v71
  let v73 ← abi_field_head_size_u256
  Sum_decode_from_CallData_k3 v0 v1 v2 v4 v9 v16 v25 v36 v49 v64 v72 v73

def Sum_decode_from_CallData_k1 (v0 : CallData) (v1 : UInt256) (v2 : UInt256) (v4 : UInt256) (v9 : UInt256) (v16 : UInt256) (v25 : UInt256) : FeM Sum := do
  let v28 ← abi_field_head_size_u256
  let v29 ← checkedAdd v1 v28
  let v30 ← abi_field_head_size_u256
  let v31 ← checkedAdd v29 v30
  let v32 ← abi_field_head_size_u256
  let v33 ← checkedAdd v31 v32
  let v34 ← abi_field_head_size_u256
  let v35 ← checkedAdd v33 v34
  let v36 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v35 v2
  let v39 ← abi_field_head_size_u256
  let v40 ← checkedAdd v1 v39
  let v41 ← abi_field_head_size_u256
  let v42 ← checkedAdd v40 v41
  let v43 ← abi_field_head_size_u256
  let v44 ← checkedAdd v42 v43
  let v45 ← abi_field_head_size_u256
  let v46 ← checkedAdd v44 v45
  let v47 ← abi_field_head_size_u256
  let v48 ← checkedAdd v46 v47
  let v49 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v48 v2
  Sum_decode_from_CallData_k2 v0 v1 v2 v4 v9 v16 v25 v36 v49

/-- `<Sum as Decode>::decode_from<CallData>` -/
def Sum_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Sum := do
  let v2 ← len_CallData v0
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v2
  let v7 ← abi_field_head_size_u256
  let v8 ← checkedAdd v1 v7
  let v9 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v8 v2
  let v12 ← abi_field_head_size_u256
  let v13 ← checkedAdd v1 v12
  let v14 ← abi_field_head_size_u256
  let v15 ← checkedAdd v13 v14
  let v16 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v15 v2
  let v19 ← abi_field_head_size_u256
  let v20 ← checkedAdd v1 v19
  let v21 ← abi_field_head_size_u256
  let v22 ← checkedAdd v20 v21
  let v23 ← abi_field_head_size_u256
  let v24 ← checkedAdd v22 v23
  let v25 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v24 v2
  Sum_decode_from_CallData_k1 v0 v1 v2 v4 v9 v16 v25

/-- `core::abi::Decode::decode_from_prechecked_head<Sum, Sol, CallData>` -/
def decode_from_prechecked_head_Sum_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Sum := do
  -- Self::decode_from(input, pos)
  let v3 ← Sum_decode_from_CallData input pos
  return v3

/-- `core::contracts::decode_runtime_args<Evm, Sol, Sum>` -/
def decode_runtime_args_Evm_Sol_Sum : FeM Sum := do
  let mut input : CallData := default
  -- let input = host.input()
  let input_2 ← Evm_input
  input := input_2
  -- let base = A::SELECTOR_SIZE
  let base ← Sol_SELECTOR_SIZE
  -- let len = input.len()
  let len ← len_CallData input
  -- A::validate_runtime_head(input_len: len, base, head_size: T::HEAD_SIZE)
  let v9 ← Sum_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  -- T::decode_from_prechecked_head(input, base, len)
  let v12 ← decode_from_prechecked_head_Sum_Sol_CallData input base len
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

/-- `cell.v` -/
abbrev Field.cell.v : Place :=
  Field.cell.field Layout.Cell 0

/-- The `init` of contract `Projections`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `Cell::slot` -/
def Cell_slot (self : Place) : FeM Place := do
  -- mut self.v
  let v1 := (self.field Layout.Cell 0)
  return v1

/-- `Direct { by } -> u256`, selector `0x9bbc59f9` (`direct(uint256)`) -/
def recv_Direct («by» : UInt256) : FeM UInt256 := do
  -- cell.slot() += by
  let v1 := Field.cell
  let v2 ← Cell_slot v1
  let v3 ← load v2
  let v4 ← checkedAdd v3 «by»
  store v2 v4
  -- cell.v
  let v6 ← load Field.cell.v
  return v6

/-- `Cell::get` -/
def Cell_get (self : Place) : FeM UInt256 := do
  -- self.v
  let v1 ← load (self.field Layout.Cell 0)
  return v1

/-- `Cell::set` -/
def Cell_set (self : Place) (v : UInt256) : FeM Unit := do
  -- self.v = v
  store (self.field Layout.Cell 0) v
  return ()

/-- `Cell::cached` -/
def Cell_cached (self_0 : Place) : FeM (UInt256 × (UInt256 → FeM Unit)) := do
  let mut tmp : UInt256 := default
  -- var tmp = self.get()
  let tmp_2 ← Cell_get self_0
  tmp := tmp_2
  let slide : UInt256 → FeM Unit := fun g => do
    let mut tmp := tmp
    tmp := g
    -- self.set(tmp)
    let _ ← Cell_set self_0 tmp
    return ()
  return (tmp, slide)

/-- `Slide { by } -> u256`, selector `0x235361d9` (`slide(uint256)`) -/
def recv_Slide («by» : UInt256) : FeM UInt256 := do
  let mut v2 : UInt256 := default
  -- cell.cached() += by
  let v1 := Field.cell
  let (v2_g, v2_k) ← Cell_cached v1
  v2 := v2_g
  let v4 ← checkedAdd v2 «by»
  v2 := v4
  let _ ← v2_k v2
  -- cell.v
  let v6 ← load Field.cell.v
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
  -- var pair = (a, b)
  pair := (a, b)
  -- first(mut pair) += b
  let (v5_g, v5_k) ← first pair
  v5 := v5_g
  let v7 ← checkedAdd v5 b
  v5 := v7
  let v5_0 ← v5_k v5
  pair := v5_0
  return pair.fst

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

/-! ## `collide`: binders spelled like what the body names

Locals named like a function, a constant and the prelude's `load` and `store` that the body
calls, top-level names spelled like the exporter's own binders (`v3`, `size`, `b1`), two msgs
with a `Run` variant, and a field a pattern destructures.  The exporter names every binder apart
from what its definition names: the call of the Fe function `b1` inside the loop stays a call of
it. -/

namespace FeProofs.Fixtures.Collide

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: collide

export Lib (CallData Evm_input Evm_return_value_Sol_u256 Sol_SELECTOR_SIZE Sol_validate_runtime_head abi_field_head_size_tuple_u256_u256 abi_field_head_size_u256 decode_msg_field_from_Sol_tuple_u256_u256_CallData decode_msg_field_from_Sol_u256_CallData len_CallData)

def Field.count : Place :=
  .storage (UInt256.ofNat 0)

structure Run where
  x : UInt256
deriving Inhabited

structure Spin where
  n : UInt256
deriving Inhabited

structure Pairs where
  t : (UInt256 × UInt256)
deriving Inhabited

/-- The `init` of contract `Collide`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `collide::double` -/
def double (x : UInt256) : FeM UInt256 := do
  -- x * 2
  let v3_1 ← checkedMul x (UInt256.ofNat 2)
  return v3_1

/-- `collide::v3` -/
def v3 (x : UInt256) : FeM UInt256 := do
  -- x + 3
  let v3_1 ← checkedAdd x (UInt256.ofNat 3)
  return v3_1

/-- `collide::bounds::limit` -/
def limit : FeM UInt256 := do
  return UInt256.ofNat 10

/-- `collide::size` -/
def size : FeM UInt256 := do
  return UInt256.ofNat 4

/-- `Run { x } -> u256`, selector `0xa444f5e9` (`run(uint256)`) -/
def recv_CollideMsg_Run (x : UInt256) : FeM UInt256 := do
  -- let limit = x * 2
  let limit_1 ← checkedMul x (UInt256.ofNat 2)
  -- let double = limit + 1
  let double_1 ← checkedAdd limit_1 (UInt256.ofNat 1)
  -- let load = double + count
  let count_7 ← load Field.count
  let load_1 ← checkedAdd double_1 count_7
  -- let store = load + 1
  let store_1 ← checkedAdd load_1 (UInt256.ofNat 1)
  -- count = total
  store Field.count store_1
  -- v3(double(total)) + bounds::limit + size + count
  let v15 ← double store_1
  let v16 ← v3 v15
  let v17 ← limit
  let v18 ← checkedAdd v16 v17
  let v19 ← size
  let v20 ← checkedAdd v18 v19
  let count_21 ← load Field.count
  let v22 ← checkedAdd v20 count_21
  return v22

/-- `collide::b1` -/
def b1 (total : UInt256) (i : UInt256) : FeM UInt256 := do
  -- total + i
  let v4 ← checkedAdd total i
  return v4

/-- `Spin { n } -> u256`, selector `0xa5b6ea8f` (`spin(uint256)`) -/
def recv_Spin (n : UInt256) : FeM UInt256 := do
  let mut total : UInt256 := default
  let mut i : UInt256 := default
  -- var total: u256 = 0
  total := (UInt256.ofNat 0)
  -- var i: u256 = 0
  i := (UInt256.ofNat 0)
  let rec loop (total : UInt256) (i : UInt256) : FeM UInt256 := do
    let mut total := total
    let mut i := i
    -- while i < n {
    if decide (i.toNat < n.toNat) then
      -- i += 1
      let i_10 ← checkedAdd i (UInt256.ofNat 1)
      i := i_10
      -- total = b1(total, i)
      let total_17 ← b1 total i
      total := total_17
      loop total i
    else
      return total
  partial_fixpoint
  loop total i

/-- `Run { x } -> u256`, selector `0xeb034fa7` (`rerun(uint256)`) -/
def recv_OtherMsg_Run (x : UInt256) : FeM UInt256 := do
  return x

/-- `Pairs { t: (a, b) } -> u256`, selector `0x6a530d0d` (`pairs((uint256,uint256))`) -/
def recv_Pairs (v0 : (UInt256 × UInt256)) : FeM UInt256 := do
  -- a + b
  let v5 ← checkedAdd v0.fst v0.snd
  return v5

/-- `<Run as AbiSize>::HEAD_SIZE` -/
def Run_HEAD_SIZE : FeM UInt256 := do
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd (UInt256.ofNat 0) v1
  return v2

/-- `<Run as Decode>::decode_from<CallData>` -/
def Run_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Run := do
  let v2 ← len_CallData v0
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v2
  return Run.mk v4

/-- `core::abi::Decode::decode_from_prechecked_head<Run, Sol, CallData>` -/
def decode_from_prechecked_head_Run_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Run := do
  -- Self::decode_from(input, pos)
  let v3_1 ← Run_decode_from_CallData input pos
  return v3_1

/-- `core::contracts::decode_runtime_args<Evm, Sol, Run>` -/
def decode_runtime_args_Evm_Sol_Run : FeM Run := do
  let mut input : CallData := default
  -- let input = host.input()
  let input_2 ← Evm_input
  input := input_2
  -- let base = A::SELECTOR_SIZE
  let base ← Sol_SELECTOR_SIZE
  -- let len = input.len()
  let len ← len_CallData input
  -- A::validate_runtime_head(input_len: len, base, head_size: T::HEAD_SIZE)
  let v9 ← Run_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  -- T::decode_from_prechecked_head(input, base, len)
  let v12 ← decode_from_prechecked_head_Run_Sol_CallData input base len
  return v12

/-- The entry of `recv_CollideMsg_Run`, for `collide::CollideMsg::Run` -/
def recv_CollideMsg_Run_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Run
  let result ← recv_CollideMsg_Run message.x
  Evm_return_value_Sol_u256 result

/-- `<Spin as AbiSize>::HEAD_SIZE` -/
def Spin_HEAD_SIZE : FeM UInt256 := do
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd (UInt256.ofNat 0) v1
  return v2

/-- `<Spin as Decode>::decode_from<CallData>` -/
def Spin_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Spin := do
  let v2 ← len_CallData v0
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v2
  return Spin.mk v4

/-- `core::abi::Decode::decode_from_prechecked_head<Spin, Sol, CallData>` -/
def decode_from_prechecked_head_Spin_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Spin := do
  -- Self::decode_from(input, pos)
  let v3_1 ← Spin_decode_from_CallData input pos
  return v3_1

/-- `core::contracts::decode_runtime_args<Evm, Sol, Spin>` -/
def decode_runtime_args_Evm_Sol_Spin : FeM Spin := do
  let mut input : CallData := default
  -- let input = host.input()
  let input_2 ← Evm_input
  input := input_2
  -- let base = A::SELECTOR_SIZE
  let base ← Sol_SELECTOR_SIZE
  -- let len = input.len()
  let len ← len_CallData input
  -- A::validate_runtime_head(input_len: len, base, head_size: T::HEAD_SIZE)
  let v9 ← Spin_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  -- T::decode_from_prechecked_head(input, base, len)
  let v12 ← decode_from_prechecked_head_Spin_Sol_CallData input base len
  return v12

/-- The entry of `recv_Spin`, for `collide::CollideMsg::Spin` -/
def recv_Spin_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Spin
  let result ← recv_Spin message.n
  Evm_return_value_Sol_u256 result

/-- The entry of `recv_OtherMsg_Run`, for `collide::OtherMsg::Run` -/
def recv_OtherMsg_Run_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Run
  let result ← recv_OtherMsg_Run message.x
  Evm_return_value_Sol_u256 result

/-- `<Pairs as AbiSize>::HEAD_SIZE` -/
def Pairs_HEAD_SIZE : FeM UInt256 := do
  let v1 ← abi_field_head_size_tuple_u256_u256
  let v2 ← checkedAdd (UInt256.ofNat 0) v1
  return v2

/-- `<Pairs as Decode>::decode_from<CallData>` -/
def Pairs_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Pairs := do
  let v2 ← len_CallData v0
  let v4 ← decode_msg_field_from_Sol_tuple_u256_u256_CallData v0 v1 v1 v2
  return Pairs.mk v4

/-- `core::abi::Decode::decode_from_prechecked_head<Pairs, Sol, CallData>` -/
def decode_from_prechecked_head_Pairs_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Pairs := do
  -- Self::decode_from(input, pos)
  let v3_1 ← Pairs_decode_from_CallData input pos
  return v3_1

/-- `core::contracts::decode_runtime_args<Evm, Sol, Pairs>` -/
def decode_runtime_args_Evm_Sol_Pairs : FeM Pairs := do
  let mut input : CallData := default
  -- let input = host.input()
  let input_2 ← Evm_input
  input := input_2
  -- let base = A::SELECTOR_SIZE
  let base ← Sol_SELECTOR_SIZE
  -- let len = input.len()
  let len ← len_CallData input
  -- A::validate_runtime_head(input_len: len, base, head_size: T::HEAD_SIZE)
  let v9 ← Pairs_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  -- T::decode_from_prechecked_head(input, base, len)
  let v12 ← decode_from_prechecked_head_Pairs_Sol_CallData input base len
  return v12

/-- The entry of `recv_Pairs`, for `collide::OtherMsg::Pairs` -/
def recv_Pairs_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Pairs
  let result ← recv_Pairs message.t
  Evm_return_value_Sol_u256 result

/-- The runtime entry of contract `Collide`: the entry of the arm the call's selector picks -/
def runtime : FeM Empty := do
  let size_1 ← calldatasize
  if size_1.toNat < 4 then
    revertEmpty
  else
    let selector ← calldataSelector
    if selector = UInt256.ofNat 0x6a530d0d then
      recv_Pairs_entry
    else if selector = UInt256.ofNat 0xa444f5e9 then
      recv_CollideMsg_Run_entry
    else if selector = UInt256.ofNat 0xa5b6ea8f then
      recv_Spin_entry
    else if selector = UInt256.ofNat 0xeb034fa7 then
      recv_OtherMsg_Run_entry
    else
      revertEmpty

/-- The deployment entry of contract `Collide`: `init` on the arguments after the creation code -/
def init_entry (args : ByteArray) : FeM ByteArray := do
  nonPayable
  let _ ← init
  return ByteArray.empty

-- END fe-lean-export

end

/- The constants the compiler folded: each is the value the exporter printed in its place. -/
-- BEGIN fe-lean-export: collide.checks

set_option maxRecDepth 10000 in
example : limit = pure (UInt256.ofNat 10) := rfl
set_option maxRecDepth 10000 in
example : size = pure (UInt256.ofNat 4) := rfl
set_option maxRecDepth 10000 in
example : Run_HEAD_SIZE = pure (UInt256.ofNat 32) := rfl
set_option maxRecDepth 10000 in
example : Spin_HEAD_SIZE = pure (UInt256.ofNat 32) := rfl
set_option maxRecDepth 10000 in
example : Pairs_HEAD_SIZE = pure (UInt256.ofNat 64) := rfl
-- END fe-lean-export

end FeProofs.Fixtures.Collide

/-! ## `names`: top-level names the exporter makes, spelled by the program

A function named like the loader of a stored struct (`load_Pair`), one named like a piece of a
long function (`long_k1`), and a struct named like a Lean keyword (`Prop`). -/

namespace FeProofs.Fixtures.Names

section
set_option linter.unusedVariables false

-- BEGIN fe-lean-export: names

export Lib (CallData Evm_input Evm_return_value_Sol_u256 Sol_SELECTOR_SIZE Sol_validate_runtime_head abi_field_head_size_u256 decode_msg_field_from_Sol_u256_CallData len_CallData)

def Field.counter : Place :=
  .storage (UInt256.ofNat 4)

def Layout.Counter : Layout :=
  { storage := [0, 1] }

structure Pair where
  a : UInt256
  b : UInt256
deriving Inhabited

def Field.pair : Place :=
  .storage (UInt256.ofNat 0)

def store_Pair (p : Place) (v : Pair) : FeM Unit := do
  store (p.offset 0) v.a
  store (p.offset 1) v.b

structure Prop_1 where
  flag : Bool
  n : UInt256
deriving Inhabited

def Field.prop : Place :=
  .storage (UInt256.ofNat 2)

def store_Prop (p : Place) (v : Prop_1) : FeM Unit := do
  let b0 ← Lane.pack ⟨0, 1, false⟩ (.u 8) (Bool.toUInt256 v.flag)
  store (p.offset 0) (packed [(0, b0)])
  store (p.offset 1) v.n

def load_Pair_1 (p : Place) : FeM Pair := do
  let f0 ← load (p.offset 0)
  let f1 ← load (p.offset 1)
  return (Pair.mk f0 f1)

def load_Prop (p : Place) : FeM Prop_1 := do
  let f0 ← loadBoolAt (p.offset 0) ⟨0, 1, false⟩
  let f1 ← load (p.offset 1)
  return (Prop_1.mk f0 f1)

structure Run where
  x : UInt256
deriving Inhabited

/-- The `init` of contract `Names`, which its source leaves out -/
def init : FeM Unit := do
  return ()

/-- `names::load_Pair` -/
def load_Pair (x : UInt256) : FeM UInt256 := do
  -- x + 1
  let v3 ← checkedAdd x (UInt256.ofNat 1)
  return v3

/-- `names::long_k1` -/
def long_k1 (x : UInt256) : FeM UInt256 := do
  -- x + 2
  let v3 ← checkedAdd x (UInt256.ofNat 2)
  return v3

def long_k9 (v216 : UInt256) : FeM UInt256 := do
  let a43 ← checkedAdd v216 (UInt256.ofNat 43)
  -- let a44 = a43 * 3 + 44
  let v221 ← checkedMul a43 (UInt256.ofNat 3)
  let a44 ← checkedAdd v221 (UInt256.ofNat 44)
  return a44

def long_k8 (v191 : UInt256) : FeM UInt256 := do
  let a38 ← checkedAdd v191 (UInt256.ofNat 38)
  -- let a39 = a38 * 3 + 39
  let v196 ← checkedMul a38 (UInt256.ofNat 3)
  let a39 ← checkedAdd v196 (UInt256.ofNat 39)
  -- let a40 = a39 * 3 + 40
  let v201 ← checkedMul a39 (UInt256.ofNat 3)
  let a40 ← checkedAdd v201 (UInt256.ofNat 40)
  -- let a41 = a40 * 3 + 41
  let v206 ← checkedMul a40 (UInt256.ofNat 3)
  let a41 ← checkedAdd v206 (UInt256.ofNat 41)
  -- let a42 = a41 * 3 + 42
  let v211 ← checkedMul a41 (UInt256.ofNat 3)
  let a42 ← checkedAdd v211 (UInt256.ofNat 42)
  -- let a43 = a42 * 3 + 43
  let v216 ← checkedMul a42 (UInt256.ofNat 3)
  long_k9 v216

def long_k7 (a33 : UInt256) : FeM UInt256 := do
  -- let a34 = a33 * 3 + 34
  let v171 ← checkedMul a33 (UInt256.ofNat 3)
  let a34 ← checkedAdd v171 (UInt256.ofNat 34)
  -- let a35 = a34 * 3 + 35
  let v176 ← checkedMul a34 (UInt256.ofNat 3)
  let a35 ← checkedAdd v176 (UInt256.ofNat 35)
  -- let a36 = a35 * 3 + 36
  let v181 ← checkedMul a35 (UInt256.ofNat 3)
  let a36 ← checkedAdd v181 (UInt256.ofNat 36)
  -- let a37 = a36 * 3 + 37
  let v186 ← checkedMul a36 (UInt256.ofNat 3)
  let a37 ← checkedAdd v186 (UInt256.ofNat 37)
  -- let a38 = a37 * 3 + 38
  let v191 ← checkedMul a37 (UInt256.ofNat 3)
  long_k8 v191

def long_k6 (a28 : UInt256) : FeM UInt256 := do
  -- let a29 = a28 * 3 + 29
  let v146 ← checkedMul a28 (UInt256.ofNat 3)
  let a29 ← checkedAdd v146 (UInt256.ofNat 29)
  -- let a30 = a29 * 3 + 30
  let v151 ← checkedMul a29 (UInt256.ofNat 3)
  let a30 ← checkedAdd v151 (UInt256.ofNat 30)
  -- let a31 = a30 * 3 + 31
  let v156 ← checkedMul a30 (UInt256.ofNat 3)
  let a31 ← checkedAdd v156 (UInt256.ofNat 31)
  -- let a32 = a31 * 3 + 32
  let v161 ← checkedMul a31 (UInt256.ofNat 3)
  let a32 ← checkedAdd v161 (UInt256.ofNat 32)
  -- let a33 = a32 * 3 + 33
  let v166 ← checkedMul a32 (UInt256.ofNat 3)
  let a33 ← checkedAdd v166 (UInt256.ofNat 33)
  long_k7 a33

def long_k5 (a23 : UInt256) : FeM UInt256 := do
  -- let a24 = a23 * 3 + 24
  let v121 ← checkedMul a23 (UInt256.ofNat 3)
  let a24 ← checkedAdd v121 (UInt256.ofNat 24)
  -- let a25 = a24 * 3 + 25
  let v126 ← checkedMul a24 (UInt256.ofNat 3)
  let a25 ← checkedAdd v126 (UInt256.ofNat 25)
  -- let a26 = a25 * 3 + 26
  let v131 ← checkedMul a25 (UInt256.ofNat 3)
  let a26 ← checkedAdd v131 (UInt256.ofNat 26)
  -- let a27 = a26 * 3 + 27
  let v136 ← checkedMul a26 (UInt256.ofNat 3)
  let a27 ← checkedAdd v136 (UInt256.ofNat 27)
  -- let a28 = a27 * 3 + 28
  let v141 ← checkedMul a27 (UInt256.ofNat 3)
  let a28 ← checkedAdd v141 (UInt256.ofNat 28)
  long_k6 a28

def long_k4 (v96 : UInt256) : FeM UInt256 := do
  let a19 ← checkedAdd v96 (UInt256.ofNat 19)
  -- let a20 = a19 * 3 + 20
  let v101 ← checkedMul a19 (UInt256.ofNat 3)
  let a20 ← checkedAdd v101 (UInt256.ofNat 20)
  -- let a21 = a20 * 3 + 21
  let v106 ← checkedMul a20 (UInt256.ofNat 3)
  let a21 ← checkedAdd v106 (UInt256.ofNat 21)
  -- let a22 = a21 * 3 + 22
  let v111 ← checkedMul a21 (UInt256.ofNat 3)
  let a22 ← checkedAdd v111 (UInt256.ofNat 22)
  -- let a23 = a22 * 3 + 23
  let v116 ← checkedMul a22 (UInt256.ofNat 3)
  let a23 ← checkedAdd v116 (UInt256.ofNat 23)
  long_k5 a23

def long_k3 (v71 : UInt256) : FeM UInt256 := do
  let a14 ← checkedAdd v71 (UInt256.ofNat 14)
  -- let a15 = a14 * 3 + 15
  let v76 ← checkedMul a14 (UInt256.ofNat 3)
  let a15 ← checkedAdd v76 (UInt256.ofNat 15)
  -- let a16 = a15 * 3 + 16
  let v81 ← checkedMul a15 (UInt256.ofNat 3)
  let a16 ← checkedAdd v81 (UInt256.ofNat 16)
  -- let a17 = a16 * 3 + 17
  let v86 ← checkedMul a16 (UInt256.ofNat 3)
  let a17 ← checkedAdd v86 (UInt256.ofNat 17)
  -- let a18 = a17 * 3 + 18
  let v91 ← checkedMul a17 (UInt256.ofNat 3)
  let a18 ← checkedAdd v91 (UInt256.ofNat 18)
  -- let a19 = a18 * 3 + 19
  let v96 ← checkedMul a18 (UInt256.ofNat 3)
  long_k4 v96

def long_k2 (a9 : UInt256) : FeM UInt256 := do
  -- let a10 = a9 * 3 + 10
  let v51 ← checkedMul a9 (UInt256.ofNat 3)
  let a10 ← checkedAdd v51 (UInt256.ofNat 10)
  -- let a11 = a10 * 3 + 11
  let v56 ← checkedMul a10 (UInt256.ofNat 3)
  let a11 ← checkedAdd v56 (UInt256.ofNat 11)
  -- let a12 = a11 * 3 + 12
  let v61 ← checkedMul a11 (UInt256.ofNat 3)
  let a12 ← checkedAdd v61 (UInt256.ofNat 12)
  -- let a13 = a12 * 3 + 13
  let v66 ← checkedMul a12 (UInt256.ofNat 3)
  let a13 ← checkedAdd v66 (UInt256.ofNat 13)
  -- let a14 = a13 * 3 + 14
  let v71 ← checkedMul a13 (UInt256.ofNat 3)
  long_k3 v71

def long_k1_1 (a4 : UInt256) : FeM UInt256 := do
  -- let a5 = a4 * 3 + 5
  let v26 ← checkedMul a4 (UInt256.ofNat 3)
  let a5 ← checkedAdd v26 (UInt256.ofNat 5)
  -- let a6 = a5 * 3 + 6
  let v31 ← checkedMul a5 (UInt256.ofNat 3)
  let a6 ← checkedAdd v31 (UInt256.ofNat 6)
  -- let a7 = a6 * 3 + 7
  let v36 ← checkedMul a6 (UInt256.ofNat 3)
  let a7 ← checkedAdd v36 (UInt256.ofNat 7)
  -- let a8 = a7 * 3 + 8
  let v41 ← checkedMul a7 (UInt256.ofNat 3)
  let a8 ← checkedAdd v41 (UInt256.ofNat 8)
  -- let a9 = a8 * 3 + 9
  let v46 ← checkedMul a8 (UInt256.ofNat 3)
  let a9 ← checkedAdd v46 (UInt256.ofNat 9)
  long_k2 a9

/-- `names::long` -/
def long (x : UInt256) : FeM UInt256 := do
  -- let a0 = x + 1
  let a0 ← checkedAdd x (UInt256.ofNat 1)
  -- let a1 = a0 * 3 + 1
  let v6 ← checkedMul a0 (UInt256.ofNat 3)
  let a1 ← checkedAdd v6 (UInt256.ofNat 1)
  -- let a2 = a1 * 3 + 2
  let v11 ← checkedMul a1 (UInt256.ofNat 3)
  let a2 ← checkedAdd v11 (UInt256.ofNat 2)
  -- let a3 = a2 * 3 + 3
  let v16 ← checkedMul a2 (UInt256.ofNat 3)
  let a3 ← checkedAdd v16 (UInt256.ofNat 3)
  -- let a4 = a3 * 3 + 4
  let v21 ← checkedMul a3 (UInt256.ofNat 3)
  let a4 ← checkedAdd v21 (UInt256.ofNat 4)
  long_k1_1 a4

/-- `Run { x } -> u256`, selector `0xa444f5e9` (`run(uint256)`) -/
def recv_Run (x : UInt256) : FeM UInt256 := do
  -- counter.1 += x
  let v1 ← load (Field.counter.field Layout.Counter 1)
  let v2 ← checkedAdd v1 x
  store (Field.counter.field Layout.Counter 1) v2
  -- pair = Pair { a: x, b: load_Pair(x) }
  let v4 ← load_Pair x
  store_Pair Field.pair (Pair.mk x v4)
  -- prop = Prop { flag: true, n: long_k1(x) }
  let v8 ← long_k1 x
  store_Prop Field.prop (Prop_1.mk true v8)
  -- let stored = pair
  let pair ← load_Pair_1 Field.pair
  -- let p = prop
  let prop ← load_Prop Field.prop
  -- stored.a + stored.b + p.n + long(x)
  let v17 ← checkedAdd pair.a pair.b
  let v19 ← checkedAdd v17 prop.n
  let v20 ← long x
  let v21 ← checkedAdd v19 v20
  return v21

/-- `<Run as AbiSize>::HEAD_SIZE` -/
def Run_HEAD_SIZE : FeM UInt256 := do
  let v1 ← abi_field_head_size_u256
  let v2 ← checkedAdd (UInt256.ofNat 0) v1
  return v2

/-- `<Run as Decode>::decode_from<CallData>` -/
def Run_decode_from_CallData (v0 : CallData) (v1 : UInt256) : FeM Run := do
  let v2 ← len_CallData v0
  let v4 ← decode_msg_field_from_Sol_u256_CallData v0 v1 v1 v2
  return Run.mk v4

/-- `core::abi::Decode::decode_from_prechecked_head<Run, Sol, CallData>` -/
def decode_from_prechecked_head_Run_Sol_CallData (input : CallData) (pos : UInt256) (input_len : UInt256) : FeM Run := do
  -- Self::decode_from(input, pos)
  let v3 ← Run_decode_from_CallData input pos
  return v3

/-- `core::contracts::decode_runtime_args<Evm, Sol, Run>` -/
def decode_runtime_args_Evm_Sol_Run : FeM Run := do
  let mut input : CallData := default
  -- let input = host.input()
  let input_2 ← Evm_input
  input := input_2
  -- let base = A::SELECTOR_SIZE
  let base ← Sol_SELECTOR_SIZE
  -- let len = input.len()
  let len ← len_CallData input
  -- A::validate_runtime_head(input_len: len, base, head_size: T::HEAD_SIZE)
  let v9 ← Run_HEAD_SIZE
  let _ ← Sol_validate_runtime_head len base v9
  -- T::decode_from_prechecked_head(input, base, len)
  let v12 ← decode_from_prechecked_head_Run_Sol_CallData input base len
  return v12

/-- The entry of `recv_Run`, for `names::NamesMsg::Run` -/
def recv_Run_entry : FeM Empty := do
  nonPayable
  let message ← decode_runtime_args_Evm_Sol_Run
  let result ← recv_Run message.x
  Evm_return_value_Sol_u256 result

/-- The runtime entry of contract `Names`: the entry of the arm the call's selector picks -/
def runtime : FeM Empty := do
  let size ← calldatasize
  if size.toNat < 4 then
    revertEmpty
  else
    let selector ← calldataSelector
    if selector = UInt256.ofNat 0xa444f5e9 then
      recv_Run_entry
    else
      revertEmpty

/-- The deployment entry of contract `Names`: `init` on the arguments after the creation code -/
def init_entry (args : ByteArray) : FeM ByteArray := do
  nonPayable
  let _ ← init
  return ByteArray.empty

-- END fe-lean-export

end

/- The constants the compiler folded: each is the value the exporter printed in its place. -/
-- BEGIN fe-lean-export: names.checks

set_option maxRecDepth 10000 in
example : Run_HEAD_SIZE = pure (UInt256.ofNat 32) := rfl
-- END fe-lean-export

end FeProofs.Fixtures.Names
