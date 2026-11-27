import Fe.Sonatina.H.Value

/-!
# The state of H and its memory (design §3.3, §3.4)

`State` is the design's `HWorld`: the model library's `World` for accounts, logs, return data,
the feed and the record of calls, and H's own memory: the blocks allocated so far and the heap
request counter.  The world's `memory` field is not H's memory: H never reads or writes it, and
`EndsAs` ignores it.  There is no fixed region (decision 9): nothing reads or writes memory
except through a block.

- **Allocation** (§3.3): `State.alloc` adds a block with id `blocks.size` (fresh, as blocks
  never die), the chosen address word and the chosen fresh bytes, each a plain byte (R2: a fresh
  allocation holds arbitrary bytes, no pointer fragment).  The choice is constrained by
  `AddrOk addr size`: `1 ≤ addr` and `addr + size < 2 ^ 256`, nothing else; blocks may get
  equal or overlapping words (decision 2).  The relation (`H/Sem.lean`) quantifies over both.
- **The heap budget** (§3.3, decision 3): `heapReq` sums `align32 n` over the message call's
  `evm_malloc n`; a request that would bring it to `heapBudget = 2 ^ 255` or more ends the run
  as `exhausted` (`H/Sem.lean`).  This dialect has no `obj.alloc` or `mem.alloc_dynamic`.
- **Access** (§3.4, E1, U1): `State.range st a len` resolves an access of `len` bytes at `a`:
  `len = 0` touches nothing and is never `ub`; otherwise `a` must be `ptr b o` with
  `o + len ≤ size b`, else the access is `ub` (`none`): U1a out of its block, U1b through an
  integer address.
- **Bytes** (§3.4): typed 32-byte stores write `Val.cells`; a typed 32-byte load of the 32
  fragments of one pointer, in order, gives the pointer at pointer and `i256` types; any other
  read uses the byte values (`MByte.val`) and has no origin; a narrow load of a word with upper
  bits set is `ub` (U2b).
-/

namespace Fe.Sonatina.H

open Ethereum Fe.EVM Fe.Sonatina

/-- The state of a run of H (the design's `HWorld`). -/
structure State where
  /-- Accounts, logs, return data, the feed and the calls made.  Its `memory` is unused. -/
  world : World
  blocks : Array MemBlock := #[]
  /-- The sum of `align32 n` over the `evm_malloc n` so far. -/
  heapReq : Nat := 0

/-- The state a section's run starts in. -/
def State.init (w : World) : State := { world := w }

/-- The address word of block `b`.  Every pointer of a run is into a block it allocated; the
    default is never read. -/
def State.addrOf (st : State) (b : Nat) : Nat := (st.blocks[b]?.map (·.addr)).getD 0

/-- The word of a value in the state (§3.2). -/
def State.word (st : State) (v : Val) : Nat := v.word st.addrOf

/-- The word of a value, as the EVM primitives take it. -/
def State.uword (st : State) (v : Val) : UInt256 := UInt256.ofNat (st.word v)

/-- The constraint on an address word chosen for a block of `size` bytes (§3.3, decision 2):
    at least 1, and the block's range does not wrap. -/
def AddrOk (addr size : Nat) : Prop := 1 ≤ addr ∧ addr + size < 2 ^ 256

instance (addr size : Nat) : Decidable (AddrOk addr size) := by
  unfold AddrOk; infer_instance

/-- A request rounded up to whole words, in the naturals. -/
def align32 (n : Nat) : Nat := (n + 31) / 32 * 32

/-- The heap budget (§3.3, decision 3). -/
def heapBudget : Nat := 2 ^ 255

/-- The state with a new block of `size` bytes at address word `addr`, holding the bytes
    `fresh`.  Its id is `st.blocks.size`. -/
def State.alloc (st : State) (kind : BlockKind) (size addr : Nat) (fresh : List UInt8) :
    State :=
  { st with blocks := st.blocks.push ⟨size, (fresh.map MByte.byte).toArray, addr, kind⟩ }

/-- Where an access goes (§3.4): nowhere, for zero bytes, or block `b` from offset `o`. -/
inductive Range where
  | empty
  | at (b o : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Resolve an access of `len` bytes at `a` (§3.4, E1, U1): `none` is `ub`. -/
def State.range (st : State) (a : Val) (len : Nat) : Option Range :=
  if len = 0 then some .empty
  else match a with
    | .ptr b o => match st.blocks[b]? with
      | some blk => if o + len ≤ blk.size then some (.at b o) else none
      | none => none
    | .int _ _ => none

/-- The `len` cells of block `b` from offset `o`. -/
def State.cellsAt (st : State) (b o len : Nat) : List MByte :=
  match st.blocks[b]? with
  | some blk => (List.range len).map fun i => blk.bytes.getD (o + i) (.byte 0)
  | none => []

/-- The cells of a range of `len` bytes. -/
def State.cells (st : State) (r : Range) (len : Nat) : List MByte :=
  match r with
  | .empty => []
  | .at b o => st.cellsAt b o len

/-- The byte values of a range of `len` bytes: what world operations read (§3.4, E3). -/
def State.bytes (st : State) (r : Range) (len : Nat) : ByteArray :=
  ⟨((st.cells r len).map (·.val st.addrOf)).toArray⟩

/-- Write cells at a range: block `b` from offset `o`.  An empty range writes nothing. -/
def State.write (st : State) (r : Range) (cs : List MByte) : State :=
  match r with
  | .empty => st
  | .at b o =>
    { st with blocks := st.blocks.modify b fun blk =>
        { blk with bytes := cs.zipIdx.foldl (fun a (c, i) => a.set! (o + i) c) blk.bytes } }

/-- Write plain bytes at a range: a copy from outside memory (§3.4). -/
def State.writeBytes (st : State) (r : Range) (bs : ByteArray) : State :=
  st.write r (bs.toList.map .byte)

/-- A typed 32-byte load at block `b`, offset `o`, of a scalar type (§3.4): the pointer whose
    fragments the cells are, at pointer and `i256` types; otherwise the word of the byte values,
    `ub` (`none`) at a narrow type if a bit above its width is set (U2b). -/
def State.load (st : State) (b o : Nat) (ty : Ty) : Option Val :=
  let cs := st.cellsAt b o 32
  let w := (uInt256OfByteArray ⟨(cs.map (·.val st.addrOf)).toArray⟩).toNat
  match fragsOf cs, ty with
  | some (b', o'), .ptr _ | some (b', o'), .int 256 => some (.ptr b' o')
  | _, .int n => if w < 2 ^ n then some (.int n w) else none
  | _, _ => some (.int 256 w)

/-- The bytes of a size, in Sonatina's EVM layout (`crates/ir/src/isa/evm.rs`): every scalar and
    pointer a word, a struct the sum of its fields, an array its length times its element's.
    `none` past `fuel` levels of nesting, or for a struct the module does not declare. -/
def sizeOf (structs : List (String × List Ty)) : Nat → Ty → Option Nat
  | _, .int _ | _, .ptr _ | _, .objRef _ | _, .constRef _ => some 32
  | _, .unit => some 0
  | 0, _ => none
  | fuel + 1, .array elem len => (sizeOf structs fuel elem).map (len * ·)
  | fuel + 1, .struct name => do
    let fields ← structs.lookup name
    fields.foldlM (fun acc t => (acc + ·) <$> sizeOf structs fuel t) 0

/-- The nesting `sizeOf` allows: far more than any type of the corpus. -/
def sizeFuel : Nat := 64

end Fe.Sonatina.H
