import Fe.Sonatina.H.Syntax
import Fe.Sonatina.Interp

/-!
# Values and bytes of H (design §3.2, §3.3, §3.4)

- `Val` (§3.2, the design's `HVal`): an integer `int bits value` with `value < 2 ^ bits` (V2) and
  no origin, or a pointer `ptr b off` with origin block `b` and offset `off < 2 ^ 256`.  A
  pointer stands at pointer, `objref` and `i256` types.  The design's `agg`, `enum`, `tag` and
  `cref` values belong to the dialects before S12, S4d and S3 (§4.2); this dialect has none,
  and the well-formedness predicate (`H/Wf.lean`) rejects every type and instruction that would
  make one.
- `MByte` (§3.4): a memory cell, a byte or byte `i` of a stored pointer.
- `MemBlock` (§3.3, the design's `HBlock`): an allocation, with its size, its cells (always
  concrete, R1), its address word and its kind.  The `init` ghost of §3.3 is for `.obj` blocks,
  which this dialect does not have.

**The word of a pointer** (§3.2): `ptr b o` denotes `(addr b + o) mod 2 ^ 256`, where `addr b`
is block `b`'s address word; `Val.word` takes the address words as a function.
-/

namespace Fe.Sonatina.H

open Ethereum Fe.Sonatina

/-- A value of H (§3.2). -/
inductive Val where
  /-- An `iN` (or a pointer-typed integer, `N = 256`) with no origin: `value < 2 ^ bits`. -/
  | int (bits value : Nat)
  /-- A pointer with origin block `b`, at offset `off < 2 ^ 256` from the block's address
      word. -/
  | ptr (b off : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The word a value denotes, given each block's address word: an integer's value, and a
    pointer's `(addr b + o) mod 2 ^ 256` (§3.2). -/
def Val.word (addr : Nat → Nat) : Val → Nat
  | .int _ v => v
  | .ptr b o => (addr b + o) % 2 ^ 256

/-- The bits a value has as an operand: an integer's width; a pointer is a word (§3.2). -/
def Val.bits : Val → Nat
  | .int bits _ => bits
  | .ptr _ _ => 256

/-- The integer widths of Sonatina's types. -/
def widths : List Nat := [1, 8, 16, 32, 64, 128, 256]

/-- An integer of a Sonatina width, or a pointer: the value types of this dialect.  Whether a
    value is of such a type depends on its width only (`Ty.bits`): an `iN` has width `N`, a
    pointer 256 (`Val.fits`). -/
def Ty.value : Ty → Bool
  | .int n => widths.contains n
  | .ptr _ => true
  | _ => false

/-- The value is one of type `ty`: an `iN` of width `N`, in range; at a pointer type a pointer
    or a 256-bit integer; at `i256` a pointer too (§3.2: a pointer stands at pointer and `i256`
    types).  No value of this dialect has another type. -/
def Val.fits : Val → Ty → Bool
  | .int bits v, .int n => bits == n && decide (v < 2 ^ n)
  | .int bits v, .ptr _ => bits == 256 && decide (v < 2 ^ 256)
  | .ptr _ o, .int n => n == 256 && decide (o < 2 ^ 256)
  | .ptr _ o, .ptr _ => decide (o < 2 ^ 256)
  | _, _ => false

/-- A memory cell (§3.4): a byte, or byte `i` (big-endian) of the pointer `ptr b o` a typed
    store wrote.  Its value is byte `i` of the pointer's word. -/
inductive MByte where
  | byte (x : UInt8)
  | frag (b o : Nat) (i : Fin 32)
  deriving Repr, DecidableEq, Inhabited

/-- The 32 big-endian bytes of a word, as the machine IR's `mstore` writes them. -/
def wordBytes (w : Nat) : ByteArray := (UInt256.ofNat w).toByteArray

/-- The byte value of a cell, given each block's address word. -/
def MByte.val (addr : Nat → Nat) : MByte → UInt8
  | .byte x => x
  | .frag b o i => (wordBytes ((addr b + o) % 2 ^ 256)).get! i

/-- The cells a typed store of `v` writes (§3.4): the 32 fragments of a pointer, in order, or
    the 32 big-endian bytes of an integer, zero-extended (an `i1` as 0 or 1). -/
def Val.cells : Val → List MByte
  | .int _ x => (wordBytes x).toList.map .byte
  | .ptr b o => (List.finRange 32).map (.frag b o)

/-- The pointer whose 32 fragments the cells are, in order (§3.4), if they are. -/
def fragsOf (cs : List MByte) : Option (Nat × Nat) :=
  match cs with
  | .frag b o _ :: _ => if cs = (List.finRange 32).map (.frag b o) then some (b, o) else none
  | _ => none

/-- How a block came to be. -/
inductive BlockKind where
  | alloca
  | malloc
  deriving Repr, DecidableEq, Inhabited

/-- An allocation (§3.3): `size` bytes, its cells (`bytes.size = size`), its address word,
    chosen when it was allocated, and its kind.  Blocks never die (decision 1). -/
structure MemBlock where
  size : Nat
  bytes : Array MByte
  addr : Nat
  kind : BlockKind
  deriving Repr, Inhabited

end Fe.Sonatina.H
