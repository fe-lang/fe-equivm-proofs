import Fe.Sonatina.Plan

/-!
# The syntax of the handover dialect (H, Slice 1)

The IR H runs (design `s3/design.md` §3, §10 Slice 1) is the section IR machine lowering reads,
the sidecar's `source_ir`: scalar `i1`/`i256`/pointer values, `alloca`, `evm_malloc`, `gep`,
typed `mload`/`mstore`, `memzero`, `evm_mload_bytes`, `evm_keccak256`, calls with pointer
arguments, the `evm_*` operations and the terminals.  It is the machine IR's syntax
(`Fe/Sonatina/Syntax.lean`) plus what that syntax lacks: `HInst.base` and `HTerm.base` hold an
instruction or terminator of the existing syntax, and the other constructors are the
instructions of this dialect it has no constructor for.

- `gep` carries the type its base operand is declared with (`*T`): the offsets of a `gep`
  depend on it, and the text names the base by its value only.  The reader fills it in from
  the function's declarations (`H/Parse.lean`).
- `evm_mload_bytes addr len` (R4 of Sonatina's `docs/memory.md`, U5a of the design).
- `trunc_nuw x T` (§3.6, U2c).
- `evm_return_code off len`, a terminal (E5, §3.6).
- `evm_revert_word sel word`, a terminal (decision 9.2, §3.6): the panic and error payload as
  operands.

Later slices add the instructions of the earlier dialects (objects, enums, aggregates,
constant references); none of them is in `source_ir`.
-/

namespace Fe.Sonatina.H

open Fe.Sonatina

/-- An instruction of the dialect. -/
inductive HInst where
  /-- An instruction the machine IR's syntax has. -/
  | base (i : Inst)
  /-- `gep base idx…` with `base` declared at type `baseTy`, which is `*T`. -/
  | gep (baseTy : Ty) (base : Operand) (idxs : List Operand)
  /-- `evm_mload_bytes addr len`: the `len ≤ 32` bytes at `addr`, big-endian, zero-extended. -/
  | mloadBytes (addr len : Operand)
  /-- `trunc_nuw x T`: `x` as a `T`, undefined if a dropped bit is set. -/
  | truncNuw (arg : Operand) (ty : Ty)
  deriving Repr, BEq, Inhabited

/-- A terminator of the dialect. -/
inductive HTerm where
  | base (t : Term)
  /-- `evm_return_code off len`: return `code[off, off + len)`, touching no memory (E5). -/
  | returnCode (off len : Operand)
  /-- `evm_revert_word sel word` (`sel : i32`, `word : i256`): revert with the 36 bytes
      `be4(sel) ++ be32(word)`, touching no memory (decision 9.2). -/
  | revertWord (sel word : Operand)
  deriving Repr, BEq, Inhabited

/-- An instruction and the values it defines. -/
structure HStmt where
  dsts : List (Nat × Ty)
  inst : HInst
  deriving Repr, BEq, Inhabited

/-- A basic block: its phis lead it. -/
structure HBlock where
  id : Nat
  phis : List Phi
  body : List HStmt
  term : HTerm
  deriving Repr, BEq, Inhabited

/-- A function; its first block is the entry. -/
structure HFunc where
  name : String
  params : List (Nat × Ty)
  rets : List Ty
  blocks : List HBlock
  deriving Repr, BEq, Inhabited

/-- The struct types and functions of a section's module. -/
structure HModule where
  structs : List (String × List Ty)
  funcs : List HFunc
  deriving Repr, BEq, Inhabited

def HModule.func? (m : HModule) (name : String) : Option HFunc := m.funcs.find? (·.name == name)

def HFunc.block? (f : HFunc) (id : Nat) : Option HBlock := f.blocks.find? (·.id == id)

/-- The blocks a terminator may go to. -/
def HTerm.succs : HTerm → List Nat
  | .base t => t.succs
  | .returnCode _ _ | .revertWord _ _ => []

/-- A section of the handover object: its module, entry function, and the place and size of
    each symbol of its compiled code (`sym_addr`, `sym_size`). -/
structure HSection where
  module : HModule
  entry : String
  symbols : List (String × Nat × Nat)
  deriving Repr, Inhabited

/-- The handover object of a contract: its constructor's section and its runtime's.  For
    Slice 1 each section's module is its `source_ir` (design §10): the IR machine lowering
    reads. -/
structure Object where
  init : HSection
  runtime : HSection
  deriving Repr, Inhabited

end Fe.Sonatina.H
