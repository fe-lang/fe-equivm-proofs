import Fe.Sonatina.H.Sem
import Fe.Sonatina.Steps.NatMap

/-!
# The placement record of a section (design `s3/design.md` §6.1)

What the backend decided about memory when it lowered a section to machine IR, as the S14
checker reads it: per `alloca` its frame word, per `evm_malloc` its placement rule, per function
its frame shape, and per section the address of word 0 of the frames (`arena_base`).  Records
are untrusted: a wrong record makes the check fail, never pass.  The value map (which machine
value stands for which source value) is not recorded; the checker infers it and checks it
(`Place/Lower.lean`).

Allocations are named by the source value they define: `vN = alloca T` is site `N`.

The JSON form the compiler will write is fixed by the format note
(`s3/placement-record-format.md`); until it exists, the tests write records by hand.
-/

namespace Fe.Sonatina.Stage3.Place

/-- Where an `alloca` lives: an absolute word of the scratch overlay or of the stable chain,
    counted from `arena_base` (`ObjLoc::ScratchAbs`, `ObjLoc::StableAbs`).  A dynamic frame
    location (`StableFrame`) is outside rule set S (S1) and has no constructor. -/
inductive Loc where
  | scratch (word : Nat)
  | stable (word : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Loc.word : Loc → Nat
  | .scratch w | .stable w => w

/-- The rule a `Fixed` malloc was placed by (§6.1).  Only `terminal` (`MinBase`, terminal) is
    in rule set S (S2). -/
inductive FixedRule where
  | terminal
  | program
  | exactEntry
  | privateStatic
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Where an `evm_malloc` lives (`MallocPlacement`). -/
inductive Malloc where
  /-- On the heap: the base is `max(w[0x40], minBase)` (or `exactBase`); with `updateFp` the
      free pointer is bumped past the block, else the block is transient (S10a). -/
  | heap (minBase : Nat) (exactBase : Option Nat) (updateFp : Bool)
  /-- At a fixed base. -/
  | fixed (base : Nat) (rule : FixedRule)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A function's placement: its `alloca`s and `evm_malloc`s by result value, and the frame
    facts rule S1 and S2 read. -/
structure FuncRec where
  name : String
  allocas : List (Nat × Loc) := []
  mallocs : List (Nat × Malloc) := []
  /-- The function saves the free pointer at entry and restores it before each return. -/
  restoresFp : Bool := false
  dynFrame : Bool := false
  lazyFrame : Bool := false
  callPreserves : Nat := 0
  dynSpClamp : Bool := false
  /-- The spill reserves of the function, as absolute word ranges `[lo, hi)` (S9). -/
  reserves : List (Nat × Nat) := []
  /-- Source block ↦ machine block; when absent the checker takes the `k`-th source block to
      machine block `k`, as machine lowering numbers them (`create_source_blocks`). -/
  blockMap : Option (List (Nat × Nat)) := none
  /-- Hint: the place of the function's machine function in the lowered module. -/
  mfunc : Nat := 0
  /-- Hint: per source block, in order, the place among the source module's functions of the
      callee of each `call` statement.  The checker compares each callee's name once, and then
      works with places: comparing names is what costs the most in the kernel. -/
  calls : List (List Nat) := []
  /-- Certificates, which the checker computes itself when absent and checks either way: the
      value map (source value ↦ machine operand), the live set at the start of each block's body,
      and each value's origins (S3). -/
  vmCert : Option (List (Nat × Operand)) := none
  liveCert : Option (List (Nat × List Nat)) := none
  origCert : Option (List (Nat × List Nat)) := none
  deriving Repr, BEq, Inhabited

/-- A section's placement record.  `funcs` lists the source module's functions in their order
    (checked). -/
structure Record where
  /-- The byte address of word 0 of the frames (`arena_base`). -/
  arenaBase : Nat
  funcs : List FuncRec
  /-- The fixed spill slots `[0, 64)` are in use (S9). -/
  fixedSlots : Bool := false
  /-- Certificates by function place, checked: the parameters that may receive a frame pointer
      (S3), the footprints (S7), and the derived values, parameters and returns (S8). -/
  flagsCert : Option (List (Nat × List Nat)) := none
  fpCert : Option (List (Nat × List (Nat × Nat))) := none
  derivedCert : Option (List (Nat × List Nat) × List (Nat × List Nat) × List Nat) := none
  deriving Repr, BEq, Inhabited

def Record.func? (r : Record) (name : String) : Option FuncRec := r.funcs.find? (·.name == name)

/-- The byte address of frame word `w`. -/
def Record.wordAddr (r : Record) (w : Nat) : Nat := r.arenaBase + 32 * w

end Fe.Sonatina.Stage3.Place
