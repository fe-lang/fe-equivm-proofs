import Fe.Sonatina.Steps.Record

/-!
# The sidecar

What `fe build --emit sidecar` writes for an object: the IR of `Syntax.lean`, and per section the
bytes, the symbols, and how the backend lowered it (`Lowering`), with the record of the machine
pipeline's steps (`Steps.MachineSteps`).  `Parse.parseSidecar` reads it from the JSON, record
included, so that a sidecar and its records are one term read from one file.  These are apart
from `Syntax.lean` because the record's types (`Steps/Record.lean`) are made of its functions.
-/

namespace Fe.Sonatina

/-- How the backend lowered a section: the IR machine lowering read (`source`), the machine IR
    the code is emitted from (`machine`), the record of the machine pipeline's steps that made
    it (`machineSteps`), and what connects the machine IR to the bytes. -/
structure Lowering where
  /-- `none` when the section IR uses what the subset does not read: only the machine IR is
      needed to check the bytes. -/
  source : Option Module
  machine : Module
  codeSize : Nat
  arenaBase : Nat
  dynBase : Nat
  entryFreePtr : Option Nat
  funcs : List FuncHint
  /-- The outlined code units: name, offset and size. -/
  units : List (String × Nat × Nat)
  /-- Code that went to the first label goes to the second. -/
  redirects : List (CodeLabel × CodeLabel)
  /-- The machine IR right after lowering and each step from it to `machine` (sidecar version
      5's `machine_steps`).  Empty (`default`: no lowered function, no pass) in a version 4
      sidecar, which has no record: an empty record validates only against a machine IR
      without functions. -/
  machineSteps : Steps.MachineSteps
  deriving Repr, Inhabited, Lean.ToExpr

/-- A section of compiled code: its bytes, the place and size of each symbol it defines, and
    how it was lowered. -/
structure CodeSection where
  name : String
  bytecode : ByteArray
  symbols : List (String × Nat × Nat)
  lowering : Option Lowering

/-- The sidecar of an object: the objects of the module the backend compiled it from, that
    module, and the object's sections. -/
structure Sidecar where
  object : String
  /-- Each section's entry function and embeds. -/
  objects : List Object
  /-- `none` when the module uses what the subset does not read: only each section's machine
      IR is needed to check the bytes. -/
  module : Option Module
  sections : List CodeSection

def Sidecar.section? (s : Sidecar) (name : String) : Option CodeSection :=
  s.sections.find? (·.name == name)

end Fe.Sonatina
