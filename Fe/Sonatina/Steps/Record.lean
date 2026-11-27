import Fe.Sonatina.Syntax
import Fe.Sonatina.Steps.SchemasFacts

/-!
# The record of the machine pipeline's steps

`MachineSteps` is the record a section's lowering carries in sidecar version 5
(`machine_steps`, design §3.1): the machine IR of every function of the section right after
lowering, and per pass the steps that changed it, each with the whole of every function it
changed.  `Steps/Read.lean` reads it from the sidecar's JSON.

Instruction ids are a side array (design §2.2): per function, per block in layout order, the id
of each line of its text, its phis first and its terminator last.
-/

namespace Fe.Sonatina.Steps

/-- A step of the machine pipeline: the column "Step" of design §1.2. -/
inductive StepKind where
  | cfgCleanup | branchCanonicalize | scalarCanonicalize | knownBitsSimplify
  | sccpPrune | sccpFold | adce | gvnPrune | gvnRewrite | lowerSwitches
  | branchConditions | coalesceCopies | edgeSplit
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- The record's name of a step kind. -/
def StepKind.name : StepKind → String
  | .cfgCleanup => "cfg_cleanup"
  | .branchCanonicalize => "branch_canonicalize"
  | .scalarCanonicalize => "scalar_canonicalize"
  | .knownBitsSimplify => "known_bits_simplify"
  | .sccpPrune => "sccp_prune"
  | .sccpFold => "sccp_fold"
  | .adce => "adce"
  | .gvnPrune => "gvn_prune"
  | .gvnRewrite => "gvn_rewrite"
  | .lowerSwitches => "lower_switches"
  | .branchConditions => "branch_conditions"
  | .coalesceCopies => "coalesce_copies"
  | .edgeSplit => "edge_split"

def StepKind.all : List StepKind :=
  [.cfgCleanup, .branchCanonicalize, .scalarCanonicalize, .knownBitsSimplify, .sccpPrune,
   .sccpFold, .adce, .gvnPrune, .gvnRewrite, .lowerSwitches, .branchConditions,
   .coalesceCopies, .edgeSplit]

/-- A function of a snapshot: as parsed from its text, its `FuncRef` (a cross-check only), and
    the instruction id of each line, per block. -/
structure FuncSnap where
  func : Func
  funcRef : Nat
  insts : List (List Nat)
  deriving Repr, Inhabited, Lean.ToExpr

/-- A function a step changed: the whole function after the step and the step's facts on it,
    as `Schemas.readFacts` reads them. -/
structure FuncStep where
  func : String
  out : FuncSnap
  facts : Schemas.StepFacts
  deriving Repr, Inhabited, Lean.ToExpr

/-- A step has no facts: no known bits, no demand round, no SCCP facts, no finite loops, no
    other key. -/
def noFacts (F : Schemas.StepFacts) : Bool :=
  F.knownBits.isEmpty && F.demanded.isNone && F.consts.isNone && F.deadEdges.isEmpty &&
    F.finiteLoops.isEmpty && F.gvn.isNone && F.unread.isEmpty

structure Step where
  kind : StepKind
  funcs : List FuncStep
  deriving Repr, Inhabited, Lean.ToExpr

/-- A function's behavior as a pass reads it (design §3.3, `func_behavior`). -/
structure Summary where
  func : String
  noreturn : Bool
  willReturn : Bool
  reads : Bool
  writes : Bool
  mutates : Bool
  deriving Repr, Inhabited, Lean.ToExpr

structure Pass where
  name : String
  funcBehavior : Option (List Summary)
  steps : List Step
  deriving Repr, Inhabited, Lean.ToExpr

structure MachineSteps where
  version : Nat
  profile : String
  lowered : List FuncSnap
  passes : List Pass
  deriving Repr, Inhabited, Lean.ToExpr

/-- The step kinds a record uses. -/
def MachineSteps.kinds (r : MachineSteps) : List StepKind :=
  r.passes.flatMap fun p => p.steps.map (·.kind)

end Fe.Sonatina.Steps
