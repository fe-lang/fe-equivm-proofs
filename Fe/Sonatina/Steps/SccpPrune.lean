import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.Prune

/-!
# The `sccp_prune` checker

SCCP's prune (`optim/sccp.rs`, `remove_unreachable_edges`, recorded as `sccp_prune` with the
solver's facts on the unpruned function: `known_bits` and `sccp`, as `sccp_fold`'s) deletes the
blocks the solver found unreachable (`delete_blocks_unreachable`, which drops their operands from
the phis of the blocks they went to and replaces the phis left trivial), then removes from each
reachable block the slots to targets it never takes (`CfgEditor::remove_succ`: a `br` with one
slot left becomes a `jump`; a `br_table` loses its dead cases and its dead default, and becomes a
`jump` with one slot left; the target's phis lose their operands from the block, and the phis left
trivial are replaced by their one operand).  The record's dead slots are those of the reachable
blocks whose target the terminator never takes.

The check splits the step in two at `pruneFunc f dead` (`Prune.lean`), the input with every dead
slot removed and the phi operands of the removed edges dropped, and nothing else changed:

1. **The dead slots** (from `f` to `pruneFunc f dead`), checked on the input with `sccp_fold`'s
   check of SCCP's facts (`sccpFactsOk`, the known bits by `kbFactsOk`): the executable set (the
   entry's closure over slots not claimed dead) is closed, each dead slot of an executable block
   is one its terminator does not take under the claimed constants (`slotTaken`: a `br` on a
   constant takes one slot, a `br_table` with a default on a constant scrutinee its first case of
   that key, else the default), and every claimed constant of a value of an executable block
   holds (a phi's from every executable incoming edge, a pure statement's by evaluation or a
   schema).  Nothing in the facts is trusted.
2. **The cleanup** (from `pruneFunc f dead` to the output): `cfg_cleanup`'s check with no summary
   table (`checkCfgCleanup none`): the blocks the pruned function no longer reaches are deleted
   and the phis left trivial replaced by their value.  The pruned function's control flow is
   checked (`cfgOk`), so that it is well formed.

The compiler's step can do what this rejects: prune the default of a `br_table` whose live slots
are two or more cases (to one target), which leaves a `br_table` with no default, not machine IR
(`Term.wf`); and prune every slot of a terminator whose condition SCCP left undefined, which
`slotTaken` never allows.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

/-- Why an `sccp_prune` step is rejected. -/
inductive SPReject where
  | noIds | unread | wrongFacts | inputSsa | kbFacts | sccpFacts | prunedCfg | cleanup
  deriving Repr, DecidableEq

def sccpPruneReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option SPReject :=
  match ids with
  | none => some .noIds
  | some is =>
    let B : NatMap Block := .ofListBy (·.id) f.blocks
    if !(F.unread.isEmpty && F.finiteLoops.isEmpty) then some .unread
    else if F.demanded.isSome || F.gvn.isSome then some .wrongFacts
    else if !ssaOk f then some .inputSsa
    else if !(F.knownBits.isEmpty || kbFactsOk B (defsOf f) F) then some .kbFacts
    else if !sccpFactsOk f B (defsOf f) (kbMap F) F then some .sccpFacts
    else if !(pruneFunc f F.deadEdges).cfgOk then some .prunedCfg
    else if !checkCfgCleanup none (pruneFunc f F.deadEdges) (some is) s then some .cleanup
    else none

/-- `sccp_prune` (design §4.7). -/
def checkSccpPrune (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Bool :=
  (sccpPruneReject f ids s F).isNone

def diagnoseSccpPrune (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option String :=
  (sccpPruneReject f ids s F).map fun r => s!"{repr r}"

end Fe.Sonatina.Steps.Schemas
