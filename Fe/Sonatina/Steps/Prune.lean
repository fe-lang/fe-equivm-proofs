import Fe.Sonatina.Steps.Wf

/-!
# Removing dead slots

The prunes of `sccp_prune` and `gvn_prune` (`remove_unreachable_edges` of `optim/sccp.rs` and
`optim/gvn.rs`) remove the slots a solver found dead (`CfgEditor::remove_succ`,
`CfgEditor::retain_out_edges`, `BranchInfo::remove_edges_to_block`): a `br` with one slot left
becomes a `jump`; a `br_table` loses its dead cases and, if dead, its default, and becomes a
`jump` with one slot left, `unreachable` with none; the targets' phis lose their operands from a
predecessor with no slot left to them.  `pruneFunc f dead` is the input with exactly that done
and nothing else; the blocks left unreachable and the phis left trivial are `cfg_cleanup`'s
(`checkCfgCleanup`), which both checkers run from `pruneFunc f dead` to the output.

A `br_table` whose default is dead keeps it when two or more cases are left: the machine IR's
`br_table` has a default (`Term.wf`), and the compiler's table without one is rejected by the
output's well-formedness anyway.
-/

namespace Fe.Sonatina.Steps.Schemas

/-- The cases of a `br_table` of block `b` whose slots are not claimed dead (slot `i + 1` is
    case `i`, slot `0` the default). -/
def liveCases (dead : List (Nat × Nat)) (b : Nat) (cases : List (Operand × Nat)) :
    List (Operand × Nat) :=
  ((cases.zipIdx 1).filter fun ci => !dead.contains (b, ci.2)).map (·.1)

/-- A terminator with its dead slots removed: a `br` with one slot dead becomes a `jump` to the
    other; a `br_table` with a dead slot keeps its live cases, and its default if live or if two
    or more cases are left, then is a `jump` with one slot left and `unreachable` with none; any
    other terminator, and a `br` with both slots dead, is kept. -/
def pruneTerm (dead : List (Nat × Nat)) (b : Nat) : Fe.Sonatina.Term → Fe.Sonatina.Term
  | .br c nz z =>
    if dead.contains (b, 1) && !dead.contains (b, 0) then .jump nz
    else if dead.contains (b, 0) && !dead.contains (b, 1) then .jump z
    else .br c nz z
  | .brTable s (some D) cases =>
    let cs := liveCases dead b cases
    if dead.contains (b, 0) then
      match cs with
      | [] => .unreachable
      | [c] => .jump c.2
      | _ => .brTable s (some D) cs
    else if cs.length == cases.length then .brTable s (some D) cases
    else if cs.isEmpty then .jump D
    else .brTable s (some D) cs
  | t => t

/-- A phi operand of block `T` survives the prune: its predecessor did not go to `T`, or still
    does. -/
def keepIn (B : NatMap Block) (dead : List (Nat × Nat)) (T : Nat) (ob : Operand × Nat) : Bool :=
  match B.find? ob.2 with
  | some pb => !pb.term.succs.contains T || (pruneTerm dead ob.2 pb.term).succs.contains T
  | none => true

def pruneBlock (B : NatMap Block) (dead : List (Nat × Nat)) (b : Block) : Block :=
  { b with
    phis := b.phis.map fun φ => { φ with incoming := φ.incoming.filter (keepIn B dead b.id) }
    term := pruneTerm dead b.id b.term }

/-- The input with every dead slot removed and the phi operands of the removed edges dropped. -/
def pruneFunc (f : Func) (dead : List (Nat × Nat)) : Func :=
  { f with blocks := f.blocks.map (pruneBlock (.ofListBy (·.id) f.blocks) dead) }

end Fe.Sonatina.Steps.Schemas
