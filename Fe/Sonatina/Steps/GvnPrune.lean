import Fe.Sonatina.Steps.GvnRewrite
import Fe.Sonatina.Steps.Prune

/-!
# The `gvn_prune` checker

GVN's prune (`optim/gvn.rs`, `remove_unreachable_edges`, recorded as `gvn_prune` with the facts of
the unpruned function) removes the slots the solver found dead from the solver's reachable blocks
(`CfgEditor::retain_out_edges`: a `br` with one slot left becomes a `jump`, the target's phis lose
their operands from a predecessor with no slot left, the phis that leaves trivial are replaced by
their one operand), then deletes the blocks no longer reachable (`delete_blocks_unreachable`,
which drops their operands from the phis of the blocks they went to, and again replaces the phis
left trivial).

The check splits the step in two at `pruneFunc f dead`, the input with every dead slot removed and
the phi operands of the removed edges dropped, and nothing else changed:

1. **The dead slots** (from `f` to `pruneFunc f dead`), checked on the input: the executable set
   (`execSet`, the entry's closure over slots not claimed dead) is closed (`execClosed`), and each
   dead slot of an executable block is a slot its `br` does not take: the condition's term at the
   block's end, through the classes and the predicates (`gTermAt`), is a literal that selects the
   other slot (`deadOk`).  A dead slot of a `jump` or a `br_table`, or both slots of a `br`, is
   rejected (`pruneShapeOk`; none occurs).
   - A predicate `(P, k, l, r)` (`l = r` once slot `k` of `P` is taken) is used where its target
     `T` dominates, if it holds by the terminator's semantics (`predOk`: `br c` slot 0 gives `c = 1`
     when `c`'s known bits make it a boolean, slot 1 gives `c = 0`, a `br_table` case slot gives the
     scrutinee equal to its key), `l` and `r` are defined strictly above `T`, and `(P, k)` is the one
     slot of an executable block into `T` not claimed dead (`usePred`).  Predicates that fail are
     dropped; none is trusted.
   - The classes, the pairs a check fails dropped to a fixpoint (`keepValidP`): each pair is
     `gvn_rewrite`'s (`pairOk`), but a phi's operands are compared at their predecessors' ends,
     through the predicates that hold there (`gTermAt`), and only from executable edges
     (`pairOkP`).
2. **The cleanup** (from `pruneFunc f dead` to the output): `cfg_cleanup`'s check with no summary
   table (`checkCfgCleanup none`): the blocks the pruned function no longer reaches are deleted and
   the phis left trivial replaced by their value.  The pruned function's control flow is checked
   (`cfgOk`), so that it is well formed.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

/-! ## The pruned function (`pruneFunc`, `Prune.lean`) -/

/-- Every dead slot is one of a `br` of the input, and no `br` has both dead. -/
def pruneShapeOk (B : NatMap Block) (dead : List (Nat × Nat)) : Bool :=
  dead.all fun bk => match B.find? bk.1 with
    | some blk => match blk.term with
      | .br _ _ _ => decide (bk.2 < 2) && !(dead.contains (bk.1, 0) && dead.contains (bk.1, 1))
      | _ => false
    | none => false

/-! ## Predicates -/

/-- `l = r` once slot `k` of terminator `t` is taken: `br c` slot 0 gives `c = 1` if `c`'s known
    bits make it a boolean (`branch_resolved_cond`), slot 1 gives `c = 0`; a `br_table` case slot
    gives the scrutinee equal to the case's key.  No other form is validated (`extract_edge_predicate`'s
    `eq`/`ne`/`is_zero` forms are dropped). -/
def predOk (K : NatMap KB) (t : Fe.Sonatina.Term) (k : Nat) (l r : Operand) : Bool :=
  match t with
  | .br c _ _ => l == c &&
      ((k == 0 && r == .imm 256 1 && (opFact K c).allZero (M ^^^ 1)) || (k == 1 && r == .imm 256 0))
  | .brTable s d cases => l == s && match d with
    | some _ => k != 0 && (cases[k - 1]?).any (·.1 == r)
    | none => (cases[k]?).any (·.1 == r)
  | _ => false

/-- The slots of executable blocks into `T` not claimed dead. -/
def inSlots (f : Func) (E : NatMap Unit) (dead : List (Nat × Nat)) (T : Nat) : List (Nat × Nat) :=
  f.blocks.flatMap fun b => if (E.find? b.id).isSome then
    (b.term.succs.zipIdx.filter fun tk => tk.1 == T && !dead.contains (b.id, tk.2)).map
      fun tk => (b.id, tk.2)
  else []

/-- A predicate used where its target dominates: `(T, P, k, l, r)`. -/
abbrev UPred := Nat × Nat × Nat × Operand × Operand

/-- A record's predicate `(P, k, l, r)` as a usable one: it holds by `P`'s terminator, `l` and `r`
    are defined strictly above the target `T`, and `(P, k)` is the one slot into `T` of an
    executable block not claimed dead. -/
def usePred (X : StepCtx) (f : Func) (E : NatMap Unit) (dead : List (Nat × Nat))
    (e : Nat × Nat × GOp × GOp) : Option UPred :=
  let l := e.2.2.1.toOperand
  let r := e.2.2.2.toOperand
  match X.inB.find? e.1 with
  | some pb => match pb.term.succs[e.2.1]? with
    | some T =>
      if l.wf && r.wf && predOk X.K pb.term e.2.1 l r && X.above T l && X.above T r &&
          inSlots f E dead T == [(e.1, e.2.1)] then some (T, e.1, e.2.1, l, r) else none
    | none => none
  | none => none

/-- An operand as a term at the end of block `b`: through its representative, then, if that is a
    value, through a predicate whose target dominates `b` and one of whose sides has that
    representative, the other side's. -/
def gTermAt (X : StepCtx) (C : NatMap Operand) (PU : List UPred) (b : Nat) (o : Operand) : Term :=
  match gTerm C o with
  | .atom a =>
    match PU.find? (fun u => X.T.anc u.1 b && gTerm C u.2.2.2.1 == .atom a) with
    | some u => gTerm C u.2.2.2.2
    | none => match PU.find? (fun u => X.T.anc u.1 b && gTerm C u.2.2.2.2 == .atom a) with
      | some u => gTerm C u.2.2.2.1
      | none => .atom a
  | t => t

/-! ## Classes -/

/-- A class pair of the unpruned input: a statement's as in `gvn_rewrite` (`pairOk`); a phi `v` of
    block `B`, from each executable edge `q → B`, has an operand whose term at `q`'s end is that of
    `r`'s operand from `q` (`r` a phi of `B`) or of `r` (`r` above `B`). -/
def StepCtx.pairOkP (X : StepCtx) (E : NatMap Unit) (dead : List (Nat × Nat)) (C : NatMap Operand)
    (PU : List UPred) (v : Nat) (r : Operand) : Bool :=
  match X.inD.find? v with
  | some (.stmt _ _) => X.pairOk C v r
  | some (.phi B) => (phiOf X.inB B v).any fun φ =>
    let live := φ.incoming.filter fun ob => edgeExec X.inB E dead ob.2 B
    let same : Bool := match r with
      | .var w => X.inD.find? w == some (.phi B) && (phiOf X.inB B w).any fun ψ =>
          live.all fun ob => (inc ψ ob.2).any fun o => gTermAt X C PU ob.2 ob.1 == gTermAt X C PU ob.2 o
      | .imm _ _ => false
    same || (X.above B r && live.all fun ob => gTermAt X C PU ob.2 ob.1 == gTermAt X C PU ob.2 r)
  | _ => false

/-- The classes hold on the input: each representative dominates its value, and each pair is
    justified. -/
def StepCtx.clsOkP (X : StepCtx) (E : NatMap Unit) (dead : List (Nat × Nat)) (PU : List UPred)
    (cls : List (Nat × Operand)) : Bool :=
  let C := NatMap.ofList cls
  cls.all fun e => e.2.wf && X.before e.2 e.1 && X.pairOkP E dead C PU e.1 e.2

/-- The class pairs, those a check fails dropped, to a fixpoint (at most `n` rounds). -/
def keepValidP (X : StepCtx) (E : NatMap Unit) (dead : List (Nat × Nat)) (PU : List UPred) :
    Nat → List (Nat × Operand) → List (Nat × Operand)
  | 0, cls => cls
  | n + 1, cls =>
    let C := NatMap.ofList cls
    let cls' := cls.filter fun e => e.2.wf && X.before e.2 e.1 && X.pairOkP E dead C PU e.1 e.2
    if cls'.length == cls.length then cls else keepValidP X E dead PU n cls'

/-! ## The check -/

/-- A dead slot: of a block outside the executable set, or of a `br` whose condition's term at the
    block's end is a literal selecting the other slot. -/
def deadOk (X : StepCtx) (E : NatMap Unit) (C : NatMap Operand) (PU : List UPred)
    (bk : Nat × Nat) : Bool :=
  (E.find? bk.1).isNone || (X.inB.find? bk.1).any fun blk => match blk.term with
    | .br c _ _ => match gTermAt X C PU bk.1 c with
      | .lit w => (if w % W != 0 then 1 else 0) == bk.2
      | _ => false
    | _ => false

/-- Why a `gvn_prune` step is rejected. -/
inductive PReject where
  | noIds | noFacts | wrongFacts | inputSsa | kbFacts | exec | shape | cert
  | dead (bk : Nat × Nat) | prunedCfg | cleanup
  deriving Repr, DecidableEq

/-- The dead slots, the executable set, the usable predicates and the validated classes. -/
def prunePrep (f : Func) (s : FuncSnap) (F : StepFacts) (G : GvnFacts) :
    StepCtx × NatMap Unit × List UPred × List (Nat × Operand) :=
  let X := StepCtx.of f s F false
  let E := execSet f G.deadEdges
  let PU := G.preds.filterMap (usePred X f E G.deadEdges)
  let cls := G.cls.map fun e => (e.1, e.2.toOperand)
  (X, E, PU, keepValidP X E G.deadEdges PU (cls.length + 1) cls)

def gvnPruneReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option PReject :=
  match ids, F.gvn with
  | none, _ => some .noIds
  | _, none => some .noFacts
  | some is, some G =>
    if !F.unread.isEmpty || F.consts.isSome || F.demanded.isSome || !F.deadEdges.isEmpty ||
        !F.finiteLoops.isEmpty || !G.phis.isEmpty || !G.valuePhis.isEmpty then some .wrongFacts
    else if !ssaOk f then some .inputSsa
    else
      let (X, E, PU, cls) := prunePrep f s F G
      if !(F.knownBits.isEmpty || kbFactsOk X.inB X.inD F) then some .kbFacts
      else if !execClosed f E G.deadEdges then some .exec
      else if !pruneShapeOk X.inB G.deadEdges then some .shape
      else if !X.clsOkP E G.deadEdges PU cls then some .cert
      else match G.deadEdges.find? (fun bk => !deadOk X E (.ofList cls) PU bk) with
        | some bk => some (.dead bk)
        | none =>
          if !(pruneFunc f G.deadEdges).cfgOk then some .prunedCfg
          else if !checkCfgCleanup none (pruneFunc f G.deadEdges) (some is) s then some .cleanup
          else none

/-- `gvn_prune` (design §4.8). -/
def checkGvnPrune (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Bool :=
  (gvnPruneReject f ids s F).isNone

def diagnoseGvnPrune (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option String :=
  (gvnPruneReject f ids s F).map fun r => s!"{repr r}"

end Fe.Sonatina.Steps.Schemas
