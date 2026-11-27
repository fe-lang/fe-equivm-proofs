import Fe.Sonatina.Steps.Run

/-!
# `lower_switches` (design §4.9, review H-5 and M-4)

Sonatina's `lower_switches` (`isa/evm/machine/switch.rs`) turns a `br_table s D cases` of block
`r` whose keys are immediates, with a default and more cases than a leaf holds, into a tree:
`r` keeps its phis and statements and ends with `v = lt s k; br v lo hi`, each new internal
block is exactly `v = lt s k; br v lo hi`, and each leaf is exactly `br_table s D cases'`.  The
cases are sorted by unsigned key and split at the middle; the pivot `k` is the upper half's
first key, so `s < k` goes to the lower half.  Phis of the targets take, from each leaf that
goes to them, the operand they took from `r`, and lose their operand from `r`.  Nothing else
changes; every tree instruction is new (`insert_inst_data_from` copies only the attribution).

The check (`checkLowerSwitches`):
- the output's blocks of the input's ids, in the input's order: phis that are the input's with
  each operand from a lowered `r` replaced by one from each leaf of `r`'s tree that goes there
  (the operand the input takes from `r`; `phiOk`, through `lab`, and as a permutation of
  `expected`); the input's statements and terminator, the targets input blocks; or, for a
  lowered switch, the input's statements, then `v = lt s k` with `v` a value the input does
  not mention, and `br v lo hi` (`rootOk`);
- the trees (`nodeOk`): an interval `[a, b)` of words, `[0, 2 ^ 256)` at the root, narrowed at
  each internal node to `[a, k)` towards `lo` and `[k, b)` towards `hi`, with `a < k < b`; each
  internal node a new block with no phis, `v = lt s k` (`v` fresh) and `br v lo hi`; each leaf
  a new block with no phis or statements and the terminator `br_table s D cases'` whose cases
  are, on the interval, the input's (`leafOk`: each leaf case has a key in the interval and the
  input's target for it; each input case with a key in the interval is a leaf case), with
  distinct keys and input blocks as targets, and the leaf stands for `r` as a predecessor
  (`lab`);
- every new block is a node of one tree, once; the input's blocks keep their order; the trees'
  new values are distinct (`shapeOk`);
- instruction ids (`idsOk`): an unchanged block keeps its ids; a lowered block its phis' and
  statements' ids, with two new ones for `lt` and `br`; a new block has new ids;
- the input's dominator tree valid and the input in strict SSA on it (the proof reads the
  input's scrutinee and phi operands through the definedness invariant).

The proof (`LowerSwitchesSound.lean`) needs the semantic parts only; `shapeOk`, `idsOk`, the
permutation of `expected`, the leaf's distinct keys and the pivots' bounds are checked to hold
the output to what the lowering emits (H-5, M-4).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-- The value an operand reads, if any. -/
def opVar : Operand → Option Nat
  | .var v => some v
  | .imm _ _ => none

/-- The values `f` mentions: its parameters, and each block's phis and their operands, its
    statements' results and operands, and its terminator's operands. -/
def funcVars (f : Func) : List Nat :=
  f.params.map (·.1) ++ f.blocks.flatMap fun b =>
    b.phis.flatMap (fun p => p.dst :: p.incoming.filterMap (opVar ·.1)) ++
    b.body.flatMap (fun s => s.dsts.map (·.1) ++ s.inst.args.filterMap opVar) ++
    b.term.args.filterMap opVar

/-- The target of the first case with the immediate key `k`, if any. -/
def look (cs : List (Operand × Nat)) (k : Nat) : Option Nat :=
  (cs.find? fun c => c.1.immVal? == some k).map (·.2)

/-- The blocks of the tree below `n`, in pre-order: `n`'s block, then, if it branches, the
    trees below its targets. -/
def subtree (B' : NatMap Block) : Nat → Nat → List Block
  | 0, _ => []
  | fuel + 1, n => match B'.find? n with
    | none => []
    | some nb => nb :: match nb.term with
      | .br _ lo hi => subtree B' fuel lo ++ subtree B' fuel hi
      | _ => []

/-- A block that ends in a table: a leaf. -/
def isLeafBlock (b : Block) : Bool :=
  match b.term with
  | .brTable .. => true
  | _ => false

/-- A leaf's cases `cs'` against the input's `cs` on the interval `[a, b)`: each leaf case has an
    immediate key in the interval and the input's target for it; each input case with a key in
    the interval is a leaf case. -/
def leafOk (a b : Nat) (cs cs' : List (Operand × Nat)) : Bool :=
  cs'.all (fun c => match c.1.immVal? with
    | some k => decide (a ≤ k ∧ k < b) && look cs k == some c.2
    | none => false) &&
  cs.all fun c => match c.1.immVal? with
    | some k => !decide (a ≤ k ∧ k < b) || look cs' k == some c.2
    | none => false

/-- What the check reads of a pair of functions. -/
structure LSCtx where
  B : NatMap Block
  B' : NatMap Block
  /-- The values the input mentions (`funcVars`). -/
  V : NatMap Unit
  /-- Each lowered switch's block and the leaves of its tree. -/
  leaves : NatMap (List Block)
  /-- Each leaf and its tree's lowered switch. -/
  leafRoot : NatMap Nat
  /-- Each lowered switch's block and the blocks of its tree below it, in pre-order. -/
  trees : List (Nat × List Block)
  fuel : Nat

def LSCtx.of (f f' : Func) : LSCtx :=
  let B : NatMap Block := .ofListBy (·.id) f.blocks
  let B' : NatMap Block := .ofListBy (·.id) f'.blocks
  let fuel := f'.blocks.length + 1
  let trees := f'.blocks.filterMap fun b' => match B.find? b'.id with
    | some bb => if b'.term = bb.term then none else some (b'.id, match b'.term with
      | .br _ lo hi => subtree B' fuel lo ++ subtree B' fuel hi
      | _ => [])
    | none => none
  let lv := trees.map fun t => (t.1, t.2.filter isLeafBlock)
  ⟨B, B', .ofList ((funcVars f).map (·, ())), .ofList lv,
    .ofList (lv.flatMap fun t => t.2.map (·.id, t.1)), trees, fuel⟩

namespace LSCtx

variable (X : LSCtx)

/-- An input block. -/
def orig (id : Nat) : Bool := (X.B.find? id).isSome

/-- A value the input does not mention. -/
def fresh (v : Nat) : Bool := (X.V.find? v).isNone

/-- The input block an output block stands for as a predecessor: itself, or a leaf's switch. -/
def lab (q : Nat) : Option Nat := if X.orig q then some q else X.leafRoot.find? q

/-- A tree node's last statement `st` and its branch's condition `c`: `v = lt s k` with `v`
    fresh and `c` the value `v`; its pivot `k`. -/
def pivot? (s : Operand) (st : Stmt) (c : Operand) : Option Nat :=
  match st.dsts, st.inst with
  | [(d, ty)], .cmp .lt s' (.imm bits k) =>
    if ty = .int 256 ∧ bits = 256 ∧ s' = s ∧ c = .var d ∧ X.fresh d = true then some k else none
  | _, _ => none

/-- Block `n` is a node, on the interval `[a, b)`, of the tree of the switch `br_table s D cs`
    of block `r`. -/
def nodeOk (r : Nat) (s : Operand) (D : Nat) (cs : List (Operand × Nat)) :
    Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, a, b, n => !X.orig n && match X.B'.find? n with
    | none => false
    | some nb => nb.phis.isEmpty && match nb.body, nb.term with
      | [], .brTable s' (some D') cs' => decide (s' = s) && D' == D && X.orig D &&
          cs'.all (X.orig ·.2) && X.lab n == some r && leafOk a b cs cs' &&
          distinct (cs'.filterMap (·.1.immVal?))
      | [st], .br c lo hi => match X.pivot? s st c with
        | some k => decide (a < k ∧ k < b) && nodeOk r s D cs fuel a k lo &&
            nodeOk r s D cs fuel k b hi
        | none => false
      | _, _ => false

/-- A lowered switch: the input block `bb` ends in `br_table s D cs` with immediate keys and
    input blocks as targets; the output block `b'` has `bb`'s statements, then `v = lt s k`,
    then `br v lo hi`, and the trees below `lo` and `hi` are nodes on `[0, k)` and
    `[k, 2 ^ 256)`. -/
def rootOk (bb b' : Block) : Bool :=
  match bb.term, b'.body.getLast?, b'.term with
  | .brTable s (some D) cs, some st, .br c lo hi =>
    cs.all (fun c => X.orig c.2 && c.1.immVal?.isSome) && X.orig D &&
      decide (b'.body = bb.body ++ [st]) && match X.pivot? s st c with
      | some k => decide (0 < k ∧ k < 2 ^ 256) && X.nodeOk b'.id s D cs X.fuel 0 k lo &&
          X.nodeOk b'.id s D cs X.fuel k (2 ^ 256) hi
      | none => false
  | _, _, _ => false

/-- The operands a phi of block `b` must have: the input's, each one from a lowered switch
    replaced by one from each leaf of its tree that goes to `b`. -/
def expected (b : Nat) (p : Phi) : List (Operand × Nat) :=
  p.incoming.flatMap fun (o, q) => match X.leaves.find? q with
    | some ls => (ls.filter (·.term.succs.contains b)).map (o, ·.id)
    | none => [(o, q)]

/-- An output phi of block `b` against the input's: the same value and type; each operand the
    input's from the block its predecessor stands for; the operands those of `expected`. -/
def phiOk (b : Nat) (p' p : Phi) : Bool :=
  p'.dst == p.dst && decide (p'.ty = p.ty) &&
    p'.incoming.all (fun (o, q') => match X.lab q' with
      | some q => decide (inc p q = some o)
      | none => false) &&
    p'.incoming.isPerm (X.expected b p)

def phisOk (b : Nat) : List Phi → List Phi → Bool
  | [], [] => true
  | p' :: ps', p :: ps => X.phiOk b p' p && phisOk b ps' ps
  | _, _ => false

/-- An output block of an input block's id: the input's phis, rewritten (`phiOk`), and the
    input's statements and terminator, the targets input blocks, or a lowered switch
    (`rootOk`).  The new blocks are checked as nodes of the trees. -/
def blockOk (b' : Block) : Bool :=
  match X.B.find? b'.id with
  | some bb => X.phisOk b'.id b'.phis bb.phis &&
    if b'.term = bb.term then decide (b'.body = bb.body) && b'.term.succs.all X.orig
    else X.rootOk bb b'
  | none => true

/-- Every new block is a node of one tree, once; the input's blocks keep their order in the
    output; the trees' new values are distinct. -/
def shapeOk (f f' : Func) : Bool :=
  let nodes := X.trees.flatMap fun t => t.2.map (·.id)
  let N : NatMap Unit := .ofList (nodes.map (·, ()))
  distinct nodes && f'.blocks.all (fun b => X.orig b.id || (N.find? b.id).isSome) &&
    (f'.blocks.filter (X.orig ·.id)).map (·.id) == f.blocks.map (·.id) &&
    distinct ((X.trees.flatMap fun t => t.2 ++ (X.B'.find? t.1).toList).flatMap fun b =>
      b.body.getLast?.toList.flatMap fun st => st.dsts.map (·.1))

/-- An output block's instruction ids (`I'`) against the input's (`I`, all of them `inIds`): an
    unchanged block keeps them; a lowered switch keeps those of its phis and statements and has
    two new ones; a new block has new ones. -/
def idsOk (I I' : NatMap (List Nat)) (inIds : NatMap Unit) (b' : Block) : Bool :=
  let new := fun (ids : List Nat) => ids.all fun i => (inIds.find? i).isNone
  match I'.find? b'.id, X.B.find? b'.id, I.find? b'.id with
  | some oids, some bb, some iids =>
    if b'.term = bb.term then oids == iids
    else oids.length == iids.length + 1 &&
      oids.take (iids.length - 1) == iids.take (iids.length - 1) &&
      new (oids.drop (iids.length - 1))
  | some oids, none, _ => new oids
  | _, _, _ => false

end LSCtx

/-- The check of a `lower_switches` step of `f` (instruction ids `ids`) to the snapshot `s`. -/
def checkLowerSwitches (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) : Bool :=
  let f' := s.func
  let X := LSCtx.of f f'
  let T := domTree f
  match ids, f.blocks.head?, f'.blocks.head? with
  | some ids, some e, some e' =>
    let I : NatMap (List Nat) := .ofList ((f.blocks.zip ids).map fun bi => (bi.1.id, bi.2))
    let I' : NatMap (List Nat) := .ofList ((f'.blocks.zip s.insts).map fun bi => (bi.1.id, bi.2))
    let inIds : NatMap Unit := .ofList (ids.flatten.map (·, ()))
    f'.name == f.name && decide (f'.params = f.params) && e'.id == e.id && T.valid f &&
      ssa f T && f'.blocks.all X.blockOk && X.shapeOk f f' && f'.blocks.all (X.idsOk I I' inIds)
  | _, _, _ => false

end Fe.Sonatina.Steps
