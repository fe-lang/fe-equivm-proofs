import Fe.Sonatina.Steps.SchemasCheck
import Fe.Sonatina.Steps.CfgCleanup
import Fe.Sonatina.Steps.SchemasFacts

/-!
# The `known_bits_simplify`, `sccp_fold` and `scalar_canonicalize` checkers

The three steps keep the control flow and every terminator.  The first two change the function
by aliasing: `change_to_alias(v, x)` replaces every use of `v` by `x` (an immediate or a value),
and the instruction that defined `v` is erased (`remove_rewritten_inst`, SCCP's `fold`).
`sccp_fold` may also replace an instruction in place by `is_zero x`
(`SimplifyAction::BuildIsZero`, the only in-place replacement `sccp.rs` builds on machine IR:
`Bitcast` and `FoldFreshInsert` build instructions machine IR does not have), and alias a phi
whose executable incoming operands are one value (`try_fold_phi`).  A `scalar_canonicalize`
round replaces instructions in place (`RewritePlan::ReplaceInst`; its `Copy` plans come from
casts, which machine IR does not have) by any pure instruction, each plan made on the round's
input, and deletes dead pure instructions (`prune_dead_pure_insts`); it exports no facts.

**Frame** (review 13, finding 3).  The checks stand on their own under `f.wf` of the input: the
output keeps the input's name, parameters and results, is machine IR, every output operand is
well formed (`Operand.wf`: an `i256` immediate below `2 ^ 256`), and both snapshots have one
distinct id per line of every block (no `zip` truncates).  The output is also `wordTyped`,
`cfgOk` and its terminators `Term.wf`: with the pairing (every output statement but an
`is_zero` is an input statement with operands substituted) that makes it `Func.wf` under the
input's `sig` and `syms`, which L2 on the output side needs.

**Pairing** (`pairBlock`).  The output has the input's blocks, in order, with the same ids.  In
each block the output's lines are input lines of the same instruction id, in order; the input
lines left over are *deleted*.  A deleted line is a phi or a pure, single-result statement other
than `clz` (review H-2), never a terminator.

**σ** (`sigmaOf`).  Zipping the operands of each paired line gives, where they differ, an entry
`v ↦ x` for an input operand `v`.  σ must be a function, and every paired line must be its input
line with σ applied to its operands (`mapLine`), except, for `sccp_fold` and
`scalar_canonicalize`, a replaced statement (`replaceOk`).  Every value σ maps is the result of
a deleted line.

**Justification** of each σ entry `v ↦ x` (design §4.7 and §4.5, review C-2):
- `sccp_fold`: `x` is the immediate `c` and SCCP claims `v = c`; or a schema (`checkExact`)
  maps the unfolded input definition of `v` to `x` unfolded in the output, with SCCP's constants
  as literals (ruling 5);
- `known_bits_simplify` without demanded bits: a schema (`checkExact`) with the known bits;
- `scalar_canonicalize`: a schema (`checkExact`) without facts;
- `known_bits_simplify` with demanded bits (a round of demand rewrites only, C-2): a demand
  schema (`checkDemand`) on the demanded bits of `v`, and `x` a value whose demand contains
  `v`'s.

Unfolding (`unfold`) goes through pure statements other than `clz` of the snapshot's own
definitions (the input's for `T_in`, the output's for `T_out`): the same depth on both sides, 1
to 3, or the output side a leaf and the input side 0 to 3 levels (ruling R-11.1).  Its leaves
are values: paired ones on the output side (the output's strict SSA rejects a use of a deleted
one), any value of the input on the input side.  An entry may also go through a chain of at most
three deleted operands, each step justified (`resolve_replacements` collapses copy chains).  A
replaced statement's input term may also be unfolded three levels down to the replacement's
operands (`unfoldStop`), for rewrites whose operands sit at different depths
(`not (add (not x) y) → sub x y`).  No term has `clz` (review H-2, review 13 finding 2).

**Facts**, checked on the input (design §3.3, ruling 8): known bits as a post-fixpoint
(`kbFactsOk`); SCCP's dead edges and constants on the executable blocks, a set the check
validates itself: it holds the entry and is closed under every slot not claimed dead
(`execClosed`, review 13 finding 1; the fixpoint computed is only a candidate); demanded bits
over every instruction (`dbFactsOk`).  Both snapshots are checked in strict SSA under a validated dominator
tree.

`checkKnownBitsSimplify f ids s F`, `checkSccpFold f ids s F` and
`checkScalarCanonicalize f ids s F`: the input function `f` with
its instruction ids `ids`, the output snapshot `s`, the step's facts `F` (`readFacts` reads them
from the record's JSON, at elaboration).  `diagnose…` give the first failing check by name.
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

/-! ## Unfolding definitions into terms -/

/-- The term of a pure instruction, its operands mapped by `g`. -/
def termOf (g : Operand → Term) : PureInst → Term
  | .op1 o a => .op1 o (g a)
  | .op2 o a b => .op2 o (g a) (g b)
  | .op3 o a b c => .op3 o (g a) (g b) (g c)

/-- The statement defining `v`, from a function's maps. -/
def defStmt (B : NatMap Block) (D : NatMap Def) (v : Nat) : Option Stmt :=
  match D.find? v with
  | some (.stmt b k) => (B.find? b).bind (·.body[k]?)
  | _ => none

/-- An operand as a term: an immediate a literal, a value with an SCCP constant its literal, a
    value defined by a pure statement unfolded `d` more levels, any other value an atom. -/
def unfold (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) : Nat → Operand → Term
  | _, .imm _ w => .lit w
  | d, .var v => match cs.find? v with
    | some c => .lit c
    | none => match d with
      | 0 => .atom v
      | d + 1 => match (defStmt B D v).bind (pureInst? ·.inst) with
        | some (.op1 .clz _) | none => .atom v
        | some p => termOf (unfold B D cs d) p

/-- `unfold`, leaving the values of `stop` atoms: the input's term of a replaced statement
    stops at the operands of its replacement, however deep they sit in it. -/
def unfoldStop (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) (stop : List Nat) :
    Nat → Operand → Term
  | _, .imm _ w => .lit w
  | d, .var v => match cs.find? v with
    | some c => .lit c
    | none => if stop.contains v then .atom v else match d with
      | 0 => .atom v
      | d + 1 => match (defStmt B D v).bind (pureInst? ·.inst) with
        | some (.op1 .clz _) | none => .atom v
        | some p => termOf (unfoldStop B D cs stop d) p

/-- A pure instruction other than `clz`. -/
def noClz : PureInst → Bool
  | .op1 .clz _ => false
  | _ => true

/-- The term of a pure instruction other than `clz`, its operands unfolded `d` levels. -/
def instTerm (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) (d : Nat) (i : Inst) :
    Option Term :=
  match pureInst? i with
  | some p => if noClz p then some (termOf (unfold B D cs d) p) else none
  | none => none

/-- `instTerm` with `unfoldStop`. -/
def instTermStop (B : NatMap Block) (D : NatMap Def) (cs : NatMap Nat) (stop : List Nat)
    (d : Nat) (i : Inst) : Option Term :=
  match pureInst? i with
  | some p => if noClz p then some (termOf (unfoldStop B D cs stop d) p) else none
  | none => none

/-- The values among the operands. -/
def opVars (os : List Operand) : List Nat :=
  os.filterMap fun o => match o with
    | .var v => some v
    | _ => none

/-! ## Pairing the two snapshots -/

/-- A block's lines with their instruction ids. -/
def idLines (b : Block) (ids : List Nat) : List (Nat × Line) :=
  ids.zip (b.phis.map Line.phi ++ b.body.map Line.stmt ++ [Line.term b.term])

/-- Pair the output's lines with the input's of the same id, in order: the pairs, and the input
    lines left over. -/
def pairUp : List (Nat × Line) → List (Nat × Line) → Option (List (Line × Line) × List Line)
  | ins, [] => some ([], ins.map (·.2))
  | [], _ :: _ => none
  | (i, L) :: ins, (i', L') :: outs =>
    if i == i' then (pairUp ins outs).map fun r => ((L, L') :: r.1, r.2)
    else (pairUp ins ((i', L') :: outs)).map fun r => (r.1, L :: r.2)

/-- The operands of a line, in order. -/
def lineOps : Line → List Operand
  | .phi p => p.incoming.map (·.1)
  | .stmt s => s.inst.args
  | .term t => t.args

/-- A deleted line: a phi, or a pure single-result statement other than `clz`. -/
def deletable : Line → Bool
  | .phi _ => true
  | .stmt s => s.dsts.length == 1 && match pureInst? s.inst with
    | some (.op1 .clz _) | none => false
    | some _ => true
  | .term _ => false

/-- The values a line defines. -/
def lineDefs : Line → List Nat
  | .phi p => [p.dst]
  | .stmt s => s.dsts.map (·.1)
  | .term _ => []

/-- A block's line count: its phis, statements and terminator. -/
def lineCount (b : Block) : Nat := b.phis.length + b.body.length + 1

/-- One id per line of every block. -/
def idsFit (bs : List Block) (ids : List (List Nat)) : Bool :=
  ids.length == bs.length && (bs.zip ids).all fun bi => bi.2.length == lineCount bi.1

/-- The input lines paired with the output's, and the deleted ones, block by block. -/
def pairFunc (f : Func) (ids : List (List Nat)) (s : FuncSnap) :
    Option (List (Line × Line) × List Line) :=
  if f.blocks.length == s.func.blocks.length && idsFit f.blocks ids &&
      idsFit s.func.blocks s.insts && f.blocks.map (·.id) == s.func.blocks.map (·.id) then
    ((f.blocks.zip ids).zip (s.func.blocks.zip s.insts)).foldlM (fun acc bb =>
      (pairUp (idLines bb.1.1 bb.1.2) (idLines bb.2.1 bb.2.2)).map fun r =>
        (acc.1 ++ r.1, acc.2 ++ r.2)) ([], [])
  else none

/-- `σ` applied to an operand. -/
def subst (σ : NatMap Operand) : Operand → Operand
  | .var v => (σ.find? v).getD (.var v)
  | o => o

/-- σ from the paired lines: each differing operand pair `(var v, x)`; a function.  The
    operands of two statements are not zipped if their counts differ (a replaced statement), or
    at all if `zipStmts` is off (`scalar_canonicalize`, whose replacements may keep the count). -/
def sigmaOf (zipStmts : Bool) (pairs : List (Line × Line)) : Option (NatMap Operand) :=
  pairs.foldlM (fun σ LL =>
    let a := lineOps LL.1
    let b := lineOps LL.2
    if a.length != b.length || (!zipStmts && match LL.1, LL.2 with
        | .stmt _, .stmt _ => true
        | _, _ => false) then
      -- a replaced statement: its operands are not zipped
      match LL.1, LL.2 with
      | .stmt _, .stmt _ => some σ
      | _, _ => none
    else (a.zip b).foldlM (fun σ ob =>
      if ob.1 == ob.2 then some σ
      else match ob.1 with
        | .var v => match σ.find? v with
          | some x => if x == ob.2 then some σ else none
          | none => some (σ.insert v ob.2)
        | _ => none) σ) .empty

/-- The input line with σ applied to its operands. -/
def mapLine (σ : NatMap Operand) : Line → Line
  | .phi p => .phi { p with incoming := p.incoming.map fun ob => (subst σ ob.1, ob.2) }
  | .stmt s => .stmt (s.mapOps (subst σ))
  | .term t => .term (t.mapOps (subst σ))

def lineEq : Line → Line → Bool
  | .phi p, .phi q => p == q
  | .stmt s, .stmt t => s == t
  | .term t, .term u => t == u
  | _, _ => false

/-! ## Facts on the input -/

def kbMap (F : StepFacts) : NatMap KB := .ofList (F.knownBits.map fun e => (e.1, ⟨e.2.1, e.2.2⟩))

def kbOf (K : NatMap KB) (v : Nat) : KB := (K.find? v).getD unknown

/-- An operand's fact: an immediate's exact, a value's claimed or unknown. -/
def opFact (K : NatMap KB) : Operand → KB
  | .imm _ w => exact (w % W)
  | .var v => kbOf K v

/-- The fact the transfer functions give a pure instruction from its operands' facts. -/
def transferOf (K : NatMap KB) : PureInst → KB
  | .op1 o a => transfer1 o (opFact K a)
  | .op2 o a b => transfer2 o (opFact K a) (opFact K b)
  | .op3 o a b c => transfer3 o (opFact K a) (opFact K b) (opFact K c)

/-- The phi of value `v` in block `b`. -/
def phiOf (B : NatMap Block) (b v : Nat) : Option Phi :=
  (B.find? b).bind fun blk => blk.phis.find? (·.dst == v)

/-- The meet over all incoming operands. -/
def meetAll (K : NatMap KB) : List Operand → KB
  | [] => unknown
  | o :: os => os.foldl (fun a x => meet a (opFact K x)) (opFact K o)

/-- Known bits as a post-fixpoint (design §3.3, ruling 8): each claim valid, of a phi or a pure
    statement's result, and no stronger than the transfer (the meet for a phi) of the claims. -/
def kbFactsOk (B : NatMap Block) (D : NatMap Def) (F : StepFacts) : Bool :=
  let K := kbMap F
  distinct (F.knownBits.map (·.1)) && F.knownBits.all fun e =>
    let c : KB := ⟨e.2.1, e.2.2⟩
    c.valid && match D.find? e.1 with
    | some (.phi b) => (phiOf B b e.1).any fun p => c.le (meetAll K (p.incoming.map (·.1)))
    | some (.stmt _ _) => ((defStmt B D e.1).bind fun s => pureInst? s.inst).any fun p =>
        c.le (transferOf K p)
    | _ => false

/-- The word an operand is under SCCP's constants. -/
def constOf (cs : NatMap Nat) : Operand → Option Nat
  | .imm _ w => some (w % W)
  | .var v => cs.find? v

/-- Slot `k` of the terminator may be taken under the constants. -/
def slotTaken (cs : NatMap Nat) (t : Fe.Sonatina.Term) (k : Nat) : Bool :=
  match t with
  | .br c _ _ => match constOf cs c with
    | some x => (if x != 0 then 0 else 1) == k
    | none => true
  | .brTable sc d cases => match constOf cs sc with
    | some x =>
      if d.isNone || !cases.all (fun ci => (constOf cs ci.1).isSome) then true
      else match (cases.zipIdx.find? fun ci => constOf cs ci.1.1 == some x) with
        | some ci => ci.2 + 1 == k
        | none => k == 0
    | none => true
  | _ => true

/-- The blocks the entry reaches over slots not claimed dead. -/
def execSet (f : Func) (dead : List (Nat × Nat)) : NatMap Unit :=
  let S : NatMap (List Nat) := .ofList (f.blocks.map fun b =>
    (b.id, ((b.term.succs.zipIdx.filter fun tk => !dead.contains (b.id, tk.2)).map (·.1)).eraseDups))
  let n := f.blocks.length
  match f.blocks.head? with
  | none => .empty
  | some e => reachAux S (4 * n * (n + 1) + 4) [e.id] .empty

/-- The executable set is closed (review 13, finding 1): it holds the entry, and every slot not
    claimed dead of a block in it goes to a block in it.  The proof reads this, not `reachAux`. -/
def execClosed (f : Func) (E : NatMap Unit) (dead : List (Nat × Nat)) : Bool :=
  (f.blocks.head?.any fun e => (E.find? e.id).isSome) && f.blocks.all fun b =>
    (E.find? b.id).isNone || b.term.succs.zipIdx.all fun tk =>
      dead.contains (b.id, tk.2) || (E.find? tk.1).isSome

/-- The edge `p → b` is executable: `p` is, and a slot of its terminator not claimed dead goes to
    `b`. -/
def edgeExec (B : NatMap Block) (E : NatMap Unit) (dead : List (Nat × Nat)) (p b : Nat) : Bool :=
  (E.find? p).isSome && (B.find? p).any fun blk =>
    blk.term.succs.zipIdx.any fun tk => tk.1 == b && !dead.contains (p, tk.2)

/-- A claimed constant of a pure statement's result: its operands' constants evaluate to it, or
    a schema maps its term to the literal. -/
def stmtConstOk (B : NatMap Block) (D : NatMap Def) (K : NatMap KB) (cs : NatMap Nat) (p : PureInst)
    (c : Nat) : Bool :=
  noClz p && ((match (p.args.mapM (constOf cs)) with
    | some xs => evalConst p.op xs == some c
    | none => false) ||
  [0, 1, 2, 3].any fun d => checkExact (kbOf K) (termOf (unfold B D cs d) p) (.lit c))

/-- SCCP's facts (design §3.3): every dead edge from an executable block is one its terminator
    does not take under the constants; every constant of a value in an executable block holds,
    for a phi from every executable incoming edge, for a pure statement by evaluation or a
    schema; no constant of a parameter or an effectful result. -/
def sccpFactsOk (f : Func) (B : NatMap Block) (D : NatMap Def) (K : NatMap KB) (F : StepFacts) :
    Bool :=
  match F.consts with
  | none => false
  | some consts =>
    let cs : NatMap Nat := .ofList consts
    let E := execSet f F.deadEdges
    distinct (consts.map (·.1)) && consts.all (fun e => decide (e.2 < W)) &&
    execClosed f E F.deadEdges &&
    F.deadEdges.all (fun pk => (E.find? pk.1).isNone ||
      (B.find? pk.1).any fun blk => !slotTaken cs blk.term pk.2) &&
    consts.all fun e => match D.find? e.1 with
      | some (.phi b) => (E.find? b).isNone || (phiOf B b e.1).any fun p =>
          p.incoming.all fun ob => !edgeExec B E F.deadEdges ob.2 b || constOf cs ob.1 == some e.2
      | some (.stmt b _) => (E.find? b).isNone ||
          ((defStmt B D e.1).bind fun s => pureInst? s.inst).any fun p =>
            stmtConstOk B D K cs p e.2
      | _ => false

def dbMap (ds : List (Nat × Nat)) : NatMap Nat := .ofList ds

def dOf (DB : NatMap Nat) (v : Nat) : Nat := (DB.find? v).getD 0

/-- The operand's claimed demand contains `m` (an immediate needs none). -/
def demandHas (DB : NatMap Nat) (m : Nat) : Operand → Bool
  | .var v => m &&& M &&& dOf DB v == m &&& M
  | _ => true

/-- Demanded bits over every instruction of the input (design §3.3, review L-2): an impure
    statement and a terminator demand every bit of their operands (`mstore8` only the low byte of
    its value); a pure statement whose result has demanded bits demands what the backward
    function gives; a phi with demanded bits demands them of every incoming operand. -/
def dbFactsOk (f : Func) (ds : List (Nat × Nat)) : Bool :=
  let DB := dbMap ds
  distinct (ds.map (·.1)) && ds.all (fun e => decide (e.2 < W)) && f.blocks.all fun b =>
    b.phis.all (fun p => p.incoming.all fun ob => demandHas DB (dOf DB p.dst) ob.1) &&
    b.body.all (fun s => match pureInst? s.inst, s.dsts with
      | some p, [(r, _)] =>
        let d := dOf DB r
        match p with
        | .op1 o a => demandHas DB (demand1 o d) a
        | .op2 o a b2 =>
          let dd := demand2 o a.immVal? d
          demandHas DB dd.1 a && demandHas DB dd.2 b2
        | .op3 o a b2 c => let dd := demand3 o d
          demandHas DB dd.1 a && demandHas DB dd.2.1 b2 && demandHas DB dd.2.2 c
      | _, _ => match s.inst with
        | .evm .mstore8 [p, v] => demandHas DB M p && demandHas DB 0xff v
        | i => i.args.all (demandHas DB M)) &&
    b.term.args.all (demandHas DB M)

/-! ## The checks -/

/-- What both checkers share: the maps of both snapshots. -/
structure StepCtx where
  inB : NatMap Block
  inD : NatMap Def
  outB : NatMap Block
  outD : NatMap Def
  K : NatMap KB
  /-- SCCP's constants, as literals of the terms. -/
  cs : NatMap Nat
  /-- The input's dominator tree. -/
  T : DomTree
  /-- SCCP's executable blocks and dead edges (`sccp_fold`). -/
  E : NatMap Unit
  dead : List (Nat × Nat)

def StepCtx.of (f : Func) (s : FuncSnap) (F : StepFacts) (useConsts : Bool) : StepCtx where
  inB := .ofListBy (·.id) f.blocks
  inD := defsOf f
  outB := .ofListBy (·.id) s.func.blocks
  outD := defsOf s.func
  K := kbMap F
  cs := if useConsts then .ofList (F.consts.getD []) else .empty
  T := domTree f
  E := execSet f F.deadEdges
  dead := F.deadEdges

/-- `T_in` of value `v` at depth `d`: its input definition, unfolded. -/
def StepCtx.tin (X : StepCtx) (d v : Nat) : Option Term :=
  (defStmt X.inB X.inD v).bind fun s => instTerm X.inB X.inD X.cs d s.inst

/-- `T_out` of an output operand at depth `d`. -/
def StepCtx.tout (X : StepCtx) (d : Nat) (o : Operand) : Term := unfold X.outB X.outD X.cs d o

/-- The depths tried, `(input, output)`: equal, 1 to 3, or the output a leaf (R-11.1). -/
def depths : List (Nat × Nat) := [(1, 1), (2, 2), (3, 3), (0, 0), (1, 0), (2, 0), (3, 0)]

/-- How a σ entry may be justified. -/
inductive Mode where
  /-- `known_bits_simplify` without demanded bits. -/
  | exact
  /-- `known_bits_simplify` with demanded bits. -/
  | demand (DB : NatMap Nat)
  /-- `sccp_fold`. -/
  | sccp
  /-- `scalar_canonicalize`: no facts; statements replaced in place by any pure instruction. -/
  | scalar
  /-- `gvn_rewrite`: GVN's classes, `(value, representative)`, and the phis it inserted,
      `(phi, block, term)`, both checked on the input (`GvnRewrite.lean`). -/
  | gvn (cls : List (Nat × Operand)) (pts : List (Nat × Nat × Term))

/-- `x` is an immediate, or a parameter, or defined in a strict dominator of block `b` of the
    input: its value is the same on every entry of `b`. -/
def StepCtx.above (X : StepCtx) (b : Nat) : Operand → Bool
  | .imm _ _ => true
  | .var w => match X.inD.find? w with
    | some .param => true
    | some (.phi d) | some (.stmt d _) => d != b && X.T.anc d b
    | none => false

/-- `try_fold_phi`: the deleted phi `v` of block `b`, whose operands on executable edges are `x`
    or `v` itself, with at least one `x`, and `x` the same on every entry of `b`. -/
def StepCtx.phiFold (X : StepCtx) (v : Nat) (x : Operand) : Bool :=
  match X.inD.find? v with
  | some (.phi b) => X.above b x && (phiOf X.inB b v).any fun p =>
      let live := p.incoming.filter fun ob => edgeExec X.inB X.E X.dead ob.2 b
      live.any (·.1 == x) && live.all fun ob => ob.1 == x || ob.1 == .var v
  | _ => false

/-! ## GVN's certificate -/

/-- The representative of an operand: its class's chain followed at most `n` links. -/
def gRoot (C : NatMap Operand) : Nat → Operand → Operand
  | 0, o => o
  | n + 1, .var v => match C.find? v with
    | some r => gRoot C n r
    | none => .var v
  | _ + 1, o => o

/-- An operand as a term through its representative: a literal or an atom. -/
def gTerm (C : NatMap Operand) (o : Operand) : Term :=
  match gRoot C 16 o with
  | .var v => .atom v
  | .imm _ w => .lit w

/-- `x`'s definition dominates `v`'s: an immediate, a parameter, a phi of a block that is a tree
    ancestor-or-self of `v`'s, or a statement before `v`'s definition (in a strict tree ancestor of
    its block, or earlier in it), and `v` is defined. -/
def StepCtx.before (X : StepCtx) (x : Operand) (v : Nat) : Bool :=
  match x with
  | .imm _ _ => true
  | .var w => match X.inD.find? w, X.inD.find? v with
    | some .param, some _ => true
    | some (.phi d), some (.phi b) => X.T.anc d b
    | some (.phi d), some (.stmt b _) => X.T.anc d b
    | some (.stmt d _), some (.phi b) => d != b && X.T.anc d b
    | some (.stmt d j), some (.stmt b k) => (d != b && X.T.anc d b) || (d == b && decide (j < k))
    | _, _ => false

/-- The block of `v`'s definition. -/
def StepCtx.blockOf (X : StepCtx) (v : Nat) : Option Nat :=
  match X.inD.find? v with
  | some (.phi b) | some (.stmt b _) => some b
  | _ => none

/-- A representative's term: a literal, its pure statement other than `clz` with operands through
    their representatives, or its representative. -/
def StepCtx.repTerm (X : StepCtx) (C : NatMap Operand) : Operand → Term
  | .imm _ w => .lit w
  | .var w => match (defStmt X.inB X.inD w).bind fun st => pureInst? st.inst with
    | some q => if noClz q then termOf (gTerm C) q else gTerm C (.var w)
    | none => gTerm C (.var w)

/-- A class pair `(v, r)`, from the classes `C`: `v` a pure statement other than `clz` whose term,
    each operand through its representative, a schema equates with `r`'s (a literal, an atom, or
    `r`'s pure statement likewise); or `v` a phi of block `B` whose operands from each predecessor
    have the representative of `r`'s operand from it (`r` a phi of `B`) or of `r` (`r` above
    `B`). -/
def StepCtx.pairOk (X : StepCtx) (C : NatMap Operand) (v : Nat) (r : Operand) : Bool :=
  match X.inD.find? v with
  | some (.stmt _ _) =>
    ((defStmt X.inB X.inD v).bind fun st => pureInst? st.inst).any fun p =>
      noClz p && checkExact (kbOf X.K) (termOf (gTerm C) p) (X.repTerm C r)
  | some (.phi B) => (phiOf X.inB B v).any fun φ =>
    let same : Bool := match r with
      | .var w => X.inD.find? w == some (.phi B) && (phiOf X.inB B w).any fun ψ =>
          φ.incoming.all fun ob => (inc ψ ob.2).any fun o => gTerm C ob.1 == gTerm C o
      | .imm _ _ => false
    same || (X.above B r && φ.incoming.all fun ob => gTerm C ob.1 == gTerm C r)
  | _ => false

/-- The classes hold on the input: each representative dominates its value, and each pair is
    justified. -/
def StepCtx.clsOk (X : StepCtx) (cls : List (Nat × Operand)) : Bool :=
  let C := NatMap.ofList cls
  cls.all fun e => e.2.wf && X.before e.2 e.1 && X.pairOk C e.1 e.2

/-- The incoming operand from `p` of the phi `a` of block `Q`, as a term. -/
def phiArgTerm (X : StepCtx) (Q p a : Nat) : Term :=
  match (phiOf X.inB Q a).bind fun φ => inc φ p with
  | some (.var u) => .atom u
  | some (.imm _ w) => .lit w
  | none => .atom a

/-- A term with each phi of block `Q` replaced by its operand from `p`. -/
def substPhis (X : StepCtx) (Q p : Nat) : Term → Term
  | .atom a => if X.inD.find? a == some (.phi Q) then phiArgTerm X Q p a else .atom a
  | .lit w => .lit w
  | .op1 o a => .op1 o (substPhis X Q p a)
  | .op2 o a b => .op2 o (substPhis X Q p a) (substPhis X Q p b)
  | .op3 o a b c => .op3 o (substPhis X Q p a) (substPhis X Q p b) (substPhis X Q p c)

/-- The atoms of a term. -/
def Term.atoms : Term → List Nat
  | .atom a => [a]
  | .lit _ => []
  | .op1 _ a => a.atoms
  | .op2 _ a b => a.atoms ++ b.atoms
  | .op3 _ a b c => a.atoms ++ b.atoms ++ c.atoms

/-- The inserted phis hold their terms: each a phi `ψ` of its block `Q`; its term without `clz`,
    its atoms phis of `Q` or above `Q`; from each predecessor `p`, `ψ`'s operand is, by a schema,
    the term with `Q`'s phis replaced by their operands from `p`: the operand unfolded, or an
    inserted phi whose term it is. -/
def StepCtx.ptOk (X : StepCtx) (pts : List (Nat × Nat × Term)) : Bool :=
  let P := NatMap.ofList pts
  pts.all fun e =>
    let (ψ, Q, t) := e
    X.inD.find? ψ == some (.phi Q) && !t.hasClz &&
    t.atoms.all (fun a => X.inD.find? a == some (.phi Q) || X.above Q (.var a)) &&
    (phiOf X.inB Q ψ).any fun φ => φ.incoming.all fun ob =>
      let tq := substPhis X Q ob.2 t
      (match ob.1 with
        | .var ψ' => (P.find? ψ').any fun Qt => checkExact (kbOf X.K) tq Qt.2
        | _ => false) ||
      [0, 1, 2, 3].any fun d => checkExact (kbOf X.K) tq (unfold X.inB X.inD X.cs d ob.1)

/-- The certificate of a mode, checked on the input (`gvn` only). -/
def Mode.certOk (X : StepCtx) : Mode → Bool
  | .gvn cls pts => X.clsOk cls && X.ptOk pts
  | _ => true

/-- A `gvn_rewrite` justification of `v ↦ x` by the certificate: `v` and `x` have one
    representative and `x`'s definition dominates `v`'s; or `x` is an inserted phi of a block
    dominating `v`'s whose term `v`'s definition unfolds to. -/
def entryGvn (X : StepCtx) (cls : List (Nat × Operand)) (pts : List (Nat × Nat × Term)) (v : Nat)
    (x : Operand) : Bool :=
  let C := NatMap.ofList cls
  (gTerm C (.var v) == gTerm C x && X.before x v) ||
  match x with
  | .var ψ => ((NatMap.ofList pts).find? ψ).any fun Qt =>
      (X.blockOf v).any (X.T.anc Qt.1 ·) &&
      [1, 2, 3].any fun d => (X.tin d v).any fun tv => checkExact (kbOf X.K) tv Qt.2
  | _ => false

/-- One justification of `v ↦ x`, without chains. -/
def entryDirect (X : StepCtx) (m : Mode) (v : Nat) (x : Operand) : Bool :=
  match m with
  | .exact | .scalar =>
    depths.any fun dd => (X.tin dd.1 v).any fun t => checkExact (kbOf X.K) t (X.tout dd.2 x)
  | .sccp =>
    (match x with
      | .imm _ c => X.cs.find? v == some (c % W) && decide (c < W)
      | _ => false) || X.phiFold v x ||
    depths.any fun dd => (X.tin dd.1 v).any fun t => checkExact (kbOf X.K) t (X.tout dd.2 x)
  | .demand DB =>
    (match x with
      | .var a => dOf DB v &&& M &&& dOf DB a == dOf DB v &&& M
      | _ => true) &&
    depths.any fun dd => (X.tin dd.1 v).any fun t =>
      checkDemand (kbOf X.K) (dOf DB v) t (X.tout dd.2 x)
  | .gvn cls pts => entryGvn X cls pts v x ||
    depths.any fun dd => (X.tin dd.1 v).any fun t => checkExact (kbOf X.K) t (X.tout dd.2 x)

/-- The input operands of `v`'s definition. -/
def StepCtx.inOps (X : StepCtx) (v : Nat) : List Operand :=
  ((defStmt X.inB X.inD v).map (·.inst.args)).getD []

/-- The justification of a σ entry `v ↦ x`: directly, or through a deleted operand `u` of `v`'s
    definition with `v ↦ u` justified and `u ↦ x` in turn, at most `n` links. -/
def entryOk (X : StepCtx) (m : Mode) (dels : List Nat) : Nat → Nat → Operand → Bool
  | 0, v, x => entryDirect X m v x
  | n + 1, v, x => entryDirect X m v x || (X.inOps v).any fun o => match o with
    | .var u => dels.contains u && entryDirect X m v (.var u) && entryOk X m dels n u x
    | _ => false

/-- The replacement may build this instruction: `sccp_fold` builds only `is_zero` in place
    (`BuildIsZero`), `scalar_canonicalize` any pure instruction (`instTerm` asks it pure and not
    `clz`). -/
def Mode.builds : Mode → Inst → Bool
  | .scalar, _ => true
  | _, .isZero _ => true
  | _, _ => false

/-- An in-place replacement of a statement (`sccp_fold`'s `BuildIsZero`, every rewrite of
    `scalar_canonicalize`): the same results, both instructions pure and not `clz`, and a schema
    maps the input's term to the output's: unfolded to the same depth, or the output's a leaf
    and the input's at depth 0 to 3, or the input's unfolded 3 levels down to the output's
    operands (`unfoldStop`) and the output's a leaf. -/
def replaceOk (m : Mode) (X : StepCtx) (s s' : Stmt) : Bool :=
  s.dsts == s'.dsts && m.builds s'.inst &&
    ((depths.any fun dd =>
      match instTerm X.inB X.inD X.cs dd.1 s.inst, instTerm X.outB X.outD X.cs dd.2 s'.inst with
      | some t, some t' => checkExact (kbOf X.K) t t'
      | _, _ => false) ||
    match instTermStop X.inB X.inD X.cs (opVars s'.inst.args) 3 s.inst,
      instTerm X.outB X.outD X.cs 0 s'.inst with
    | some t, some t' => checkExact (kbOf X.K) t t'
    | _, _ => false)

/-- The values σ maps that the paired input lines read. -/
def sigmaKeys (pairs : List (Line × Line)) (σ : NatMap Operand) : List Nat :=
  pairs.flatMap fun LL => (lineOps LL.1).filterMap fun o => match o with
    | .var v => if (σ.find? v).isSome then some v else none
    | _ => none

/-- Strict SSA under a validated dominator tree. -/
def ssaOk (f : Func) : Bool := (domTree f).valid f && ssa f (domTree f)

/-- Every operand of the function is well formed. -/
def opsWf (f : Func) : Bool := f.blocks.all fun b =>
  b.phis.all (·.incoming.all (·.1.wf)) && b.body.all (·.inst.args.all Operand.wf) &&
    b.term.args.all Operand.wf

/-- Whether the mode reads SCCP's constants. -/
def Mode.sccp? : Mode → Bool
  | .sccp => true
  | _ => false

/-- `scalar_canonicalize`'s mode. -/
def Mode.scalar? : Mode → Bool
  | .scalar => true
  | _ => false

/-- Every paired output line is its input line with σ applied, or, for `sccp_fold` and
    `scalar_canonicalize`, a statement replaced in place. -/
def linesOk (m : Mode) (X : StepCtx) (σ : NatMap Operand) (pairs : List (Line × Line)) : Bool :=
  pairs.all fun LL => lineEq (mapLine σ LL.1) LL.2 || match m, LL.1, LL.2 with
    | .sccp, .stmt a, .stmt b | .scalar, .stmt a, .stmt b => replaceOk m X a b
    | _, _, _ => false

/-- Why a step is rejected. -/
inductive Reject where
  | noIds | frame | pairing | sigma | inputSsa | outputSsa | deletion | changed | kbFacts
  | dbFacts | sccpFacts | unread | wrongFacts | notDeleted (v : Nat) | noSchema (v : Nat)
  | fresh | demandRound | gvnCert
  deriving Repr, DecidableEq

/-- The shared check, in a mode: why it rejects, or `none`. -/
def aliasReject (m : Mode) (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Option Reject :=
  match ids with
  | none => some .noIds
  | some is =>
  if !(s.func.name == f.name && decide (s.func.params = f.params) && decide (s.func.rets = f.rets)
      && s.func.machine && opsWf s.func && s.func.wordTyped && s.func.cfgOk &&
      s.func.blocks.all (·.term.wf s.func.rets.length) && distinct is.flatten &&
      distinct s.insts.flatten) then some .frame else
  match pairFunc f is s with
  | none => some .pairing
  | some (pairs, deleted) =>
    let X := StepCtx.of f s F m.sccp?
    match sigmaOf (!m.scalar?) pairs with
    | none => some .sigma
    | some σ =>
      let dels := deleted.flatMap lineDefs
      if !ssaOk f then some .inputSsa
      else if !ssaOk s.func then some .outputSsa
      else if !deleted.all deletable then some .deletion
      else if !linesOk m X σ pairs then some .changed
      else if !(F.knownBits.isEmpty || kbFactsOk X.inB X.inD F) then some .kbFacts
      else if !m.certOk X then some .gvnCert
      else
        let keys := sigmaKeys pairs σ
        match keys.find? (fun v => !dels.contains v) with
        | some v => some (.notDeleted v)
        | none => match keys.find? (fun v => !((σ.find? v).any (entryOk X m dels 3 v))) with
          | some v => some (.noSchema v)
          | none =>
            -- no deleted value is a value of the output (implied by the checks above with the
            -- input's unique definitions; checked so that the proof need not derive it)
            if !dels.all (fun v => (X.outD.find? v).isNone) then some .fresh else none

/-- Demand rounds (`known_bits_simplify` with demanded bits, review C-2): their rewrites keep
    only the demanded bits of a value, and their soundness is not proved
    (`SchemasStepSound.lean`).  The proved checker rejects them; `kbsRejectWith true` is the
    unproved demand checker, which the tests exercise. -/
def demandRounds : Bool := false

def kbsRejectWith (demand : Bool) (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Option Reject :=
  if !F.unread.isEmpty then some .unread
  else if F.consts.isSome || !F.deadEdges.isEmpty || F.gvn.isSome then some .wrongFacts
  else match F.demanded with
    | none => aliasReject .exact f ids s F
    | some ds =>
      if !demand then some .demandRound
      else if !dbFactsOk f ds then some .dbFacts else aliasReject (.demand (dbMap ds)) f ids s F

def kbsReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option Reject :=
  kbsRejectWith demandRounds f ids s F

def sccpReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option Reject :=
  if !F.unread.isEmpty then some .unread
  else if F.demanded.isSome || F.gvn.isSome then some .wrongFacts
  else if !sccpFactsOk f (.ofListBy (·.id) f.blocks) (defsOf f) (kbMap F) F then some .sccpFacts
  else aliasReject .sccp f ids s F

/-- A `scalar_canonicalize` round exports no facts (`StepLog::step(…, None)`). -/
def scalarReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option Reject :=
  if !F.unread.isEmpty then some .unread
  else if !(F.knownBits.isEmpty && F.demanded.isNone && F.consts.isNone && F.deadEdges.isEmpty &&
    F.gvn.isNone) then some .wrongFacts
  else aliasReject .scalar f ids s F

/-- `known_bits_simplify` (design §4.5, review C-2): a round of exact rewrites, or, with
    demanded bits, a round of demand rewrites only.  Range facts are not read: a step that has
    them is rejected (I6 is not done). -/
def checkKnownBitsSimplify (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Bool :=
  (kbsReject f ids s F).isNone

/-- `sccp_fold` (design §4.7, review H-2, H-4). -/
def checkSccpFold (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Bool :=
  (sccpReject f ids s F).isNone

/-- `scalar_canonicalize` (design §4.5): one round, its statements replaced in place, each by a
    schema on the two unfolded terms (ruling R-11.1), and dead pure statements deleted
    (`prune_dead_pure_insts`). -/
def checkScalarCanonicalize (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Bool :=
  (scalarReject f ids s F).isNone

def diagnoseScalarCanonicalize (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Option String :=
  (scalarReject f ids s F).map fun r => s!"{repr r}"

/-- The first failing check, by name (for measurement). -/
def diagnoseKnownBitsSimplify (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Option String :=
  (kbsReject f ids s F).map fun r => s!"{repr r}"

def diagnoseSccpFold (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option String :=
  (sccpReject f ids s F).map fun r => s!"{repr r}"

end Fe.Sonatina.Steps.Schemas
