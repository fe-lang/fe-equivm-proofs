import Fe.Sonatina.Stage3.Place.Lower
import Fe.Sonatina.Plan

/-!
# The static analyses of rule set S (design §5.2)

Each analysis is computed by rounds with a bound (untrusted) and then checked as a
post-fixpoint (the standing ruling: what a checker computes with fuel is a certificate):

- **Liveness** of source values (`Live`, `liveOk`): per block, the values live at the start of
  its body (after its phis); the sets before each statement follow backwards (`livePoints`).
  The certificate: each block's set contains what its body and terminator need, given its
  successors' sets, and the entry's set holds only parameters.  The simulation relates only
  live values; with the entry condition every use is defined in H, with no dominance argument.
- **Origins** (S3, `Orig`, `origOk`): the `alloca` and fixed-buffer sites, and the marker
  `param`, a value may carry a pointer into, through exactly H's origin-keeping operations
  (PLAN §3, with `black_box`, H's I7).  Encoded as naturals: `0` is `param`, `x + 1` is site
  `vx`.
- **Footprints** (`FP`, `fpOk`): byte ranges each function's frame, and its callees', may
  write: its `alloca` ranges and its callees' footprints, as list members.
- **Derived values** (S8, `derivedOk`): the values that may carry an allocation's address.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The values an operand list reads. -/
def varsOf (os : List Operand) : List Nat := os.filterMap fun
  | .var x => some x
  | .imm .. => none

def _root_.Fe.Sonatina.H.HStmt.uses (s : HStmt) : List Nat := varsOf s.inst.args
def _root_.Fe.Sonatina.H.HStmt.defs (s : HStmt) : List Nat := s.dsts.map (·.1)
def _root_.Fe.Sonatina.H.HTerm.uses (t : HTerm) : List Nat := varsOf t.skel.args

/-- The operands block `c`'s phis take on the edge from `pred`. -/
def phiOps (c : HBlock) (pred : Nat) : List Operand :=
  c.phis.filterMap fun p => (p.incoming.find? (·.2 == pred)).map (·.1)

/-! ## Liveness -/

/-- Block id ↦ the values live at the start of its body. -/
abbrev Live := NatMap (List Nat)

def liveGet (L : Live) (b : Nat) : List Nat := (L.find? b).getD []

/-- The values live at the end of block `b`: at each successor's start, other than its phis,
    and the operands its phis take from `b`. -/
def liveOut (f : HFunc) (L : Live) (b : HBlock) : List Nat :=
  normSet (b.term.succs.flatMap fun c => match f.block? c with
    | some cb => (liveGet L c).filter (fun v => !cb.phis.any (·.dst == v)) ++ varsOf (phiOps cb b.id)
    | none => [])

/-- The values live before a statement, from those live after it. -/
def stepBack (s : HStmt) (after : List Nat) : List Nat :=
  normSet (s.uses ++ after.filter fun v => !s.defs.contains v)

/-- The values live before each statement of `b` and, last, before its terminator. -/
def livePoints (f : HFunc) (L : Live) (b : HBlock) : List (List Nat) :=
  b.body.foldr (fun s acc => stepBack s (acc.headD []) :: acc)
    [normSet (b.term.uses ++ liveOut f L b)]

def blockIn (f : HFunc) (L : Live) (b : HBlock) : List Nat := (livePoints f L b).headD []

/-- Rounds of liveness from nothing, last block first, until one changes nothing. -/
def liveIter (f : HFunc) : Nat → Live → Live
  | 0, L => L
  | n + 1, L =>
    let (L', changed) := f.blocks.foldr (fun b (L, ch) =>
      let s := blockIn f L b
      (L.insert b.id s, ch || s != liveGet L b.id)) (L, false)
    if changed then liveIter f n L' else L'

def liveOf (f : HFunc) : Live := liveIter f (f.blocks.length + 2) .empty

/-- The liveness certificate: every block's set holds what its body and terminator read and
    what its successors need; the entry's set holds only parameters. -/
def liveOk (f : HFunc) (L : Live) : Bool :=
  f.blocks.all (fun b => (blockIn f L b).all (liveGet L b.id).contains) &&
    match f.blocks.head? with
    | some e => (liveGet L e.id).all fun v => f.params.any (·.1 == v)
    | none => false

/-! ## Origins (S3) -/

/-- Source value ↦ its origins (`0` the caller's frame, `x + 1` site `vx`). -/
abbrev Orig := NatMap (List Nat)

def origOf (O : Orig) : Operand → List Nat
  | .var y => (O.find? y).getD []
  | .imm .. => []

/-- The fixed-buffer sites of a function. -/
def FuncRec.isFixed (fr : FuncRec) (x : Nat) : Bool :=
  fr.mallocs.any fun (y, m) => y == x && m matches .fixed ..

/-- The origins a statement's result may carry, from its operands': exactly H's origin-keeping
    rules (`ptrBin`, `castVal`, `gep`, `black_box`, `select`), over-approximated by operand
    (an `or`, `xor`, `and`, `add` of anything takes the union).  A load or a call gives none: no
    memory byte holds a fragment of an `alloca` or a fixed buffer, and no function returns
    one. -/
def stmtOrig (fr : FuncRec) (O : Orig) (s : HStmt) : List Nat :=
  let x := (s.dsts.head?.map (·.1)).getD 0
  match s.inst with
  | .base (.alloca _) => [x + 1]
  | .base (.malloc _) => if fr.isFixed x then [x + 1] else []
  | .gep _ b _ => origOf O b
  | .base (.bin op a b) => match op with
    | .add | .or | .xor | .and => normSet (origOf O a ++ origOf O b)
    | .sub => origOf O a
    | _ => []
  | .base (.cast op a _) => match op with
    | .ptrToInt | .intToPtr | .bitcast => origOf O a
    | _ => []
  | .base (.blackBox a) => origOf O a
  | .base (.select _ a b) => normSet (origOf O a ++ origOf O b)
  | _ => []

/-- Which parameters of each function may receive an `alloca` or fixed-buffer pointer. -/
abbrev Flags := List (String × List Nat)

def flagged (F : Flags) (g : String) (i : Nat) : Bool := ((F.lookup g).getD []).contains i

/-- One round of origins in `f`: parameters, phis and statements, in block order. -/
def origRound (fr : FuncRec) (F : Flags) (f : HFunc) (O : Orig) : Orig :=
  let O := f.params.zipIdx.foldl (fun O (p, i) =>
    if flagged F f.name i then O.insert p.1 [0] else O) O
  f.blocks.foldl (fun O b =>
    let O := b.phis.foldl (fun O p =>
      O.insert p.dst (normSet (origOf O (.var p.dst) ++ p.incoming.flatMap (origOf O ·.1)))) O
    b.body.foldl (fun O s => match s.dsts with
      | [(x, _)] => O.insert x (normSet (origOf O (.var x) ++ stmtOrig fr O s))
      | _ => O) O) O

/-- The sets of every definition, for detecting that a round changed nothing. -/
def origKey (f : HFunc) (O : Orig) : List (List Nat) :=
  (f.params.map (·.1) ++ f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap HStmt.defs).map
    fun x => origOf O (.var x)

def origIter (fr : FuncRec) (F : Flags) (f : HFunc) : Nat → Orig → Orig
  | 0, O => O
  | n + 1, O =>
    let O' := origRound fr F f O
    if origKey f O' == origKey f O then O else origIter fr F f n O'

/-- The certificate of origins in `f`: each definition's set holds what its rule gives. -/
def origOk (fr : FuncRec) (F : Flags) (f : HFunc) (O : Orig) : Bool :=
  f.params.zipIdx.all (fun (p, i) => !flagged F f.name i || (origOf O (.var p.1)).contains 0) &&
  f.blocks.all fun b =>
    b.phis.all (fun p => p.incoming.all fun (o, _) => (origOf O o).all (origOf O (.var p.dst)).contains) &&
    b.body.all fun s => match s.dsts with
      | [(x, _)] => (stmtOrig fr O s).all (origOf O (.var x)).contains
      | _ => stmtOrig fr O s == []

/-- The flags the calls of `f` demand: a parameter receives an argument with origins. -/
def callFlags (f : HFunc) (O : Orig) : Flags :=
  f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst with
    | .base (.call g args) =>
      some (g, (args.zipIdx.filter fun (a, _) => !(origOf O a).isEmpty).map (·.2))
    | _ => none

/-- The flags are a post-fixpoint: every argument with origins is passed to a flagged
    parameter. -/
def flagsOk (F : Flags) (f : HFunc) (O : Orig) : Bool :=
  (callFlags f O).all fun (g, is) => is.all (flagged F g)

/-! ## Footprints -/

/-- A half-open byte range. -/
abbrev Range := Nat × Nat

/-- Two ranges are disjoint; an empty one is disjoint from every range. -/
def disjoint (r s : Range) : Bool := r.1 == r.2 || s.1 == s.2 || r.2 ≤ s.1 || s.2 ≤ r.1

/-- The byte range of `alloca` site `x` of `f`: its record word's address and its type's size. -/
def allocaRange (prec : Record) (fr : FuncRec) (structs : List (String × List Ty)) (f : HFunc)
    (x : Nat) : Option Range := do
  let loc ← fr.allocas.lookup x
  let s ← f.blocks.findSome? fun b => b.body.find? fun s => s.defs == [x]
  let .base (.alloca t) := s.inst | none
  let n ← sizeOf structs sizeFuel t
  let lo := prec.wordAddr loc.word
  some (lo, lo + n)

/-- The `alloca` sites of `f`. -/
def allocaSites (f : HFunc) : List Nat :=
  f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst, s.dsts with
    | .base (.alloca _), [(x, _)] => some x
    | _, _ => none

/-- The callees of `f`. -/
def callees (f : HFunc) : List String :=
  (f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst with
    | .base (.call g _) => some g
    | _ => none).eraseDups

/-- Function ↦ the ranges its frame and its callees' may write. -/
abbrev FP := List (String × List Range)

def fpOf (P : FP) (g : String) : List Range := (P.lookup g).getD []

/-- The machine ranges of a function's own `alloca`s (`none` for one without a range). -/
def ownRanges (prec : Record) (structs : List (String × List Ty)) (frs : String → FuncRec)
    (f : HFunc) : List Range :=
  (allocaSites f).filterMap (allocaRange prec (frs f.name) structs f)

/-- Rounds of footprints, each the own ranges and the callees' footprints. -/
def fpIter (own : String → List Range) (fs : List HFunc) : Nat → FP → FP
  | 0, P => P
  | n + 1, P =>
    let P' := fs.map fun f => (f.name, (own f.name ++ (callees f).flatMap (fpOf P)).eraseDups)
    if P'.map (·.2.length) == P.map (·.2.length) then P' else fpIter own fs n P'

/-- The footprint certificate: own ranges and callees' footprints are members. -/
def fpOk (own : String → List Range) (fs : List HFunc) (P : FP) : Bool :=
  fs.all fun f => (own f.name).all (fpOf P f.name).contains &&
    (callees f).all fun g => (fpOf P g).all (fpOf P f.name).contains

/-! ## Derived values (S8) -/

/-- The values of each function that may carry an allocation's address (`D`), the parameters
    that receive one, and whether a function returns one. -/
structure Derived where
  vals : List (String × List Nat)
  params : List (String × List Nat)
  rets : List String

def Derived.has (D : Derived) (f : String) (x : Nat) : Bool := ((D.vals.lookup f).getD []).contains x

def Derived.op (D : Derived) (f : String) : Operand → Bool
  | .var x => D.has f x
  | .imm .. => false

/-- Whether a statement's result is derived (§5.2 S8's closure, with `black_box`): the
    allocations; a `gep` of a derived base; `add` of a derived operand; `sub` of a derived left
    operand; `ptr_to_int`/`bitcast` to a word, `int_to_ptr`, of a derived operand; `black_box`,
    `select` arms; calls of a function that returns one. -/
def stmtDerived (D : Derived) (f : String) (s : HStmt) : Bool :=
  let d := D.op f
  match s.inst with
  | .base (.alloca _) | .base (.malloc _) => true
  | .gep _ b _ => d b
  | .base (.bin .add a b) => d a || d b
  | .base (.bin .sub a _) => d a
  | .base (.cast op a t) => match op with
    | .ptrToInt | .bitcast => isWord t && d a
    | .intToPtr => d a
    | _ => false
  | .base (.blackBox a) => d a
  | .base (.select _ a b) => d a || d b
  | .base (.call g _) => D.rets.contains g
  | _ => false

/-- One round of the derived closure over the section. -/
def derivedRound (fs : List HFunc) (D : Derived) : Derived :=
  let vals := fs.map fun f =>
    let ps := f.params.zipIdx.filterMap fun (p, i) =>
      if ((D.params.lookup f.name).getD []).contains i then some p.1 else none
    let xs := f.blocks.flatMap fun b =>
      (b.phis.filterMap fun p => if p.incoming.any (D.op f.name ·.1) then some p.dst else none) ++
      b.body.flatMap fun s => if stmtDerived D f.name s then s.defs else []
    (f.name, normSet (ps ++ xs ++ ((D.vals.lookup f.name).getD [])))
  let D' : Derived := { D with vals }
  let params := fs.map fun g => (g.name, normSet (((D.params.lookup g.name).getD []) ++
    fs.flatMap fun f => f.blocks.flatMap fun b => b.body.flatMap fun s => match s.inst with
      | .base (.call g' args) => if g' == g.name then
          (args.zipIdx.filter fun (a, _) => D'.op f.name a).map (·.2) else []
      | _ => []))
  let rets := (D.rets ++ (fs.filter fun f => f.blocks.any fun b => match b.term with
    | .base (.ret vs) => vs.any (D'.op f.name)
    | _ => false).map (·.name)).eraseDups
  { vals, params, rets }

def Derived.size (D : Derived) : Nat :=
  (D.vals.map (·.2.length)).sum + (D.params.map (·.2.length)).sum + D.rets.length

def derivedIter (fs : List HFunc) : Nat → Derived → Derived
  | 0, D => D
  | n + 1, D =>
    let D' := derivedRound fs D
    if D'.size == D.size then D' else derivedIter fs n D'

/-- The derived certificate: closed under its rules. -/
def derivedOk (fs : List HFunc) (D : Derived) : Bool :=
  fs.all fun f =>
    f.params.zipIdx.all (fun (p, i) => !((D.params.lookup f.name).getD []).contains i || D.has f.name p.1) &&
    f.blocks.all fun b =>
      b.phis.all (fun p => !p.incoming.any (D.op f.name ·.1) || D.has f.name p.dst) &&
      b.body.all (fun s => !stmtDerived D f.name s || s.defs.all (D.has f.name)) &&
      b.body.all (fun s => match s.inst with
        | .base (.call g args) => args.zipIdx.all fun (a, i) =>
            !D.op f.name a || ((D.params.lookup g).getD []).contains i
        | _ => true) &&
      match b.term with
      | .base (.ret vs) => !vs.any (D.op f.name) || D.rets.contains f.name
      | _ => true

/-- An operand that is an immediate zero: a length that makes an access touch nothing. -/
def isZeroImm : Operand → Bool
  | .imm _ 0 => true
  | _ => false

/-- The operand positions of an EVM operation that are memory addresses, with each one's
    length operand. -/
def _root_.Fe.Sonatina.EvmOp.addrPos : EvmOp → List (Nat × Nat)
  | .mload => [(0, 0)] | .mstore => [(0, 0)] | .mstore8 => [(0, 0)]
  | .keccak256 => [(0, 1)] | .mcopy => [(0, 2), (1, 2)] | .log _ => [(0, 1)]
  | .calldataCopy | .codeCopy | .returnDataCopy => [(0, 2)] | .extCodeCopy => [(1, 3)]
  | .create => [(1, 2)] | .create2 => [(1, 2)]
  | .call | .callCode => [(3, 4), (5, 6)] | .staticCall | .delegateCall => [(2, 3), (4, 5)]
  | _ => []

/-- The operand positions of a statement where a derived value is not observed (§5.2 S8);
    `mload`/`mstore` lengths are 32, never zero. -/
def nonObserving (D : Derived) (f : String) (s : HStmt) : List Nat :=
  let d := D.op f
  match s.inst with
  | .gep _ _ idxs => if idxs.any d then [] else [0]
  | .base (.bin .add a b) => if d a && d b then [] else [0, 1]
  | .base (.bin .sub _ b) => if d b then [] else [0]
  | .base (.cast op _ t) => match op with
    | .ptrToInt | .bitcast => if isWord t then [0] else []
    | .intToPtr => [0]
    | _ => []
  | .base (.blackBox _) => [0]
  | .base (.select _ _ _) => [1, 2]
  | .base (.mload _ _) => [0]
  | .base (.mstore _ _ _) => [0]
  | .base (.memzero _ l) => if isZeroImm l then [] else [0]
  | .mloadBytes _ l => if isZeroImm l then [] else [0]
  | .base (.evm op args) => (op.addrPos.filter fun (_, li) =>
      !((args[li]?.map isZeroImm).getD false)).map (·.1)
  | .base (.call _ args) => List.range args.length
  | _ => []

/-- No derived value is observed in `f` (S8's check, used when a block is at address 0). -/
def notObserved (D : Derived) (f : HFunc) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun s => let ok := nonObserving D f.name s
      s.inst.args.zipIdx.all fun (a, i) => !D.op f.name a || ok.contains i) &&
    match b.term with
    | .base (.ret _) => true
    | .base (.evmReturn a l) | .base (.evmRevert a l) =>
      !D.op f.name l && (!D.op f.name a || !isZeroImm l)
    | t => !t.skel.args.any (D.op f.name)

end Fe.Sonatina.Stage3.Place
