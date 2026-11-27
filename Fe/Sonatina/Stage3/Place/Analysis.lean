import Fe.Sonatina.Stage3.Place.Lower


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
  nset (b.term.succs.flatMap fun c => match f.block? c with
    | some cb => (liveGet L c).filter (fun v => !cb.phis.any (·.dst == v)) ++ varsOf (phiOps cb b.id)
    | none => [])

/-- The values live before a statement, from those live after it. -/
def stepBack (s : HStmt) (after : List Nat) : List Nat :=
  nset (s.uses ++ after.filter fun v => !s.defs.contains v)

/-- The values live before each statement of `b` and, last, before its terminator. -/
def livePoints (f : HFunc) (L : Live) (b : HBlock) : List (List Nat) :=
  b.body.foldr (fun s acc => stepBack s (acc.headD []) :: acc)
    [nset (b.term.uses ++ liveOut f L b)]

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
    | .add | .or | .xor | .and => nset (origOf O a ++ origOf O b)
    | .sub => origOf O a
    | _ => []
  | .base (.cast op a _) => match op with
    | .ptrToInt | .intToPtr | .bitcast => origOf O a
    | _ => []
  | .base (.blackBox a) => origOf O a
  | .base (.select _ a b) => nset (origOf O a ++ origOf O b)
  | _ => []

/-- The `call` statements of `f`, in block and statement order, each with its callee's place
    among the section's functions (the hints `fr.calls`, which the translation check verifies)
    and its arguments. -/
def callSites (fr : FuncRec) (f : HFunc) : List (Nat × List Operand) :=
  f.blocks.zipIdx.flatMap fun (b, k) =>
    ((fr.calls[k]?).getD []).zip (b.body.filterMap fun s => match s.inst with
      | .base (.call _ args) => some args
      | _ => none)

/-- The callees of `f`, by place. -/
def callees (fr : FuncRec) (f : HFunc) : List Nat := ((callSites fr f).map (·.1)).dedupB

/-- Function place ↦ the parameters that may receive an `alloca` or fixed-buffer pointer. -/
abbrev Flags := NatMap (List Nat)

def flagged (F : Flags) (g i : Nat) : Bool := ((F.find? g).getD []).contains i

/-- One round of origins in `f` (place `k`): parameters, phis and statements, in block order. -/
def origRound (fr : FuncRec) (F : Flags) (k : Nat) (f : HFunc) (O : Orig) : Orig :=
  let O := f.params.zipIdx.foldl (fun O (p, i) =>
    if flagged F k i then O.insert p.1 [0] else O) O
  f.blocks.foldl (fun O b =>
    let O := b.phis.foldl (fun O p =>
      O.insert p.dst (nset (origOf O (.var p.dst) ++ p.incoming.flatMap (origOf O ·.1)))) O
    b.body.foldl (fun O s => match s.dsts with
      | [(x, _)] => O.insert x (nset (origOf O (.var x) ++ stmtOrig fr O s))
      | _ => O) O) O

/-- The sets of every definition, for detecting that a round changed nothing. -/
def origKey (f : HFunc) (O : Orig) : List (List Nat) :=
  (f.params.map (·.1) ++ f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap HStmt.defs).map
    fun x => origOf O (.var x)

def origIter (fr : FuncRec) (F : Flags) (k : Nat) (f : HFunc) : Nat → Orig → Orig
  | 0, O => O
  | n + 1, O =>
    let O' := origRound fr F k f O
    if origKey f O' == origKey f O then O else origIter fr F k f n O'

/-- The certificate of origins in `f` (place `k`): each definition's set holds what its rule
    gives. -/
def origOk (fr : FuncRec) (F : Flags) (k : Nat) (f : HFunc) (O : Orig) : Bool :=
  f.params.zipIdx.all (fun (p, i) => !flagged F k i || (origOf O (.var p.1)).contains 0) &&
  f.blocks.all fun b =>
    b.phis.all (fun p => p.incoming.all fun (o, _) => (origOf O o).all (origOf O (.var p.dst)).contains) &&
    b.body.all fun s => match s.dsts with
      | [(x, _)] => (stmtOrig fr O s).all (origOf O (.var x)).contains
      | _ => stmtOrig fr O s == []

/-- The flags the calls of `f` demand: a parameter receives an argument with origins. -/
def callFlags (fr : FuncRec) (f : HFunc) (O : Orig) : List (Nat × List Nat) :=
  (callSites fr f).map fun (g, args) =>
    (g, (args.zipIdx.filter fun (a, _) => !(origOf O a).isEmpty).map (·.2))

/-- The flags are a post-fixpoint: every argument with origins is passed to a flagged
    parameter. -/
def flagsOk (F : Flags) (fr : FuncRec) (f : HFunc) (O : Orig) : Bool :=
  (callFlags fr f O).all fun (g, is) => is.all (flagged F g)

/-! ## Footprints -/

/-- A half-open byte range. -/
abbrev Range := Nat × Nat

/-- Two ranges are disjoint; an empty one is disjoint from every range. -/
def disjoint (r s : Range) : Bool := r.1 == r.2 || s.1 == s.2 || r.2 ≤ s.1 || s.2 ≤ r.1

/-- The byte range of each `alloca` site of `f` with a record location: its word's address and
    its type's size. -/
def rangesOf (prec : Record) (fr : FuncRec) (structs : List (String × List Ty)) (f : HFunc) :
    NatMap Range :=
  f.blocks.foldl (fun R b => b.body.foldl (fun R s => match s.inst, s.dsts with
    | .base (.alloca t), [(x, _)] => match fr.allocas.lookup x, sizeOf structs sizeFuel t with
      | some loc, some n => R.insert x (prec.wordAddr loc.word, prec.wordAddr loc.word + n)
      | _, _ => R
    | _, _ => R) R) .empty

/-- The `alloca` sites of `f`. -/
def allocaSites (f : HFunc) : List Nat :=
  f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst, s.dsts with
    | .base (.alloca _), [(x, _)] => some x
    | _, _ => none

/-- The ranges of a function's own `alloca`s. -/
def ownRanges (R : NatMap Range) (f : HFunc) : List Range :=
  (allocaSites f).filterMap R.find?

/-- Function place ↦ the ranges its frame and its callees' may write. -/
abbrev FP := NatMap (List Range)

def fpOf (P : FP) (g : Nat) : List Range := (P.find? g).getD []

/-- Rounds of footprints, each a function's own ranges and its callees' footprints.  `fs` lists
    each function with its place, own ranges and callees. -/
def fpIter (fs : List (Nat × List Range × List Nat)) : Nat → FP → FP
  | 0, P => P
  | n + 1, P =>
    let (P', changed) := fs.foldl (fun (P', ch) (k, own, cs) =>
      let r := (own ++ cs.flatMap (fpOf P)).dedupB
      (P'.insert k r, ch || r.length != (fpOf P k).length)) (P, false)
    if changed then fpIter fs n P' else P'

/-- The footprint certificate: own ranges and callees' footprints are members. -/
def fpOk (fs : List (Nat × List Range × List Nat)) (P : FP) : Bool :=
  fs.all fun (k, own, cs) => own.all (fpOf P k).contains &&
    cs.all fun g => (fpOf P g).all (fpOf P k).contains

/-! ## Derived values (S8) -/

/-- The values of each function (by place) that may carry an allocation's address (`D`), the
    parameters that receive one, and the functions that return one. -/
structure Derived where
  vals : NatMap (List Nat)
  params : NatMap (List Nat)
  rets : List Nat

def Derived.has (D : Derived) (k x : Nat) : Bool := ((D.vals.find? k).getD []).contains x

def Derived.op (D : Derived) (k : Nat) : Operand → Bool
  | .var x => D.has k x
  | .imm .. => false

def Derived.param (D : Derived) (g i : Nat) : Bool := ((D.params.find? g).getD []).contains i

/-- Whether a statement's result is derived (§5.2 S8's closure, with `black_box`): the
    allocations; a `gep` of a derived base; `add` of a derived operand; `sub` of a derived left
    operand; `ptr_to_int`/`bitcast` to a word, `int_to_ptr`, of a derived operand; `black_box`,
    `select` arms; a call of a function that returns one (`callee?`, its place). -/
def stmtDerived (D : Derived) (k : Nat) (s : HStmt) (callee? : Option Nat) : Bool :=
  let d := D.op k
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
  | .base (.call _ _) => callee?.any D.rets.contains
  | _ => false

/-- Each statement of each block of `f` with the place of its callee, if it is a call. -/
def withCallees (fr : FuncRec) (f : HFunc) : List (List (HStmt × Option Nat)) :=
  f.blocks.zipIdx.map fun (b, k) =>
    let rec go : List HStmt → List Nat → List (HStmt × Option Nat)
      | [], _ => []
      | s :: rest, cs =>
        if s.inst matches .base (.call ..) then (s, cs.head?) :: go rest cs.tail
        else (s, none) :: go rest cs
    go b.body ((fr.calls[k]?).getD [])

/-- One round of the derived closure over the section; `fs` lists each function with its place
    and `withCallees`. -/
def derivedRound (fs : List (Nat × HFunc × List (List (HStmt × Option Nat)))) (D : Derived) : Derived :=
  let vals := fs.foldl (fun V (k, f, bss) =>
    let ps := f.params.zipIdx.filterMap fun (p, i) => if D.param k i then some p.1 else none
    let xs := (f.blocks.zip bss).flatMap fun (b, ss) =>
      (b.phis.filterMap fun p => if p.incoming.any (D.op k ·.1) then some p.dst else none) ++
      ss.flatMap fun (s, c) => if stmtDerived D k s c then s.defs else []
    V.insert k (nset (ps ++ xs ++ ((D.vals.find? k).getD [])))) D.vals
  let D' : Derived := { D with vals }
  let params := fs.foldl (fun P (k, _, bss) => bss.foldl (fun P ss => ss.foldl (fun P (s, c) =>
    match s.inst, c with
    | .base (.call _ args), some g =>
      P.insert g (nset (((P.find? g).getD []) ++ (args.zipIdx.filter fun (a, _) => D'.op k a).map (·.2)))
    | _, _ => P) P) P) D.params
  let rets := (D.rets ++ (fs.filter fun (k, f, _) => f.blocks.any fun b => match b.term with
    | .base (.ret vs) => vs.any (D'.op k)
    | _ => false).map (·.1)).dedupB
  { vals, params, rets }

def Derived.size (D : Derived) (ks : List Nat) : Nat :=
  (ks.map fun k => ((D.vals.find? k).getD []).length + ((D.params.find? k).getD []).length).sum +
    D.rets.length

def derivedIter (fs : List (Nat × HFunc × List (List (HStmt × Option Nat)))) : Nat → Derived → Derived
  | 0, D => D
  | n + 1, D =>
    let D' := derivedRound fs D
    let ks := fs.map (·.1)
    if D'.size ks == D.size ks then D' else derivedIter fs n D'

/-- The derived certificate: closed under its rules. -/
def derivedOk (fs : List (Nat × HFunc × List (List (HStmt × Option Nat)))) (D : Derived) : Bool :=
  fs.all fun (k, f, bss) =>
    f.params.zipIdx.all (fun (p, i) => !D.param k i || D.has k p.1) &&
    (f.blocks.zip bss).all fun (b, ss) =>
      b.phis.all (fun p => !p.incoming.any (D.op k ·.1) || D.has k p.dst) &&
      ss.all (fun (s, c) => (!stmtDerived D k s c || s.defs.all (D.has k)) &&
        match s.inst, c with
        | .base (.call _ args), some g => args.zipIdx.all fun (a, i) => !D.op k a || D.param g i
        | _, _ => true) &&
      match b.term with
      | .base (.ret vs) => !vs.any (D.op k) || D.rets.contains k
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
def nonObserving (D : Derived) (k : Nat) (s : HStmt) : List Nat :=
  let d := D.op k
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

/-- No derived value is observed in `f`, of place `k` (S8's check, used when a block is at address 0). -/
def notObserved (D : Derived) (k : Nat) (f : HFunc) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun s => let ok := nonObserving D k s
      s.inst.args.zipIdx.all fun (a, i) => !D.op k a || ok.contains i) &&
    match b.term with
    | .base (.ret _) => true
    | .base (.evmReturn a l) | .base (.evmRevert a l) =>
      !D.op k l && (!D.op k a || !isZeroImm l)
    | t => !t.skel.args.any (D.op k)

end Fe.Sonatina.Stage3.Place
