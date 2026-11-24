import Fe.Sonatina.Steps.EdgeSplit
import Fe.Sonatina.Steps.Summary

/-!
# `cfg_cleanup` (design §4.3, review C-4, M-4)

The input's blocks reachable from the entry once paths are cut at calls to functions the pass's
table claims do not return (`liveSet`) survive; the others may be deleted.  Each output block is
a merge chain of surviving input blocks, from the input block of its id (`chainFrom`,
`linksOk`): a link's terminator is a `jump`, or a `br` or `br_table` whose slots all lead to the
next block through tunnel blocks (`walk`); the next block is no output block, and its surviving
predecessors are the ends of those paths.  Tunnel blocks have no statements, end in a `jump`,
survive, and are no output blocks; the input binds their phis on the way.

The output block holds the chain's statements in order, each operand rewritten by `σ`
(`chainBody`, `CCtx.hat`), the phis of the chain's head that it keeps, and a terminator that
corresponds to the last block's slot by slot (`termRel`), each slot reaching its output target
through tunnel blocks, with the phi operands at the target composed through the tunnel blocks'
phis (`slotOk`, `arrive`).  A block cut after a claimed-noreturn call ends in `unreachable`
after the call.  The entry keeps its id.

`σ` maps the trivial phis the output deletes to their values: a phi `v` of a surviving block `B`
whose operands from surviving, uncut predecessors are, through `σ`, `v` itself or one operand
`x`, that is an immediate or a value defined strictly above `B` in the dominator tree.  Chains
(`v₁ ↦ v₂ ↦ x`) are resolved by the inference (`sigmaOf`), and only its result is checked
(`sigOk`).  Every phi of a surviving block that the output does not keep is no value of the
output (`phisDefOk`).

The instruction ids (`blockIdsOk`): each output phi has its input phi's id, the output body has
the chain's body ids in order, and the terminator keeps its id, but for an `unreachable` after a
noreturn call, which is new unless the input block already ended `call; unreachable`.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## Operand maps -/

def _root_.Fe.Sonatina.Inst.mapOps (g : Operand → Operand) : Inst → Inst
  | .bin op a b => .bin op (g a) (g b)
  | .cmp op a b => .cmp op (g a) (g b)
  | .isZero a => .isZero (g a)
  | .not a => .not (g a)
  | .neg a => .neg (g a)
  | .clz a => .clz (g a)
  | .ctz a => .ctz (g a)
  | .ovf op a b => .ovf op (g a) (g b)
  | .cast op a ty => .cast op (g a) ty
  | .select c a b => .select (g c) (g a) (g b)
  | .evm op args => .evm op (args.map g)
  | .mload a ty => .mload (g a) ty
  | .mstore a v ty => .mstore (g a) (g v) ty
  | .memzero d l => .memzero (g d) (g l)
  | .malloc s => .malloc (g s)
  | .alloca ty => .alloca ty
  | .symAddr s => .symAddr s
  | .symSize s => .symSize s
  | .insertValue a i v => .insertValue (g a) (g i) (g v)
  | .extractValue a i => .extractValue (g a) (g i)
  | .keccakWords ws => .keccakWords (ws.map g)
  | .call f args => .call f (args.map g)

def _root_.Fe.Sonatina.Stmt.mapOps (g : Operand → Operand) (s : Stmt) : Stmt :=
  ⟨s.dsts, s.inst.mapOps g⟩

def _root_.Fe.Sonatina.Term.mapOps (g : Operand → Operand) : Term → Term
  | .br c nz z => .br (g c) nz z
  | .brTable s d cs => .brTable (g s) d (cs.map fun c => (g c.1, c.2))
  | .ret vs => .ret (vs.map g)
  | .evmReturn a l => .evmReturn (g a) (g l)
  | .evmRevert a l => .evmRevert (g a) (g l)
  | t => t

/-- A phi's first operand from block `p`, the one `enter` takes. -/
def inc (φ : Phi) (p : Nat) : Option Operand := (φ.incoming.find? (·.2 == p)).map (·.1)

/-! ## The check -/

/-- The phi's operands from surviving predecessors (in `L`) that no call cuts. -/
def liveOpsOf (O : Option (List Summary)) (B : NatMap Block) (L : NatMap Unit) (φ : Phi) :
    List Operand :=
  (φ.incoming.filter fun p => (L.find? p.2).isSome && !(B.find? p.2).any (cut O)).map (·.1)

/-- The phis of surviving blocks that the output does not define: the candidates for `σ`. -/
def candsOf (L : NatMap Unit) (OD : NatMap Def) (f : Func) : List (Block × Phi) :=
  f.blocks.flatMap fun b => if (L.find? b.id).isSome then
    (b.phis.filter fun φ => (OD.find? φ.dst).isNone).map (b, ·) else []

/-- Follow `m` from an operand, at most `n` times. -/
def resolve (m : NatMap Operand) : Nat → Operand → Operand
  | 0, o => o
  | n + 1, .var u => match m.find? u with
    | some o => resolve m n o
    | none => .var u
  | _ + 1, o => o

/-- One round of the inference: a candidate whose operands, resolved, are itself or one other
    operand maps to it. -/
def inferRound (ops : Phi → List Operand) (n : Nat) (cs : List (Block × Phi))
    (m : NatMap Operand) : NatMap Operand :=
  cs.foldl (fun m bφ =>
    if (m.find? bφ.2.dst).isSome then m else
    match (((ops bφ.2).map (resolve m n)).filter (· != .var bφ.2.dst)).eraseDups with
    | [u] => m.insert bφ.2.dst u
    | _ => m) m

def inferRounds (ops : Phi → List Operand) (n : Nat) (cs : List (Block × Phi)) :
    Nat → NatMap Operand → NatMap Operand
  | 0, m => m
  | k + 1, m => inferRounds ops n cs k (inferRound ops n cs m)

/-- The inferred `σ`, resolved: each candidate that the inference maps, to the end of its
    chain. -/
def sigmaOf (ops : Phi → List Operand) (n : Nat) (cs : List (Block × Phi)) : NatMap Operand :=
  let m := inferRounds ops n cs (cs.length + 1) .empty
  .ofList (cs.filterMap fun bφ => match resolve m n (.var bφ.2.dst) with
    | .var u => if u == bφ.2.dst then none else some (bφ.2.dst, .var u)
    | x => some (bφ.2.dst, x))

/-- The surviving predecessors of each block, by edges no call cuts. -/
def livePredsOf (O : Option (List Summary)) (L : NatMap Unit) (f : Func) : NatMap (List Nat) :=
  f.blocks.foldl (fun m b => if (L.find? b.id).isSome then
    (liveSuccs O b).eraseDups.foldl (fun m s => m.insert s (b.id :: (m.find? s).getD [])) m
    else m) .empty

/-- What the check reads of a pair of functions. -/
structure CCtx where
  O : Option (List Summary)
  B : NatMap Block
  B' : NatMap Block
  T : DomTree
  D : NatMap Def
  OD : NatMap Def
  L : NatMap Unit
  preds : NatMap (List Nat)
  cs : List (Block × Phi)
  σ : NatMap Operand
  fuel : Nat

def CCtx.of (O : Option (List Summary)) (f f' : Func) : CCtx :=
  let B := NatMap.ofListBy (·.id) f.blocks
  let OD := defsOf f'
  let L := liveSet O f
  let cs := candsOf L OD f
  let n := f.blocks.length + 1
  { O, B, B' := .ofListBy (·.id) f'.blocks, T := domTree f, D := defsOf f, OD, L,
    preds := livePredsOf O L f, cs, σ := sigmaOf (liveOpsOf O B L) n cs, fuel := n }

namespace CCtx

variable (X : CCtx)

/-- The block survives. -/
def live (b : Nat) : Bool := (X.L.find? b).isSome

/-- A call cuts the block. -/
def cutAt (b : Nat) : Bool := (X.B.find? b).any (cut X.O)

/-- An operand through `σ`. -/
def hat : Operand → Operand
  | .var u => (X.σ.find? u).getD (.var u)
  | o => o

/-- `u` is defined strictly above block `b` in the tree: a parameter, or in a strict ancestor. -/
def strictDom (b u : Nat) : Bool :=
  match X.D.find? u with
  | some .param => true
  | some (.phi d) => d != b && X.T.anc d b
  | some (.stmt d _) => d != b && X.T.anc d b
  | none => false

/-- `σ` maps phi `φ` of block `b` to `x`: a word or a value strictly above `b` that `σ` does not
    map, and every operand from a surviving, uncut predecessor is `φ`'s own value or, through
    `σ`, `x` (review C-4). -/
def sigOk (b : Block) (φ : Phi) (x : Operand) : Bool :=
  let ops := liveOpsOf X.O X.B X.L φ
  x.wf && (match x with
    | .var u => (X.σ.find? u).isNone && X.strictDom b.id u
    | _ => true) &&
  ops.all (fun o => o == .var φ.dst || X.hat o == x) && ops.any (X.hat · == x)

/-- Every entry of `σ` is checked. -/
def sigmaOk : Bool := X.cs.all fun bφ => match X.σ.find? bφ.2.dst with
  | some x => X.sigOk bφ.1 bφ.2 x
  | none => true

/-- A phi of a surviving block is no value of the output, unless the output block of its id
    keeps it. -/
def phisDefOk (f : Func) : Bool := f.blocks.all fun b => !X.live b.id ||
  b.phis.all fun φ => (X.OD.find? φ.dst).isNone || match X.B'.find? b.id with
    | some ob => ob.phis.any (·.dst == φ.dst)
    | none => false

/-- An operand at the end of a tunnel block `tb`, entered from `r`, as one before it: its phi's
    operand from `r`, or itself; then through `θ`. -/
def through (θ : Operand → Operand) (tb : Block) (r : Nat) (o : Operand) : Operand :=
  match o with
  | .var w => match tb.phis.find? (·.dst == w) with
    | some φ => match inc φ r with
      | some a => θ a
      | none => θ o
    | none => θ o
  | o => θ o

/-- A tunnel block: no statements, a `jump`, surviving, no block of the output. -/
def tunnel (t : Nat) : Option (Block × Nat) :=
  match X.B.find? t with
  | some tb => if tb.body.isEmpty && (X.B'.find? t).isNone && X.live t then
      match tb.term with
      | .jump t₂ => some (tb, t₂)
      | _ => none
    else none
  | none => none

/-- From target `t` of a slot of block `r`, through tunnel blocks to `d'`: the block `d'` is
    entered from, and how the operands there read at `r`'s end (`through`). -/
def walk (d' : Nat) : Nat → (Operand → Operand) → Nat → Nat → Option (Nat × (Operand → Operand))
  | 0, _, _, _ => none
  | n + 1, θ, r, t =>
    if t == d' then some (r, θ) else
    match X.tunnel t with
    | some (tb, t₂) => walk d' n (through θ tb r) t t₂
    | none => none

/-- Block `d'` entered from `q` in the input, and from output block `b` (whose chain ends at
    `cm`, `k` statements) in the output: `q` survives, no call cuts it, and each phi the output
    block `d'` keeps takes from `b` the input phi's operand from `q`, read at `cm`'s end through
    `θ` and `σ`, a value whose definition dominates `cm`'s end. -/
def arrive (b cm k d' : Nat) (θ : Operand → Operand) (q : Nat) : Bool :=
  X.live q && !X.cutAt q &&
  match X.B'.find? d' with
  | none => true
  | some ob => match X.B.find? d' with
    | none => false
    | some ib => ob.phis.all fun φ' => match inc φ' b with
      | none => true
      | some o' => match ib.phis.find? (·.dst == φ'.dst) with
        | none => false
        | some φ => φ.ty == φ'.ty && match inc φ q with
          | none => false
          | some o => o' == X.hat (θ o) && useOk X.D X.T cm k (θ o)

/-- A slot of the output block `b`, whose chain ends at `cm` (`k` statements), targeting `d'`
    where the input's targets `d`. -/
def slotOk (b cm k d' d : Nat) : Bool :=
  match X.walk d' X.fuel id cm d with
  | some (q, θ) => X.arrive b cm k d' θ q
  | none => false

/-- A link of a chain: `c`'s every slot reaches `n` through tunnel blocks, from a surviving
    block no call cuts. -/
def linkTo (c n : Nat) (d : Nat) : Bool :=
  (X.walk n X.fuel id c d).any fun qθ => X.live qθ.1 && !X.cutAt qθ.1

/-- The ends of the paths from `c`'s slots to `n`. -/
def linkEnds (c n : Nat) (t : Term) : List Nat :=
  t.succs.filterMap fun d => (X.walk n X.fuel id c d).map (·.1)

/-- Where a slot target leads through tunnel blocks. -/
def endOf : Nat → Nat → Nat
  | 0, t => t
  | n + 1, t => match X.tunnel t with
    | some (_, t₂) => endOf n t₂
    | none => t

/-- A link from `c` to `n`: `c` survives, no call cuts it, its terminator goes to `n` by every
    slot (`termRel` against `jump n`), `n` is no output block, and `n`'s surviving predecessors
    are the ends of the paths. -/
def linkOk (c n : Nat) : Bool :=
  X.live c && (match X.B.find? c with
    | some cb => !cut X.O cb && termRel (X.linkTo c) (.jump n) cb.term &&
        ((X.preds.find? n).getD []).all (X.linkEnds c n cb.term).contains
    | none => false) && (X.B'.find? n).isNone

/-- The merge chain from block `c`. -/
def chainFrom : Nat → Nat → List Nat
  | 0, c => [c]
  | n + 1, c => match X.B.find? c with
    | some cb => match cb.term.succs.head? with
      | some d => let m := X.endOf X.fuel d
        if X.linkOk c m then c :: chainFrom n m else [c]
      | none => [c]
    | none => [c]

def linksOk : List Nat → Bool
  | [] => false
  | [c] => X.live c
  | c :: n :: rest => X.linkOk c n && linksOk (n :: rest)

/-- The statements of the last block of a chain: up to the first claimed-noreturn call. -/
def lastBody (cb : Block) : List Stmt :=
  match trimIdx X.O cb with
  | some k => cb.body.take (k + 1)
  | none => cb.body

/-- The statements of a chain. -/
def chainBody : List Nat → List Stmt
  | [] => []
  | [c] => ((X.B.find? c).map X.lastBody).getD []
  | c :: rest => ((X.B.find? c).map (·.body)).getD [] ++ chainBody rest

/-- The output terminator against the chain's last block `cm`: `unreachable` after a
    claimed-noreturn call, else slot by slot. -/
def termOk (ob cm : Block) : Bool :=
  match trimIdx X.O cm with
  | some _ => ob.term == .unreachable
  | none => termRel (fun d' d => X.slotOk ob.id cm.id cm.body.length d' d) ob.term
      (cm.term.mapOps X.hat)

/-- An output block: the merge chain from the input block of its id, the phis it keeps of the
    chain's head, the chain's statements through `σ`, and its terminator. -/
def blockOk (ob : Block) : Bool :=
  let ch := X.chainFrom X.fuel ob.id
  match X.B.find? ob.id, ch.getLast? >>= X.B.find? with
  | some c0, some cm => X.linksOk ch &&
      ob.phis.all (fun φ' => c0.phis.any fun φ => φ.dst == φ'.dst && φ.ty == φ'.ty) &&
      decide (ob.body = (X.chainBody ch).map (Stmt.mapOps X.hat)) && X.termOk ob cm
  | _, _ => false

/-! ### Instruction ids -/

def phiIds (b : Block) (ids : List Nat) : List Nat := ids.take b.phis.length
def bodyIds (b : Block) (ids : List Nat) : List Nat := (ids.drop b.phis.length).take b.body.length

/-- The body ids of a chain, `I` the input's ids by block. -/
def chainIds (I : NatMap (List Nat)) : List Nat → List Nat
  | [] => []
  | [c] => match X.B.find? c, I.find? c with
    | some cb, some ids => match trimIdx X.O cb with
      | some k => (bodyIds cb ids).take (k + 1)
      | none => bodyIds cb ids
    | _, _ => []
  | c :: rest => (match X.B.find? c, I.find? c with
    | some cb, some ids => bodyIds cb ids
    | _, _ => []) ++ chainIds I rest

/-- An output block's ids (`I'`) against the input's (`I`, all of them `inIds`). -/
def blockIdsOk (I I' : NatMap (List Nat)) (inIds : NatMap Unit) (ob : Block) : Bool :=
  let ch := X.chainFrom X.fuel ob.id
  match I'.find? ob.id, X.B.find? ob.id, I.find? ob.id, ch.getLast? with
  | some oids, some c0, some c0ids, some cmId => match X.B.find? cmId, I.find? cmId with
    | some cm, some cmids =>
      ((ob.phis.zip (phiIds ob oids)).all fun pi => (c0.phis.zip (phiIds c0 c0ids)).any
        fun pj => pj.1.dst == pi.1.dst && pj.2 == pi.2) &&
      bodyIds ob oids == X.chainIds I ch &&
      (match oids.getLast?, cmids.getLast?, trimIdx X.O cm with
        | some t', some t, none => t' == t
        | some t', some t, some k =>
          if k + 1 == cm.body.length && cm.term == .unreachable then t' == t
          else (inIds.find? t').isNone
        | _, _, _ => false)
    | _, _ => false
  | _, _, _, _ => false

end CCtx

/-- The check of a `cfg_cleanup` step of `f` (instruction ids `ids`) to the snapshot `s`, under
    the pass's table `O`. -/
def checkCfgCleanup (O : Option (List Summary)) (f : Func) (ids : Option (List (List Nat)))
    (s : FuncSnap) : Bool :=
  let f' := s.func
  let X := CCtx.of O f f'
  match ids, f.blocks.head?, f'.blocks.head? with
  | some ids, some e, some e' =>
    let I := NatMap.ofList ((f.blocks.zip ids).map fun bi => (bi.1.id, bi.2))
    let I' := NatMap.ofList ((f'.blocks.zip s.insts).map fun bi => (bi.1.id, bi.2))
    let inIds : NatMap Unit := .ofList (ids.flatten.map (·, ()))
    f'.name == f.name && decide (f'.params = f.params) && e'.id == e.id && f'.machine &&
      X.T.valid f && ssa f X.T && X.phisDefOk f && X.sigmaOk && f'.blocks.all X.blockOk &&
      f'.blocks.all (X.blockIdsOk I I' inIds)
  | _, _, _ => false

end Fe.Sonatina.Steps
