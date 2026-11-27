import Fe.Sonatina.Steps.BranchCanon

/-!
# `adce` (design §4.6, review C-5)

Sonatina's ADCE (`optim/adce.rs`) on machine IR removes, per round: statements that are not
roots and that no live statement uses, phis no live statement uses, and blocks with no live
statement; a live terminator whose target died goes to the target's nearest live
post-dominator (`replace_succ_allow_existing_pred`, only when that block has no phis or the
terminator already goes there), or loses the slot (`remove_succ`).

The check (`checkAdce`), driven by the output's blocks, each an input block of its id:

- its phis are input phis, and each input phi it drops defines a value the output does not
  define (`freshV`);
- its statements are the input's in order, less removable ones (`removable`): an instruction the
  model runs to the number of values its statement binds, total on words and without a change of
  the world (`Inst.deadRes`: arithmetic, comparisons, `select`, `ctz`, casts, `keccak_words`, the
  EVM reads but `evm_gas`; not `clz`, which traps before Osaka, not a call, a store, a log or
  `evm_gas`), whose results the output does not define;
- its terminator is the input's slot by slot (`termRel`), a `br` or `br_table` possibly
  collapsed to a `jump`, each output target the input's or a bypass of it (`bypassOk`): the
  input blocks reachable from the input's target `d` before the output's `t` can be ordered so
  that each one's successors are `t` or come later (`order`, `chainOk`), so no path from `d`
  loops before `t`; each such block is no output block, defines no output value, holds only
  removable statements and ends in a `jump`, `br` or `br_table` (`crossOk`); and `t` has no
  phis in the output.  From `d` the input then runs to `t` through blocks that change nothing
  the output reads, in finitely many steps.
- the entry keeps its id, the parameters are the input's, the input's dominator tree is valid
  and the input in strict SSA (the definedness invariant makes the removed work total); every
  value the output uses it defines (`closedOk`); instruction ids are kept (`adIdsOk`).

A bypassed region with a cycle (ADCE removing a loop it proved finite) is rejected, whatever the
step's facts: the order does not reach `d` (`ACtx.loopBypass` names it for the measurement).
This is the first stage's one exclusion; no step of the corpora removes a loop.  The record's
`finite_loops` facts are read (`Schemas.StepFacts.finiteLoops`) and not used: a loop certificate
would be checked from them, with a termination proof the check does not have.
-/

namespace Fe.Sonatina.Steps

/-- An EVM instruction the model runs, on words, to one word without a change of the world: its
    operand count.  Not `evm_gas`, which takes from the gas feed. -/
def _root_.Fe.Sonatina.EvmOp.readArity : EvmOp → Option Nat
  | .address | .origin | .caller | .callValue | .calldataSize | .codeSize | .gasPrice
  | .returnDataSize | .coinbase | .timestamp | .number | .prevRandao | .gasLimit | .chainId
  | .selfBalance | .baseFee | .blobBaseFee => some 0
  | .balance | .calldataLoad | .extCodeSize | .extCodeHash | .blockHash | .blobHash | .codeLoad
  | .mload | .sload | .tload => some 1
  | .keccak256 => some 2
  | .addMod | .mulMod => some 3
  | _ => none

/-- An instruction a dead-code step may remove: total on words in the model, without a change of
    the world; the number of values it gives. -/
def _root_.Fe.Sonatina.Inst.deadRes : Inst → Option Nat
  | .bin .. | .cmp .. | .isZero _ | .not _ | .neg _ | .ctz _ | .sat .. | .cast .. | .select ..
  | .keccakWords _ => some 1
  | .ovf .. => some 2
  | .evm op args => if op.readArity = some args.length then some 1 else none
  | _ => none

/-- A value the output does not define. -/
def freshV (OD : NatMap Def) (u : Nat) : Bool := (OD.find? u).isNone

/-- A statement the step may remove: a removable instruction with as many results as it gives,
    none a value of the output. -/
def removable (OD : NatMap Def) (s : Stmt) : Bool :=
  s.inst.deadRes == some s.dsts.length && s.dsts.all (freshV OD ·.1)

/-- The output's statements are the input's, in order, less removable ones. -/
def adBodyOk (OD : NatMap Def) : List Stmt → List Stmt → Bool
  | [], [] => true
  | [], s :: is => removable OD s && adBodyOk OD [] is
  | _ :: _, [] => false
  | s' :: os, s :: is =>
    (decide (s' = s) && adBodyOk OD os is) || (removable OD s && adBodyOk OD (s' :: os) is)

/-- A terminator a bypassed path may cross: it goes on to one of its successors. -/
def _root_.Fe.Sonatina.Term.isGoto : Term → Bool
  | .jump _ | .br _ _ _ | .brTable _ (some _) _ => true
  | _ => false

/-- What the check reads of a pair of functions. -/
structure ACtx where
  B : NatMap Block
  B' : NatMap Block
  OD : NatMap Def
  fuel : Nat

def ACtx.of (f f' : Func) : ACtx :=
  ⟨.ofListBy (·.id) f.blocks, .ofListBy (·.id) f'.blocks, defsOf f',
    f.blocks.foldl (fun n b => n + b.term.succs.length + 1) 1⟩

/-- The input successors of block `b`. -/
def ACtx.succs (X : ACtx) (b : Nat) : List Nat := ((X.B.find? b).map (·.term.succs)).getD []

/-- An input block a bypassed path crosses: no output block, no value of the output, removable
    statements, a terminator that goes on. -/
def ACtx.crossOk (X : ACtx) (blk : Block) : Bool :=
  (X.B'.find? blk.id).isNone && blk.phis.all (freshV X.OD ·.dst) && blk.body.all (removable X.OD) &&
    blk.term.isGoto

/-- Blocks in an order where each one's successors are `t` or come later in the list, each a
    block a bypassed path may cross. -/
def ACtx.chainOk (X : ACtx) (t : Nat) : List Nat → Bool
  | [] => true
  | r :: rest =>
    (match X.B.find? r with
      | some blk => X.crossOk blk && blk.term.succs.all (fun x => x == t || rest.contains x)
      | none => false) && X.chainOk t rest

/-- The input blocks reachable from the work list before `t` (at most `n` visits). -/
def ACtx.region (X : ACtx) (t : Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, x :: todo, seen =>
    if x == t || seen.contains x then X.region t n todo seen
    else X.region t n (X.succs x ++ todo) (x :: seen)

/-- One round of ordering: each block of `R` not yet placed whose successors are all `t` or
    placed goes in front. -/
def ACtx.peel (X : ACtx) (t : Nat) (R placed : List Nat) : List Nat :=
  R.foldl (fun pl x =>
    if pl.contains x then pl
    else if (X.succs x).all (fun y => y == t || pl.contains y) then x :: pl else pl) placed

/-- `n` rounds of ordering. -/
def ACtx.order (X : ACtx) (t : Nat) (R : List Nat) : Nat → List Nat → List Nat
  | 0, pl => pl
  | n + 1, pl => X.order t R n (X.peel t R pl)

/-- The order of the blocks reachable from `d` before `t`: blocks on a cycle stay out. -/
def ACtx.bypassOrder (X : ACtx) (t d : Nat) : List Nat :=
  let R := X.region t X.fuel [d] []
  X.order t R R.length []

/-- Output block `t` has no phis. -/
def ACtx.noPhis' (X : ACtx) (t : Nat) : Bool := (X.B'.find? t).all (·.phis.isEmpty)

/-- The output goes to `t` where the input goes to `d`, which runs on to `t` through blocks that
    change nothing the output reads, without a cycle. -/
def ACtx.bypassOk (X : ACtx) (t d : Nat) : Bool :=
  t != d && X.noPhis' t && (let L := X.bypassOrder t d; L.contains d && X.chainOk t L)

/-- A bypass the check rejects because the region loops: ADCE removed a loop (for the
    measurement). -/
def ACtx.loopBypass (X : ACtx) (t d : Nat) : Bool :=
  t != d && !(X.bypassOrder t d).contains d

/-- `φ` is one of the phis. -/
def hasPhi (ps : List Phi) (φ : Phi) : Bool := ps.any fun ψ => decide (ψ = φ)

/-- An output target against the input's in the same slot. -/
def ACtx.slotOk (X : ACtx) (t d : Nat) : Bool := t == d || X.bypassOk t d

/-- An output block against the input block of its id. -/
def ACtx.blockOk (X : ACtx) (b' : Block) : Bool :=
  match X.B.find? b'.id with
  | some b =>
    b'.phis.all (fun φ => hasPhi b.phis φ) &&
      b.phis.all (fun φ => hasPhi b'.phis φ || freshV X.OD φ.dst) &&
      adBodyOk X.OD b'.body b.body && termRel X.slotOk b'.term b.term
  | none => false

/-- Every value the output uses it defines. -/
def closedOk (f' : Func) : Bool :=
  let OD := defsOf f'
  f'.blocks.all fun b =>
    (b.phis.all fun phi => phi.incoming.all fun o => match o.1 with
      | .var u => (OD.find? u).isSome
      | _ => true) &&
    (b.body.all fun s => s.inst.args.all fun o => match o with
      | .var u => (OD.find? u).isSome
      | _ => true) &&
    b.term.args.all fun o => match o with
      | .var u => (OD.find? u).isSome
      | _ => true

/-- `l'` is a subsequence of `l`. -/
def subseqN : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: l', y :: l => if x == y then subseqN l' l else subseqN (x :: l') l

/-- The instruction ids: each output block's phis and statements keep their ids, a subsequence of
    the input block's, and its terminator its id. -/
def adIdsOk (f f' : Func) (ids ids' : List (List Nat)) : Bool :=
  let I : NatMap (Block × List Nat) := .ofList ((f.blocks.zip ids).map fun bi => (bi.1.id, bi))
  ids.length == f.blocks.length && ids'.length == f'.blocks.length &&
    (f'.blocks.zip ids').all fun (b', i') => match I.find? b'.id with
      | some (b, i) =>
        subseqN (i'.take b'.phis.length) (i.take b.phis.length) &&
          subseqN ((i'.drop b'.phis.length).take b'.body.length)
            ((i.drop b.phis.length).take b.body.length) &&
          i'.getLast? == i.getLast?
      | none => false

/-- The facts an `adce` step may have: none but the loops it proved finite. -/
def adceFactsOk (F : Schemas.StepFacts) : Bool :=
  F.knownBits.isEmpty && F.demanded.isNone && F.consts.isNone && F.deadEdges.isEmpty &&
    F.unread.isEmpty

/-- The check of an `adce` step of `f` (instruction ids `ids`) to the snapshot `s`. -/
def checkAdce (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : Schemas.StepFacts) :
    Bool :=
  let f' := s.func
  let X := ACtx.of f f'
  adceFactsOk F && match ids, f.blocks.head?, f'.blocks.head? with
  | some ids, some e, some e' =>
    e'.id == e.id && f'.name == f.name && decide (f'.params = f.params) && f'.machine &&
      (domTree f).valid f && ssa f (domTree f) && f'.blocks.all X.blockOk && closedOk f' &&
      adIdsOk f f' ids s.insts
  | _, _, _ => false

/-- Why `checkAdce` rejects: its first failing part (for the measurement). -/
def adceWhy (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : Schemas.StepFacts) :
    String := Id.run do
  let f' := s.func
  let X := ACtx.of f f'
  if !adceFactsOk F then return "facts other than finite_loops"
  let (some _, some e, some e') := (ids, f.blocks.head?, f'.blocks.head?) | return "no ids or entry"
  if e'.id != e.id then return "entry changed"
  if f'.params != f.params then return "parameters changed"
  if !f'.machine then return "output not machine IR"
  if !((domTree f).valid f && ssa f (domTree f)) then return "input dominators or SSA rejected"
  for b' in f'.blocks do
    if !X.blockOk b' then
      let some b := X.B.find? b'.id | return s!"block {b'.id}: no input block"
      if !(b'.phis.all (fun φ => hasPhi b.phis φ) &&
          b.phis.all (fun φ => hasPhi b'.phis φ || freshV X.OD φ.dst)) then
        return s!"block {b'.id}: phis"
      if !adBodyOk X.OD b'.body b.body then
        let bad := b.body.filter fun st => !b'.body.contains st && !removable X.OD st
        return s!"block {b'.id}: statements (not removable: {bad.map (fun st => repr st.inst)})"
      let tgts := b.term.succs.zip b'.term.succs
      if tgts.any (fun (d, t) => X.loopBypass t d) then
        return s!"block {b'.id}: loop removal (rejected)"
      return s!"block {b'.id}: terminator"
  if !closedOk f' then return "output uses a value it does not define"
  return "instruction ids"

end Fe.Sonatina.Steps
