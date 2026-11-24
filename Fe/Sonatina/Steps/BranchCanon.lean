import Fe.Sonatina.Steps.EdgeSplit

/-!
# `branch_canonicalize` and `branch_conditions` (design §4.4, review M-3)

The output has the input's blocks, in order, with their ids and phis.  Each output block's
statements are the input block's, in order, less some `is_zero` statements whose results the
output neither defines nor uses (`bodyOk`, `deletable`, `unusedOk`): pure, total on words, and
dead.  Each terminator is the input's (`termRel` with equal targets), or, for `br c a b`,
`br c' a' b'` where `c` is `is_zero^k c'` for some `k ≥ 1`, each `is_zero` a statement of a
reachable block, and the targets are swapped iff `k` is odd (`peelOk`).

This is the part of Sonatina's `BranchCanonicalize` the records use: peeling `is_zero`s from a
branch condition (on `i256` values the pass peels nothing else).  Its other rewrites, a zero
compare to a new `is_zero` and a compare to its inverse, insert an instruction; the check
rejects them (none occurs in the corpus).  `branch_conditions` (machine/branch.rs) is the case
`k = 1`.

The input's dominator tree is checked valid and the input in strict SSA on it: the proof reads
the peeled values' definitions at the branch (an equational invariant on the input, like
`cfg_cleanup`'s trivial-phi invariant), and the definedness invariant makes the deleted
statements total.
-/

namespace Fe.Sonatina.Steps

/-- The operand of the `is_zero` that defines `c`: a statement of a block the tree reaches, with
    one result, `c`. -/
def isZeroArg (B : NatMap Block) (D : NatMap Def) (T : DomTree) : Operand → Option Operand
  | .var u => match D.find? u with
    | some (.stmt d j) =>
      if (T.reach.find? d).isSome then
        match B.find? d with
        | some blk => match blk.body[j]? with
          | some s => match s.inst, s.dsts with
            | .isZero a, [(u', _)] => if u' = u then some a else none
            | _, _ => none
          | none => none
        | none => none
      else none
    | _ => none
  | _ => none

/-- `br c' a' b'` is `br c a b` with `k ≥ 1` `is_zero`s peeled from `c` (at most `n`), the
    targets swapped iff `k` is odd. -/
def peelOk (B : NatMap Block) (D : NatMap Def) (T : DomTree) (c' : Operand) (a' b' : Nat) :
    Nat → Operand → Nat → Nat → Bool
  | 0, _, _, _ => false
  | n + 1, c, a, b => match isZeroArg B D T c with
    | some c₁ => (decide (c' = c₁) && a' == b && b' == a) || peelOk B D T c' a' b' n c₁ b a
    | none => false

/-- A statement the step may delete: an `is_zero` with one result, which the output does not
    define. -/
def deletable (OD : NatMap Def) (s : Stmt) : Bool :=
  match s.inst, s.dsts with
  | .isZero _, [(u, _)] => (OD.find? u).isNone
  | _, _ => false

/-- The output's statements are the input's, in order, less deletable ones. -/
def bodyOk (OD : NatMap Def) : List Stmt → List Stmt → Bool
  | [], [] => true
  | [], s :: is => deletable OD s && bodyOk OD [] is
  | _ :: _, [] => false
  | s' :: os, s :: is =>
    (decide (s' = s) && bodyOk OD os is) || (deletable OD s && bodyOk OD (s' :: os) is)

/-- What the check reads of a pair of functions. -/
structure BCtx where
  B : NatMap Block
  D : NatMap Def
  OD : NatMap Def
  T : DomTree
  fuel : Nat

def BCtx.of (f f' : Func) : BCtx :=
  ⟨.ofListBy (·.id) f.blocks, defsOf f, defsOf f', domTree f, f.blocks.length + 1⟩

/-- An output terminator against the input's: the same, or a `br` with peeled `is_zero`s. -/
def BCtx.termOk (X : BCtx) (t' t : Term) : Bool :=
  termRel (· == ·) t' t || match t', t with
    | .br c' a' b', .br c a b => peelOk X.B X.D X.T c' a' b' X.fuel c a b
    | _, _ => false

/-- An output block against the input block at its place. -/
def BCtx.blockOk (X : BCtx) (b' b : Block) : Bool :=
  b'.id == b.id && decide (b'.phis = b.phis) && bodyOk X.OD b'.body b.body && X.termOk b'.term b.term

/-- The values a function's phis, statements and terminators read. -/
def usedVars (f : Func) : NatMap Unit :=
  .ofList ((f.blocks.flatMap fun b =>
    (b.phis.flatMap fun phi => phi.incoming.map (·.1)) ++ (b.body.flatMap (·.inst.args)) ++
      b.term.args).filterMap fun o => match o with
    | .var u => some (u, ())
    | _ => none)

/-- No `is_zero` result the output does not define is used in the output. -/
def unusedOk (f f' : Func) : Bool :=
  let U := usedVars f'
  let OD := defsOf f'
  f.blocks.all fun b => b.body.all fun s => match s.inst, s.dsts with
    | .isZero _, [(u, _)] => (OD.find? u).isSome || (U.find? u).isNone
    | _, _ => true

/-- `l'` is a subsequence of `l`. -/
def subseq : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: l', y :: l => if x == y then subseq l' l else subseq (x :: l') l

/-- The instruction ids: each output block keeps its phis' and terminator's ids, and its
    statements' ids are a subsequence of the input block's. -/
def bcIdsOk (f f' : Func) (ids ids' : List (List Nat)) : Bool :=
  ids.length == f.blocks.length && ids'.length == f'.blocks.length &&
    ((f'.blocks.zip ids').zip (f.blocks.zip ids)).all fun p =>
      let (b', i') := p.1
      let (b, i) := p.2
      i'.take b'.phis.length == i.take b.phis.length && i'.getLast? == i.getLast? &&
        subseq ((i'.drop b'.phis.length).take b'.body.length)
          ((i.drop b.phis.length).take b.body.length)

/-- The check of a `branch_canonicalize` or `branch_conditions` step of `f` (instruction ids
    `ids`) to the snapshot `s`. -/
def checkBranchCanon (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) : Bool :=
  let f' := s.func
  let X := BCtx.of f f'
  match ids with
  | some ids =>
    f'.name == f.name && decide (f'.params = f.params) && f'.machine && X.T.valid f &&
      ssa f X.T && f'.blocks.length == f.blocks.length &&
      (f'.blocks.zip f.blocks).all (fun p => X.blockOk p.1 p.2) && unusedOk f f' &&
      bcIdsOk f f' ids s.insts
  | none => false

end Fe.Sonatina.Steps
