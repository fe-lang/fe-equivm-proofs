import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.LowerSwitches

/-!
# The `gvn_rewrite` checker

One GVN run is recorded as two steps (`optim/gvn.rs`, `remove_redundant_code`): `gvn_prune`
removes the edges and blocks GVN proved dead; `gvn_rewrite`, on the pruned function, replaces
each value by an available member of its congruence class (`remove_code_in_block`,
`change_to_alias`), resolves value phis by inserting phis at block tops
(`resolve_value_phi_in_block`, `resolve_value_phi`) and replacing values by them, and erases the
instructions whose results were all replaced.  Its facts (`gvn`, of the pruned function): the
classes as `(value, representative)` (a representative an immediate or a live member that
strictly dominates the value), the edge predicates, and the inserted phis, each with the term it
stands for at its block (`InsertedPhi::term`).

The check is the schema checkers' (`aliasReject`) in the mode `gvn`, on the input with the
inserted phis added (`insPhis`):

1. **Phi insertion.**  The output's leading phis whose instruction ids the input has not are the
   inserted ones; the input with them prepended to their blocks is `f₁`.  Their results are no
   value the input mentions, their operands well formed, and `f₁` keeps the control flow, the
   phis' predecessors and the types (`insOk`).  `f₁` approximates `f`: its runs bind the new
   phis besides, or are stuck where one's operand is unbound.
2. **The rewrite from `f₁`** (`aliasReject (.gvn cls pts)`): lines paired by id, deletions phis or
   pure statements other than `clz`, `σ` from the changed operands; both snapshots in strict
   SSA.  Each `σ` entry `v ↦ x` is justified by a schema on unfolded terms (as in
   `known_bits_simplify`), or by the classes: `v` and `x` have one representative and `x`'s
   definition dominates `v`'s; or by an inserted phi `ψ` of block `Q` with term `t`: `Q`
   dominates `v`'s block and `v`'s definition unfolds to `t`.
3. **The certificate, checked on `f₁`, not trusted** (`Mode.certOk`): each class pair `(v, r)`:
   `r` dominates `v`'s definition, and `v`'s pure statement, operands through their
   representatives, equals `r`'s by a schema, or `v`'s phi takes from each predecessor an operand
   with the representative of `r`'s operand from it (`r` a phi of the same block) or of `r` (`r`
   above the block).  The pairs a check fails are dropped first, to a fixpoint (`keepValid`); the
   remaining set is what is checked.  Each inserted phi `ψ` of `Q` with term `t`: `t` has no
   `clz`, its atoms are phis of `Q` or above `Q`, and from each predecessor `p` its operand is
   `t` with `Q`'s phis replaced by their operands from `p`, by a schema: the operand unfolded,
   or an inserted phi of that term.

The facts' known bits are checked as a post-fixpoint on `f₁`.  The record's `value_phis` are not
needed (each replacement is justified anew), its predicates are not used (a class a predicate
justifies is dropped), and a rewrite step with dead edges is rejected.
-/

namespace Fe.Sonatina.Steps.Schemas

/-! ## The record's terms -/

def GOp.toOperand : GOp → Operand
  | .val v => .var v
  | .imm w => .imm 256 w

/-- The input's statements' instructions by instruction id. -/
def instById (f : Func) (ids : List (List Nat)) : NatMap Inst :=
  .ofList ((f.blocks.zip ids).flatMap fun bi => (bi.2.drop bi.1.phis.length).zip (bi.1.body.map (·.inst)))

/-- A record term as a term: each instruction pure, with one argument per operand. -/
def GTerm.toTerm (I : NatMap Inst) : GTerm → Option Term
  | .val v => some (.atom v)
  | .imm w => some (.lit w)
  | .inst id [a] => match (I.find? id).bind pureInst? with
    | some (.op1 o _) => (a.toTerm I).map (.op1 o)
    | _ => none
  | .inst id [a, b] => match (I.find? id).bind pureInst? with
    | some (.op2 o _ _) => do return .op2 o (← a.toTerm I) (← b.toTerm I)
    | _ => none
  | .inst id [a, b, c] => match (I.find? id).bind pureInst? with
    | some (.op3 o _ _ _) => do return .op3 o (← a.toTerm I) (← b.toTerm I) (← c.toTerm I)
    | _ => none
  | .inst _ _ => none

/-! ## The inserted phis -/

/-- The function with `news[i]` prepended to the phis of its `i`-th block. -/
def insPhis (f : Func) (news : List (List Phi)) : Func :=
  { f with blocks := (f.blocks.zip news).map fun bn => { bn.1 with phis := bn.2 ++ bn.1.phis } }

/-- The instruction ids of `insPhis`. -/
def insIds (ids : List (List Nat)) (newIds : List (List Nat)) : List (List Nat) :=
  (ids.zip newIds).map fun ii => ii.2 ++ ii.1

/-- An output block's leading phis whose ids are not in `inIds`, with their ids. -/
def leadNew (inIds : NatMap Unit) (ob : Block) (oids : List Nat) : List (Phi × Nat) :=
  (ob.phis.zip oids).takeWhile fun pi => (inIds.find? pi.2).isNone

/-- The phis the step inserted, block by block, with their ids. -/
def newPhisOf (ids : List (List Nat)) (s : FuncSnap) : List (List (Phi × Nat)) :=
  let inIds : NatMap Unit := .ofList (ids.flatten.map (·, ()))
  (s.func.blocks.zip s.insts).map fun bi => leadNew inIds bi.1 bi.2

/-- The insertion: one list per block, the new phis' results no value the input mentions, their
    operands well formed, and the function with them keeps the control flow and the types. -/
def insOk (f : Func) (news : List (List Phi)) : Bool :=
  let V : NatMap Unit := .ofList ((funcVars f).map (·, ()))
  news.length == f.blocks.length &&
    news.all (·.all fun φ => (V.find? φ.dst).isNone && φ.incoming.all (·.1.wf)) &&
    (insPhis f news).cfgOk && (insPhis f news).wordTyped

/-! ## The check -/

/-- The class pairs, those a check fails dropped, to a fixpoint (at most `n` rounds). -/
def keepValid (X : StepCtx) : Nat → List (Nat × Operand) → List (Nat × Operand)
  | 0, cls => cls
  | n + 1, cls =>
    let C := NatMap.ofList cls
    let cls' := cls.filter fun e => e.2.wf && X.before e.2 e.1 && (X.pairOk C e.1 e.2 || X.symPair e.1 e.2)
    if cls'.length == cls.length then cls else keepValid X n cls'

/-- Why a `gvn_rewrite` step is rejected. -/
inductive GReject where
  | noIds | noFacts | wrongFacts | shape | inserted | alias (r : Reject)
  deriving Repr, DecidableEq

/-- The input with the inserted phis, its ids, and the mode with the checked certificate. -/
def gvnPrep (f : Func) (is : List (List Nat)) (s : FuncSnap) (F : StepFacts) (G : GvnFacts) :
    List (List Phi) × Func × List (List Nat) × Mode :=
  let news := newPhisOf is s
  let ps := news.map (·.map (·.1))
  let f₁ := insPhis f ps
  let I := instById f is
  let pts := G.phis.filterMap fun e => (e.2.2.bind (·.toTerm I)).map fun t => (e.1, e.2.1, t)
  let cls := G.cls.map fun e => (e.1, e.2.toOperand)
  (ps, f₁, insIds is (news.map (·.map (·.2))),
    .gvn (keepValid (StepCtx.of f₁ s F false) (cls.length + 1) cls) pts)

def gvnRewriteReject (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option GReject :=
  match ids, F.gvn with
  | none, _ => some .noIds
  | _, none => some .noFacts
  | some is, some G =>
    if !F.unread.isEmpty || F.consts.isSome || F.demanded.isSome || !F.deadEdges.isEmpty ||
        !F.finiteLoops.isEmpty || !G.deadEdges.isEmpty then some .wrongFacts
    else if !(s.func.blocks.length == f.blocks.length && is.length == f.blocks.length &&
        s.insts.length == f.blocks.length) then some .shape
    else
      let (ps, f₁, is₁, m) := gvnPrep f is s F G
      if !insOk f ps then some .inserted
      else (aliasReject m f₁ (some is₁) s F).map .alias

/-- `gvn_rewrite` (design §4.8, review C-3). -/
def checkGvnRewrite (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Bool :=
  (gvnRewriteReject f ids s F).isNone

def diagnoseGvnRewrite (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) (F : StepFacts) :
    Option String :=
  (gvnRewriteReject f ids s F).map fun r => s!"{repr r}"

end Fe.Sonatina.Steps.Schemas
