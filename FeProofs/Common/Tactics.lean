import Reasoning.Reach
import Reasoning.JumpDest

/-!
# Chaining generated block summaries

`scripts/generate_rd_blocks.py` (EquiVM) emits one lemma per basic block, named after the
bytecode constant: for `…feXBytecode` the block at `pc` is `feXBlocks.feX_block_<pc>`, with
`_taken`/`_fallthrough` variants for a conditional jump, and for creation code
(`feXCreationBytecode ++ tail`) it is `feXCreationBlocks.feXCreation_block_<pc>`.

* `rd_step h` applies the summary of the block at `h`'s program counter to `h : RD code …`,
  replacing `h` with the summary's conclusion and unfolding its `_stack`/`_memory` definitions.
* `rd_run h to N` repeats `rd_step` until the program counter is `N` (or, without `to`, until no
  block applies or the run ends in `RDrev`/`RDret`/`RDstatic`).

Side conditions are discharged automatically: stack bounds by `simp`/`omega`, jump destinations by
`jump_dest`, and branch conditions and other hypotheses by a `using [t, …]` term (as a proof, up to
`≠`/`¬¬`, or as equations to rewrite with, one or all in order, before `decide`), `assumption`, `decide`, `simp` or `omega`. At a conditional jump the taken branch is tried first; when neither
condition can be discharged the step fails (`rd_step`) or the run stops there (`rd_run`). A
program counter written as a closed sum, such as `UInt256.ofNat 891 + ⟨1⟩`, is normalized first.
`as h'` names the result instead of reusing `h`.
-/

open Lean Meta Elab Tactic Simp
open Ethereum Reasoning.Reach

namespace FeProofs.RDTactic

/-- The value of a closed program counter: `UInt256.ofNat n`, `⟨n⟩`, or a sum of those. -/
partial def pcValue? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  let natLit (x : Expr) : Option Nat :=
    match x.nat? with
    | some n => some n
    | none => match_expr x with
      | OfNat.ofNat _ n _ => n.rawNatLit?
      | _ => x.rawNatLit?
  match_expr e with
  | Ethereum.UInt256.ofNat n => return (natLit n).map (· % UInt256.size)
  | Ethereum.UInt256.mk v => return natLit v
  | HAdd.hAdd _ _ _ _ a b =>
    let some x ← pcValue? a | return none
    let some y ← pcValue? b | return none
    return some ((x + y) % UInt256.size)
  | _ => return none

/-- The block-lemma prefix for a bytecode term, from its constant's name. -/
def blockPrefix? (code : Expr) : MetaM (Option Name) := do
  let code ← instantiateMVars code
  let c := match_expr code with
    | HAppend.hAppend _ _ _ _ a _ => a
    | _ => code
  let .const n _ := c.getAppFn | return none
  let s := n.lastComponentAsString
  unless s.endsWith "Bytecode" do return none
  let base := String.ofList (s.toList.take (s.length - "Bytecode".length))
  return some (Name.mkStr (Name.mkSimple (base ++ "Blocks")) (base ++ "_block"))

/-- `(code, pc)` of a hypothesis type `RD code ee g s0 pc …`. -/
def rdView? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isAppOfArity ``RD 12 then
    return some (ty.getArg! 0, ty.getArg! 4)
  return none

/-- `decide`, only on a goal without local variables (a symbolic goal could take long to fail). -/
elab "decide_closed" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if ty.hasFVar || ty.hasMVar then throwError "decide_closed: goal is not closed"
  evalTactic (← `(tactic| decide))

/-- Whether `e` mentions a constant whose last name component is `n`. -/
def mentions (e : Expr) (n : String) : Bool :=
  (e.find? fun x => x.isConst && x.constName!.lastComponentAsString == n).isSome

/-- Close a side goal of a block summary. Candidate proofs (hints and hypotheses) are compared with
the goal at reducible transparency, and only with goals of their own kind: comparing a
jump-destination goal with anything else makes Lean unfold the bytecode's jump-destination table,
which takes very long to fail. -/
def discharge (g : MVarId) (hints : Array (Term × Expr × Expr)) : TacticM Bool := do
  let ty ← instantiateMVars (← g.getType)
  let gs ← getGoals
  let tryTac (tac : TacticM Unit) : TacticM Bool := do
    let s ← saveState
    try
      setGoals [g]
      tac
      if (← getUnsolvedGoals).isEmpty then setGoals gs; return true
      s.restore; return false
    catch _ => s.restore; return false
  let isJump := mentions ty "D_J"
  let fits (t : Expr) : Bool :=
    mentions t "D_J" == isJump && !(t.isAppOf ``RD || t.isAppOf ``RDrev || t.isAppOf ``RDret)
  -- hints and hypotheses as proofs
  let mut cands : Array Expr := hints.filterMap fun (_, e, t) => if fits t then some e else none
  for d in (← g.getDecl).lctx do
    if !d.isImplementationDetail && fits (← instantiateMVars d.type) then cands := cands.push d.toExpr
  -- reducible transparency: at default transparency a mismatch can unfold word arithmetic for long
  for e in cands do
    let s ← saveState
    if ← withReducible (isDefEq (← inferType e) ty) then
      g.assign e; return true
    s.restore
  if isJump then return ← tryTac (evalTactic (← `(tactic| jump_dest)))
  -- stack bounds
  if mentions ty "length" then
    for tac in [← `(tactic| (simp; done)), ← `(tactic| omega), ← `(tactic| (simp; omega))] do
      if ← tryTac (evalTactic tac) then return true
    return false
  -- branch conditions: decide, or rewrite with the hints first
  if ← tryTac (evalTactic (← `(tactic| decide_closed))) then return true
  let eqs := hints.filter fun (_, _, t) => t.isAppOf ``Eq && fits t
  for (stx, _, _) in eqs do
    if ← tryTac (evalTactic (← `(tactic| (rw [$stx:term]; decide_closed)))) then return true
  if eqs.size > 1 then
    let rws ← eqs.mapM fun (stx, _, _) => `(Lean.Parser.Tactic.rwRule| $stx:term)
    if ← tryTac (evalTactic (← `(tactic| (rw [$rws,*]; decide_closed)))) then return true
  for (stx, _, t) in hints do
    if fits t then
      if ← tryTac (evalTactic (← `(tactic|
          set_option linter.unnecessarySimpa false in simpa only [ne_eq, not_not] using $stx)))
      then return true
  return false

/-- Elaborate the `using` terms once per step: each with its proof and type. -/
def elabHints (hints : Array Term) : TacticM (Array (Term × Expr × Expr)) :=
  hints.filterMapM fun (stx : Term) => do
    try
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasExprMVar then return none
      let t ← instantiateMVars (← inferType e)
      return some ((stx, e, t) : Term × Expr × Expr)
    catch _ => return none

/-- Apply the block summary `blk` to the hypothesis `h`; on success return the new proof and
its type. -/
def applyBlock (h : FVarId) (blk : Name) (hints : Array (Term × Expr × Expr)) :
    TacticM (Option (Expr × Expr)) := do
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels blk
    let (args, binfos, concl) ← forallMetaTelescopeReducing (← inferType c)
    -- the RD hypothesis is the last explicit argument
    let some i := (List.range args.size).reverse.find? (binfos[·]! == .default) | throw (.error .missing "")
    unless ← isDefEq args[i]! (mkFVar h) do s.restore; return none
    for j in [0:args.size] do
      if j != i && binfos[j]! == .default then
        let g := args[j]!.mvarId!
        unless ← g.isAssigned do
          unless ← discharge g hints do s.restore; return none
    let val ← instantiateMVars (mkAppN c args)
    if val.hasExprMVar then s.restore; return none
    return some (val, ← instantiateMVars concl)
  catch _ => s.restore; return none

/-- The main goal's hypothesis named `name`. -/
def lookup (name : Name) : TacticM LocalDecl := withMainContext do
  let some d := (← getLCtx).findFromUserName? name | throwError "rd_step: lost hypothesis {name}"
  return d

/-- Replace `h` by `val : ty` under the name `name`, destructuring leading existentials and
unfolding the block's `_stack`/`_memory` definitions. Returns the new hypothesis. -/
def install (h : FVarId) (name : Name) (blk : Name) (val ty : Expr) : TacticM FVarId := do
  let g ← getMainGoal
  let (_, g) ← g.note name val ty
  let g ← (do pure (← g.tryClear h))
  replaceMainGoal [g]
  let nameId := mkIdent name
  -- `∃ k' C', RD …` (packed or warm/cold summaries)
  let mut t ← whnfR ty
  while t.isAppOfArity ``Exists 2 do
    evalTactic (← `(tactic| obtain ⟨_, $nameId⟩ := $nameId))
    t ← withMainContext do whnfR (← instantiateMVars (← lookup name).type)
  let defs := [blk.appendAfter "_stack", blk.appendAfter "_memory"].filter ((← getEnv).contains ·)
  unless defs.isEmpty do
    let ids := defs.toArray.map fun n => mkIdent n
    try evalTactic (← `(tactic| simp only [$[$ids:ident],*] at $nameId:ident)) catch _ => pure ()
  return (← lookup name).fvarId

/-- One block step from `h`. Returns the new hypothesis, or `none` when no block applies. -/
def step (h : FVarId) (name : Name) (hints : Array Term) : TacticM (Option FVarId) := do
  let ty ← instantiateMVars (← h.getType)
  let some (code, pc) ← rdView? ty | return none
  let some pre ← blockPrefix? code | throwError "rd_step: no block prefix for {code}"
  let some n ← pcValue? pc | return none
  -- normalize a non-literal program counter
  let h ← if pc.isAppOfArity ``Ethereum.UInt256.ofNat 1 then pure h else do
    let hName ← h.getUserName
    let pcId := mkIdent hName
    let lit := Syntax.mkNumLit (toString n)
    evalTactic (← `(tactic| replace $pcId:ident := RD.normalizePC (pc' := UInt256.ofNat $lit) $pcId (by decide)))
    pure (← lookup hName).fvarId
  let base := pre.appendAfter s!"_{n}"
  for blk in [base, base.appendAfter "_taken", base.appendAfter "_fallthrough"] do
    if (← getEnv).contains blk then
      if let some (val, vty) ← withMainContext (do applyBlock h blk (← elabHints hints)) then
        return some (← install h name blk val vty)
  return none

/-- `UInt256.toNat` of a closed word literal (`UInt256.ofNat n`, `⟨n⟩`, or a sum of those) is a
`Nat` literal, by evaluation. Normalizes the offsets and lengths in memory terms, which block
summaries write in either form, so that lemmas stated with plain `Nat` offsets apply. -/
simproc_decl reduceUInt256ToNat (UInt256.toNat _) := fun e => do
  let_expr Ethereum.UInt256.toNat x ← e | return .continue
  let some n ← pcValue? x | return .continue
  return .done { expr := mkNatLit n }

/-- Rewrites `UInt256.toNat` of word literals to `Nat` literals (`reduceUInt256ToNat`). -/
macro "u256_lits" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [reduceUInt256ToNat] $(loc)?)

syntax rdUsing := " using " "[" term,* "]"
syntax rdAs := " as " ident

/-- Apply the generated summary of the block at `h`'s program counter. -/
syntax (name := rdStep) "rd_step " ident (rdUsing)? (rdAs)? : tactic

/-- Apply generated block summaries from `h` until the program counter is `N`, or until none
applies. -/
syntax (name := rdRun) "rd_run " ident (" to " num)? (rdUsing)? (rdAs)? : tactic

def hintsOf (u : Option (TSyntax ``rdUsing)) : Array Term :=
  match u with
  | some stx => match stx with
    | `(rdUsing| using [$ts,*]) => ts.getElems
    | _ => #[]
  | none => #[]

def nameOf (h : Ident) (a : Option (TSyntax ``rdAs)) : Name :=
  match a with
  | some stx => match stx with
    | `(rdAs| as $x) => x.getId
    | _ => h.getId
  | none => h.getId

elab_rules : tactic
  | `(tactic| rd_step $h:ident $[$u]? $[$a]?) => withMainContext do
    let fv ← getFVarId h
    match ← step fv (nameOf h a) (hintsOf u) with
    | some _ => pure ()
    | none => throwError "rd_step: no block summary applies to {h.getId}"

elab_rules : tactic
  | `(tactic| rd_run $h:ident $[to $target]? $[$u]? $[$a]?) => withMainContext do
    let name := nameOf h a
    let hints := hintsOf u
    let mut fv ← getFVarId h
    let mut fuel := 500
    while fuel > 0 do
      fuel := fuel - 1
      let some (_, pc) ← withMainContext (do rdView? (← fv.getType)) | break
      if let some t := target then
        if (← withMainContext (pcValue? pc)) == some t.getNat then return
      match ← withMainContext (step fv name hints) with
      | some fv' => fv := fv'
      | none => break
    if let some t := target then
      let ty ← withMainContext (do instantiateMVars (← fv.getType))
      throwError "rd_run: stopped before pc {t.getNat}:{indentExpr ty}"

end FeProofs.RDTactic
