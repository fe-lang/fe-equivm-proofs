import Reasoning.Reach
import Reasoning.JumpDest
import FeProofs.Common.Calls
import FeProofs.Common.Basic
import FeProofs.Common.Fallback

/-!
# Chaining generated block summaries

`scripts/generate_rd_blocks.py` (EquiVM) emits one lemma per basic block, named after the
bytecode constant: for `…feXBytecode` the block at `pc` is `feXBlocks.feX_block_<pc>`, with
`_taken`/`_fallthrough` variants for a conditional jump (and `_static` twins, from
`scripts/static_twins.py`, that halt at a state change when `ee.perm = false`), and for creation code
(`feXCreationBytecode ++ tail`) it is `feXCreationBlocks.feXCreation_block_<pc>`.

* `rd_step h` applies the summary of the block at `h`'s program counter to `h : RD code …`,
  replacing `h` with the summary's conclusion and unfolding its `_stack`/`_memory` definitions.
* `rd_run h to N` repeats `rd_step` until the program counter is `N` (or, without `to`, until no
  block applies or the run ends in `RDrev`/`RDret`/`RDstatic`).

Side conditions are discharged automatically: stack bounds by `simp`/`omega`, jump destinations by
`jump_dest`, and branch conditions and other hypotheses by a `using [t, …]` term (as a proof, up to
`¬¬`, or as equations to rewrite with, one or all in order, before `decide`), local hypotheses,
`decide`, `simp` or `omega`. Local hypotheses are tried at reducible transparency first, with
filtered default-transparency search after the other solvers. At a conditional jump the taken
branch is tried first; when neither condition can be discharged the step fails (`rd_step`) or the
run stops there (`rd_run`). A program counter written as a closed sum, such as
`UInt256.ofNat 891 + ⟨1⟩`, is normalized first.
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
  let code ← whnfR (← instantiateMVars code)
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

/-- `UInt256.toNat` of a closed word literal (`UInt256.ofNat n`, `⟨n⟩`, or a sum of those) is a
`Nat` literal, by evaluation. Normalizes the offsets and lengths in memory terms, which block
summaries write in either form, so that lemmas stated with plain `Nat` offsets apply. -/
simproc_decl reduceUInt256ToNat (UInt256.toNat _) := fun e => do
  let_expr Ethereum.UInt256.toNat x ← e | return .continue
  let some n ← pcValue? x | return .continue
  return .done { expr := mkNatLit n }

/-- A word literal `⟨n⟩` (`UInt256.mk` of a `Fin` literal) is `UInt256.ofNat n`: the two spellings
block summaries and library lemmas use for the same constant. -/
simproc_decl reduceUInt256Mk (Ethereum.UInt256.mk _) := fun e => do
  let_expr Ethereum.UInt256.mk v ← e | return .continue
  let_expr OfNat.ofNat _ n _ ← v | return .continue
  unless n.rawNatLit?.isSome do return .continue
  return .done { expr := mkApp (mkConst ``Ethereum.UInt256.ofNat) (mkNatLit n.rawNatLit?.get!) }

/-- Rewrites `UInt256.toNat` of word literals to `Nat` literals (`reduceUInt256ToNat`). -/
macro "u256_lits" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [reduceUInt256ToNat] $(loc)?)

/-- `decide`, only on a goal without local variables (a symbolic goal could take long to fail). -/
elab "decide_closed" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if ty.hasFVar || ty.hasMVar then throwError "decide_closed: goal is not closed"
  evalTactic (← `(tactic| decide))

/-- Run `x` with at most `budget` heartbeats (raw units, as `IO.getNumHeartbeats` counts them);
on running out, restore the state and return `none`. Failing comparisons between unrelated terms
can unfold the jump-destination table or symbolic word arithmetic for a very long time. -/
def withBudgetM? (budget : Nat) (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  let now ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (some <$> withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget, initHeartbeats := now }) x)
    (fun _ => do s.restore; return none)

/-- `withBudgetM?` for tactics. -/
def withBudgetT? (budget : Nat) (x : TacticM α) : TacticM (Option α) := do
  let s ← saveState
  let now ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (some <$> withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget, initHeartbeats := now }) x)
    (fun _ => do s.restore; return none)

/-- Heartbeat budget of one side-goal attempt. -/
def attemptBudget : Nat := 3000000

/-- Whether `e` mentions a constant whose last name component is `n`. -/
def mentions (e : Expr) (n : String) : Bool :=
  (e.find? fun x => x.isConst && x.constName!.lastComponentAsString == n).isSome

/-- A cheap filter for default-transparency context search: the same relation, and for equality
the same carrier type. Compare negations by their propositions, without unfolding word arithmetic.
Other unfoldings can be requested explicitly with a `using` hint. -/
partial def sameGoalKind (t ty : Expr) : MetaM Bool := withReducible do
  let t ← whnf t
  let ty ← whnf ty
  match t, ty with
  | .forallE _ a b _, .forallE _ c d _ =>
    return b.isConstOf ``False && d.isConstOf ``False && (← sameGoalKind a c)
  | _, _ =>
    if t.isAppOfArity ``Eq 3 && ty.isAppOfArity ``Eq 3 then
      isDefEq (t.getArg! 0) (ty.getArg! 0)
    else
      return t.getAppFn == ty.getAppFn

/-- Close a side goal of a block summary. Search hints and local hypotheses at reducible
transparency first, then try explicit hints and the specialized solvers. Default-transparency
context search is a last resort, restricted to facts of the same kind, within `attemptBudget`.
Unrelated facts must not exhaust budgets before a trivial goal or a useful hint is reached. -/
def discharge (g : MVarId) (hints : Array (Term × Option (Expr × Expr))) : TacticM Bool := do
  let ty ← instantiateMVars (← g.getType)
  let gs ← getGoals
  -- elaboration errors must fail the attempt, not close the goal with `sorry`
  let tryTac (tac : TacticM Unit) (budget := attemptBudget) : TacticM Bool := do
    let s ← saveState
    try
      setGoals [g]
      let some () ← (if budget == 0 then some <$> Term.withoutErrToSorry tac
        else withBudgetT? budget (Term.withoutErrToSorry tac)) | s.restore; return false
      if (← getUnsolvedGoals).isEmpty && !(← instantiateMVars (mkMVar g)).hasSorry then
        setGoals gs; return true
      s.restore; return false
    catch _ => s.restore; return false
  let isJump := mentions ty "D_J"
  let fits (t : Expr) : Bool :=
    mentions t "D_J" == isJump && !(t.isAppOf ``RD || t.isAppOf ``RDrev || t.isAppOf ``RDret)
  -- hints and hypotheses as proofs
  let elabd := hints.filterMap fun (stx, et) => et.map fun (e, t) => (stx, e, t)
  let mut cands : Array (Expr × Expr) :=
    elabd.filterMap fun (_, e, t) => if fits t then some (e, t) else none
  for d in (← g.getDecl).lctx do
    let t ← instantiateMVars d.type
    if !d.isImplementationDetail && fits t then cands := cands.push (d.toExpr, t)
  -- reducible transparency: at default transparency a mismatch can unfold word arithmetic for long
  for (e, t) in cands do
    let s ← saveState
    if ← withReducible (isDefEq t ty) then
      g.assign e; return true
    s.restore
  -- A known opposite condition rules out this block. Do not exhaust the hint solvers trying
  -- to prove it. Only compare fully determined propositions, without assigning goal parameters.
  if !ty.hasMVar then
    let negTy ← withReducible (matchNot? ty)
    for (_, t) in cands do
      if !t.hasMVar then
        let s ← saveState
        let opposite ← withReducible do
          if let some p := negTy then
            if ← isDefEq t p then return true
          if let some p ← matchNot? t then isDefEq ty p else pure false
        s.restore
        if opposite then return false
  -- stack bounds, before any default-transparency comparison
  let isStack := mentions ty "length"
  if isStack then
    for tac in [← `(tactic| (simp; done)), ← `(tactic| omega), ← `(tactic| (simp; omega))] do
      if ← tryTac (evalTactic tac) then return true
  -- explicit hints at default transparency, unfiltered: they may need definitions unfolded
  for (_, e, t) in elabd do
    if fits t then
      let s ← saveState
      if (← withBudgetM? attemptBudget (isDefEq t ty)).getD false then
        g.assign e; return true
      s.restore
  if isJump then return ← tryTac (evalTactic (← `(tactic| jump_dest))) (budget := 0)
  if isStack then return false
  -- branch conditions: hints that need the goal to elaborate, decide, or rewrite with the hints first
  for (stx, et) in hints do
    if et.isNone then
      if ← tryTac (evalTactic (← `(tactic| exact $stx))) then return true
  if ← tryTac (evalTactic (← `(tactic| decide_closed))) then return true
  let eqs := elabd.filter fun (_, _, t) => t.isAppOf ``Eq && fits t
  for (stx, _, _) in eqs do
    if ← tryTac (evalTactic (← `(tactic| (rw [$stx:term]; decide_closed)))) then return true
  if eqs.size > 1 then
    let rws ← eqs.mapM fun (stx, _, _) => `(Lean.Parser.Tactic.rwRule| $stx:term)
    if ← tryTac (evalTactic (← `(tactic| (rw [$rws,*]; decide_closed)))) then return true
  -- an equation whose literals are written `⟨n⟩`, or `a = c` against `a ≠ b`
  for (stx, _, _) in eqs do
    if ← tryTac (evalTactic (← `(tactic| (have h := $stx; simp only [reduceUInt256Mk] at h; rw [h]; decide_closed))))
    then return true
    if ← tryTac (evalTactic (← `(tactic| exact ne_of_eq_of_ne $stx (by decide)))) then return true
  -- all hints together, each normalized (`calldataWord` unfolded, literals in one spelling), as
  -- `simp` rewrite rules: those that occur are used, the rest ignored
  let facts := elabd.filter fun (_, _, t) => fits t
  if !facts.isEmpty then
    let names := (List.range facts.size).toArray.map fun i => mkIdent (Name.mkSimple s!"rd_hint{i}")
    let args ← names.mapM fun nm => `(Lean.Parser.Tactic.simpLemma| $nm:ident)
    let normalized : TacticM Unit := do
      for ((stx, _, _), nm) in facts.zip names do
        evalTactic (← `(tactic| have $nm := $stx))
        evalTactic (← `(tactic|
          try simp only [calldataWord, reduceUInt256Mk, reduceUInt256ToNat] at $nm:ident))
      evalTactic (← `(tactic| simp only [reduceUInt256Mk, reduceUInt256ToNat, $args,*]))
      evalTactic (← `(tactic| all_goals decide_closed))
    if ← tryTac normalized then return true
  for (stx, _, t) in elabd do
    if fits t then
      if ← tryTac (evalTactic (← `(tactic| exact Classical.not_not.mp $stx))) then
        return true
  -- A local fact can still need ordinary definitions unfolded, e.g. `w ≠ ⟨0⟩` against
  -- `w ≠ UInt256.ofNat 0`. Do this only after the cheap solvers and goal-dependent hints.
  for d in (← g.getDecl).lctx do
    if !d.isImplementationDetail then
      let t ← instantiateMVars d.type
      let s ← saveState
      if fits t && (← sameGoalKind t ty) &&
          (← withBudgetM? attemptBudget (isDefEq t ty)).getD false then
        g.assign d.toExpr; return true
      s.restore
  return false

/-- Elaborate the `using` terms once per step, each with its proof and type; a term that needs
the goal to elaborate (such as a `by` block) is kept as syntax. -/
def elabHints (hints : Array Term) : TacticM (Array (Term × Option (Expr × Expr))) :=
  hints.mapM fun (stx : Term) => do
    let s ← saveState
    try
      let e ← Term.withoutErrToSorry (Term.elabTerm stx none)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasExprMVar then s.restore; return (stx, none)
      let t ← instantiateMVars (← inferType e)
      return (stx, some (e, t))
    catch _ => s.restore; return (stx, none)

/-- Apply the block summary `blk` to the hypothesis `h`; on success return the new proof and
its type. -/
def applyBlock (h : FVarId) (blk : Name) (hints : Array (Term × Option (Expr × Expr))) :
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
  for blk in [base, base.appendAfter "_taken", base.appendAfter "_fallthrough",
      base.appendAfter "_static"] do
    if (← getEnv).contains blk then
      if let some (val, vty) ← withMainContext (do applyBlock h blk (← elabHints hints)) then
        return some (← install h name blk val vty)
  return none

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

/-- After an external call, `rd : RD code … ((if z then ⟨1⟩ else ⟨0⟩) :: …) … out …` stands where
Fe checks the success flag and then `RETURNDATASIZE < 32`. `rd_checked rd z out as hrev hout`
splits on `hout : z = true ∧ 32 ≤ out.size`: first the failing case, with
`hrev : RDrev code g s0` (both checks' revert paths run by `rd_run`), then the passing case,
with `z := true`, `hout : 32 ≤ out.size` and `rd` run past the checks (to `N` with `to N`). The
call's `out.size < UInt256.size` must be a hypothesis. -/
syntax (name := rdChecked) "rd_checked " ident ident ident " as " ident ident (" to " num)? : tactic

elab_rules : tactic
  | `(tactic| rd_checked $rd $z $out as $hrev $hout $[to $n]?) => do
    let g :: rest ← getGoals | throwError "rd_checked: no goals"
    setGoals [g]
    evalTactic (← `(tactic| by_cases $hout:ident : $z = true ∧ 32 ≤ ($out).size))
    let [gpos, gneg] ← getGoals | throwError "rd_checked: unexpected goals"
    setGoals [gneg]
    -- `hrev : RDrev code g s0`, with `code g s0` read off `rd`
    let (code, gas, s0) ← gneg.withContext do
      let some d := (← getLCtx).findFromUserName? rd.getId | throwError "rd_checked: no {rd.getId}"
      let t ← whnfR (← instantiateMVars d.type)
      unless t.isAppOfArity ``RD 12 do throwError "rd_checked: {rd.getId} is not an RD hypothesis"
      return (← Term.exprToSyntax (t.getArg! 0), ← Term.exprToSyntax (t.getArg! 2),
        ← Term.exprToSyntax (t.getArg! 3))
    withMainContext <| evalTactic (← `(tactic| have $hrev : RDrev $code $gas $s0 := by
      cases $z:ident
      · rd_run $rd; exact $rd
      · rd_run $rd using [lt32_size_word_ne (Nat.lt_of_not_le fun h => $hout ⟨rfl, h⟩)]
        exact $rd))
    let negGoals ← getGoals
    setGoals [gpos]
    -- an unhygienic `rfl`, which `rcases` reads as substitution
    let rflId := mkIdent `rfl
    evalTactic (← `(tactic| obtain ⟨$rflId:ident, $hout:ident⟩ := $hout))
    match n with
    | some n => evalTactic (← `(tactic| rd_run $rd to $n using [lt32_size_word $hout ‹_›]))
    | none => evalTactic (← `(tactic| rd_run $rd using [lt32_size_word $hout ‹_›]))
    setGoals (negGoals ++ (← getGoals) ++ rest)


/-- Closes a selector arm reached with nonzero call value: Fe checks the call value at the arm's
entry and reverts, and the Stele body's non-payable guard reverts too.  `hd` is the dispatch fact:
`selectorDispatchMsg … = some t` for a contract with a fallback, `dispatchMsg … = some t` otherwise. -/
macro "nonpayable_revert " rd:ident hcode:term:max hd:term:max hwv:term:max : tactic =>
  `(tactic| (rd_run $rd using [$hwv, Reasoning.Theory.isZero_eq_zero_of_ne $hwv]
             first
               | exact Reasoning.Reach.RDrev.reEquivDispatchedRevertSel $hcode $rd $hd
                   fun _ => Reasoning.Theory.bodyReverts_nonPayable
                     (by simp only [Reasoning.Theory.initState]; exact $hwv)
               | exact Reasoning.Reach.RDrev.reEquivDispatchedRevert $hcode $rd $hd
                   fun _ => Reasoning.Theory.bodyReverts_nonPayable
                     (by simp only [Reasoning.Theory.initState]; exact $hwv)))

end FeProofs.RDTactic
