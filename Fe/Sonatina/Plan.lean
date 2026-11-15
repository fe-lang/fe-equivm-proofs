import Fe.Sonatina.Interp

/-!
# Spill plans and the instrumented machine IR

The data of Sonatina's memory spills that the instrumented model (`Spill.lean`) and the checker
(`Check.lean`) share: a `SpillPlan` gives, per function, each spilled value, its word and the
points the bytes may reload it at; `Func.instrument` adds the stores the bytes make, as
`evm_mstore` statements; `Func.reloadLive` finds the spilled values reload-live at each point;
`SpillPlan.guard` is what each statement must leave as it was.  `Spill.lean` explains them.
-/

namespace Fe.Sonatina

/-- The successors of a terminator. -/
def Term.succs : Term → List Nat
  | .jump d => [d]
  | .br _ nz z => [nz, z]
  | .brTable _ d cases => d.toList ++ cases.map (·.2)
  | _ => []

/-! ## Spill plans -/

/-- A spilled value of a function's plan: the value, its word, and the points the bytes may
    reload it at.  A point is a block and a position in the block's statements in the
    instrumented function (`Func.instrument`): `(b, k)` is before statement `k` of block `b`,
    or before its terminator for `k` the number of statements. -/
structure Spill where
  value : Nat
  word : Nat
  reloads : List (Nat × Nat)
  deriving Repr, BEq, Inhabited

/-- The spilled values of a function. -/
abbrev FuncPlan := List Spill

/-- The spill plan of a section: the plan of each function that spills. -/
abbrev SpillPlan := List (String × FuncPlan)

/-- Each spilled value of the plan and its word. -/
def FuncPlan.words (p : FuncPlan) : List (Nat × Nat) := p.map fun sp => (sp.value, sp.word)

/-- The memory spills of a function in the lowering record: each value and its word. -/
def FuncHint.spillWords (h : FuncHint) : List (Nat × Nat) :=
  h.spills.filterMap fun (v, l) => match l with
    | .memory w => some (v, w)
    | _ => none

/-! ## The instrumented machine IR -/

/-- The store of an operand at word `w`, as a statement of the machine IR. -/
def spillStore (w : Nat) (o : Operand) : Stmt := ⟨[], .evm .mstore [.imm 256 w, o]⟩

/-- Function `f` with the stores of its spilled values at their `words`: after the statement
    that defines each, of each parameter at the start of the entry block, and at the end of a
    block that jumps to another, of each spilled phi of that block with its operand from the
    block, unless the operand is the phi itself or `undef`. -/
def Func.instrument (words : List (Nat × Nat)) (f : Func) : Func :=
  let store := fun (id : Nat) => (words.lookup id).map (spillStore · (.var id))
  let entry := f.blocks.head?.map (·.id)
  { f with blocks := f.blocks.map fun b =>
    let params := if entry == some b.id then f.params.filterMap (store ·.1) else []
    let body := b.body.flatMap fun s => s :: s.dsts.filterMap (store ·.1)
    let edge := match b.term with
      | .jump d => match f.block? d with
        | some sb => sb.phis.filterMap fun phi =>
          match words.lookup phi.dst, phi.incoming.find? (·.2 == b.id) with
          | some w, some (.var v, _) => if v == phi.dst then none else some (spillStore w (.var v))
          | some w, some (.imm bits k, _) => some (spillStore w (.imm bits k))
          | _, _ => none
        | none => []
      | _ => []
    { b with body := params ++ body ++ edge } }

/-- The module with the stores of each function the plan names (`Func.instrument`). -/
def Module.instrument (plan : SpillPlan) (m : Module) : Module :=
  if plan.isEmpty then m else
  { m with funcs := m.funcs.map fun f => match plan.lookup f.name with
    | some p => f.instrument p.words
    | none => f }

/-! ## Reload-liveness -/

/-- The values a statement of an instrumented function ends the reload-liveness of: those it
    defines, and a spilled value it stores at its own word. -/
def Stmt.kills (words : List (Nat × Nat)) (s : Stmt) : List Nat :=
  s.dsts.map (·.1) ++ match s.inst with
    | .evm .mstore [.imm _ w, .var v] => if words.contains (v, w) then [v] else []
    | _ => []

/-- The values the plan reloads at point `k` of block `b`. -/
def FuncPlan.reloadsAt (p : FuncPlan) (b k : Nat) : List Nat :=
  p.filterMap fun sp => if sp.reloads.contains (b, k) then some sp.value else none

/-- Sets of values at the points of a function: for each block, one per point, before each
    statement and before the terminator. -/
abbrev Live := List (Nat × List (List Nat))

/-- The set at point `k` of block `b`, empty if there is none. -/
def Live.at (L : Live) (b k : Nat) : List Nat := ((L.lookup b).bind (·[k]?)).getD []

/-- A set of values, in order and without repeats. -/
def normSet (xs : List Nat) : List Nat := xs.mergeSort.eraseDups

/-- One round of reload-liveness for block `b` of `f`: its sets, from those of its successors'
    entries in `L`.  Before the terminator: the values reloaded there and those live at a
    successor's entry other than its phis; before a statement: those reloaded there and those
    live after it that it does not kill. -/
def blockLive (f : Func) (p : FuncPlan) (L : Live) (b : Block) : List (List Nat) :=
  let out := b.term.succs.flatMap fun S => match f.block? S with
    | some sb => (L.at S 0).filter fun v => !sb.phis.any (·.dst == v)
    | none => []
  b.body.zipIdx.foldr (fun (s, k) acc =>
      normSet (p.reloadsAt b.id k ++ (acc.headD []).filter (!(s.kills p.words).contains ·))
        :: acc)
    [normSet (p.reloadsAt b.id b.body.length ++ out)]

/-- The values of `f` reload-live under `p` at each point: some reload of the value is
    reachable from the point before the value is defined or stored again.  Rounds of
    `blockLive` from nothing, until they change nothing, at most one more than `f` has
    blocks; `Func.liveClosed` tests the result. -/
def Func.reloadLive (f : Func) (p : FuncPlan) : Live :=
  go (f.blocks.length + 1) (f.blocks.map fun b => (b.id, []))
where
  go : Nat → Live → Live
    | 0, L => L
    | n + 1, L =>
      let L' := f.blocks.map fun b => (b.id, blockLive f p L b)
      if L' == L then L else go n L'

/-- The sets `L` satisfy the equations of reload-liveness of `f` under `p`: at each point of
    each block, the values reloaded there; before each statement, the values live after it it
    does not kill; before the terminator, the values live at a successor's entry other than its
    phis. -/
def Func.liveClosed (f : Func) (p : FuncPlan) (L : Live) : Bool :=
  f.blocks.all fun b =>
    (List.range (b.body.length + 1)).all
      (fun k => (p.reloadsAt b.id k).all (L.at b.id k).contains) &&
    b.body.zipIdx.all (fun (s, k) => (L.at b.id (k + 1)).all fun v =>
      (s.kills p.words).contains v || (L.at b.id k).contains v) &&
    b.term.succs.all fun S => match f.block? S with
      | some sb => (L.at S 0).all fun v =>
        sb.phis.any (·.dst == v) || (L.at b.id b.body.length).contains v
      | none => true

/-! ## The instrumented model -/

/-- The words a plan protects across each statement of each block of the instrumented function
    `f`: those of the values reload-live after the statement that it does not kill. -/
def FuncPlan.guardOf (p : FuncPlan) (f : Func) : List (Nat × List (List Nat)) :=
  let L := f.reloadLive p
  f.blocks.map fun b => (b.id, b.body.zipIdx.map fun (s, k) =>
    ((L.at b.id (k + 1)).filter (!(s.kills p.words).contains ·)).filterMap (p.words.lookup ·))

/-- The guard of a plan over the instrumented module `m`: `FuncPlan.guardOf` of each function
    the plan names, nothing for the others. -/
def SpillPlan.guard (plan : SpillPlan) (m : Module) : Guard :=
  plan.filterMap fun (name, p) => (m.func? name).map fun f => (name, p.guardOf f)

/-- The module to run under a plan and the guard to run it under. -/
def SpillPlan.prepare (plan : SpillPlan) (m : Module) : Module × Guard :=
  let m' := m.instrument plan
  (m', plan.guard m')

/-- The value a statement of instrumented block `b` stores at its word, if it is a spill
    store: of a spilled value, or of a spilled phi of the block `b` jumps to. -/
def storedValue (f : Func) (words : List (Nat × Nat)) (b : Block) (s : Stmt) :
    Option (Nat × Nat) :=
  match s.inst with
  | .evm .mstore [.imm _ w, o] =>
    (match o with
      | .var v => if words.contains (v, w) then some v else phiAt w o
      | _ => phiAt w o).map (w, ·)
  | _ => none
where
  phiAt (w : Nat) (o : Operand) : Option Nat :=
    match b.term with
    | .jump d => (f.block? d).bind fun sb => (sb.phis.find? fun phi =>
        words.contains (phi.dst, w) &&
          (phi.incoming.find? (·.2 == b.id)).any (·.1 == o)).map (·.dst)
    | _ => none

end Fe.Sonatina
