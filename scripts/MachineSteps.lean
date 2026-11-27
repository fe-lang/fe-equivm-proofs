import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read

/-!
`lake lean scripts/MachineSteps.lean -- --run scripts/MachineSteps.lean <kinds> <sidecar>...`
(`lake lean` locates each module, as this package and fe-spec share the root `Fe`; `--run`
takes the file after it): for each section of each version-5 sidecar, whether `validateWith`
with the comma-separated step kinds accepts its record against its machine IR, and if not, the
first step that fails and why.  Interpreted, not kernel-evaluated: the verdicts are
`validateWith`'s, the reasons a diagnostic replay of it.  `validate` takes the proved kinds
only (`StepKind.proved`); naming others here measures their unproved checkers.

With `steps` for the kinds: every function step of every section, its kind and its check's
verdict (`ACCEPT`, `REJECT` with the reason, or `UNPROVED` for a kind with no checker), and every
pass whose summary table fails (`SUMMARIES`); the replay goes on past rejected steps, trusting
the record.
-/

open Fe.Sonatina Fe.Sonatina.Steps

/-- Why `checkCfgCleanup` rejects: its first failing part. -/
def cfgReason (O : Option (List Summary)) (f : Func) (ids : Option (List (List Nat)))
    (s : FuncSnap) : String := Id.run do
  let f' := s.func
  let X := CCtx.of O f f'
  if ids.isNone then return "no input ids"
  let (some e, some e') := (f.blocks.head?, f'.blocks.head?) | return "no entry"
  if e.id != e'.id then return "entry changed"
  if f'.params != f.params then return "parameters changed"
  if !f'.machine then return "output not machine IR"
  if !((domTree f).valid f && ssa f (domTree f)) then return "input dominators or SSA rejected"
  if !X.phisDefOk f then return "a deleted phi is a value of the output"
  if !X.sigmaOk then return "trivial phi"
  for ob in f'.blocks do
    if !X.blockOk ob then
      let ch := X.chainFrom X.fuel ob.id
      let part := match X.B.find? ob.id, ch.getLast? >>= X.B.find? with
        | some c0, some cm =>
          if !X.linksOk ch then "chain links"
          else if !ob.phis.all (fun φ' => c0.phis.any fun φ => φ.dst == φ'.dst && φ.ty == φ'.ty)
          then "phis"
          else if !decide (ob.body = (X.chainBody ch).map (Stmt.mapOps X.hat)) then
            s!"statements (chain {ch})"
          else if (trimIdx O cm).isSome then "trim terminator"
          else "terminator slots"
        | none, _ => "no input block"
        | _, none => "chain end"
      return s!"block {ob.id}: {part}"
  return "instruction ids"

/-- The kinds with a checker. -/
def checked : List StepKind := StepKind.proved

/-- Why `checkCoalesce` rejects: the first block that fails. -/
def kcReason (f f' : Func) : String := Id.run do
  let X := KCtx.of f f'
  if !(X.T.valid f && ssa f X.T) then return "input dominators or SSA rejected"
  for (b', b) in f'.blocks.zip f.blocks do
    if !X.blockOk b' b then return s!"block {b.id}"
  if !unusedOk' f f' then return "deleted value used"
  return "function"

/-- Why `checkLowerSwitches` rejects: its first failing part. -/
def lsReason (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) : String := Id.run do
  let f' := s.func
  let X := LSCtx.of f f'
  if ids.isNone then return "no input ids"
  let (some e, some e') := (f.blocks.head?, f'.blocks.head?) | return "no entry"
  if e.id != e'.id then return "entry changed"
  if f'.params != f.params then return "parameters changed"
  if !((domTree f).valid f && ssa f (domTree f)) then return "input dominators or SSA rejected"
  for b' in f'.blocks do
    if !X.blockOk b' then
      let part := match X.B.find? b'.id with
        | some bb =>
          if !X.phisOk b'.id b'.phis bb.phis then "phis"
          else if b'.term == bb.term then "statements or targets"
          else "switch tree"
        | none => "new block"
      return s!"block {b'.id}: {part}"
  if !X.shapeOk f f' then return "tree shape (new blocks, block order, new values)"
  return "instruction ids"

/-- Why `checkStep` rejects a function step. -/
def stepWhy (k : StepKind) (syms : List String) (O : Option (List Summary)) (M : Module)
    (I : IdTab) (fs : FuncStep) : String :=
  if !checked.contains k then "no checker"
  else if k == .sccpFold || k == .knownBitsSimplify then match M.func? fs.func with
    | some f => ((if k == .sccpFold then Schemas.diagnoseSccpFold else
        Schemas.diagnoseKnownBitsSimplify) f (I.lookup fs.func) fs.out fs.facts).getD "check rejects"
    | none => "no such function"
  else if k == .adce then match M.func? fs.func with
    | some f => if !fs.out.wf M.sig syms then "output not well formed"
        else adceWhy f (I.lookup fs.func) fs.out fs.facts
    | none => "no such function"
  else if !noFacts fs.facts then "facts present"
  else if !fs.out.func.machine then "output not machine IR"
  else if !fs.out.wf M.sig syms then "output not well formed"
  else if (M.func? fs.func).isNone then "no such function"
  else if !((M.func? fs.func).any (sameSig · fs.out.func)) then "signature changed"
  else if k == .edgeSplit && !((M.func? fs.func).any fun f =>
      (domTree f).valid f && ssa f (domTree f)) then "input dominators or SSA rejected"
  else if k == .cfgCleanup then match M.func? fs.func with
    | some f => cfgReason O f (I.lookup fs.func) fs.out
    | none => "no such function"
  else if k == .lowerSwitches then match M.func? fs.func with
    | some f => lsReason f (I.lookup fs.func) fs.out
    | none => "no such function"
  else if k == .coalesceCopies then match M.func? fs.func with
    | some f => kcReason f fs.out.func
    | none => "no such function"
  else "check rejects"

/-- Every function step's verdict, the replay trusting the record past rejected steps. -/
def stepReport (syms : List String) (r : MachineSteps) (final : Module) : List String := Id.run do
  let mut M := r.module final.structs
  let mut I := r.ids
  let mut out := []
  for p in r.passes do
    if !SummariesOk p.funcBehavior M then out := out ++ [s!"{p.name}\t-\t-\tSUMMARIES"]
    for st in p.steps do
      for fs in st.funcs do
        let v := if !checked.contains st.kind then "UNPROVED"
          else if checkStep st.kind syms p.funcBehavior M I [fs] then "ACCEPT"
          else s!"REJECT\t{stepWhy st.kind syms p.funcBehavior M I fs}"
        out := out ++ [s!"{p.name}\t{st.kind.name}\t{fs.func}\t{v}"]
      M := stepOut M st.funcs
      I := stepIds I st.funcs
  return out

/-- The first reason `validateWith allowed syms r final` rejects, or `none` if it accepts. -/
def diagnose (allowed : List StepKind) (syms : List String) (r : MachineSteps) (final : Module) :
    Option String := Id.run do
  let lowered := r.module final.structs
  if !lowered.machine then return some "lowered: not machine IR (malloc, alloca, aggregates)"
  for f in lowered.funcs do
    if !f.wf lowered.sig syms then return some s!"lowered: {f.name} not well formed"
  if !r.lowered.all FuncSnap.idsOk then return some "lowered: instruction ids do not match"
  let mut M := lowered
  let mut I := r.ids
  for p in r.passes do
    if !SummariesOk p.funcBehavior M then
      return some s!"summaries: a noreturn claim fails against the pass input (pass {p.name})"
    let mut i := 0
    for st in p.steps do
      if !allowed.contains st.kind then
        return some s!"{st.kind.name}: kind not allowed (pass {p.name}, step {i})"
      for fs in st.funcs do
        if !(checkStep st.kind syms p.funcBehavior M I [fs]) then
          return some s!"{st.kind.name}: {stepWhy st.kind syms p.funcBehavior M I fs} ({fs.func}, pass {p.name}, step {i})"
      M := stepOut M st.funcs
      I := stepIds I st.funcs
      i := i + 1
  if !sameFuncs M final then return some "final: composed module differs from machine_ir"
  return none

def main (args : List String) : IO Unit := do
  let kinds :: files := args | throw (IO.userError "usage: <kinds> <sidecar>...")
  let allowed := (kinds.splitOn ",").filterMap fun k => StepKind.all.find? (·.name == k)
  for path in files do
    let text ← IO.FS.readFile path
    match Parse.parseSidecar text with
    | .error e => IO.println s!"{path}\tNOT READ\tsidecar: {e}"
    | .ok s =>
      for sec in s.sections do
        let some low := sec.lowering | IO.println s!"{path}\t{sec.name}\tNO LOWERING"
        match Read.sectionSteps text sec.name with
        | .error e => IO.println s!"{path}\t{sec.name}\tNOT READ\tmachine_steps: {e}"
        | .ok none => IO.println s!"{path}\t{sec.name}\tNO RECORD"
        | .ok (some r) =>
          if kinds == "steps" then
            for l in stepReport (sec.symbols.map (·.1)) r low.machine do
              IO.println s!"{path}\t{sec.name}\t{l}"
            continue
          let kindsPresent := (r.kinds.eraseDups.map (·.name))
          let syms := sec.symbols.map (·.1)
          let verdict := validateWith allowed syms r low.machine
          let reason := (diagnose allowed syms r low.machine).getD "-"
          let size := low.machine.funcs.foldl (fun n f => n + f.blocks.foldl
            (fun n b => n + b.phis.length + b.body.length + 1) 0) 0
          IO.println s!"{path}\t{sec.name}\t{if verdict then "ACCEPT" else "REJECT"}\t{reason}\tinsts={size}\tkinds={kindsPresent}"
