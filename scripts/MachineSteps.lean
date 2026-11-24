import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read

/-!
`lake env lean --run scripts/MachineSteps.lean <kinds> <sidecar>...`: for each section of each
version-5 sidecar, whether `validateWith` with the comma-separated step kinds accepts its
record against its machine IR, and if not, the first step that fails and why.  Interpreted, not
kernel-evaluated: the verdicts are `validateWith`'s, the reasons a diagnostic replay of it.
-/

open Fe.Sonatina Fe.Sonatina.Steps

/-- Why `checkCfgCleanup` rejects: its first failing part. -/
def cfgReason (O : Option (List Summary)) (f : Func) (ids : Option (List (List Nat)))
    (s : FuncSnap) : String := Id.run do
  let f' := s.func
  let X := CCtx.of O f f'
  let some ids := ids | return "no input ids"
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

/-- The first reason `validateWith allowed syms r final` rejects, or `none` if it accepts. -/
def diagnose (allowed : List StepKind) (syms : List String) (r : MachineSteps) (final : Module) :
    Option String := Id.run do
  let lowered := r.module final.structs
  if !lowered.machine then return some "lowered: not machine IR (malloc, alloca, aggregates, undef)"
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
          let why := if !fs.facts.isEmpty then "facts present"
            else if !fs.out.func.machine then "output not machine IR"
            else if !fs.out.wf M.sig syms then "output not well formed"
            else if (M.func? fs.func).isNone then "no such function"
            else if !((M.func? fs.func).any (sameSig · fs.out.func)) then "signature changed"
            else if st.kind == .edgeSplit && !((M.func? fs.func).any fun f =>
                (domTree f).valid f && ssa f (domTree f)) then "input dominators or SSA rejected"
            else if st.kind == .cfgCleanup then match M.func? fs.func with
              | some f => cfgReason p.funcBehavior f (I.lookup fs.func) fs.out
              | none => "no such function"
            else "check rejects"
          return some s!"{st.kind.name}: {why} ({fs.func}, pass {p.name}, step {i})"
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
          let kindsPresent := (r.kinds.eraseDups.map (·.name))
          let syms := sec.symbols.map (·.1)
          let verdict := validateWith allowed syms r low.machine
          let reason := (diagnose allowed syms r low.machine).getD "-"
          let size := low.machine.funcs.foldl (fun n f => n + f.blocks.foldl
            (fun n b => n + b.phis.length + b.body.length + 1) 0) 0
          IO.println s!"{path}\t{sec.name}\t{if verdict then "ACCEPT" else "REJECT"}\t{reason}\tinsts={size}\tkinds={kindsPresent}"
