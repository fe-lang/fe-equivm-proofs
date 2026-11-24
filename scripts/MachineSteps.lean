import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read

/-!
`lake env lean --run scripts/MachineSteps.lean <kinds> <sidecar>...`: for each section of each
version-5 sidecar, whether `validateWith` with the comma-separated step kinds accepts its
record against its machine IR, and if not, the first step that fails and why.  Interpreted, not
kernel-evaluated: the verdicts are `validateWith`'s, the reasons a diagnostic replay of it.
-/

open Fe.Sonatina Fe.Sonatina.Steps

/-- The first reason `validateWith allowed r final` rejects, or `none` if it accepts. -/
def diagnose (allowed : List StepKind) (r : MachineSteps) (final : Module) : Option String := Id.run do
  let lowered := r.module final.structs
  if !lowered.machine then return some "lowered: not machine IR (malloc/alloca)"
  let mut M := lowered
  for p in r.passes do
    let mut i := 0
    for st in p.steps do
      if !allowed.contains st.kind then
        return some s!"{st.kind.name}: kind not allowed (pass {p.name}, step {i})"
      for fs in st.funcs do
        if !(checkStep st.kind p.funcBehavior M [fs]) then
          let why := if !fs.facts.isEmpty then "facts present"
            else if !fs.out.func.machine then "output not machine IR"
            else if (M.func? fs.func).isNone then "no such function"
            else "check rejects"
          return some s!"{st.kind.name}: {why} ({fs.func}, pass {p.name}, step {i})"
      M := stepOut M st.funcs
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
          let verdict := validateWith allowed r low.machine
          let reason := (diagnose allowed r low.machine).getD "-"
          let size := low.machine.funcs.foldl (fun n f => n + f.blocks.foldl
            (fun n b => n + b.phis.length + b.body.length + 1) 0) 0
          IO.println s!"{path}\t{sec.name}\t{if verdict then "ACCEPT" else "REJECT"}\t{reason}\tinsts={size}\tkinds={kindsPresent}"
