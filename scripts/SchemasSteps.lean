import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.Validate
import Fe.Sonatina.Steps.Read

/-!
`lake env lean --run scripts/SchemasSteps.lean [--mutate] <sidecar>...`: replay each version-5
record of each sidecar without checking, and run `checkSccpFold` and `checkKnownBitsSimplify` on
every function of every step of those kinds.  One line per function step:
`path  section  kind  func  ACCEPT|REJECT  reason`.  Interpreted, not kernel-evaluated.

With `--mutate`, each step's facts are made wrong first: every SCCP constant `c` becomes
`c + 1`, and the first known-bits claim claims every bit zero; steps whose facts are empty are
skipped.  Every mutated step should be rejected.
-/

open Fe.Sonatina Fe.Sonatina.Steps Fe.Sonatina.Steps.Schemas

/-- The step's facts made wrong (see the header), or `none` if it has none to change. -/
def mutate (F : StepFacts) : Option StepFacts :=
  match F.consts with
  | some (_ :: _) => some { F with consts := F.consts.map (·.map fun e => (e.1, e.2 + 1)) }
  | _ => match F.knownBits with
    | e :: es => some { F with knownBits := (e.1, 2 ^ 256 - 1, 0) :: es }
    | [] => none

def main (args : List String) : IO Unit := do
  let (mut', args) := match args with
    | "--mutate" :: rest => (true, rest)
    | rest => (false, rest)
  for path in args do
    let text ← IO.FS.readFile path
    match Parse.parseSidecar text with
    | .error e => IO.println s!"{path}\t-\t-\t-\tNOT READ\tsidecar: {e}"
    | .ok s =>
      for sec in s.sections do
        let some low := sec.lowering | pure ()
        match Read.sectionSteps text sec.name with
        | .error e => IO.println s!"{path}\t{sec.name}\t-\t-\tNOT READ\tmachine_steps: {e}"
        | .ok none => pure ()
        | .ok (some r) =>
          let mut M := r.module low.machine.structs
          let mut I := r.ids
          for p in r.passes do
            for st in p.steps do
              if st.kind == StepKind.sccpFold || st.kind == StepKind.knownBitsSimplify then
                for fs in st.funcs do
                  let res := match M.func? fs.func, readFacts fs.facts with
                    | none, _ => (false, "no such function")
                    | _, .error e => (false, s!"facts not read: {e}")
                    | some f, .ok F₀ =>
                      match (if mut' then mutate F₀ else some F₀) with
                      | none => (true, "skipped: no facts to mutate")
                      | some F =>
                      let ids := I.lookup fs.func
                      if st.kind == StepKind.sccpFold then
                        (checkSccpFold f ids fs.out F, (diagnoseSccpFold f ids fs.out F).getD "-")
                      else
                        (checkKnownBitsSimplify f ids fs.out F,
                          (diagnoseKnownBitsSimplify f ids fs.out F).getD "-")
                  IO.println s!"{path}\t{sec.name}\t{st.kind.name}\t{fs.func}\t{if res.1 then "ACCEPT" else "REJECT"}\t{res.2}"
              M := stepOut M st.funcs
              I := stepIds I st.funcs
