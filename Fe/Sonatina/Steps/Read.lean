import Fe.Sonatina.Parse

/-!
# Reading a record of machine steps alone

A sidecar's records are read with the sidecar (`Parse.parseSidecar`, `Lowering.machineSteps`).
`machine_steps_file name "path"` defines `name : MachineSteps` from a file holding one record
alone, read as a sidecar's are (`Parse.parseMachineSteps`): the hand-written tests.
-/

namespace Fe.Sonatina.Steps

open Lean Elab Command

/-- `machine_steps_file name "path"`: define `name : MachineSteps` from a file holding one
    record. -/
elab "machine_steps_file " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  match Json.parse text >>= Parse.parseMachineSteps with
  | .error e => throwError "{path.getString}: {e}"
  | .ok r =>
    liftCoreM <| addAndCompile <| .defnDecl {
      name := (← getCurrNamespace) ++ name.getId
      levelParams := []
      type := mkConst ``MachineSteps
      value := toExpr r
      hints := .abbrev
      safety := .safe }

end Fe.Sonatina.Steps
