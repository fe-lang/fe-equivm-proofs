import Fe.Sonatina.Parse
import Fe.Sonatina.Steps.Record

/-!
# Reading a record of machine steps

`parseMachineSteps` reads the JSON of design §3.1: a section lowering's `machine_steps`
(sidecar version 5; absent or `null` in version 4, whose sidecars read unchanged).  Each
snapshot's text is one function as `FuncWriter` prints it, read by `Parse.parseModule`.  As for
the sidecar, the reader runs at elaboration only: a misread record is a different record, which
then fails to validate against the machine IR or is about other IR than the bytes.

- `machine_steps name "path" "section"` defines `name : Option MachineSteps` from a sidecar;
- `machine_steps_file name "path"` defines `name : MachineSteps` from a file holding the record
  alone (the hand-written tests).
-/

namespace Fe.Sonatina.Steps.Read

open Lean Fe.Sonatina.Parse

/-- A function snapshot: its text, of exactly one function of the name given, and the
    instruction ids of each block's lines, as many as the block has lines. -/
def parseFuncSnap (j : Json) : P FuncSnap := do
  let name ← j.getObjValAs? String "func"
  let m ← parseModule (← j.getObjValAs? String "text")
  let [f] := m.funcs | throw s!"snapshot of {name}: not one function"
  unless f.name == name do throw s!"snapshot of {name} holds {f.name}"
  let insts ← j.getObjValAs? (List (List Nat)) "insts"
  unless insts.length == f.blocks.length &&
      (insts.zip f.blocks).all (fun (ids, b) => ids.length == b.phis.length + b.body.length + 1) do
    throw s!"snapshot of {name}: instruction ids do not match its lines"
  return ⟨f, ← j.getObjValAs? Nat "func_ref", insts⟩

def parseStepKind (s : String) : P StepKind :=
  match StepKind.all.find? (·.name == s) with
  | some k => pure k
  | none => throw s!"unknown step kind {s}"

/-- A step's facts, each kept as its key and its JSON, unread; keys whose value is empty (`[]`
    or `null`, as every key of a step without facts is) are dropped. -/
def parseFacts : Json → P (List (String × String))
  | .null => pure []
  | .obj kvs => pure (kvs.toList.filterMap fun (k, v) => match v with
    | .null => none
    | .arr a => if a.isEmpty then none else some (k, v.compress)
    | v => some (k, v.compress))
  | j => throw s!"facts: expected an object, got {j.compress}"

def parseSummary (j : Json) : P Summary := do
  return { func := ← j.getObjValAs? String "func"
           noreturn := ← j.getObjValAs? Bool "noreturn"
           willReturn := ← j.getObjValAs? Bool "will_return"
           reads := ← j.getObjValAs? Bool "reads"
           writes := ← j.getObjValAs? Bool "writes"
           mutates := ← j.getObjValAs? Bool "mutates" }

/-- The record, as sidecar version 5 writes it (`sidecar-v5.md` of the export): no version key,
    a pass's `kind`, a function step named by its `out`. -/
def parseMachineSteps (j : Json) : P MachineSteps := do
  let lowered ← (← j.getObjValAs? (Array Json) "lowered").toList.mapM parseFuncSnap
  let passes ← (← j.getObjValAs? (Array Json) "passes").toList.mapM fun p => do
    let funcBehavior ← match ← p.getObjVal? "func_behavior" with
      | .null => pure none
      | b => some <$> ((← b.getArr?).toList.mapM parseSummary)
    let steps ← (← p.getObjValAs? (Array Json) "steps").toList.mapM fun st => do
      let funcs ← (← st.getObjValAs? (Array Json) "funcs").toList.mapM fun fs => do
        let out ← parseFuncSnap (← fs.getObjVal? "out")
        return ({ func := out.func.name
                  out
                  facts := ← parseFacts ((fs.getObjVal? "facts").toOption.getD .null) } : FuncStep)
      return ({ kind := ← parseStepKind (← st.getObjValAs? String "kind"), funcs } : Step)
    return ({ name := ← p.getObjValAs? String "kind", funcBehavior, steps } : Pass)
  return { version := 5, profile := ← j.getObjValAs? String "profile", lowered, passes }

/-- The record of section `name` of a sidecar, if its lowering has one. -/
def sectionSteps (text : String) (name : String) : P (Option MachineSteps) := do
  let json ← Json.parse text
  let sections ← json.getObjValAs? (Array Json) "sections"
  let some sec := sections.toList.find? fun s => (s.getObjValAs? String "name").toOption == some name
    | throw s!"no section {name}"
  match (sec.getObjVal? "lowering").toOption with
  | none | some .null => pure none
  | some low =>
    match (low.getObjVal? "machine_steps").toOption with
    | none | some .null => pure none
    | some r => some <$> parseMachineSteps r

end Fe.Sonatina.Steps.Read

namespace Fe.Sonatina.Steps

open Lean Elab Command

private def defineTerm (name : Ident) (type value : Expr) : CommandElabM Unit := do
  let decl := Declaration.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type, value
    hints := .abbrev
    safety := .safe }
  liftCoreM (addAndCompile decl)

/-- `machine_steps name "path" "section"`: define `name : Option MachineSteps`, the record of
    the section of the sidecar at `path`. -/
elab "machine_steps " name:ident path:str sec:str : command => do
  let text ← IO.FS.readFile path.getString
  match Read.sectionSteps text sec.getString with
  | .error e => throwError "{path.getString}: {e}"
  | .ok r => defineTerm name (toTypeExpr (Option MachineSteps)) (toExpr r)

/-- `machine_steps_file name "path"`: define `name : MachineSteps` from a file holding one
    record. -/
elab "machine_steps_file " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  match Json.parse text >>= Read.parseMachineSteps with
  | .error e => throwError "{path.getString}: {e}"
  | .ok r => defineTerm name (mkConst ``MachineSteps) (toExpr r)

end Fe.Sonatina.Steps
