import Fe.Sonatina.H.Syntax
import Fe.Sonatina.Parse

/-!
# Reading the handover dialect

`parseModule` reads a section's `source_ir` in the text form Sonatina's `ModuleWriter` prints,
with the machine IR's reader (`Fe/Sonatina/Parse.lean`) for every line that reader knows and
the instructions of `H/Syntax.lean` it does not.  An instruction outside both is an error.
Global declarations (constant data, which `sym_addr $g` locates in the code) and enum type
declarations (lowered before this dialect) are skipped, as the machine IR's reader skips them.
The header's fixed memory limit is read as the machine IR's reader reads it, and kept
(`HModule.fixedLimit`).

Each `gep` is given the type its base operand is declared with, from the function's parameters,
phis and statement results.

`objectOfSidecar` reads the handover object of a sidecar's JSON: each section's `source_ir`, its
entry function from the object declarations, and its symbol table.  The machine IR's reader
keeps a section's IR only where it is in its own subset (`Lowering.source`), which `source_ir`
never is (it has `gep`), so this reader reads the JSON itself.
-/

namespace Fe.Sonatina.H.Parse

open Lean Fe.Sonatina Fe.Sonatina.Parse

/-- An instruction from its name and the words after it: one of this dialect's own, else the
    machine IR reader's.  A `gep`'s base type is filled in later (`annotate`). -/
def parseInst (name : String) (args : List String) : P HInst := do
  match name, args with
  | "gep", base :: idxs@(_ :: _) =>
    return .gep .unit (← parseOperand base) (← operands idxs)
  | "evm_mload_bytes", [a, l] => return .mloadBytes (← parseOperand a) (← parseOperand l)
  | "trunc_nuw", [a, ty] => return .truncNuw (← parseOperand a) (← parseTy ty)
  | _, _ => return .base (← Fe.Sonatina.Parse.parseInst name args)

/-- A terminator from its name and the words after it, or `none` if the name is not one. -/
def parseTerm? (name : String) (args : List String) : P (Option HTerm) := do
  match name, args with
  | "evm_return_code", [o, l] => return some (.returnCode (← parseOperand o) (← parseOperand l))
  | "evm_revert_word", [s, w] => return some (.revertWord (← parseOperand s) (← parseOperand w))
  | _, _ => return (← Fe.Sonatina.Parse.parseTerm? name args).map .base

/-- A block in the making: its phis and statements so far, last first. -/
structure OpenBlock where
  id : Nat
  phis : List Phi := []
  body : List HStmt := []

/-- Add a statement line, without its `;`, to the block; a terminator closes it. -/
def statement (b : OpenBlock) (line : String) : P (OpenBlock ⊕ HBlock) := do
  let ws := tokens line
  let (dsts, rest) ← match ws.span (· != "=") with
    | (_, []) => pure ([], ws)
    | (lhs, _ :: rhs) =>
      let decls := lhs.filter fun w => w != "(" && w != ")" && w != ","
      pure (← decls.mapM parseDecl, rhs)
  let name :: args := rest | throw s!"empty statement: {line}"
  if name == "phi" then
    let [(dst, ty)] := dsts | throw s!"phi defines one value: {line}"
    unless b.body.isEmpty do throw s!"phi after a statement: {line}"
    return .inl { b with phis := ⟨dst, ty, ← pairs args⟩ :: b.phis }
  if dsts.isEmpty then
    if let some term ← parseTerm? name args then
      return .inr ⟨b.id, b.phis.reverse, b.body.reverse, term⟩
  return .inl { b with body := ⟨dsts, ← parseInst name args⟩ :: b.body }

/-- The declared type of each value of the function: parameters, phis, statement results. -/
def declTypes (params : List (Nat × Ty)) (blocks : List HBlock) : List (Nat × Ty) :=
  params ++ blocks.flatMap fun b =>
    b.phis.map (fun p => (p.dst, p.ty)) ++ b.body.flatMap (·.dsts)

/-- Give each `gep` the type its base is declared with; an immediate base has its integer
    type, which no `gep` accepts. -/
def annotate (params : List (Nat × Ty)) (blocks : List HBlock) : P (List HBlock) := do
  let decls := declTypes params blocks
  blocks.mapM fun b => do
    let body ← b.body.mapM fun s => match s.inst with
      | .gep _ base idxs => do
        let ty ← match base with
          | .var id => match decls.lookup id with
            | some ty => pure ty
            | none => throw s!"gep of the undeclared value v{id}"
          | .imm bits _ => pure (.int bits)
        return { s with inst := .gep ty base idxs }
      | _ => pure s
    return { b with body }

/-- A module from the lines of a section's `source_ir`, with the fixed memory limit its header
    declares (`Fe.Sonatina.Parse.header`). -/
def parseLines (lines : List String) : P HModule := do
  let (fixedLimit, lines) ← Fe.Sonatina.Parse.header lines
  let mut structs : List (String × List Ty) := []
  let mut funcs : List HFunc := []
  let mut func : Option (String × List (Nat × Ty) × List Ty × List HBlock) := none
  let mut block : Option OpenBlock := none
  let mut inEnum := false
  for line in lines do
    if inEnum then
      inEnum := line != "};"
    else if let some (name, params, rets, blocks) := func then
      if line == "}" then
        if block.isSome then throw s!"block of {name} has no terminator"
        funcs := ⟨name, params, rets, ← annotate params blocks.reverse⟩ :: funcs
        func := none
      else if line.endsWith ":" then
        if block.isSome then throw s!"block of {name} has no terminator"
        block := some { id := ← blockId (line.dropEnd 1).toString }
      else
        let some b := block | throw s!"statement outside a block: {line}"
        match ← statement b (line.dropEndWhile (· == ';')).toString with
        | .inl b => block := some b
        | .inr done =>
          func := some (name, params, rets, done :: blocks)
          block := none
    else if line.startsWith "target" || line.startsWith "declare" || line.startsWith "global "
    then
      pure ()
    else if line.startsWith "type " && (line.splitOn "= enum {").length == 2 then
      inEnum := !line.endsWith "};"
    else if line.startsWith "type " then
      let ws := tokens line
      let name :: _ := ws.drop 1 | throw s!"bad type: {line}"
      let body := (line.dropWhile (· != '{')).toString
      unless body.startsWith "{" do throw s!"unsupported type declaration: {line}"
      let fields := body.drop 1 |>.takeWhile (· != '}') |>.toString
      let fields ← (fields.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
        |>.mapM parseTy
      structs := ((name.drop 1).toString, fields) :: structs
    else if line.startsWith "func " then
      let (name, params, rets) ← funcHeader line
      func := some (name, params, rets, [])
    else throw s!"unsupported declaration: {line}"
  if func.isSome then throw "unterminated function"
  return ⟨structs.reverse, funcs.reverse, fixedLimit⟩

/-- A module from the text of a section's `source_ir`. -/
def parseModule (text : String) : P HModule := parseLines (Fe.Sonatina.Parse.lines text)

/-- The handover object of a sidecar, from the JSON `fe build --emit sidecar` writes: for each
    of `init` and `runtime`, its `source_ir`, its entry from the object declarations of `ir`,
    and its symbols. -/
def objectOfSidecar (text : String) : P Object := do
  let json ← Json.parse text
  let objectName ← json.getObjValAs? String "object"
  let (objectLines, _) := splitObjects (Fe.Sonatina.Parse.lines (← json.getObjValAs? String "ir"))
  let (_, objects) ← Fe.Sonatina.Parse.parseLines objectLines
  let some obj := objects.find? (·.name == objectName) | throw s!"no object {objectName}"
  let sections ← json.getObjValAs? (Array Json) "sections"
  let sectionOf (name : String) : P HSection := do
    let some sec := obj.sections.find? (·.name == name) | throw s!"no section {name}"
    let some s := sections.find? (·.getObjValAs? String "name" == .ok name)
      | throw s!"no compiled section {name}"
    let symbols ← (← s.getObjValAs? (Array Json) "symbols").toList.mapM fun sym =>
      return (← sym.getObjValAs? String "symbol", ← sym.getObjValAs? Nat "offset",
        ← sym.getObjValAs? Nat "size")
    let lowering ← s.getObjVal? "lowering"
    let module ← (parseModule (← lowering.getObjValAs? String "source_ir")).mapError
      (s!"{name}: " ++ ·)
    return ⟨module, sec.entry, symbols⟩
  return ⟨← sectionOf "init", ← sectionOf "runtime"⟩

end Fe.Sonatina.H.Parse
