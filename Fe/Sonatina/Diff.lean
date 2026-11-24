import Fe.Sonatina.Hints
import Fe.Sonatina.Interp
import Fe.Sonatina.Parse
import Fe.EVM.Generate

/-!
# Differential tests of Sonatina IR

The IR of a sidecar, run by `Interp.lean`, is a contract model, so the runner and generators
that compare exported models with bytecode (`Fe/EVM/Diff.lean`, `Generate.lean`) compare it with
the bytecode compiled from it: on sequences of generated calls, and on the calls a Fe test
suite makes.  `scripts/sonatina_diff.lean` runs them on the sidecars in `Fixtures/`.
-/

namespace Fe.Sonatina

open Lean Ethereum Fe.EVM.Diff

/-- The target whose model is the sidecar's IR.  Its creation code is the init section; the
    model's constructor ends with the whole deployed code, so the target adds no runtime code
    to what the constructor returns. -/
def Sidecar.target (s : Sidecar) (interface : Interface) (level : Level := .postOpt) :
    Target where
  name := s.object
  creation := (s.section? "init").map (·.bytecode) |>.getD .empty
  runtime := .empty
  model := some (s.model level)
  interface := interface

/-- The level `SONATINA_LEVEL` names (`post-opt`, `source` or `machine`), `post-opt` if unset. -/
def levelOfEnv : IO Level := do
  match (← IO.getEnv "SONATINA_LEVEL").getD "post-opt" with
  | "post-opt" => return .postOpt
  | "source" => return .source
  | "machine" => return .machine
  | other => throw (.userError s!"unknown SONATINA_LEVEL {other}")

/-- The canonical type of an ABI parameter, as a selector signature spells it. -/
partial def abiType (param : Json) : Except String String := do
  let ty ← param.getObjValAs? String "type"
  if ty.startsWith "tuple" then
    let items ← (← param.getObjValAs? (Array Json) "components").toList.mapM abiType
    return s!"({",".intercalate items}){ty.drop 5}"
  return ty

/-- The interface of a contract from its JSON ABI. -/
def interfaceOfAbi (text : String) : Except String Interface := do
  let entries ← (← Json.parse text).getArr?
  let inputs (e : Json) : Except String String := do
    let ps ← (e.getObjValAs? (Array Json) "inputs").toOption.getD #[] |>.toList.mapM abiType
    return s!"({",".intercalate ps})"
  let payable (e : Json) := e.getObjValAs? String "stateMutability" == .ok "payable"
  let mut interface : Interface := {}
  for e in entries do
    match e.getObjValAs? String "type" with
    | .ok "constructor" =>
      interface := { interface with init := ← inputs e, initPayable := payable e }
    | .ok "function" =>
      let signature := (← e.getObjValAs? String "name") ++ (← inputs e)
      let digest := KEC signature.toUTF8
      let selector := fromByteArrayBigEndian (digest.extract 0 4)
      interface := { interface with
        arms := interface.arms ++ [⟨selector, ← inputs e, payable e⟩] }
    | _ => pure ()
  return interface

/-- The targets of the sidecars at the paths, each with its interface, running the IR of the
    level `SONATINA_LEVEL` names.  A sidecar whose IR this subset does not read is left out,
    with a line `UNSUPPORTED <file>::<path>: <reason>`.  For each section of the others a line
    `HINTS <file>::<path> <section> blocks=<n> failures=<n>`, and one per failure, gives the
    checks of its lowering hints against its bytes (`Hints.lean`). -/
def targetsOf (file : String) (sidecars : List (String × Interface)) : IO (List Target) := do
  let level ← levelOfEnv
  sidecars.filterMapM fun (path, interface) => do
    match Parse.parseSidecar (← IO.FS.readFile path) with
    | .ok s =>
      if level == .postOpt && s.module.isNone then
        IO.println s!"UNSUPPORTED {file}::{path}: a module IR this subset does not read"
        return none
      if level == .source && s.sections.any (·.lowering.any (·.source.isNone)) then
        IO.println s!"UNSUPPORTED {file}::{path}: a section IR this subset does not read"
        return none
      for code in s.sections do
        let blocks := (code.lowering.map (·.funcs.foldl (· + ·.blocks.length) 0)).getD 0
        let failures := Hints.check code
        IO.println s!"HINTS {file}::{path} {code.name} blocks={blocks} failures={failures.length}"
        for failure in failures do IO.println s!"HINTFAIL {file}::{path} {code.name} {failure}"
      return some (s.target interface level)
    | .error e =>
      IO.println s!"UNSUPPORTED {file}::{path}: {e}"
      return none

/-- A sidecar for pinned bytecode and the IR text committed beside it, which `fe build --emit ir`
    printed: the object has one section `runtime` embedded at the end of `init`, where Sonatina
    lays out embeds, and no other symbol is read.  An error unless `runtime` ends `init`. -/
def Sidecar.ofPinned (ir : String) (creation runtime : ByteArray) : Except String Sidecar := do
  let (module, objects) ← Parse.parseLines (Parse.lines ir)
  let [obj] := objects | throw "expected one object"
  let offset := creation.size - runtime.size
  unless runtime.size ≤ creation.size && creation.extract offset creation.size == runtime do
    throw "the runtime code does not end the creation code"
  let embeds := (obj.sections.find? (·.name == "init")).map (·.embeds) |>.getD []
  let [(symbol, "runtime")] := embeds | throw "expected init to embed runtime alone"
  return ⟨obj.name, objects, some module,
    [⟨"init", creation, [(".", 0, creation.size), (symbol, offset, runtime.size)], none⟩,
     ⟨"runtime", runtime, [(".", 0, runtime.size)], none⟩]⟩

/-- Compare the pinned bytecode of the contract directory `dir` with the IR `<dir>/<name>.sona`,
    on generated calls from the interface of `<dir>/<name>.abi.json`. -/
def pinnedOf (dir name : String) (sequences calls : Nat) : IO Unit := do
  let read (file : String) : IO String := do
    return (← IO.FS.readFile s!"{dir}/{file}").trimAscii.toString
  let s ← IO.ofExcept ((Sidecar.ofPinned (← read s!"{name}.sona")
    (hex (← read "creation.hex")) (hex (← read "runtime.hex"))).mapError (s!"{dir}: " ++ ·))
  let interface ← IO.ofExcept (interfaceOfAbi (← read s!"{name}.abi.json"))
  generated s!"{s.object} (pinned)" [s.target interface] sequences calls

/-- Compare the IR of the level of the sidecar at `sidecar` with its bytecode on `sequences`
    sequences of `calls` generated calls each, from the interface of the ABI at `abi`. -/
def generatedOf (sidecar abi : String) (level : Level) (sequences calls : Nat) : IO Unit := do
  let s ← IO.ofExcept ((Parse.parseSidecar (← IO.FS.readFile sidecar)).mapError
    (s!"{sidecar}: " ++ ·))
  let interface ← IO.ofExcept ((interfaceOfAbi (← IO.FS.readFile abi)).mapError
    (s!"{abi}: " ++ ·))
  generated s!"{s.object} ({repr level})" [s.target interface level] sequences calls

end Fe.Sonatina
