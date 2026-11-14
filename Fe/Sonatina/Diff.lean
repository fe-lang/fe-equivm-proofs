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
def Sidecar.target (s : Sidecar) (interface : Interface) : Target where
  name := s.object
  creation := (s.section? "init").map (·.bytecode) |>.getD .empty
  runtime := .empty
  model := s.model
  interface := interface

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

/-- The targets of the sidecars at the paths, each with its interface.  A sidecar whose IR this
    subset does not read is left out, with a line `UNSUPPORTED <file>::<path>: <reason>`. -/
def targetsOf (file : String) (sidecars : List (String × Interface)) : IO (List Target) :=
  sidecars.filterMapM fun (path, interface) => do
    match Parse.parseSidecar (← IO.FS.readFile path) with
    | .ok s => return some (s.target interface)
    | .error e =>
      IO.println s!"UNSUPPORTED {file}::{path}: {e}"
      return none

/-- A sidecar for pinned bytecode and the IR text committed beside it, which `fe build --emit ir`
    printed: the object has one section `runtime` embedded at the end of `init`, where Sonatina
    lays out embeds, and no other symbol is read.  An error unless `runtime` ends `init`. -/
def Sidecar.ofPinned (ir : String) (creation runtime : ByteArray) : Except String Sidecar := do
  let module ← Parse.parseModule ir
  let [obj] := module.objects | throw "expected one object"
  let offset := creation.size - runtime.size
  unless runtime.size ≤ creation.size && creation.extract offset creation.size == runtime do
    throw "the runtime code does not end the creation code"
  let embeds := (obj.sections.find? (·.name == "init")).map (·.embeds) |>.getD []
  let [(symbol, "runtime")] := embeds | throw "expected init to embed runtime alone"
  return ⟨obj.name, module,
    [⟨"init", creation, [(".", 0, creation.size), (symbol, offset, runtime.size)]⟩,
     ⟨"runtime", runtime, [(".", 0, runtime.size)]⟩]⟩

/-- Compare the pinned bytecode of the contract directory `dir` with the IR `<dir>/<name>.sona`,
    on generated calls from the interface of `<dir>/<name>.abi.json`. -/
def pinnedOf (dir name : String) (sequences calls : Nat) : IO Unit := do
  let read (file : String) : IO String := do
    return (← IO.FS.readFile s!"{dir}/{file}").trimAscii.toString
  let s ← IO.ofExcept ((Sidecar.ofPinned (← read s!"{name}.sona")
    (hex (← read "creation.hex")) (hex (← read "runtime.hex"))).mapError (s!"{dir}: " ++ ·))
  let interface ← IO.ofExcept (interfaceOfAbi (← read s!"{name}.abi.json"))
  generated s!"{s.object} (pinned)" [s.target interface] sequences calls

/-- Compare the IR of the sidecar at `sidecar` with its bytecode on `sequences` sequences of
    `calls` generated calls each, from the interface of the ABI at `abi`. -/
def generatedOf (sidecar abi : String) (sequences calls : Nat) : IO Unit := do
  let s ← IO.ofExcept ((Parse.parseSidecar (← IO.FS.readFile sidecar)).mapError
    (s!"{sidecar}: " ++ ·))
  let interface ← IO.ofExcept ((interfaceOfAbi (← IO.FS.readFile abi)).mapError
    (s!"{abi}: " ++ ·))
  generated s.object [s.target interface] sequences calls

end Fe.Sonatina
