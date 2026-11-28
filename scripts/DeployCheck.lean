import Fe.Sonatina.Stage3.Place.Deploy

/-!
# `deployCheck` on sidecars

`lake lean scripts/DeployCheck.lean -- --run scripts/DeployCheck.lean SIDECAR...`: for each
sidecar, `DEPLOY<TAB>file<TAB>accepted` if `Sidecar.deployCheck` (`Place/Deploy.lean`) holds of it
and its handover object, else `DEPLOY<TAB>file<TAB>rejected<TAB>reasons`, separated by ` | `: no
runtime symbol, the runtime bytes not at it in the init bytes (`embedsRuntime`), and each init
block's statement or terminator that `deployReturns` rejects; then `DEPLOYTOTAL`.
-/

open Lean Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Stage3.Place

def reasons (s : Sidecar) (h : H.Object) : List String := Id.run do
  let mut out : List String := []
  match s.runtimeSym with
  | none => out := out ++ ["no runtime symbol"]
  | some sym =>
    unless s.embedsRuntime do out := out ++ [s!"embedsRuntime false (sym {sym}, at {s.runtimeAt})"]
    for f in h.init.module.funcs do
      for b in f.blocks do
        for st in b.body do
          unless st.inst.noStop do out := out ++ [s!"{f.name} block{b.id}: inst {reprStr st.inst}"]
        match b.term with
        | .base t => unless t.noStop do out := out ++ [s!"{f.name} block{b.id}: term {reprStr t}"]
        | .returnCode o l =>
          unless b.returnsSym sym do
            let tail := (b.body.reverse.take 3).reverse.map fun st => reprStr st.inst
            out := out ++ [s!"{f.name} block{b.id}: return_code {reprStr o} {reprStr l} not of sym {sym}; last: {tail}"]
        | .revertWord .. => pure ()
  return out

def main (args : List String) : IO Unit := do
  let mut acc := 0
  for path in args do
    let text ← IO.FS.readFile path
    let file := (System.FilePath.mk path).fileName.getD path
    match Parse.parseSidecar text, H.Parse.objectOfSidecar text with
    | .ok s, .ok h =>
      if s.deployCheck h then
        acc := acc + 1
        IO.println s!"DEPLOY\t{file}\taccepted"
      else
        IO.println s!"DEPLOY\t{file}\trejected\t{" | ".intercalate (reasons s h)}"
    | .error e, _ => IO.println s!"DEPLOY\t{file}\tunread\t{e}"
    | _, .error e => IO.println s!"DEPLOY\t{file}\thunread\t{e}"
  IO.println s!"DEPLOYTOTAL {args.length} accepted={acc}"
