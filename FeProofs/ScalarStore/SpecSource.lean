import FeSpecProofs.Programs.ScalarStore

/-!
# FeScalarStore: the interpreter's program and the bytecode come from one source

The capstone (`SpecCorrect.lean`, `SpecDeploy.lean`) is about fe-spec's `fixtures/scalar_store.json`
and about the bytes in `runtime.hex`/`creation.hex` (with the Sonatina sidecar).  No proof ties
them to one Fe source and one compiler.  This check ties the sources: building this module fails
unless `FeScalarStore.fe` here is byte-for-byte the source fe-spec's fixture was serialized
from, `fixtures/scalar_store.fe` in the fe-spec package.  The compilers are recorded, not checked:
`FeScalarStore.build.json` names the Fe commit of the bytecode, fe-spec's `fixtures/fe.rev` the
Fe checkout the fixtures were synced from.
-/

open Lean in
#eval show IO Unit from do
  -- `<fe-spec>/.lake/build/lib/lean/FeSpecProofs/Programs/ScalarStore.olean`
  let olean ← findOLean `FeSpecProofs.Programs.ScalarStore
  let root := (List.range 7).foldl (fun p _ => p.parent.getD p) olean
  let fixture ← IO.FS.readBinFile (root / "fixtures" / "scalar_store.fe")
  let here ← IO.FS.readBinFile ("FeProofs" / "ScalarStore" / "FeScalarStore.fe")
  unless fixture == here do
    throw <| IO.userError s!"{root / "fixtures" / "scalar_store.fe"} differs from FeScalarStore.fe"
