import FeSpecProofs.Programs.ScalarStore
import FeProofs.ScalarStore.Bytecode
import Fe.Host.Keccak

/-!
# FeScalarStore: the interpreter's program, the bytecode and the source

The capstone (`SpecCorrect.lean`, `SpecDeploy.lean`) is about fe-spec's `fixtures/scalar_store.json`
(`Fe.Proofs.scalarStore`) and about the bytes of `runtime.hex`/`creation.hex`
(`feScalarStoreBytecode`, `feScalarStoreCreationBytecode`).  The fixture records its provenance:
the compiler run that serialized it, the keccak256 of its source, and the keccak256 of the
creation and runtime code the same run compiled (`Fe.Proofs.scalarStore.provenance`).

* `runtime_provenance`, `creation_provenance` (kernel-checked, `decide +kernel` on Keccak-256 of
  the bytes): the certified bytecode is the bytecode of the compiler run that serialized the
  program the certificate is about.
* The `#eval` below fails the build unless `FeScalarStore.fe` here hashes to the source the
  fixture records (a file is not a kernel term, so this check is compiled).
-/

namespace FeProofs.ScalarStore

open Fe.Host.Keccak

theorem runtime_provenance :
    (Fe.Proofs.scalarStore.provenance.runtime.map (·.data) ==
      some (keccak256 feScalarStoreBytecode).data) = true := by
  decide +kernel

theorem creation_provenance :
    (Fe.Proofs.scalarStore.provenance.creation.map (·.data) ==
      some (keccak256 feScalarStoreCreationBytecode).data) = true := by
  decide +kernel

end FeProofs.ScalarStore

open Lean in
#eval show IO Unit from do
  let here ← IO.FS.readBinFile ("FeProofs" / "ScalarStore" / "FeScalarStore.fe")
  let recorded := Fe.Proofs.scalarStore.provenance.sources.map (·.keccak256.data)
  unless recorded == #[(Fe.Host.Keccak.keccak256 here).data] do
    throw <| IO.userError
      "FeScalarStore.fe does not hash to the source fixtures/scalar_store.json records"
