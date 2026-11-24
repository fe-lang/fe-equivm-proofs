import Fe.Sonatina.Diff
import Fe.Sonatina.Hints

/-!
Compares the Sonatina IR of the certified contracts with their bytecode on generated calls: the
sidecars in `Fe/Sonatina/Fixtures/` (IR and bytecode from one compilation, `fe build --emit
sidecar`) at each level, the IR after optimization, each section's IR after the backend's pipeline
and its machine IR, and the pinned bytecode with the `.sona` file committed beside it.  Then
checks each fixture's lowering hints against its bytes (`Fe/Sonatina/Hints.lean`).  Run with
`lake lean scripts/SonatinaDiff.lean -- --load-dynlib=.lake/ffi/libfeffi.dylib` (the library
that `scripts/build_ffi.sh` builds runs the SHA-256 precompile the deposit contract calls).
-/

open Fe.Sonatina

def fixtures : List (String × String) :=
  [("FeConstant", "Constant/FeConstant"), ("FeScalarStore", "ScalarStore/FeScalarStore"),
   ("FeERC20", "ERC20/FeERC20"), ("DepositContract", "Deposit/FeDeposit")]

#eval show IO Unit from do
  for (sidecar, abi) in fixtures do
    for level in [Level.postOpt, .source, .machine] do
      generatedOf s!"Fe/Sonatina/Fixtures/{sidecar}.sidecar.json" s!"FeProofs/{abi}.abi.json"
        level 16 32

#eval pinnedOf "FeProofs/ERC20" "FeERC20" 16 32
#eval pinnedOf "FeProofs/Deposit" "FeDeposit" 16 32
#eval pinnedOf "FeProofs/WETH9" "FeWETH9" 16 32

#eval show IO Unit from do
  for (sidecar, _) in fixtures do
    let s ← IO.ofExcept (Parse.parseSidecar
      (← IO.FS.readFile s!"Fe/Sonatina/Fixtures/{sidecar}.sidecar.json"))
    for code in s.sections do
      let blocks := (code.lowering.map (·.funcs.foldl (· + ·.blocks.length) 0)).getD 0
      let failures := Hints.check code
      IO.println s!"HINTS {sidecar} {code.name} blocks={blocks} failures={failures.length}"
      for failure in failures do IO.println s!"  {failure}"
