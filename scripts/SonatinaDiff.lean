import Fe.Sonatina.Diff

/-!
Compares the Sonatina IR of the certified contracts with their bytecode on generated calls: the
sidecars in `Fe/Sonatina/Fixtures/` (IR and bytecode from one compilation, `fe build --emit
sidecar`) at each level, the IR after optimization, each section's IR after the backend's pipeline
and its machine IR, and the pinned bytecode with the `.sona` file committed beside it.  Run with
`lake env lean --load-dynlib=.lake/ffi/libfeffi.dylib scripts/SonatinaDiff.lean` (the library
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
