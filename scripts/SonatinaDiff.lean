import Fe.Sonatina.Diff

/-!
Compares the Sonatina IR of the certified contracts with their bytecode on generated calls:
the sidecars in `Fe/Sonatina/Fixtures/` (IR and bytecode from one compilation, `fe build --emit
sidecar`), and the pinned bytecode with the `.sona` file committed beside it.  Run with
`lake env lean --load-dynlib=.lake/ffi/libfeffi.dylib scripts/SonatinaDiff.lean` (the library
that `scripts/build_ffi.sh` builds runs the SHA-256 precompile the deposit contract calls).
-/

open Fe.Sonatina

#eval generatedOf "Fe/Sonatina/Fixtures/FeConstant.sidecar.json"
  "FeProofs/Constant/FeConstant.abi.json" 16 32
#eval generatedOf "Fe/Sonatina/Fixtures/FeScalarStore.sidecar.json"
  "FeProofs/ScalarStore/FeScalarStore.abi.json" 16 32
#eval generatedOf "Fe/Sonatina/Fixtures/FeERC20.sidecar.json"
  "FeProofs/ERC20/FeERC20.abi.json" 16 32
#eval generatedOf "Fe/Sonatina/Fixtures/DepositContract.sidecar.json"
  "FeProofs/Deposit/FeDeposit.abi.json" 16 32

#eval pinnedOf "FeProofs/ERC20" "FeERC20" 16 32
#eval pinnedOf "FeProofs/Deposit" "FeDeposit" 16 32
#eval pinnedOf "FeProofs/WETH9" "FeWETH9" 16 32
