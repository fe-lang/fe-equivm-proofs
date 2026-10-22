import FeProofs
/-! Prints the axioms each contract's capstone theorem depends on, counting the `native_decide`
evaluations instead of listing them. Run: `lake env lean scripts/Audit.lean`. -/
open Lean

#eval show CoreM Unit from do
  for n in [``FeProofs.Constant.feConstantContractCorrect, ``FeProofs.Identity.feIdentityContractCorrect,
      ``FeProofs.ScalarStore.feScalarStoreContractCorrect, ``FeProofs.NarrowAbi.feNarrowAbiContractCorrect,
      ``FeProofs.PackedStore.fePackedStoreContractCorrect,
      ``FeProofs.IndexedPackedStore.feIndexedPackedStoreContractCorrect,
      ``FeProofs.Deposit.feDepositContractCorrect, ``FeProofs.ERC20.feERC20ContractCorrect,
      ``FeProofs.WETH9.feWETH9ContractCorrect] do
    let axs ← collectAxioms n
    let (nd, other) := axs.partition (fun a => (`_nativeDecide).isPrefixOf a || a.toString.endsWith "_native_decide" ||
      (a.toString.splitOn "native").length > 1)
    IO.println s!"{n.lastComponentAsString}: {other.toList} + {nd.size} native_decide"
