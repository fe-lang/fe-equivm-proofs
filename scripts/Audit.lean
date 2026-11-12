import FeProofs
/-! Prints the axioms each capstone theorem depends on, counting the `native_decide` evaluations
instead of listing them.  The capstones are each contract's Stele certificate
(`fe…ContractCorrect`), the refinement certificates (`fe…Refines…`) and the conservation
theorems (`…conserves…`).  Run: `lake env lean scripts/Audit.lean`. -/
open Lean

#eval show CoreM Unit from do
  let capstones := (← getEnv).constants.toList.filterMap fun (n, _) =>
    let last := n.lastComponentAsString
    let has (part : String) := (last.splitOn part).length > 1
    if (`FeProofs).isPrefixOf n && (last.endsWith "ContractCorrect" || last.startsWith "fe" && has "Refines"
        || has "conserves") then some n else none
  for n in capstones.toArray.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms n
    let (nd, other) := axs.partition (fun a => (`_nativeDecide).isPrefixOf a || a.toString.endsWith "_native_decide" ||
      (a.toString.splitOn "native").length > 1)
    IO.println s!"{n}: {other.toList} + {nd.size} native_decide"
