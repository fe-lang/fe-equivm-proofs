import FeProofs
import FeModel
/-! Prints the axioms each capstone theorem depends on, in order of name, counting the
`native_decide` evaluations instead of listing them.  The capstones are each contract's Stele certificate
(`fe…ContractCorrect`), the refinement certificates (`fe…Refines…`), the conservation theorems
(`…conserves…`) and the invariants through every call and from deployment (`fe…Keeps…`,
`fe…Solvent…`), and the machine pipeline's theorems under `Fe.Sonatina` (`check_sound`,
`checkSpills_sound`, `machine_sound_proved` and its variants, `machine_sound_sidecar`,
`machine_sound_spills_sidecar`, `StepKind.proved_sound`, each step kind's
`…_stepSound`, the known-bits invariant `kb_reaches` and `kb_point`, and the handover semantics'
`runH_sound`, `runRuntime_sound`, `runDeploy_sound`, `message_eq_core`, `createWith_eq_core`).  Run:
`lake lean scripts/Audit.lean`. -/
open Lean

#eval show CoreM Unit from do
  let machine := ["check_sound", "checkSpills_sound", "machine_sound_proved",
    "machine_sound_proved_of_sound", "machine_sound_spills_proved", "machine_sound_sidecar",
    "machine_sound_spills_sidecar", "proved_sound",
    "runH_sound", "runRuntime_sound", "runDeploy_sound", "message_eq_core", "createWith_eq_core",
    "kb_reaches", "kb_point"]
  let capstones := (← getEnv).constants.toList.filterMap fun (n, _) =>
    let last := n.lastComponentAsString
    let has (part : String) := (last.splitOn part).length > 1
    if (`FeProofs).isPrefixOf n && (last.endsWith "ContractCorrect"
        || last.startsWith "fe" && (has "Refines" || has "Keeps" || has "Solvent")
        || has "conserves")
      || (`Fe.Sonatina).isPrefixOf n && (machine.contains last || last.endsWith "_stepSound") then
      some n
    else none
  for n in capstones.toArray.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms n
    let (nd, other) := axs.partition (fun a => (`_nativeDecide).isPrefixOf a || a.toString.endsWith "_native_decide" ||
      (a.toString.splitOn "native").length > 1)
    let other := other.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{n}: {other.toList} + {nd.size} native_decide"
