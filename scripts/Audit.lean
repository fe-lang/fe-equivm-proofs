import FeProofs
import FeModel
/-! Prints the axioms each capstone theorem depends on, in order of name, counting the
`native_decide` evaluations instead of listing them.  The capstones are each contract's Stele certificate
(`fe…ContractCorrect`), the refinement certificates (`fe…Refines…`), the conservation theorems
(`…conserves…`) and the invariants through every call and from deployment (`fe…Keeps…`,
`fe…Solvent…`), and the machine pipeline's theorems under `Fe.Sonatina` (`check_sound`,
`checkSpills_sound`, `machine_sound_proved` and its variants, `machine_sound_sidecar`,
`machine_sound_spills_sidecar`, their forms under the real feed (`…_fut`, `…_at`),
`StepKind.proved_sound`, each step kind's `…_stepSound`, the known-bits invariant `kb_reaches`
and `kb_point`, and the handover semantics' `runH_sound`, `runRuntime_sound`,
`runDeploy_sound`, `message_eq_core`, `createWith_eq_core`, and its composition with the real feed's
refinement, `Fe.EVM.RefinesOnFut.toH`, `Fe.EVM.RefinesDeployFut.toH`; Stage 3 Slice 1's
`place_lower_sound`, `place_sidecar_sound` and `slice1_sound`, with the deployed code
`slice1_deploy_runtime` and `slice1_deploy_code`, and its instances' `refines_bin` and
`deploy_code` for FeConstant and FeERC20).  Run:
`lake lean scripts/Audit.lean`. -/
open Lean

#eval show CoreM Unit from do
  let machine := ["check_sound", "checkSpills_sound", "machine_sound_proved",
    "machine_sound_proved_of_sound", "machine_sound_spills_proved", "machine_sound_sidecar",
    "machine_sound_spills_sidecar", "check_sound_fut", "checkSpills_sound_fut",
    "checkSpills_sound_at", "checkSpills_deploy_at", "machine_sound_proved_fut",
    "machine_sound_proved_of_sound_fut", "machine_sound_spills_proved_fut",
    "machine_sound_spills_at", "machine_deploy_spills_at", "machine_sound_sidecar_fut",
    "machine_sound_spills_sidecar_fut", "proved_sound",
    "runH_sound", "runRuntime_sound", "runDeploy_sound", "message_eq_core", "createWith_eq_core",
    "kb_reaches", "kb_point", "place_lower_sound", "place_sidecar_sound", "slice1_sound",
    "slice1_deploy_runtime", "slice1_deploy_code"]
  let capstones := (← getEnv).constants.toList.filterMap fun (n, _) =>
    let last := n.lastComponentAsString
    let has (part : String) := (last.splitOn part).length > 1
    if (`FeProofs).isPrefixOf n && (last.endsWith "ContractCorrect"
        || last.startsWith "fe" && (has "Refines" || has "Keeps" || has "Solvent")
        || has "conserves")
      || (`Fe.Sonatina).isPrefixOf n && (machine.contains last || last.endsWith "_stepSound")
      || [``Fe.EVM.RefinesOnFut.toH, ``Fe.EVM.RefinesDeployFut.toH,
          ``Fe.Sonatina.Stage3.Place.Examples.FeConstant.refines_bin,
          ``Fe.Sonatina.Stage3.Place.Examples.FeConstant.deploy_code,
          ``Fe.Sonatina.Stage3.Place.Examples.FeERC20.refines_bin,
          ``Fe.Sonatina.Stage3.Place.Examples.FeERC20.deploy_code].contains n then
      some n
    else none
  for n in capstones.toArray.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms n
    let (nd, other) := axs.partition (fun a => (`_nativeDecide).isPrefixOf a || a.toString.endsWith "_native_decide" ||
      (a.toString.splitOn "native").length > 1)
    let other := other.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{n}: {other.toList} + {nd.size} native_decide"
