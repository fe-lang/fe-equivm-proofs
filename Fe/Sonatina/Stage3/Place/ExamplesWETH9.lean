import Fe.Sonatina.Stage3.Place.Examples

/-!
# Slice 1 on WETH9

`Examples.lean` for a third contract of another shape: WETH9 as corpus v10 builds it at `-O0`
(`Tests/WETH9.O0.sidecar.json`, the corpus sidecar; the `.bin` files are the corpus ones), whose
runtime has 226 functions (FeERC20's 125) and whose constructor stores through `evm_sstore`.

Not in the default build: its kernel checks take about three minutes and peak at about 21 GB
resident (`Examples.lean`'s at about 12 GB).  Build it on its own, with
`lake build Fe.Sonatina.Stage3.Place.ExamplesWETH9`.  It imports `Examples.lean` so that a build
of both does not check the two at once.
-/

namespace Fe.Sonatina.Stage3.Place.Examples

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Fe.Sonatina.Stage3.Place

-- The kernel checks the fixtures' terms, deep lists, by recursion.
set_option maxRecDepth 1000000

/-! ## WETH9 -/

slice1_fixture WETH9 "Fe/Sonatina/Stage3/Place/Tests/WETH9.O0.sidecar.json"
hex_bytes WETH9.runtimeBin "Fe/Sonatina/Stage3/Place/Tests/WETH9.O0.runtime.bin"
hex_bytes WETH9.initBin "Fe/Sonatina/Stage3/Place/Tests/WETH9.O0.bin"

theorem WETH9.code_runtime : WETH9.s.code "runtime" = WETH9.runtimeBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem WETH9.code_init : WETH9.s.code "init" = WETH9.initBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem WETH9.validate_runtime : Steps.validate (WETH9.s.symbolsOf "runtime")
    (WETH9.s.stepsOf "runtime") (WETH9.s.machineOf "runtime") = true := by
  decide +kernel

theorem WETH9.validate_init : Steps.validate (WETH9.s.symbolsOf "init")
    (WETH9.s.stepsOf "init") (WETH9.s.machineOf "init") = true := by
  decide +kernel

theorem WETH9.validate : WETH9.s.validate = true := by
  rw [Sidecar.validate, WETH9.validate_runtime, WETH9.validate_init, Bool.and_self]

theorem WETH9.check : Check.check WETH9.s = true := by decide +kernel

theorem WETH9.place_runtime :
    placeSec WETH9.s.asLowered WETH9.h.runtime "runtime" WETH9.rr = true := by
  decide +kernel

theorem WETH9.place_init :
    placeSec WETH9.s.asLowered WETH9.h.init "init" WETH9.ri = true := by
  decide +kernel

theorem WETH9.placeCheck : WETH9.s.placeCheck WETH9.h WETH9.rr WETH9.ri = true := by
  rw [Sidecar.placeCheck, WETH9.place_runtime, WETH9.place_init, Bool.and_self]

/-- WETH9's bytes refine its handover object on every call and deployment. -/
theorem WETH9.refines : RefinesOnH .P1 (WETH9.s.code "runtime") WETH9.h CalldataFits ∧
    RefinesDeployH .P1 (WETH9.s.code "init") WETH9.h (fun _ => True) CalldataFits :=
  slice1_sound WETH9.validate WETH9.check WETH9.placeCheck

/-- `WETH9.refines` of the bytes of the corpus `.bin` files. -/
theorem WETH9.refines_bin : RefinesOnH .P1 WETH9.runtimeBin WETH9.h CalldataFits ∧
    RefinesDeployH .P1 WETH9.initBin WETH9.h (fun _ => True) CalldataFits := by
  rw [← WETH9.code_runtime, ← WETH9.code_init]; exact WETH9.refines

theorem WETH9.deployCheck : WETH9.s.deployCheck WETH9.h = true := by decide +kernel

/-- A deployment by WETH9's init bytes that succeeds deploys its runtime bytes, unless H's init
    section has a run that is `ub` or `exhausted` under the call's real feed. -/
theorem WETH9.deploy_code {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {args : ByteArray} (hI : I.code = WETH9.initBin ++ args) (ho : OwnerExists σ I)
    (hperm : I.perm = true) (hcf : CalldataFits I) {accounts : AccountMap} {g' : UInt256}
    {A' : Substate} {code : ByteArray}
    (hx : Ξ σ σ₀ g A I = .ok (.success (accounts, g', A') code)) :
    code = WETH9.runtimeBin ∨ ∃ feed, RealFeed σ σ₀ g A I feed ∧
      (WETH9.h.Deploy args I (World.init σ A feed) .ub ∨
        WETH9.h.Deploy args I (World.init σ A feed) .exhausted) := by
  rw [← WETH9.code_init] at hI
  rw [← WETH9.code_runtime]
  exact slice1_deploy_code WETH9.validate WETH9.check WETH9.placeCheck WETH9.deployCheck hI ho hperm hcf hx

end Fe.Sonatina.Stage3.Place.Examples
