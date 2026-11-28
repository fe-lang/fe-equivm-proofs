import Fe.Sonatina.Stage3.Place.Fixture
import Fe.Sonatina.Stage3.Place.Sidecar

/-!
# Slice 1 on real contracts

`slice1_sound` for FeConstant and FeERC20 as the compiler of corpus v8 builds them at `-O0`
(`Tests/*.O0.sidecar.json`, the corpus sidecars): the three hypotheses are decided by the
kernel, so each contract's bytes refine its handover object with no hypothesis left.  The bytes
are the ones the compiler wrote: `Tests/*.O0.runtime.bin` and `Tests/*.O0.bin` are the corpus
`.bin` files, and `code_runtime`/`code_init` show the sidecar's sections hold them, so
`refines_bin` is about those files' bytes.

Each hypothesis is decided per section where its definition splits by section (`validate`,
`placeCheck`), so the sections are checked as separate declarations; `check` is decided whole.
-/

namespace Fe.Sonatina.Stage3.Place.Examples

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Fe.Sonatina.Stage3.Place

-- The kernel checks the fixtures' terms, deep lists, by recursion.
set_option maxRecDepth 1000000

/-! ## FeConstant -/

slice1_fixture FeConstant "Fe/Sonatina/Stage3/Place/Tests/FeConstant.O0.sidecar.json"
hex_bytes FeConstant.runtimeBin "Fe/Sonatina/Stage3/Place/Tests/FeConstant.O0.runtime.bin"
hex_bytes FeConstant.initBin "Fe/Sonatina/Stage3/Place/Tests/FeConstant.O0.bin"

theorem FeConstant.code_runtime : FeConstant.s.code "runtime" = FeConstant.runtimeBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem FeConstant.code_init : FeConstant.s.code "init" = FeConstant.initBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem FeConstant.validate_runtime : Steps.validate (FeConstant.s.symbolsOf "runtime")
    (FeConstant.s.stepsOf "runtime") (FeConstant.s.machineOf "runtime") = true := by
  decide +kernel

theorem FeConstant.validate_init : Steps.validate (FeConstant.s.symbolsOf "init")
    (FeConstant.s.stepsOf "init") (FeConstant.s.machineOf "init") = true := by
  decide +kernel

theorem FeConstant.validate : FeConstant.s.validate = true := by
  rw [Sidecar.validate, FeConstant.validate_runtime, FeConstant.validate_init, Bool.and_self]

theorem FeConstant.check : Check.check FeConstant.s = true := by decide +kernel

theorem FeConstant.place_runtime :
    placeSec FeConstant.s.asLowered FeConstant.h.runtime "runtime" FeConstant.rr = true := by
  decide +kernel

theorem FeConstant.place_init :
    placeSec FeConstant.s.asLowered FeConstant.h.init "init" FeConstant.ri = true := by
  decide +kernel

theorem FeConstant.placeCheck :
    FeConstant.s.placeCheck FeConstant.h FeConstant.rr FeConstant.ri = true := by
  rw [Sidecar.placeCheck, FeConstant.place_runtime, FeConstant.place_init, Bool.and_self]

/-- FeConstant's bytes refine its handover object on every call and deployment. -/
theorem FeConstant.refines : RefinesOnH .P1 (FeConstant.s.code "runtime") FeConstant.h CalldataFits ∧
    RefinesDeployH .P1 (FeConstant.s.code "init") FeConstant.h (fun _ => True) CalldataFits :=
  slice1_sound FeConstant.validate FeConstant.check FeConstant.placeCheck

/-- `FeConstant.refines` of the bytes of the corpus `.bin` files. -/
theorem FeConstant.refines_bin : RefinesOnH .P1 FeConstant.runtimeBin FeConstant.h CalldataFits ∧
    RefinesDeployH .P1 FeConstant.initBin FeConstant.h (fun _ => True) CalldataFits := by
  rw [← FeConstant.code_runtime, ← FeConstant.code_init]; exact FeConstant.refines

/-! ## FeERC20 -/

slice1_fixture FeERC20 "Fe/Sonatina/Stage3/Place/Tests/FeERC20.O0.sidecar.json"
hex_bytes FeERC20.runtimeBin "Fe/Sonatina/Stage3/Place/Tests/FeERC20.O0.runtime.bin"
hex_bytes FeERC20.initBin "Fe/Sonatina/Stage3/Place/Tests/FeERC20.O0.bin"

theorem FeERC20.code_runtime : FeERC20.s.code "runtime" = FeERC20.runtimeBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem FeERC20.code_init : FeERC20.s.code "init" = FeERC20.initBin :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

theorem FeERC20.validate_runtime : Steps.validate (FeERC20.s.symbolsOf "runtime")
    (FeERC20.s.stepsOf "runtime") (FeERC20.s.machineOf "runtime") = true := by
  decide +kernel

theorem FeERC20.validate_init : Steps.validate (FeERC20.s.symbolsOf "init")
    (FeERC20.s.stepsOf "init") (FeERC20.s.machineOf "init") = true := by
  decide +kernel

theorem FeERC20.validate : FeERC20.s.validate = true := by
  rw [Sidecar.validate, FeERC20.validate_runtime, FeERC20.validate_init, Bool.and_self]

theorem FeERC20.check : Check.check FeERC20.s = true := by decide +kernel

theorem FeERC20.place_runtime :
    placeSec FeERC20.s.asLowered FeERC20.h.runtime "runtime" FeERC20.rr = true := by
  decide +kernel

theorem FeERC20.place_init :
    placeSec FeERC20.s.asLowered FeERC20.h.init "init" FeERC20.ri = true := by
  decide +kernel

theorem FeERC20.placeCheck : FeERC20.s.placeCheck FeERC20.h FeERC20.rr FeERC20.ri = true := by
  rw [Sidecar.placeCheck, FeERC20.place_runtime, FeERC20.place_init, Bool.and_self]

/-- FeERC20's bytes refine its handover object on every call and deployment. -/
theorem FeERC20.refines : RefinesOnH .P1 (FeERC20.s.code "runtime") FeERC20.h CalldataFits ∧
    RefinesDeployH .P1 (FeERC20.s.code "init") FeERC20.h (fun _ => True) CalldataFits :=
  slice1_sound FeERC20.validate FeERC20.check FeERC20.placeCheck

/-- `FeERC20.refines` of the bytes of the corpus `.bin` files. -/
theorem FeERC20.refines_bin : RefinesOnH .P1 FeERC20.runtimeBin FeERC20.h CalldataFits ∧
    RefinesDeployH .P1 FeERC20.initBin FeERC20.h (fun _ => True) CalldataFits := by
  rw [← FeERC20.code_runtime, ← FeERC20.code_init]; exact FeERC20.refines

end Fe.Sonatina.Stage3.Place.Examples
