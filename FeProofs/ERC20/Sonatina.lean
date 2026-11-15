import Fe.Sonatina.CheckCert
import Fe.Sonatina.Parse
import FeProofs.ERC20.Bytecode

/-!
# FeERC20 through Sonatina's lowering record

The sidecar `fe build --emit sidecar` wrote for FeERC20 (`Fe/Sonatina/Fixtures`), and the facts
the certificate through `check_sound` needs of it: its runtime and init bytes are
`runtime.hex` and `creation.hex`, the bytecode the pinned Fe commit compiles; the creation
code holds the runtime code where the init section's symbol `&FeERC20_runtime` puts it; and the
checker accepts the sidecar.  All four are decided by the kernel.  `runtimeFunc` and `initFunc`
are the machine IR's functions of the two sections, read from the sidecar.
-/

namespace FeProofs.ERC20.Sonatina

open Fe.Sonatina

sonatina_sidecar sidecar "Fe/Sonatina/Fixtures/FeERC20.sidecar.json"

sonatina_func runtimeFunc "Fe/Sonatina/Fixtures/FeERC20.sidecar.json" "runtime"
  "contract_runtime_root_FeERC20"

sonatina_func initFunc "Fe/Sonatina/Fixtures/FeERC20.sidecar.json" "init"
  "contract_init_root_FeERC20"

/-- The sidecar's runtime bytes are `runtime.hex`.  The bytes are compared as lists, which
    the kernel does in one pass. -/
theorem sidecar_runtime : sidecar.code "runtime" = feERC20Bytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The sidecar's init bytes are `creation.hex`. -/
theorem sidecar_init : sidecar.code "init" = feERC20CreationBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The creation bytecode holds the runtime bytecode at offset 124, as the init section's symbol
    `&FeERC20_runtime` says, and is 986 bytes long, its symbol `.`. -/
theorem creation_runtime : feERC20CreationBytecode.extract 124 986 = feERC20Bytecode
    ∧ feERC20CreationBytecode.size = 986 := by
  refine ⟨ByteArray.ext (Array.toList_inj.mp ?_), by decide +kernel⟩
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts the sidecar. -/
theorem sidecar_check : Check.check sidecar = true := by decide +kernel

/-- The pinned bytecode refines the machine IR's model of FeERC20, at `P1`. -/
theorem sidecar_sound : Check.Sound sidecar := Check.check_sound sidecar_check

theorem runtimeFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_runtime_root_FeERC20") = some (some runtimeFunc) := by
  rfl

theorem initFunc_eq : (((sidecar.section? "init").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_init_root_FeERC20") = some (some initFunc) := by
  rfl

end FeProofs.ERC20.Sonatina
