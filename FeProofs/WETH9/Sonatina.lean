import Fe.Sonatina.CheckCert
import Fe.Sonatina.Parse
import FeProofs.WETH9.Bytecode

/-!
# FeWETH9 through Sonatina's lowering record

The sidecar `fe build --emit sidecar` wrote for WETH9 (`Fe/Sonatina/Fixtures`), and the facts
the certificate through `check_sound` needs of it: its runtime and init bytes are `runtime.hex`
and `creation.hex` of this directory.  Fe `8a33d20257` (Sonatina `bd20fac3`, `-O 1`, `osaka`), the
commit the sidecar comes from, compiles `FeProofs/WETH9` to these same bytes as the commit
`FeWETH9.build.json` names, which was checked by rebuilding it, so the P0 and P1 certificates are
of one bytecode;
the creation code holds the runtime code where the init section's symbol `&WETH9_runtime` puts
it; and the checker accepts the sidecar.  All four are decided by the kernel.  The `*Func`s are
the machine IR's functions of the two sections, read from the sidecar.
-/

namespace FeProofs.WETH9.Sonatina

open Fe.Sonatina

set_option maxRecDepth 100000 in
sonatina_sidecar sidecar "Fe/Sonatina/Fixtures/WETH9.sidecar.json"

sonatina_func runtimeFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime"
  "contract_runtime_root_WETH9"
sonatina_func depositFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime" "deposit"
sonatina_func loadFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime" "load"
sonatina_func returnValueFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime"
  "return_value__g7f54"
sonatina_func revertErrorFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime"
  "revert_error"
sonatina_func storedLenFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime" "stored_len"
sonatina_func transferFromFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "runtime"
  "transfer_from"

sonatina_func initFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "init"
  "contract_init_root_WETH9"
sonatina_func initStoreFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "init" "store"
sonatina_func initStoredLenFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "init" "stored_len"
sonatina_func initRevertErrorFunc "Fe/Sonatina/Fixtures/WETH9.sidecar.json" "init"
  "revert_error"

/-- The sidecar's runtime bytes are `runtime.hex`.  The bytes are compared as lists, which the
    kernel does in one pass. -/
theorem sidecar_runtime : sidecar.code "runtime" = feWETH9Bytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The sidecar's init bytes are `creation.hex`. -/
theorem sidecar_init : sidecar.code "init" = feWETH9CreationBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The creation bytecode holds the runtime bytecode at offset 445, as the init section's symbol
    `&WETH9_runtime` says, and is 2045 bytes long, its symbol `.`. -/
theorem creation_runtime : feWETH9CreationBytecode.extract 445 2045 = feWETH9Bytecode
    ∧ feWETH9CreationBytecode.size = 2045 := by
  refine ⟨ByteArray.ext (Array.toList_inj.mp ?_), by decide +kernel⟩
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts the sidecar. -/
theorem sidecar_check : Check.check sidecar = true := by decide +kernel

/-- The pinned bytecode refines the machine IR's model of WETH9, at `P1`. -/
theorem sidecar_sound : Check.Sound sidecar := Check.check_sound sidecar_check

theorem runtimeFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_runtime_root_WETH9") = some (some runtimeFunc) := by
  rfl

theorem initFunc_eq : (((sidecar.section? "init").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_init_root_WETH9") = some (some initFunc) := by
  rfl

end FeProofs.WETH9.Sonatina
