import Fe.Sonatina.CheckCert
import Fe.Sonatina.Parse
import FeProofs.Case44Bank.Bytecode

/-!
# Case44Bank through Sonatina's lowering record

The sidecar `fe build --emit sidecar` wrote for Case44Bank (`Fe/Sonatina/Fixtures`), and the
facts the certificate through `check_sound` needs of it: its runtime and init bytes are the
pinned `runtime.hex` and `creation.hex`, the creation code holds the runtime code where the init
section's symbol `&Case44Bank_runtime` puts it, and the checker accepts the sidecar.  All four
are decided by the kernel.  `runtimeFunc` and `creditFunc` are the machine IR's functions of the
runtime section (its entry and the internal function it calls twice), `initFunc` the init
section's, read from the sidecar.
-/

namespace FeProofs.Case44Bank.Sonatina

open Fe.Sonatina

sonatina_sidecar sidecar "Fe/Sonatina/Fixtures/Case44Bank.sidecar.json"

sonatina_func runtimeFunc "Fe/Sonatina/Fixtures/Case44Bank.sidecar.json" "runtime"
  "contract_runtime_root_Case44Bank"

sonatina_func creditFunc "Fe/Sonatina/Fixtures/Case44Bank.sidecar.json" "runtime" "credit"

sonatina_func initFunc "Fe/Sonatina/Fixtures/Case44Bank.sidecar.json" "init"
  "contract_init_root_Case44Bank"

/-- The sidecar's runtime bytes are the pinned runtime bytecode.  The bytes are compared as
    lists, which the kernel does in one pass. -/
theorem sidecar_runtime : sidecar.code "runtime" = case44BankBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The sidecar's init bytes are the pinned creation bytecode. -/
theorem sidecar_init : sidecar.code "init" = case44BankCreationBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The creation bytecode holds the runtime bytecode at offset 19, as the init section's symbol
    `&Case44Bank_runtime` says, and is 195 bytes long, its symbol `.`. -/
theorem creation_runtime : case44BankCreationBytecode.extract 19 195 = case44BankBytecode
    ∧ case44BankCreationBytecode.size = 195 := by
  refine ⟨ByteArray.ext (Array.toList_inj.mp ?_), by decide +kernel⟩
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts the sidecar. -/
theorem sidecar_check : Check.check sidecar = true := by decide +kernel

/-- The pinned bytecode refines the machine IR's model of Case44Bank, at `P1`. -/
theorem sidecar_sound : Check.Sound sidecar := Check.check_sound sidecar_check

theorem runtimeFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_runtime_root_Case44Bank") = some (some runtimeFunc) := by
  rfl

/-- The runtime section's machine module has `credit` as `creditFunc`: what a call to it
    runs. -/
theorem creditFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "credit") = some (some creditFunc) := by
  rfl

theorem initFunc_eq : (((sidecar.section? "init").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_init_root_Case44Bank") = some (some initFunc) := by
  rfl

end FeProofs.Case44Bank.Sonatina
