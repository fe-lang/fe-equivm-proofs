import Fe.Sonatina.CheckCert
import Fe.Sonatina.Parse
import FeProofs.Deposit.Bytecode

/-!
# FeDeposit through Sonatina's lowering record

The sidecar `fe build --emit sidecar` wrote for the deposit contract (`Fe/Sonatina/Fixtures`),
and the facts the certificate through `check_sound` needs of it: its runtime and init bytes are
`runtime.hex` and `creation.hex` of this directory, which Fe `6e2e10fe24` (the commit `fe.pin`
names and `FeDeposit.build.json` records) compiles `FeDeposit.fe` to, as `check_bytecode.sh`
checks; the creation code holds the runtime code where the init section's symbol
`&DepositContract_runtime` puts it; and the checker accepts the sidecar.  All four are decided by
the kernel.  The `*Func`s are the machine IR's functions of the two sections, read from the
sidecar.
-/

namespace FeProofs.Deposit.Sonatina

open Fe.Sonatina

set_option maxRecDepth 100000 in
sonatina_sidecar sidecar "Fe/Sonatina/Fixtures/DepositContract.sidecar.json"

sonatina_func runtimeFunc "Fe/Sonatina/Fixtures/DepositContract.sidecar.json" "runtime"
  "contract_runtime_root_DepositContract"
sonatina_func copyFunc "Fe/Sonatina/Fixtures/DepositContract.sidecar.json" "runtime"
  "copy_dynamic_payload_from_with_input_len"

sonatina_func initFunc "Fe/Sonatina/Fixtures/DepositContract.sidecar.json" "init"
  "contract_init_root_DepositContract"

/-- The sidecar's runtime bytes are `runtime.hex`.  The bytes are compared as lists, which the
    kernel does in one pass. -/
theorem sidecar_runtime : sidecar.code "runtime" = feDepositBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The sidecar's init bytes are `creation.hex`. -/
theorem sidecar_init : sidecar.code "init" = feDepositCreationBytecode :=
  ByteArray.ext (Array.toList_inj.mp (by decide +kernel))

/-- The creation bytecode holds the runtime bytecode at offset 80, as the init section's symbol
    `&DepositContract_runtime` says, and is 2341 bytes long, its symbol `.`. -/
theorem creation_runtime : feDepositCreationBytecode.extract 80 2341 = feDepositBytecode
    ∧ feDepositCreationBytecode.size = 2341 := by
  refine ⟨ByteArray.ext (Array.toList_inj.mp ?_), by decide +kernel⟩
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts the sidecar. -/
theorem sidecar_check : Check.check sidecar = true := by decide +kernel

/-- The pinned bytecode refines the machine IR's model of the deposit contract, at `P1`. -/
theorem sidecar_sound : Check.Sound sidecar := Check.check_sound sidecar_check

theorem runtimeFunc_eq : (((sidecar.section? "runtime").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_runtime_root_DepositContract") = some (some runtimeFunc) := by
  rfl

theorem initFunc_eq : (((sidecar.section? "init").bind (·.lowering)).map fun low =>
    low.machine.func? "contract_init_root_DepositContract") = some (some initFunc) := by
  rfl

end FeProofs.Deposit.Sonatina
