import Fe.Sonatina.CheckCert
import Fe.Sonatina.Parse
import FeProofs.ScalarStore.Bytecode

/-!
# FeScalarStore through Sonatina's lowering record

The sidecar `fe build --emit sidecar` wrote for FeScalarStore (`Fe/Sonatina/Fixtures`), and the
facts the certificate through `check_sound` needs of it: its runtime and init bytes are the
pinned `runtime.hex` and `creation.hex`, and the checker accepts it.  All three are decided by
the kernel.
-/

namespace FeProofs.ScalarStore.Sonatina

open Fe.Sonatina

sonatina_sidecar sidecar "Fe/Sonatina/Fixtures/FeScalarStore.sidecar.json"

/-- The sidecar's runtime bytes are the pinned runtime bytecode. -/
theorem sidecar_runtime : sidecar.code "runtime" = feScalarStoreBytecode := by decide +kernel

/-- The sidecar's init bytes are the pinned creation bytecode. -/
theorem sidecar_init : sidecar.code "init" = feScalarStoreCreationBytecode := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts the sidecar. -/
theorem sidecar_check : Check.check sidecar = true := by decide +kernel

/-- The pinned bytecode refines the machine IR's model of FeScalarStore, at `P1`. -/
theorem sidecar_sound : Check.Sound sidecar := Check.check_sound sidecar_check

end FeProofs.ScalarStore.Sonatina
