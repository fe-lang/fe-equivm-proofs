import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read

/-!
# Tests of the machine-step checkers

Hand-written records (`Tests/gen.py` writes them): small machine-IR functions before and after
a step, which `validateWith` accepts by kernel evaluation, and mutations of them, which it
rejects.  The final module is the record's own composition (`replay`), so these test the step
checkers; the comparison with a sidecar's machine IR is the same `decide` on modules.
-/

namespace Fe.Sonatina.Steps.Tests

/-- The module a record composes to, its steps unchecked. -/
def replay (r : MachineSteps) : Module :=
  r.passes.foldl (fun M p => p.steps.foldl (fun M st => stepOut M st.funcs) M) (r.module [])

machine_steps_file es_ok "Fe/Sonatina/Steps/Tests/edge_split.json"
machine_steps_file es_bad_phi "Fe/Sonatina/Steps/Tests/edge_split_bad_phi.json"
machine_steps_file es_bad_store "Fe/Sonatina/Steps/Tests/edge_split_bad_store.json"
machine_steps_file es_bad_inst "Fe/Sonatina/Steps/Tests/edge_split_bad_inst.json"
machine_steps_file es_bad_target "Fe/Sonatina/Steps/Tests/edge_split_bad_target.json"
machine_steps_file es_bad_swap "Fe/Sonatina/Steps/Tests/edge_split_bad_swap.json"

example : validateWith [.edgeSplit] es_ok (replay es_ok) = true := by decide +kernel
example : validateWith [.edgeSplit] es_bad_phi (replay es_bad_phi) = false := by decide +kernel
example : validateWith [.edgeSplit] es_bad_store (replay es_bad_store) = false := by decide +kernel
example : validateWith [.edgeSplit] es_bad_inst (replay es_bad_inst) = false := by decide +kernel
example : validateWith [.edgeSplit] es_bad_target (replay es_bad_target) = false := by
  decide +kernel
example : validateWith [.edgeSplit] es_bad_swap (replay es_bad_swap) = false := by decide +kernel
/-- A kind outside the allowed list is rejected. -/
example : validateWith [] es_ok (replay es_ok) = false := by decide +kernel
/-- The final module must be the composed one. -/
example : validateWith [.edgeSplit] es_ok (es_ok.module []) = false := by decide +kernel

end Fe.Sonatina.Steps.Tests
