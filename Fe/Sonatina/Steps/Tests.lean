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

machine_steps_file es_br_same "Fe/Sonatina/Steps/Tests/es_br_same.json"
machine_steps_file es_table_same "Fe/Sonatina/Steps/Tests/es_table_same.json"
machine_steps_file es_br_differ "Fe/Sonatina/Steps/Tests/es_br_differ.json"
machine_steps_file es_table_nodefault "Fe/Sonatina/Steps/Tests/es_table_nodefault.json"
machine_steps_file wf_table_dup "Fe/Sonatina/Steps/Tests/wf_table_dup.json"
machine_steps_file wf_table_ok "Fe/Sonatina/Steps/Tests/wf_table_ok.json"
machine_steps_file es_unreachable "Fe/Sonatina/Steps/Tests/es_unreachable.json"
machine_steps_file es_bad_ssa "Fe/Sonatina/Steps/Tests/es_bad_ssa.json"
machine_steps_file es_two_slots "Fe/Sonatina/Steps/Tests/es_two_slots.json"

/-- The records validate with no symbols: none uses one. -/
abbrev ES := validateWith [.edgeSplit] []

example : ES es_ok (replay es_ok) = true := by decide +kernel
example : ES es_bad_phi (replay es_bad_phi) = false := by decide +kernel
example : ES es_bad_store (replay es_bad_store) = false := by decide +kernel
example : ES es_bad_inst (replay es_bad_inst) = false := by decide +kernel
example : ES es_bad_target (replay es_bad_target) = false := by decide +kernel
example : ES es_bad_swap (replay es_bad_swap) = false := by decide +kernel
/-- A kind outside the allowed list is rejected. -/
example : validateWith [] [] es_ok (replay es_ok) = false := by decide +kernel
/-- The final module must be the composed one. -/
example : ES es_ok (es_ok.module []) = false := by decide +kernel

/-! The lifted restriction: `br v0 block1 block1` and an all-identical `br_table` with a
default become `jump block1`; `br` to different blocks does not. -/
example : ES es_br_same (replay es_br_same) = true := by decide +kernel
example : ES es_table_same (replay es_table_same) = true := by decide +kernel
example : ES es_br_differ (replay es_br_differ) = false := by decide +kernel

/-! Review C-6: a defaultless table turned into `jump` is rejected; so is a table with
duplicate keys, which `wf` rejects in the lowered module. -/
example : ES es_table_nodefault (replay es_table_nodefault) = false := by decide +kernel
example : ES wf_table_dup (replay wf_table_dup) = false := by decide +kernel
example : ES wf_table_ok (replay wf_table_ok) = true := by decide +kernel

/-! Review H-1: a tree whose entry has an immediate dominator is rejected; a function with an
unreachable block jumping into reachable code is accepted, and an input not in SSA form is
rejected. -/

/-- The lowered function of a record of one function. -/
def lowered₀ (r : MachineSteps) : Func := (r.lowered.head?.map (·.func)).getD default

example : (domTree (lowered₀ es_ok)).valid (lowered₀ es_ok) = true := by decide +kernel
example : ({ domTree (lowered₀ es_ok) with idom := (domTree (lowered₀ es_ok)).idom.insert 0 2 }
    : DomTree).valid (lowered₀ es_ok) = false := by decide +kernel
example : ES es_unreachable (replay es_unreachable) = true := by decide +kernel
example : ES es_bad_ssa (replay es_bad_ssa) = false := by decide +kernel

/-- Review 6 F-2: two slots of one block may go to one split block. -/
example : ES es_two_slots (replay es_two_slots) = true := by decide +kernel

end Fe.Sonatina.Steps.Tests
