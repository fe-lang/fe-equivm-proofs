import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read
import Fe.Sonatina.Steps.SchemasStepTests

/-!
# Tests of the `gvn_prune` checker

Records (`GvnPruneTests/gen.py` writes them).  Hand-written, through `validateWith` (so the
output's well-formedness counts too) and the check alone: a `br` on a boolean whose class has the
condition of a dominating branch (`prune_br`), the same leaving a phi trivial (`prune_phi`), a phi
equal to `0` through a `br_table` case predicate at its predecessor's end (`prune_case`); and
mutants, each rejected: the predicates' polarity swapped, no class, no predicate, `c = 1` of a
word condition (with and without known bits claiming it boolean), the slot taken claimed dead, the
output jumping to the dead slot's target, a predicate used where its target does not dominate, a
target with a second live slot into it, GVN's old `not` peel on a word, a predicate of the
condition that does not decide the branch, a phi operand dropped from a live edge, the removed
edge's operand kept, a case predicate of the wrong key, a non-constant phi, a predicate of the
default slot, a dead slot of a `br_table`, both slots of a `br` dead.  Real steps of corpus v6
(the 265: `erc4337` EntryPoint, `lane_holds_before_halts` C, the Blob of
`storage_bytes_encode_return` and of `storage_bytes_to_memory`), by the check alone, and two of
them with their predicates or classes removed, rejected.
-/

namespace Fe.Sonatina.Steps.Schemas.GvnPruneTests

open Fe.Sonatina.Steps.Schemas.StepTests

/-- The module a record composes to, its steps unchecked. -/
def replay (r : MachineSteps) : Module :=
  r.passes.foldl (fun M p => p.steps.foldl (fun M st => stepOut M st.funcs) M) (r.module [])

/-- The records validate with no symbols: none uses one. -/
abbrev PV (r : MachineSteps) : Bool := validateWith [.gvnPrune] [] r (replay r)

def PRUNE (t : OneStep) : Bool := checkGvnPrune t.1 t.2.1 t.2.2.1 t.2.2.2
def why (t : OneStep) : Option String := diagnoseGvnPrune t.1 t.2.1 t.2.2.1 t.2.2.2

machine_steps_file r_br "Fe/Sonatina/Steps/GvnPruneTests/prune_br.json"
machine_steps_file r_phi "Fe/Sonatina/Steps/GvnPruneTests/prune_phi.json"
machine_steps_file r_case "Fe/Sonatina/Steps/GvnPruneTests/prune_case.json"
machine_steps_file r_bad_polarity "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_polarity.json"
machine_steps_file r_bad_noclass "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_noclass.json"
machine_steps_file r_bad_nopred "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_nopred.json"
machine_steps_file r_bad_word "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_word.json"
machine_steps_file r_bad_word_kb "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_word_kb.json"
machine_steps_file r_bad_taken "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_taken.json"
machine_steps_file r_bad_target "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_target.json"
machine_steps_file r_bad_nodom "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_nodom.json"
machine_steps_file r_bad_twoin "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_twoin.json"
machine_steps_file r_bad_not "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_not.json"
machine_steps_file r_bad_not2 "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_not2.json"
machine_steps_file r_bad_phi_live "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_phi_live.json"
machine_steps_file r_bad_phi_stale "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_phi_stale.json"
machine_steps_file r_bad_case_key "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_key.json"
machine_steps_file r_bad_case_phi "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_phi.json"
machine_steps_file r_bad_case_slot "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_slot.json"
machine_steps_file r_bad_table_slot "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_table_slot.json"
machine_steps_file r_bad_both "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_both.json"

schema_step s_br "Fe/Sonatina/Steps/GvnPruneTests/prune_br.json"
schema_step s_phi "Fe/Sonatina/Steps/GvnPruneTests/prune_phi.json"
schema_step s_case "Fe/Sonatina/Steps/GvnPruneTests/prune_case.json"
schema_step s_bad_polarity "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_polarity.json"
schema_step s_bad_noclass "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_noclass.json"
schema_step s_bad_nopred "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_nopred.json"
schema_step s_bad_word "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_word.json"
schema_step s_bad_word_kb "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_word_kb.json"
schema_step s_bad_taken "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_taken.json"
schema_step s_bad_target "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_target.json"
schema_step s_bad_nodom "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_nodom.json"
schema_step s_bad_twoin "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_twoin.json"
schema_step s_bad_not "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_not.json"
schema_step s_bad_not2 "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_not2.json"
schema_step s_bad_case_key "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_key.json"
schema_step s_bad_case_phi "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_phi.json"
schema_step s_bad_case_slot "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_case_slot.json"
schema_step s_bad_table_slot "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_table_slot.json"
schema_step s_bad_both "Fe/Sonatina/Steps/GvnPruneTests/prune_bad_both.json"

schema_step s_entrypoint "Fe/Sonatina/Steps/GvnPruneTests/prune_entrypoint.json"
schema_step s_c "Fe/Sonatina/Steps/GvnPruneTests/prune_c.json"
schema_step s_blob "Fe/Sonatina/Steps/GvnPruneTests/prune_blob.json"
schema_step s_blob_mem "Fe/Sonatina/Steps/GvnPruneTests/prune_blob_mem.json"
schema_step s_c_bad_nopreds "Fe/Sonatina/Steps/GvnPruneTests/prune_c_bad_nopreds.json"
schema_step s_c_bad_nocls "Fe/Sonatina/Steps/GvnPruneTests/prune_c_bad_nocls.json"
schema_step s_blob_bad_nopreds "Fe/Sonatina/Steps/GvnPruneTests/prune_blob_bad_nopreds.json"
schema_step s_blob_bad_nocls "Fe/Sonatina/Steps/GvnPruneTests/prune_blob_bad_nocls.json"

/-! Hand-written, through `validateWith`. -/
example : PV r_br = true := by decide +kernel
example : PV r_phi = true := by decide +kernel
example : PV r_case = true := by decide +kernel
example : PV r_bad_polarity = false := by decide +kernel
example : PV r_bad_noclass = false := by decide +kernel
example : PV r_bad_nopred = false := by decide +kernel
example : PV r_bad_word = false := by decide +kernel
example : PV r_bad_word_kb = false := by decide +kernel
example : PV r_bad_taken = false := by decide +kernel
example : PV r_bad_target = false := by decide +kernel
example : PV r_bad_nodom = false := by decide +kernel
example : PV r_bad_twoin = false := by decide +kernel
example : PV r_bad_not = false := by decide +kernel
example : PV r_bad_not2 = false := by decide +kernel
example : PV r_bad_phi_live = false := by decide +kernel
example : PV r_bad_phi_stale = false := by decide +kernel
example : PV r_bad_case_key = false := by decide +kernel
example : PV r_bad_case_phi = false := by decide +kernel
example : PV r_bad_case_slot = false := by decide +kernel
example : PV r_bad_table_slot = false := by decide +kernel
example : PV r_bad_both = false := by decide +kernel
/-- Without `gvn_prune` among the allowed kinds, rejected. -/
example : validateWith [] [] r_br (replay r_br) = false := by decide +kernel

/-! The check alone.  The two phi mutants are rejected only by the output's well-formedness (a phi
operand from each predecessor): the check alone accepts them, soundly, as an output stuck where
its phi has no operand, or one never read. -/
example : PRUNE s_br = true := by decide +kernel
example : PRUNE s_phi = true := by decide +kernel
example : PRUNE s_case = true := by decide +kernel
example : PRUNE s_bad_polarity = false := by decide +kernel
example : PRUNE s_bad_noclass = false := by decide +kernel
example : PRUNE s_bad_nopred = false := by decide +kernel
example : PRUNE s_bad_word = false := by decide +kernel
example : PRUNE s_bad_word_kb = false := by decide +kernel
example : PRUNE s_bad_taken = false := by decide +kernel
example : PRUNE s_bad_target = false := by decide +kernel
example : PRUNE s_bad_nodom = false := by decide +kernel
example : PRUNE s_bad_twoin = false := by decide +kernel
example : PRUNE s_bad_not = false := by decide +kernel
example : PRUNE s_bad_not2 = false := by decide +kernel
example : PRUNE s_bad_case_key = false := by decide +kernel
example : PRUNE s_bad_case_phi = false := by decide +kernel
example : PRUNE s_bad_case_slot = false := by decide +kernel
example : PRUNE s_bad_table_slot = false := by decide +kernel
example : PRUNE s_bad_both = false := by decide +kernel

/-! Real steps. -/
example : PRUNE s_entrypoint = true := by decide +kernel
example : PRUNE s_c = true := by decide +kernel
example : PRUNE s_blob = true := by decide +kernel
example : PRUNE s_blob_mem = true := by decide +kernel
example : PRUNE s_c_bad_nopreds = false := by decide +kernel
example : PRUNE s_c_bad_nocls = false := by decide +kernel
example : PRUNE s_blob_bad_nopreds = false := by decide +kernel
example : PRUNE s_blob_bad_nocls = false := by decide +kernel

end Fe.Sonatina.Steps.Schemas.GvnPruneTests
