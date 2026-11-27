import Fe.Sonatina.Steps.GvnRewrite
import Fe.Sonatina.Steps.SchemasStepTests

/-!
# Tests of the `gvn_rewrite` checker

Records (`GvnTests/gen.py` writes them): real steps of corpus v6 (`carry` of Bn254Add, with two
inserted phis; `from_slice` of `dyn_array_from_slice`'s Builder, a class; the runtime root of
`storage_bytes_encode_return`'s Blob, two congruent phis; `odd_power` of Modexp, classes through
two levels), hand-written ones (a commutative key, congruent phis, nested inserted phis), and
mutants, each rejected: a class member of another key, no certificate, a leader that does not
dominate the use, two loads merged across a store, two `clz` merged, phis that differ on one
predecessor, a class from an edge predicate (either polarity), dead edges in a rewrite, an
inserted phi with a wrong operand, a wrong term, no term, recorded in another block, after a phi
of the input; and of the real records: a wrong inserted-phi operand, a wrong term, the wrong
inserted phi used, a representative of another class.
-/

namespace Fe.Sonatina.Steps.Schemas.GvnTests

open Fe.Sonatina.Steps.Schemas.StepTests

def GVN (t : OneStep) : Bool := checkGvnRewrite t.1 t.2.1 t.2.2.1 t.2.2.2
def why (t : OneStep) : Option String := diagnoseGvnRewrite t.1 t.2.1 t.2.2.1 t.2.2.2

schema_step gvn_bad_clz "Fe/Sonatina/Steps/GvnTests/gvn_bad_clz.json"
schema_step gvn_bad_dead "Fe/Sonatina/Steps/GvnTests/gvn_bad_dead.json"
schema_step gvn_bad_key "Fe/Sonatina/Steps/GvnTests/gvn_bad_key.json"
schema_step gvn_bad_loads "Fe/Sonatina/Steps/GvnTests/gvn_bad_loads.json"
schema_step gvn_bad_noclass "Fe/Sonatina/Steps/GvnTests/gvn_bad_noclass.json"
schema_step gvn_bad_nodom "Fe/Sonatina/Steps/GvnTests/gvn_bad_nodom.json"
schema_step gvn_bad_phi "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi.json"
schema_step gvn_bad_phi_block "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi_block.json"
schema_step gvn_bad_phi_late "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi_late.json"
schema_step gvn_bad_phi_noterm "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi_noterm.json"
schema_step gvn_bad_phi_operand "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi_operand.json"
schema_step gvn_bad_phi_term "Fe/Sonatina/Steps/GvnTests/gvn_bad_phi_term.json"
schema_step gvn_bad_pred "Fe/Sonatina/Steps/GvnTests/gvn_bad_pred.json"
schema_step gvn_bad_pred_polarity "Fe/Sonatina/Steps/GvnTests/gvn_bad_pred_polarity.json"
schema_step gvn_blob "Fe/Sonatina/Steps/GvnTests/gvn_blob.json"
schema_step gvn_carry "Fe/Sonatina/Steps/GvnTests/gvn_carry.json"
schema_step gvn_carry_bad_operand "Fe/Sonatina/Steps/GvnTests/gvn_carry_bad_operand.json"
schema_step gvn_carry_bad_term "Fe/Sonatina/Steps/GvnTests/gvn_carry_bad_term.json"
schema_step gvn_carry_bad_use "Fe/Sonatina/Steps/GvnTests/gvn_carry_bad_use.json"
schema_step gvn_from_slice "Fe/Sonatina/Steps/GvnTests/gvn_from_slice.json"
schema_step gvn_from_slice_bad_rep "Fe/Sonatina/Steps/GvnTests/gvn_from_slice_bad_rep.json"
schema_step gvn_key "Fe/Sonatina/Steps/GvnTests/gvn_key.json"
schema_step gvn_nested "Fe/Sonatina/Steps/GvnTests/gvn_nested.json"
schema_step gvn_odd_power "Fe/Sonatina/Steps/GvnTests/gvn_odd_power.json"
schema_step gvn_phi "Fe/Sonatina/Steps/GvnTests/gvn_phi.json"

example : GVN gvn_bad_clz = false := by decide +kernel
example : GVN gvn_bad_dead = false := by decide +kernel
example : GVN gvn_bad_key = false := by decide +kernel
example : GVN gvn_bad_loads = false := by decide +kernel
example : GVN gvn_bad_noclass = false := by decide +kernel
example : GVN gvn_bad_nodom = false := by decide +kernel
example : GVN gvn_bad_phi = false := by decide +kernel
example : GVN gvn_bad_phi_block = false := by decide +kernel
example : GVN gvn_bad_phi_late = false := by decide +kernel
example : GVN gvn_bad_phi_noterm = false := by decide +kernel
example : GVN gvn_bad_phi_operand = false := by decide +kernel
example : GVN gvn_bad_phi_term = false := by decide +kernel
example : GVN gvn_bad_pred = false := by decide +kernel
example : GVN gvn_bad_pred_polarity = false := by decide +kernel
example : GVN gvn_blob = true := by decide +kernel
example : GVN gvn_carry = true := by decide +kernel
example : GVN gvn_carry_bad_operand = false := by decide +kernel
example : GVN gvn_carry_bad_term = false := by decide +kernel
example : GVN gvn_carry_bad_use = false := by decide +kernel
example : GVN gvn_from_slice = true := by decide +kernel
example : GVN gvn_from_slice_bad_rep = false := by decide +kernel
example : GVN gvn_key = true := by decide +kernel
example : GVN gvn_nested = true := by decide +kernel
example : GVN gvn_odd_power = true := by decide +kernel
example : GVN gvn_phi = true := by decide +kernel

end Fe.Sonatina.Steps.Schemas.GvnTests
