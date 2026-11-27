import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read
import Fe.Sonatina.Steps.SchemasStepTests

/-!
# Tests of the `sccp_prune` checker

Records (`SccpPruneTests/gen.py` writes them; no corpus has an `sccp_prune` step), hand-written,
through `validateWith` (so the output's well-formedness counts too) and the check alone.

Accepted: a `br` on a constant condition of each polarity, the block left unreachable deleted with
the block only it reaches (`prune_nz`, `prune_z`); a `br_table` on a constant scrutinee taking a
case (`prune_table_case`) and the default (`prune_table_default`), each becoming a `jump`, and one
left a smaller table, its default and taken case to one block (`prune_table_keep`); a pruned edge
into a block whose phi keeps two live operands (`prune_phi`) and one whose phi is left trivial
(`prune_phi_trivial`); a pruned loop back-edge, the header's phi left trivial (`prune_loop`).

Rejected: the polarity swapped; a wrong constant; a constant of a value SCCP cannot know; no
constant; both slots of a `br` dead; the output going to the dead slot's target, keeping the
`br`, or deleting the live block; facts of other steps (GVN's, finite loops, demanded bits,
ranges) and no SCCP facts; the taken case's slot claimed dead; the default claimed dead where no
key matches; the default pruned with two cases left (the compiler's table without a default,
which is not machine IR); a phi operand dropped from a live edge; the removed edge's operand kept;
the trivial phi replaced by the removed edge's operand; a phi claimed constant though one of its
executable operands is not; the same with the edge of that operand claimed dead from a block whose
condition is no constant (the executable set is the checker's own, the entry's closure over the
slots not claimed dead, so a record can make a block non-executable only by a dead slot, which is
checked); a back-edge claimed dead on a condition that is no constant.
-/

namespace Fe.Sonatina.Steps.Schemas.SccpPruneTests

open Fe.Sonatina.Steps.Schemas.StepTests

/-- The module a record composes to, its steps unchecked. -/
def replay (r : MachineSteps) : Module :=
  r.passes.foldl (fun M p => p.steps.foldl (fun M st => stepOut M st.funcs) M) (r.module [])

/-- The records validate with no symbols: none uses one. -/
abbrev PV (r : MachineSteps) : Bool := validateWith [.sccpPrune] [] r (replay r)

def PRUNE (t : OneStep) : Bool := checkSccpPrune t.1 t.2.1 t.2.2.1 t.2.2.2
def why (t : OneStep) : Option String := diagnoseSccpPrune t.1 t.2.1 t.2.2.1 t.2.2.2

machine_steps_file r_nz "Fe/Sonatina/Steps/SccpPruneTests/prune_nz.json"
machine_steps_file r_z "Fe/Sonatina/Steps/SccpPruneTests/prune_z.json"
machine_steps_file r_table_case "Fe/Sonatina/Steps/SccpPruneTests/prune_table_case.json"
machine_steps_file r_table_default "Fe/Sonatina/Steps/SccpPruneTests/prune_table_default.json"
machine_steps_file r_table_keep "Fe/Sonatina/Steps/SccpPruneTests/prune_table_keep.json"
machine_steps_file r_phi "Fe/Sonatina/Steps/SccpPruneTests/prune_phi.json"
machine_steps_file r_phi_trivial "Fe/Sonatina/Steps/SccpPruneTests/prune_phi_trivial.json"
machine_steps_file r_loop "Fe/Sonatina/Steps/SccpPruneTests/prune_loop.json"
machine_steps_file r_bad_polarity "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_polarity.json"
machine_steps_file r_bad_const "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_const.json"
machine_steps_file r_bad_unjustified "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_unjustified.json"
machine_steps_file r_bad_noconst "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_noconst.json"
machine_steps_file r_bad_both "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_both.json"
machine_steps_file r_bad_target "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_target.json"
machine_steps_file r_bad_kept "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_kept.json"
machine_steps_file r_bad_live_deleted "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_live_deleted.json"
machine_steps_file r_bad_gvn "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_gvn.json"
machine_steps_file r_bad_loops "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_loops.json"
machine_steps_file r_bad_demand "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_demand.json"
machine_steps_file r_bad_ranges "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_ranges.json"
machine_steps_file r_bad_nosccp "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_nosccp.json"
machine_steps_file r_bad_table_key "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_key.json"
machine_steps_file r_bad_table_default "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_default.json"
machine_steps_file r_bad_table_nodefault "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_nodefault.json"
machine_steps_file r_bad_phi_live "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_live.json"
machine_steps_file r_bad_phi_stale "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_stale.json"
machine_steps_file r_bad_phi_trivial "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_trivial.json"
machine_steps_file r_bad_phi_const "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_const.json"
machine_steps_file r_bad_unexec "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_unexec.json"
machine_steps_file r_bad_loop "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_loop.json"

schema_step s_nz "Fe/Sonatina/Steps/SccpPruneTests/prune_nz.json"
schema_step s_z "Fe/Sonatina/Steps/SccpPruneTests/prune_z.json"
schema_step s_table_case "Fe/Sonatina/Steps/SccpPruneTests/prune_table_case.json"
schema_step s_table_default "Fe/Sonatina/Steps/SccpPruneTests/prune_table_default.json"
schema_step s_table_keep "Fe/Sonatina/Steps/SccpPruneTests/prune_table_keep.json"
schema_step s_phi "Fe/Sonatina/Steps/SccpPruneTests/prune_phi.json"
schema_step s_phi_trivial "Fe/Sonatina/Steps/SccpPruneTests/prune_phi_trivial.json"
schema_step s_loop "Fe/Sonatina/Steps/SccpPruneTests/prune_loop.json"
schema_step s_bad_polarity "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_polarity.json"
schema_step s_bad_const "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_const.json"
schema_step s_bad_unjustified "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_unjustified.json"
schema_step s_bad_noconst "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_noconst.json"
schema_step s_bad_both "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_both.json"
schema_step s_bad_target "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_target.json"
schema_step s_bad_kept "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_kept.json"
schema_step s_bad_live_deleted "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_live_deleted.json"
schema_step s_bad_gvn "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_gvn.json"
schema_step s_bad_loops "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_loops.json"
schema_step s_bad_demand "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_demand.json"
schema_step s_bad_ranges "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_ranges.json"
schema_step s_bad_nosccp "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_nosccp.json"
schema_step s_bad_table_key "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_key.json"
schema_step s_bad_table_default "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_default.json"
schema_step s_bad_table_nodefault "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_table_nodefault.json"
schema_step s_bad_phi_live "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_live.json"
schema_step s_bad_phi_stale "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_stale.json"
schema_step s_bad_phi_trivial "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_trivial.json"
schema_step s_bad_phi_const "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_phi_const.json"
schema_step s_bad_unexec "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_unexec.json"
schema_step s_bad_loop "Fe/Sonatina/Steps/SccpPruneTests/prune_bad_loop.json"

/-! Through `validateWith`. -/
example : PV r_nz = true := by decide +kernel
example : PV r_z = true := by decide +kernel
example : PV r_table_case = true := by decide +kernel
example : PV r_table_default = true := by decide +kernel
example : PV r_table_keep = true := by decide +kernel
example : PV r_phi = true := by decide +kernel
example : PV r_phi_trivial = true := by decide +kernel
example : PV r_loop = true := by decide +kernel
example : PV r_bad_polarity = false := by decide +kernel
example : PV r_bad_const = false := by decide +kernel
example : PV r_bad_unjustified = false := by decide +kernel
example : PV r_bad_noconst = false := by decide +kernel
example : PV r_bad_both = false := by decide +kernel
example : PV r_bad_target = false := by decide +kernel
example : PV r_bad_kept = false := by decide +kernel
example : PV r_bad_live_deleted = false := by decide +kernel
example : PV r_bad_gvn = false := by decide +kernel
example : PV r_bad_loops = false := by decide +kernel
example : PV r_bad_demand = false := by decide +kernel
example : PV r_bad_ranges = false := by decide +kernel
example : PV r_bad_nosccp = false := by decide +kernel
example : PV r_bad_table_key = false := by decide +kernel
example : PV r_bad_table_default = false := by decide +kernel
example : PV r_bad_table_nodefault = false := by decide +kernel
example : PV r_bad_phi_live = false := by decide +kernel
example : PV r_bad_phi_stale = false := by decide +kernel
example : PV r_bad_phi_trivial = false := by decide +kernel
example : PV r_bad_phi_const = false := by decide +kernel
example : PV r_bad_unexec = false := by decide +kernel
example : PV r_bad_loop = false := by decide +kernel
/-- Without `sccp_prune` among the allowed kinds, rejected. -/
example : validateWith [] [] r_nz (replay r_nz) = false := by decide +kernel

/-! The check alone.  The two phi mutants are rejected only by the output's well-formedness (a phi
operand from each predecessor and none from elsewhere): the check alone accepts them, soundly, as
an output stuck where its phi has no operand, or with an operand never read. -/
example : PRUNE s_nz = true := by decide +kernel
example : PRUNE s_z = true := by decide +kernel
example : PRUNE s_table_case = true := by decide +kernel
example : PRUNE s_table_default = true := by decide +kernel
example : PRUNE s_table_keep = true := by decide +kernel
example : PRUNE s_phi = true := by decide +kernel
example : PRUNE s_phi_trivial = true := by decide +kernel
example : PRUNE s_loop = true := by decide +kernel
example : PRUNE s_bad_polarity = false := by decide +kernel
example : PRUNE s_bad_const = false := by decide +kernel
example : PRUNE s_bad_unjustified = false := by decide +kernel
example : PRUNE s_bad_noconst = false := by decide +kernel
example : PRUNE s_bad_both = false := by decide +kernel
example : PRUNE s_bad_target = false := by decide +kernel
example : PRUNE s_bad_kept = false := by decide +kernel
example : PRUNE s_bad_live_deleted = false := by decide +kernel
example : PRUNE s_bad_gvn = false := by decide +kernel
example : PRUNE s_bad_loops = false := by decide +kernel
example : PRUNE s_bad_demand = false := by decide +kernel
example : PRUNE s_bad_ranges = false := by decide +kernel
example : PRUNE s_bad_nosccp = false := by decide +kernel
example : PRUNE s_bad_table_key = false := by decide +kernel
example : PRUNE s_bad_table_default = false := by decide +kernel
example : PRUNE s_bad_table_nodefault = false := by decide +kernel
example : PRUNE s_bad_phi_live = true := by decide +kernel
example : PRUNE s_bad_phi_stale = true := by decide +kernel
example : PRUNE s_bad_phi_trivial = false := by decide +kernel
example : PRUNE s_bad_phi_const = false := by decide +kernel
example : PRUNE s_bad_unexec = false := by decide +kernel
example : PRUNE s_bad_loop = false := by decide +kernel

/-! ## The compiler's own `sccp_prune` steps

`real_is_null_O1` and `real_try_alloc_O1` are the sidecars Fe `a4c2ab6eb` (Sonatina `e39b70c4d`)
writes at `-O1` for `real_is_null.fe` and `real_try_alloc.fe`.  Each runtime's message handler
allocates first, at the fresh free pointer, so memory placement gives the allocation a fixed base
(128), which lowering writes as an immediate; the null test of the pointer, which no IR pass
could fold, is then a `br` on the constant 128 (after `branch_canonicalize`), and the machine
stage's SCCP prunes its dead edge.  Both records validate and the byte checker accepts both
sidecars, so `machine_sound_sidecar` applies to them with no hypothesis. -/

sonatina_sidecar realIsNull "Fe/Sonatina/Steps/SccpPruneTests/real_is_null_O1.sidecar.json"
sonatina_sidecar realTryAlloc "Fe/Sonatina/Steps/SccpPruneTests/real_try_alloc_O1.sidecar.json"

example : (realIsNull.stepsOf "runtime").kinds.contains .sccpPrune = true := by decide +kernel
example : (realTryAlloc.stepsOf "runtime").kinds.contains .sccpPrune = true := by decide +kernel

theorem realIsNull_validate : realIsNull.validate = true := by decide +kernel
theorem realIsNull_check : Check.check realIsNull = true := by decide +kernel
theorem realTryAlloc_validate : realTryAlloc.validate = true := by decide +kernel
theorem realTryAlloc_check : Check.check realTryAlloc = true := by decide +kernel

example := machine_sound_sidecar realIsNull_validate realIsNull_check
example := machine_sound_sidecar realTryAlloc_validate realTryAlloc_check

end Fe.Sonatina.Steps.Schemas.SccpPruneTests
