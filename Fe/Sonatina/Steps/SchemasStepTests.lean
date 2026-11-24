import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.Read

/-!
# Tests of the `known_bits_simplify` and `sccp_fold` checkers

Hand-written records (`SchemasStepTests/gen.py` writes them): one function before and after one
step, with the step's facts.  The accepted ones by kernel evaluation, and mutations of them
(wrong constants, facts too strong, an effectful or `clz` deletion, a dead edge that is taken,
a demand too small, an exact rewrite in a demand round, a shift by 256, a fact that is no
post-fixpoint, a fact no transfer can derive, an unknown fact key), rejected.
-/

namespace Fe.Sonatina.Steps.Schemas.StepTests

open Lean Elab Command Fe.Sonatina.Steps

/-- A record's one step: the input function and ids, the output snapshot, the facts. -/
abbrev OneStep := Func × Option (List (List Nat)) × FuncSnap × StepFacts

/-- `schema_step name "path"`: the first step of the record file, read at elaboration. -/
elab "schema_step " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  let r ← match Json.parse text >>= Read.parseMachineSteps with
    | .ok r => pure r
    | .error e => throwError "{path.getString}: {e}"
  let some inp := r.lowered.head? | throwError "no lowered function"
  let some fs := r.passes.head? >>= (·.steps.head?) >>= (·.funcs.head?) | throwError "no step"
  let F ← match readFacts fs.facts with
    | .ok F => pure F
    | .error e => throwError "facts: {e}"
  let v : OneStep := (inp.func, some inp.insts, fs.out, F)
  let decl := Declaration.defnDecl {
    name := (← getCurrNamespace) ++ name.getId, levelParams := [],
    type := mkConst ``OneStep, value := toExpr v, hints := .abbrev, safety := .safe }
  liftCoreM (addAndCompile decl)

def KBS (t : OneStep) : Bool := checkKnownBitsSimplify t.1 t.2.1 t.2.2.1 t.2.2.2
def SCCP (t : OneStep) : Bool := checkSccpFold t.1 t.2.1 t.2.2.1 t.2.2.2

schema_step kb_add0 "Fe/Sonatina/Steps/SchemasStepTests/kb_add0.json"
schema_step kb_add0_bad_const "Fe/Sonatina/Steps/SchemasStepTests/kb_add0_bad_const.json"
schema_step kb_add0_unread "Fe/Sonatina/Steps/SchemasStepTests/kb_add0_unread.json"
schema_step kb_and_arg_nofact "Fe/Sonatina/Steps/SchemasStepTests/kb_and_arg_nofact.json"
schema_step kb_and_badfact "Fe/Sonatina/Steps/SchemasStepTests/kb_and_badfact.json"
schema_step kb_and_mask "Fe/Sonatina/Steps/SchemasStepTests/kb_and_mask.json"
schema_step kb_and_mask_bad_copy "Fe/Sonatina/Steps/SchemasStepTests/kb_and_mask_bad_copy.json"
schema_step kb_and_mask_derived "Fe/Sonatina/Steps/SchemasStepTests/kb_and_mask_derived.json"
schema_step kb_and_mask_strong "Fe/Sonatina/Steps/SchemasStepTests/kb_and_mask_strong.json"
schema_step kb_bad_del_effect "Fe/Sonatina/Steps/SchemasStepTests/kb_bad_del_effect.json"
schema_step kb_demand_mixed "Fe/Sonatina/Steps/SchemasStepTests/kb_demand_mixed.json"
schema_step kb_demand_or "Fe/Sonatina/Steps/SchemasStepTests/kb_demand_or.json"
schema_step kb_demand_or_small "Fe/Sonatina/Steps/SchemasStepTests/kb_demand_or_small.json"
schema_step kb_undo_shift "Fe/Sonatina/Steps/SchemasStepTests/kb_undo_shift.json"
schema_step kb_undo_shift_256 "Fe/Sonatina/Steps/SchemasStepTests/kb_undo_shift_256.json"
schema_step sc_bad_clz "Fe/Sonatina/Steps/SchemasStepTests/sc_bad_clz.json"
schema_step sc_bad_param "Fe/Sonatina/Steps/SchemasStepTests/sc_bad_param.json"
schema_step sc_const "Fe/Sonatina/Steps/SchemasStepTests/sc_const.json"
schema_step sc_const_bad_claim "Fe/Sonatina/Steps/SchemasStepTests/sc_const_bad_claim.json"
schema_step sc_const_bad_use "Fe/Sonatina/Steps/SchemasStepTests/sc_const_bad_use.json"
schema_step sc_const_unread "Fe/Sonatina/Steps/SchemasStepTests/sc_const_unread.json"
schema_step sc_is_zero "Fe/Sonatina/Steps/SchemasStepTests/sc_is_zero.json"
schema_step sc_is_zero_bad "Fe/Sonatina/Steps/SchemasStepTests/sc_is_zero_bad.json"
schema_step sc_phi "Fe/Sonatina/Steps/SchemasStepTests/sc_phi.json"
schema_step sc_phi_bad_cond "Fe/Sonatina/Steps/SchemasStepTests/sc_phi_bad_cond.json"
schema_step sc_phi_bad_dead "Fe/Sonatina/Steps/SchemasStepTests/sc_phi_bad_dead.json"

example : KBS kb_add0 = true := by decide +kernel
example : KBS kb_add0_bad_const = false := by decide +kernel
example : KBS kb_add0_unread = false := by decide +kernel
example : KBS kb_and_arg_nofact = false := by decide +kernel
example : KBS kb_and_badfact = false := by decide +kernel
example : KBS kb_and_mask = true := by decide +kernel
example : KBS kb_and_mask_bad_copy = false := by decide +kernel
example : KBS kb_and_mask_derived = true := by decide +kernel
example : KBS kb_and_mask_strong = false := by decide +kernel
example : KBS kb_bad_del_effect = false := by decide +kernel
example : KBS kb_demand_mixed = false := by decide +kernel
example : KBS kb_demand_or = true := by decide +kernel
example : KBS kb_demand_or_small = false := by decide +kernel
example : KBS kb_undo_shift = true := by decide +kernel
example : KBS kb_undo_shift_256 = false := by decide +kernel
example : SCCP sc_bad_clz = false := by decide +kernel
example : SCCP sc_bad_param = false := by decide +kernel
example : SCCP sc_const = true := by decide +kernel
example : SCCP sc_const_bad_claim = false := by decide +kernel
example : SCCP sc_const_bad_use = false := by decide +kernel
example : SCCP sc_const_unread = false := by decide +kernel
example : SCCP sc_is_zero = true := by decide +kernel
example : SCCP sc_is_zero_bad = false := by decide +kernel
example : SCCP sc_phi = true := by decide +kernel
example : SCCP sc_phi_bad_cond = false := by decide +kernel
example : SCCP sc_phi_bad_dead = false := by decide +kernel

end Fe.Sonatina.Steps.Schemas.StepTests
