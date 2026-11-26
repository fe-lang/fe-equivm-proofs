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
  let v : OneStep := (inp.func, some inp.insts, fs.out, fs.facts)
  let decl := Declaration.defnDecl {
    name := (← getCurrNamespace) ++ name.getId, levelParams := [],
    type := mkConst ``OneStep, value := toExpr v, hints := .abbrev, safety := .safe }
  liftCoreM (addAndCompile decl)

def KBS (t : OneStep) : Bool := checkKnownBitsSimplify t.1 t.2.1 t.2.2.1 t.2.2.2
def SCCP (t : OneStep) : Bool := checkSccpFold t.1 t.2.1 t.2.2.1 t.2.2.2
/-- The demand checker, which the proved one switches off (`demandRounds`). -/
def KBSD (t : OneStep) : Bool := (kbsRejectWith true t.1 t.2.1 t.2.2.1 t.2.2.2).isNone

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

schema_step r13_f1_fuel "Fe/Sonatina/Steps/SchemasStepTests/r13_f1_fuel.json"
schema_step r13_f2_clz_out "Fe/Sonatina/Steps/SchemasStepTests/r13_f2_clz_out.json"
schema_step r13_f2_clz_in "Fe/Sonatina/Steps/SchemasStepTests/r13_f2_clz_in.json"
schema_step r13_f3_ids_base "Fe/Sonatina/Steps/SchemasStepTests/r13_f3_ids_base.json"
schema_step r13_f3_params "Fe/Sonatina/Steps/SchemasStepTests/r13_f3_params.json"
schema_step r13_f3_params_sccp "Fe/Sonatina/Steps/SchemasStepTests/r13_f3_params_sccp.json"
schema_step r13_f3_bigimm "Fe/Sonatina/Steps/SchemasStepTests/r13_f3_bigimm.json"
schema_step r13_f3_i8imm "Fe/Sonatina/Steps/SchemasStepTests/r13_f3_i8imm.json"

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
example : KBSD kb_demand_mixed = false := by decide +kernel
example : KBSD kb_demand_or = true := by decide +kernel
example : KBSD kb_demand_or_small = false := by decide +kernel
/-- Demand rounds are switched off in the proved checker. -/
example : KBS kb_demand_or = false := by decide +kernel
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

schema_step r13_f4_chain "Fe/Sonatina/Steps/SchemasStepTests/r13_f4_chain.json"
schema_step r13_f4_chain_sccp "Fe/Sonatina/Steps/SchemasStepTests/r13_f4_chain_sccp.json"
schema_step r13_f4_deep "Fe/Sonatina/Steps/SchemasStepTests/r13_f4_deep.json"
schema_step r13_f4_same_round "Fe/Sonatina/Steps/SchemasStepTests/r13_f4_same_round.json"
schema_step r13_f4_same_round_demand "Fe/Sonatina/Steps/SchemasStepTests/r13_f4_same_round_demand.json"
schema_step r13_f6_addmod1 "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_addmod1.json"
schema_step r13_f6_addmod2_bad "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_addmod2_bad.json"
schema_step r13_f6_mulmod0a "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_mulmod0a.json"
schema_step r13_f6_mulmod0b "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_mulmod0b.json"
schema_step r13_f6_mulmod1 "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_mulmod1.json"
schema_step r13_f6_phi_fold "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_phi_fold.json"
schema_step r13_f6_phi_fold_bad "Fe/Sonatina/Steps/SchemasStepTests/r13_f6_phi_fold_bad.json"

/-! ## Review 13: the reviewer's inputs for findings 1 to 3, each expected rejected -/

/-- Finding 3's truncated ids: the output's ids emptied, or its block's ids emptied. -/
def r13_f3_ids_none : OneStep :=
  (r13_f3_ids_base.1, r13_f3_ids_base.2.1, { r13_f3_ids_base.2.2.1 with insts := [] }, r13_f3_ids_base.2.2.2)
def r13_f3_ids_empty : OneStep :=
  (r13_f3_ids_base.1, r13_f3_ids_base.2.1, { r13_f3_ids_base.2.2.1 with insts := [[]] }, r13_f3_ids_base.2.2.2)
def r13_f3_ids_none_sccp : OneStep :=
  (r13_f3_ids_none.1, r13_f3_ids_none.2.1, r13_f3_ids_none.2.2.1, { r13_f3_ids_none.2.2.2 with consts := some [] })

example : SCCP r13_f1_fuel = false := by decide +kernel
example : SCCP r13_f2_clz_out = false := by decide +kernel
example : SCCP r13_f2_clz_in = false := by decide +kernel
example : KBS r13_f3_ids_base = false := by decide +kernel
example : KBS r13_f3_ids_none = false := by decide +kernel
example : KBS r13_f3_ids_empty = false := by decide +kernel
example : SCCP r13_f3_ids_none_sccp = false := by decide +kernel
example : KBS r13_f3_params = false := by decide +kernel
example : SCCP r13_f3_params_sccp = false := by decide +kernel
/-- The parser reads `2^256.i256` as `0`: this one is the correct `add 0 0 → 0`. -/
example : KBS r13_f3_bigimm = true := by decide +kernel
/-- The output's literal `2 ^ 256` itself, unreduced, as a record could only give by bypassing
    the parser: rejected by `Operand.wf`. -/
def r13_f3_bigimm_raw : OneStep :=
  (r13_f3_bigimm.1, r13_f3_bigimm.2.1,
    { r13_f3_bigimm.2.2.1 with func := { r13_f3_bigimm.2.2.1.func with
      blocks := r13_f3_bigimm.2.2.1.func.blocks.map fun b =>
        { b with term := .ret [.imm 256 (2 ^ 256)] } } }, r13_f3_bigimm.2.2.2)
example : KBS r13_f3_bigimm_raw = false := by decide +kernel
example : SCCP r13_f3_i8imm = false := by decide +kernel

/-! ## Review 13, findings 4 and 6: what the compiler does, accepted -/

example : KBS r13_f4_chain = true := by decide +kernel
example : SCCP r13_f4_chain_sccp = true := by decide +kernel
example : KBS r13_f4_deep = true := by decide +kernel
example : KBS r13_f4_same_round = true := by decide +kernel
example : KBSD r13_f4_same_round_demand = true := by decide +kernel
example : KBS r13_f4_same_round_demand = false := by decide +kernel
example : SCCP r13_f6_addmod1 = true := by decide +kernel
example : SCCP r13_f6_addmod2_bad = false := by decide +kernel
example : SCCP r13_f6_mulmod0a = true := by decide +kernel
example : SCCP r13_f6_mulmod0b = true := by decide +kernel
example : SCCP r13_f6_mulmod1 = true := by decide +kernel
example : SCCP r13_f6_phi_fold = true := by decide +kernel
example : SCCP r13_f6_phi_fold_bad = false := by decide +kernel

-- Review 13, finding 8: a fact key twice is an error (evaluated, not a proof).
#guard (readFacts [("known_bits", "[]"), ("known_bits", "[]")]).toOption.isNone
#guard (readFacts [("known_bits", "[]")]).toOption.isSome

end Fe.Sonatina.Steps.Schemas.StepTests
