import Fe.Sonatina.Steps.SchemasStepTests

/-!
# Tests of the `scalar_canonicalize` checker

Records of one step (`ScalarStepTests/gen.py` writes them): real steps of corpus v6
(`sc_real_*`: `shr 248 x → evm_byte 0 x`, `mul x 32 → shl 5 x`, `eq x 0 → is_zero x`, and a dead
`add` deleted), and one hand-written step for every rewrite `scalar_canonicalize.rs` makes on
machine IR (S1–S24); each accepted by kernel evaluation.  The mutants, each breaking one condition
of a rewrite (a wrong constant, a shift not byte-aligned, `sub` with the shared operand crossed,
`mul` by an even or unknown factor, a zero divisor, a sign test against another bound, …) or of
the frame (a renamed result, a replacement by `clz` or by an effectful instruction, an effectful
or used statement deleted, facts, an unread key), rejected.
-/

namespace Fe.Sonatina.Steps.Schemas.ScalarTests

open Fe.Sonatina.Steps Fe.Sonatina.Steps.Schemas.StepTests

def SC (t : OneStep) : Bool := checkScalarCanonicalize t.1 t.2.1 t.2.2.1 t.2.2.2

schema_step sc_addmod0 "Fe/Sonatina/Steps/ScalarStepTests/sc_addmod0.json"
schema_step sc_addmod_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_addmod_bad.json"
schema_step sc_bad_clz "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_clz.json"
schema_step sc_bad_del_effect "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_del_effect.json"
schema_step sc_bad_del_used "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_del_used.json"
schema_step sc_bad_dst "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_dst.json"
schema_step sc_bad_effect "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_effect.json"
schema_step sc_bad_facts "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_facts.json"
schema_step sc_bad_unread "Fe/Sonatina/Steps/ScalarStepTests/sc_bad_unread.json"
schema_step sc_bitpair "Fe/Sonatina/Steps/ScalarStepTests/sc_bitpair.json"
schema_step sc_byte_mask "Fe/Sonatina/Steps/ScalarStepTests/sc_byte_mask.json"
schema_step sc_byte_shl "Fe/Sonatina/Steps/ScalarStepTests/sc_byte_shl.json"
schema_step sc_byte_shl_unaligned_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_byte_shl_unaligned_bad.json"
schema_step sc_byte_shr "Fe/Sonatina/Steps/ScalarStepTests/sc_byte_shr.json"
schema_step sc_byte_shr_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_byte_shr_bad.json"
schema_step sc_cancel_add "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_add.json"
schema_step sc_cancel_add_cross "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_add_cross.json"
schema_step sc_cancel_mul_even_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_mul_even_bad.json"
schema_step sc_cancel_mul_odd "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_mul_odd.json"
schema_step sc_cancel_mul_var_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_mul_var_bad.json"
schema_step sc_cancel_sub "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_sub.json"
schema_step sc_cancel_sub_cross_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_sub_cross_bad.json"
schema_step sc_cancel_xor "Fe/Sonatina/Steps/ScalarStepTests/sc_cancel_xor.json"
schema_step sc_compl_add "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_add.json"
schema_step sc_compl_add_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_add_bad.json"
schema_step sc_compl_shl "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_shl.json"
schema_step sc_compl_shl_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_shl_bad.json"
schema_step sc_compl_sub "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_sub.json"
schema_step sc_compl_sub1 "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_sub1.json"
schema_step sc_compl_sub1_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_sub1_bad.json"
schema_step sc_compl_sub_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_compl_sub_bad.json"
schema_step sc_const_cmp "Fe/Sonatina/Steps/ScalarStepTests/sc_const_cmp.json"
schema_step sc_const_cmp_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_const_cmp_bad.json"
schema_step sc_dyn_div "Fe/Sonatina/Steps/ScalarStepTests/sc_dyn_div.json"
schema_step sc_dyn_div_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_dyn_div_bad.json"
schema_step sc_eq_zero "Fe/Sonatina/Steps/ScalarStepTests/sc_eq_zero.json"
schema_step sc_exp_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_exp_bad.json"
schema_step sc_exp_base2 "Fe/Sonatina/Steps/ScalarStepTests/sc_exp_base2.json"
schema_step sc_exp_sq "Fe/Sonatina/Steps/ScalarStepTests/sc_exp_sq.json"
schema_step sc_merge_div "Fe/Sonatina/Steps/ScalarStepTests/sc_merge_div.json"
schema_step sc_merge_sar "Fe/Sonatina/Steps/ScalarStepTests/sc_merge_sar.json"
schema_step sc_merge_sar_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_merge_sar_bad.json"
schema_step sc_merge_shr "Fe/Sonatina/Steps/ScalarStepTests/sc_merge_shr.json"
schema_step sc_merge_shr_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_merge_shr_bad.json"
schema_step sc_mul_pow2 "Fe/Sonatina/Steps/ScalarStepTests/sc_mul_pow2.json"
schema_step sc_mulmod1 "Fe/Sonatina/Steps/ScalarStepTests/sc_mulmod1.json"
schema_step sc_quot_bad_bound "Fe/Sonatina/Steps/ScalarStepTests/sc_quot_bad_bound.json"
schema_step sc_quot_bad_zero "Fe/Sonatina/Steps/ScalarStepTests/sc_quot_bad_zero.json"
schema_step sc_quot_eq "Fe/Sonatina/Steps/ScalarStepTests/sc_quot_eq.json"
schema_step sc_quot_is_zero "Fe/Sonatina/Steps/ScalarStepTests/sc_quot_is_zero.json"
schema_step sc_real_byte_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_real_byte_bad.json"
schema_step sc_real_canonicalize_evm_byte "Fe/Sonatina/Steps/ScalarStepTests/sc_real_canonicalize_evm_byte.json"
schema_step sc_real_delete_add "Fe/Sonatina/Steps/ScalarStepTests/sc_real_delete_add.json"
schema_step sc_real_eq_zero_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_real_eq_zero_bad.json"
schema_step sc_real_eq_zero_to_is_zero "Fe/Sonatina/Steps/ScalarStepTests/sc_real_eq_zero_to_is_zero.json"
schema_step sc_real_mul_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_real_mul_bad.json"
schema_step sc_real_mul_pow2_to_shl "Fe/Sonatina/Steps/ScalarStepTests/sc_real_mul_pow2_to_shl.json"
schema_step sc_same_round "Fe/Sonatina/Steps/ScalarStepTests/sc_same_round.json"
schema_step sc_sign_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_sign_bad.json"
schema_step sc_sign_sgt_left "Fe/Sonatina/Steps/ScalarStepTests/sc_sign_sgt_left.json"
schema_step sc_sign_sgt_m1 "Fe/Sonatina/Steps/ScalarStepTests/sc_sign_sgt_m1.json"
schema_step sc_sign_slt "Fe/Sonatina/Steps/ScalarStepTests/sc_sign_slt.json"
schema_step sc_signextend "Fe/Sonatina/Steps/ScalarStepTests/sc_signextend.json"
schema_step sc_sub_nots "Fe/Sonatina/Steps/ScalarStepTests/sc_sub_nots.json"
schema_step sc_sub_nots_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_sub_nots_bad.json"
schema_step sc_top_byte "Fe/Sonatina/Steps/ScalarStepTests/sc_top_byte.json"
schema_step sc_top_byte_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_top_byte_bad.json"
schema_step sc_top_field "Fe/Sonatina/Steps/ScalarStepTests/sc_top_field.json"
schema_step sc_top_field_bad "Fe/Sonatina/Steps/ScalarStepTests/sc_top_field_bad.json"
schema_step sc_udiv_pow2 "Fe/Sonatina/Steps/ScalarStepTests/sc_udiv_pow2.json"
schema_step sc_umod_pow2 "Fe/Sonatina/Steps/ScalarStepTests/sc_umod_pow2.json"

/-! ## Accepted -/

example : SC sc_addmod0 = true := by decide +kernel
example : SC sc_bitpair = true := by decide +kernel
example : SC sc_byte_mask = true := by decide +kernel
example : SC sc_byte_shl = true := by decide +kernel
example : SC sc_byte_shr = true := by decide +kernel
example : SC sc_cancel_add = true := by decide +kernel
example : SC sc_cancel_add_cross = true := by decide +kernel
example : SC sc_cancel_mul_odd = true := by decide +kernel
example : SC sc_cancel_sub = true := by decide +kernel
example : SC sc_cancel_xor = true := by decide +kernel
example : SC sc_compl_add = true := by decide +kernel
example : SC sc_compl_shl = true := by decide +kernel
example : SC sc_compl_sub = true := by decide +kernel
example : SC sc_compl_sub1 = true := by decide +kernel
example : SC sc_const_cmp = true := by decide +kernel
example : SC sc_dyn_div = true := by decide +kernel
example : SC sc_eq_zero = true := by decide +kernel
example : SC sc_exp_base2 = true := by decide +kernel
example : SC sc_exp_sq = true := by decide +kernel
example : SC sc_merge_div = true := by decide +kernel
example : SC sc_merge_sar = true := by decide +kernel
example : SC sc_merge_shr = true := by decide +kernel
example : SC sc_mul_pow2 = true := by decide +kernel
example : SC sc_mulmod1 = true := by decide +kernel
example : SC sc_quot_eq = true := by decide +kernel
example : SC sc_quot_is_zero = true := by decide +kernel
example : SC sc_real_canonicalize_evm_byte = true := by decide +kernel
example : SC sc_real_delete_add = true := by decide +kernel
example : SC sc_real_eq_zero_to_is_zero = true := by decide +kernel
example : SC sc_real_mul_pow2_to_shl = true := by decide +kernel
example : SC sc_same_round = true := by decide +kernel
example : SC sc_sign_sgt_left = true := by decide +kernel
example : SC sc_sign_sgt_m1 = true := by decide +kernel
example : SC sc_sign_slt = true := by decide +kernel
example : SC sc_signextend = true := by decide +kernel
example : SC sc_sub_nots = true := by decide +kernel
example : SC sc_top_byte = true := by decide +kernel
example : SC sc_top_field = true := by decide +kernel
example : SC sc_udiv_pow2 = true := by decide +kernel
example : SC sc_umod_pow2 = true := by decide +kernel

/-! ## Rejected -/

example : SC sc_addmod_bad = false := by decide +kernel
example : SC sc_bad_clz = false := by decide +kernel
example : SC sc_bad_del_effect = false := by decide +kernel
example : SC sc_bad_del_used = false := by decide +kernel
example : SC sc_bad_dst = false := by decide +kernel
example : SC sc_bad_effect = false := by decide +kernel
example : SC sc_bad_facts = false := by decide +kernel
example : SC sc_bad_unread = false := by decide +kernel
example : SC sc_byte_shl_unaligned_bad = false := by decide +kernel
example : SC sc_byte_shr_bad = false := by decide +kernel
example : SC sc_cancel_mul_even_bad = false := by decide +kernel
example : SC sc_cancel_mul_var_bad = false := by decide +kernel
example : SC sc_cancel_sub_cross_bad = false := by decide +kernel
example : SC sc_compl_add_bad = false := by decide +kernel
example : SC sc_compl_shl_bad = false := by decide +kernel
example : SC sc_compl_sub1_bad = false := by decide +kernel
example : SC sc_compl_sub_bad = false := by decide +kernel
example : SC sc_const_cmp_bad = false := by decide +kernel
example : SC sc_dyn_div_bad = false := by decide +kernel
example : SC sc_exp_bad = false := by decide +kernel
example : SC sc_merge_sar_bad = false := by decide +kernel
example : SC sc_merge_shr_bad = false := by decide +kernel
example : SC sc_quot_bad_bound = false := by decide +kernel
example : SC sc_quot_bad_zero = false := by decide +kernel
example : SC sc_real_byte_bad = false := by decide +kernel
example : SC sc_real_eq_zero_bad = false := by decide +kernel
example : SC sc_real_mul_bad = false := by decide +kernel
example : SC sc_sign_bad = false := by decide +kernel
example : SC sc_sub_nots_bad = false := by decide +kernel
example : SC sc_top_byte_bad = false := by decide +kernel
example : SC sc_top_field_bad = false := by decide +kernel

end Fe.Sonatina.Steps.Schemas.ScalarTests
