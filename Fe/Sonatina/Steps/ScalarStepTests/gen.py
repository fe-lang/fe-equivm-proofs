# Generates the hand-written scalar_canonicalize records of ScalarStepTests.lean: python3 gen.py
# (here).  Each rewrite of scalar_canonicalize.rs that fires on machine IR, accepted, and mutants
# that break one of its conditions, rejected.  The sc_real_* records are real steps of corpus v6
# (extracted by fe-correctness-scratch/provable-pipeline/scalar-canon/extract.py); their
# mutants are made here from them.
import json

M = 2**256 - 1
NEG = lambda n: (-n) % 2**256

def func(name, params, rets, blocks):
    lines = [f"func private %{name}({', '.join(params)}){' -> ' + ', '.join(rets) if rets else ''} {{"]
    for b, stmts in blocks:
        lines.append(f"    block{b}:")
        lines += [f"        {s};" for s in stmts]
    lines.append("}")
    return "\n".join(lines) + "\n"

def snap(name, params, rets, blocks, insts):
    return {"func": name, "func_ref": 0, "text": func(name, params, rets, blocks), "insts": insts}

def facts(kb=(), unread=False):
    f = {"gvn": None, "known_bits": [[v, str(z), str(o)] for v, z, o in kb], "demanded_bits": None,
         "sccp": None, "finite_loops": [], "ranges": None}
    if unread:
        f["ranges"] = {"unreachable": [0]}
    return f

def one(inp, out, fs):
    return {"profile": "speed", "lowered": [inp], "passes": [{"kind": "scalar_canonicalize",
        "func_behavior": None, "steps": [{"kind": "scalar_canonicalize",
        "funcs": [{"out": out, "facts": fs}]}]}]}

def write(fn, r):
    with open(fn, "w") as f:
        json.dump(r, f, indent=1)

P2 = ["v0.i256", "v1.i256"]
P3 = ["v0.i256", "v1.i256", "v2.i256"]
R = ["i256"]

def rewrite(name, params, body_in, body_out, ids_in, ids_out, fs=None):
    """A one-block function `body_in; return vN` rewritten to `body_out` (lines paired by id)."""
    write(name + ".json", one(snap("f", params, R, [(0, body_in)], [ids_in]),
                              snap("f", params, R, [(0, body_out)], [ids_out]), fs or facts()))

def simple(name, params, prods, root_in, root_out, ret, keep=()):
    """`prods` (deleted unless listed in `keep`), then `root_in` replaced by `root_out` in place."""
    n = len(prods)
    body_in = prods + [root_in, f"return {ret}"]
    kept = [i for i in range(n) if i in keep]
    body_out = [prods[i] for i in kept] + [root_out, f"return {ret}"]
    rewrite(name, params, body_in, body_out, list(range(n + 2)), kept + [n, n + 1])

# S12 merge_shifts, as in Blake2F's `compress` (shr 32 (shr 192 v36) -> shr 224 v36); the inner
# shift is used elsewhere there, so it stays.
simple("sc_merge_shr", P2, ["v2.i256 = shr 192.i256 v0"], "v3.i256 = shr 32.i256 v2",
       "v3.i256 = shr 224.i256 v0", "v3", keep=[0])
simple("sc_merge_shr_bad", P2, ["v2.i256 = shr 192.i256 v0"], "v3.i256 = shr 32.i256 v2",
       "v3.i256 = shr 223.i256 v0", "v3", keep=[0])
simple("sc_merge_sar", P2, ["v2.i256 = sar 200.i256 v0"], "v3.i256 = sar 100.i256 v2",
       "v3.i256 = sar 255.i256 v0", "v3")
simple("sc_merge_sar_bad", P2, ["v2.i256 = sar 200.i256 v0"], "v3.i256 = sar 100.i256 v2",
       "v3.i256 = sar 254.i256 v0", "v3")

# S16 cancel_common_operand.
simple("sc_cancel_add", P3, ["v3.i256 = add v2 v0", "v4.i256 = add v2 v1"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_add_cross", P3, ["v3.i256 = add v0 v2", "v4.i256 = add v2 v1"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_sub", P3, ["v3.i256 = sub v0 v2", "v4.i256 = sub v1 v2"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_sub_cross_bad", P3, ["v3.i256 = sub v2 v0", "v4.i256 = sub v1 v2"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_mul_odd", P3, [f"v3.i256 = mul {NEG(3)}.i256 v0", f"v4.i256 = mul {NEG(3)}.i256 v1"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_mul_even_bad", P3, ["v3.i256 = mul 6.i256 v0", "v4.i256 = mul 6.i256 v1"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_mul_var_bad", P3, ["v3.i256 = mul v2 v0", "v4.i256 = mul v2 v1"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v0 v1", "v5")
simple("sc_cancel_xor", P3, ["v3.i256 = xor v2 v0", "v4.i256 = xor v1 v2"],
       "v5.i256 = eq v3 v4", "v5.i256 = eq v1 v0", "v5")

# S17 quotient zero tests.
simple("sc_quot_is_zero", P2, ["v2.i256 = evm_udiv v0 10.i256"], "v3.i256 = is_zero v2",
       "v3.i256 = lt v0 10.i256", "v3")
simple("sc_quot_eq", P2, ["v2.i256 = evm_udiv v0 10.i256"], "v3.i256 = eq 0.i256 v2",
       "v3.i256 = lt v0 10.i256", "v3")
simple("sc_quot_bad_bound", P2, ["v2.i256 = evm_udiv v0 10.i256"], "v3.i256 = is_zero v2",
       "v3.i256 = lt v0 11.i256", "v3")
simple("sc_quot_bad_zero", P2, ["v2.i256 = evm_udiv v0 0.i256"], "v3.i256 = is_zero v2",
       "v3.i256 = lt v0 0.i256", "v3")

# S18 fold_complemented_arithmetic, and sub of two nots.
simple("sc_compl_sub1", P2, ["v2.i256 = sub v0 1.i256"], "v3.i256 = not v2",
       "v3.i256 = sub 0.i256 v0", "v3")
simple("sc_compl_sub1_bad", P2, ["v2.i256 = sub v0 2.i256"], "v3.i256 = not v2",
       "v3.i256 = sub 0.i256 v0", "v3")
simple("sc_compl_shl", P2, ["v2.i256 = shl v0 1.i256", "v3.i256 = sub v2 1.i256"],
       "v4.i256 = not v3", f"v4.i256 = shl v0 {M}.i256", "v4")
simple("sc_compl_shl_bad", P2, ["v2.i256 = shl v0 2.i256", "v3.i256 = sub v2 1.i256"],
       "v4.i256 = not v3", f"v4.i256 = shl v0 {M}.i256", "v4")
# v1's own definition is pure: the input's term stops at the replacement's operands.
simple("sc_compl_add", P2, ["v5.i256 = add v1 7.i256", "v2.i256 = not v0", "v3.i256 = add v5 v2"],
       "v4.i256 = not v3", "v4.i256 = sub v0 v5", "v4", keep=[0])
simple("sc_compl_add_bad", P2, ["v5.i256 = add v1 7.i256", "v2.i256 = not v0", "v3.i256 = add v5 v2"],
       "v4.i256 = not v3", "v4.i256 = sub v5 v0", "v4", keep=[0])
simple("sc_compl_sub", P2, ["v2.i256 = not v0", "v3.i256 = sub v2 v1"],
       "v4.i256 = not v3", "v4.i256 = add v0 v1", "v4")
simple("sc_compl_sub_bad", P2, ["v2.i256 = not v0", "v3.i256 = sub v2 v1"],
       "v4.i256 = not v3", "v4.i256 = sub v0 v1", "v4")
simple("sc_sub_nots", P2, ["v2.i256 = not v0", "v3.i256 = not v1"],
       "v4.i256 = sub v2 v3", "v4.i256 = sub v1 v0", "v4")
simple("sc_sub_nots_bad", P2, ["v2.i256 = not v0", "v3.i256 = not v1"],
       "v4.i256 = sub v2 v3", "v4.i256 = sub v0 v1", "v4")

# S19 canonicalize_signed_top_field.
simple("sc_top_field", P2, ["v2.i256 = shr 192.i256 v0"], "v3.i256 = evm_signextend 7.i256 v2",
       "v3.i256 = sar 192.i256 v0", "v3")
simple("sc_top_field_bad", P2, ["v2.i256 = shr 184.i256 v0"], "v3.i256 = evm_signextend 7.i256 v2",
       "v3.i256 = sar 184.i256 v0", "v3")
simple("sc_top_byte", P2, ["v2.i256 = evm_byte 0.i256 v0"], "v3.i256 = evm_signextend 0.i256 v2",
       "v3.i256 = sar 248.i256 v0", "v3")
simple("sc_top_byte_bad", P2, ["v2.i256 = evm_byte 1.i256 v0"], "v3.i256 = evm_signextend 0.i256 v2",
       "v3.i256 = sar 248.i256 v0", "v3")

# S20 fold_shifted_byte.
simple("sc_byte_shl", P2, ["v2.i256 = shl 16.i256 v0"], "v3.i256 = evm_byte 3.i256 v2",
       "v3.i256 = evm_byte 5.i256 v0", "v3")
simple("sc_byte_shr", P2, ["v2.i256 = shr 16.i256 v0"], "v3.i256 = evm_byte 3.i256 v2",
       "v3.i256 = evm_byte 1.i256 v0", "v3")
simple("sc_byte_shr_bad", P2, ["v2.i256 = shr 24.i256 v0"], "v3.i256 = evm_byte 2.i256 v2",
       "v3.i256 = evm_byte 0.i256 v0", "v3")
simple("sc_byte_shl_unaligned_bad", P2, ["v2.i256 = shl 12.i256 v0"], "v3.i256 = evm_byte 3.i256 v2",
       "v3.i256 = evm_byte 4.i256 v0", "v3")

# S21 fold_dynamic_pow2_division; the dividend's definition is pure.
simple("sc_dyn_div", P2, ["v5.i256 = add v0 3.i256", "v2.i256 = shl v1 1.i256"],
       "v3.i256 = evm_udiv v5 v2", "v3.i256 = shr v1 v5", "v3", keep=[0])
simple("sc_dyn_div_bad", P2, ["v5.i256 = add v0 3.i256", "v2.i256 = shl v1 2.i256"],
       "v3.i256 = evm_udiv v5 v2", "v3.i256 = shr v1 v5", "v3", keep=[0])

# S22 fold_shifted_sign_test.
simple("sc_sign_slt", P2, ["v2.i256 = sar 8.i256 v0"], "v3.i256 = slt v2 0.i256",
       "v3.i256 = slt v0 0.i256", "v3")
simple("sc_sign_sgt_left", P2, ["v2.i256 = sar 300.i256 v0"], "v3.i256 = sgt 0.i256 v2",
       "v3.i256 = slt v0 0.i256", "v3")
simple("sc_sign_sgt_m1", P2, ["v2.i256 = sar v1 v0"], f"v3.i256 = sgt v2 {M}.i256",
       f"v3.i256 = sgt v0 {M}.i256", "v3")
simple("sc_sign_bad", P2, ["v2.i256 = sar 8.i256 v0"], "v3.i256 = slt v2 1.i256",
       "v3.i256 = slt v0 1.i256", "v3")

# S23 powers of two.
simple("sc_exp_base2", P2, [], "v2.i256 = evm_exp 2.i256 v0", "v2.i256 = shl v0 1.i256", "v2")
simple("sc_exp_sq", P2, [], "v2.i256 = evm_exp v0 2.i256", "v2.i256 = mul v0 v0", "v2")
simple("sc_exp_bad", P2, [], "v2.i256 = evm_exp 3.i256 v0", "v2.i256 = shl v0 1.i256", "v2")

# S24 neutral operands of evm_add_mod / evm_mul_mod.
simple("sc_addmod0", P3, [], "v3.i256 = evm_add_mod 0.i256 v0 v1", "v3.i256 = evm_umod v0 v1", "v3")
simple("sc_mulmod1", P3, [], "v3.i256 = evm_mul_mod v0 1.i256 v1", "v3.i256 = evm_umod v0 v1", "v3")
simple("sc_addmod_bad", P3, [], "v3.i256 = evm_add_mod v0 1.i256 v1", "v3.i256 = evm_umod v0 v1", "v3")

# Design-era schemas through the scalar mode: S1, S3, S4, S5, S9, S11, S13, S14, S15.
simple("sc_bitpair", P2, ["v2.i256 = and v0 v1", "v3.i256 = xor v1 v0"], "v4.i256 = or v2 v3",
       "v4.i256 = or v0 v1", "v4")
simple("sc_byte_mask", P2, ["v2.i256 = shr 8.i256 v0"], "v3.i256 = and 255.i256 v2",
       "v3.i256 = evm_byte 30.i256 v0", "v3")
simple("sc_signextend", P2, ["v2.i256 = shl 248.i256 v0"], "v3.i256 = sar 248.i256 v2",
       "v3.i256 = evm_signextend 0.i256 v0", "v3")
simple("sc_const_cmp", P2, ["v2.i256 = sub 10.i256 v0"], "v3.i256 = eq v2 3.i256",
       "v3.i256 = eq v0 7.i256", "v3")
simple("sc_const_cmp_bad", P2, ["v2.i256 = sub 10.i256 v0"], "v3.i256 = eq v2 3.i256",
       "v3.i256 = eq v0 13.i256", "v3")
simple("sc_eq_zero", P2, [], "v2.i256 = eq 0.i256 v0", "v2.i256 = is_zero v0", "v2")
simple("sc_mul_pow2", P2, [], "v2.i256 = mul v0 8.i256", "v2.i256 = shl 3.i256 v0", "v2")
simple("sc_merge_div", P2, ["v2.i256 = evm_udiv v0 3.i256"], "v3.i256 = evm_udiv v2 7.i256",
       "v3.i256 = evm_udiv v0 21.i256", "v3")
simple("sc_udiv_pow2", P2, [], "v2.i256 = evm_udiv v0 32.i256", "v2.i256 = shr 5.i256 v0", "v2")
simple("sc_umod_pow2", P2, [], "v2.i256 = evm_umod v0 32.i256", "v2.i256 = and v0 31.i256", "v2")

# The frame.  A rewrite in a round whose operand is itself rewritten (review 9, finding 4):
# both multiplications become shifts, the second's operand being the first's result.
rewrite("sc_same_round", P2, ["v2.i256 = mul v0 8.i256", "v3.i256 = mul v2 4.i256", "return v3"],
        ["v2.i256 = shl 3.i256 v0", "v3.i256 = shl 2.i256 v2", "return v3"], [0, 1, 2], [0, 1, 2])
# Rejected: the result renamed; replaced by `clz` or by an effectful instruction; an effectful
# or used statement deleted; facts present; an unread key.
rewrite("sc_bad_dst", P2, ["v2.i256 = mul v0 8.i256", "return v2"],
        ["v3.i256 = shl 3.i256 v0", "return v3"], [0, 1], [0, 1])
rewrite("sc_bad_clz", P2, ["v2.i256 = sub 255.i256 v0", "return v2"],
        ["v2.i256 = clz v0", "return v2"], [0, 1], [0, 1])
rewrite("sc_bad_effect", P2, ["v2.i256 = add v0 0.i256", "return v2"],
        ["v2.i256 = evm_mload v0", "return v2"], [0, 1], [0, 1])
rewrite("sc_bad_del_effect", P2, ["v2.i256 = evm_mload v0", "v3.i256 = mul v1 8.i256", "return v3"],
        ["v3.i256 = shl 3.i256 v1", "return v3"], [0, 1, 2], [1, 2])
rewrite("sc_bad_del_used", P2, ["v2.i256 = shr 192.i256 v0", "v3.i256 = shr 32.i256 v2", "return v2"],
        ["v3.i256 = shr 224.i256 v0", "return v2"], [0, 1, 2], [1, 2])
rewrite("sc_bad_facts", P2, ["v2.i256 = mul v0 8.i256", "return v2"],
        ["v2.i256 = shl 3.i256 v0", "return v2"], [0, 1], [0, 1], facts(kb=[(0, M ^ 255, 0)]))
rewrite("sc_bad_unread", P2, ["v2.i256 = mul v0 8.i256", "return v2"],
        ["v2.i256 = shl 3.i256 v0", "return v2"], [0, 1], [0, 1], facts(unread=True))

# Mutants of the real records: one changed literal or operand in a rewritten line.
def mutate(src, dst, old, new):
    r = json.load(open(src + ".json"))
    out = r["passes"][0]["steps"][0]["funcs"][0]["out"]
    assert out["text"].count(old) == 1, (src, old)
    out["text"] = out["text"].replace(old, new)
    write(dst + ".json", r)

mutate("sc_real_canonicalize_evm_byte", "sc_real_byte_bad", "v8.i256 = evm_byte 0.i256 v7",
       "v8.i256 = evm_byte 1.i256 v7")
mutate("sc_real_mul_pow2_to_shl", "sc_real_mul_bad", "v14.i256 = shl 5.i256 v2",
       "v14.i256 = shl 4.i256 v2")
mutate("sc_real_eq_zero_to_is_zero", "sc_real_eq_zero_bad", "v18.i256 = is_zero v14",
       "v18.i256 = is_zero v10")
