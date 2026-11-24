# Generates the hand-written step records of SchemasStepTests.lean: python3 gen.py (here).
import json

M = 2**256 - 1

def func(name, params, rets, blocks):
    lines = [f"func private %{name}({', '.join(params)}){' -> ' + ', '.join(rets) if rets else ''} {{"]
    for b, stmts in blocks:
        lines.append(f"    block{b}:")
        lines += [f"        {s};" for s in stmts]
    lines.append("}")
    return "\n".join(lines) + "\n"

def snap(name, params, rets, blocks, insts):
    return {"func": name, "func_ref": 0, "text": func(name, params, rets, blocks), "insts": insts}

def facts(kb=(), db=None, consts=None, dead=(), gvn=None):
    return {"gvn": gvn,
            "known_bits": [[v, str(z), str(o)] for v, z, o in kb],
            "demanded_bits": None if db is None else [[v, str(m)] for v, m in db],
            "sccp": None if consts is None else {"consts": [[v, str(c)] for v, c in consts],
                                                  "dead_edges": [list(e) for e in dead]},
            "finite_loops": [], "ranges": None}

def one(kind, inp, out, fs):
    return {"profile": "speed", "lowered": [inp], "passes": [{"kind": kind, "func_behavior": None,
        "steps": [{"kind": kind, "funcs": [{"out": out, "facts": fs}]}]}]}

def write(fn, r):
    with open(fn, "w") as f:
        json.dump(r, f, indent=1)

P, R = ["v0.i256"], ["i256"]
KBS, SCCP = "known_bits_simplify", "sccp_fold"

# I1 at depth 1: add 0 32 -> 32 (the corpus's commonest rewrite).
add_in = snap("f", P, [], [(0, ["v1.i256 = add 0.i256 32.i256", "evm_mstore v1 v0", "return"])], [[0, 1, 2]])
add_out = snap("f", P, [], [(0, ["evm_mstore 32.i256 v0", "return"])], [[1, 2]])
write("kb_add0.json", one(KBS, add_in, add_out, facts()))
# Rejected: the wrong constant; an effectful instruction deleted.
write("kb_add0_bad_const.json", one(KBS, add_in,
    snap("f", P, [], [(0, ["evm_mstore 33.i256 v0", "return"])], [[1, 2]]), facts()))
ld_in = snap("f", P, [], [(0, ["v1.i256 = evm_sload 0.i256", "v2.i256 = add v1 0.i256", "evm_mstore 0.i256 v2", "return"])], [[0, 1, 2, 3]])
ld_out = snap("f", P, [], [(0, ["evm_mstore 0.i256 v1", "return"])], [[2, 3]])
write("kb_bad_del_effect.json", one(KBS, ld_in, ld_out, facts()))

# I5: and (shr 248 v0) 255 -> shr 248 v0, from v1's known bits.
and_in = snap("f", P, R, [(0, ["v1.i256 = shr 248.i256 v0", "v2.i256 = and v1 255.i256", "return v2"])], [[0, 1, 2]])
and_out = snap("f", P, R, [(0, ["v1.i256 = shr 248.i256 v0", "return v1"])], [[0, 2]])
write("kb_and_mask.json", one(KBS, and_in, and_out, facts(kb=[(1, M ^ 255, 0)])))
# Accepted without a recorded fact: the transfer of the unfolded shr derives it.
write("kb_and_mask_derived.json", one(KBS, and_in, and_out, facts()))
# Rejected: a fact stronger than the transfer gives; the wrong copy.
write("kb_and_mask_strong.json", one(KBS, and_in,
    snap("f", P, R, [(0, ["v1.i256 = shr 248.i256 v0", "return v1"])], [[0, 2]]),
    facts(kb=[(1, M ^ 127, 0)])))
write("kb_and_mask_bad_copy.json", one(KBS, and_in,
    snap("f", P, R, [(0, ["v1.i256 = shr 248.i256 v0", "return v0"])], [[0, 2]]),
    facts(kb=[(1, M ^ 255, 0)])))

# I15 at depth 2: shr 8 (shl 8 v2) -> v2, v2's top byte known zero; the shl stays.
us_in = snap("f", P, R, [(0, ["v2.i256 = and v0 255.i256", "v1.i256 = shl 8.i256 v2",
    "v3.i256 = shr 8.i256 v1", "return v3"])], [[0, 1, 2, 3]])
us_out = snap("f", P, R, [(0, ["v2.i256 = and v0 255.i256", "v1.i256 = shl 8.i256 v2", "return v2"])], [[0, 1, 3]])
write("kb_undo_shift.json", one(KBS, us_in, us_out, facts(kb=[(2, M ^ 255, 0)])))
# Rejected: with a shift of 256 the identity is wrong (review H-7).
us2_in = snap("f", P, R, [(0, ["v2.i256 = and v0 255.i256", "v1.i256 = shl 256.i256 v2",
    "v3.i256 = shr 256.i256 v1", "return v3"])], [[0, 1, 2, 3]])
us2_out = snap("f", P, R, [(0, ["v2.i256 = and v0 255.i256", "v1.i256 = shl 256.i256 v2", "return v2"])], [[0, 1, 3]])
write("kb_undo_shift_256.json", one(KBS, us2_in, us2_out, facts(kb=[(2, M ^ 255, 0)])))

# D2 in a demand round: or v2 v1 -> v2 where only bits 8.. of the result are read and v1's are
# known zero there.
hi = (M << 8) & M
d_in = snap("f", ["v0.i256", "v9.i256"], R, [(0, ["v1.i256 = and v9 255.i256", "v2.i256 = shl 8.i256 v0",
    "v3.i256 = or v2 v1", "v4.i256 = shr 8.i256 v3", "return v4"])], [[0, 1, 2, 3, 4]])
d_out = snap("f", ["v0.i256", "v9.i256"], R, [(0, ["v1.i256 = and v9 255.i256", "v2.i256 = shl 8.i256 v0",
    "v4.i256 = shr 8.i256 v2", "return v4"])], [[0, 1, 3, 4]])
dbs = [(4, M), (3, hi), (2, hi), (1, hi), (9, hi), (0, M >> 8)]
write("kb_demand_or.json", one(KBS, d_in, d_out, facts(kb=[(1, M ^ 255, 0)], db=dbs)))
# Rejected: a claimed demand of the or's result too small for its use; an exact rewrite
# (`add 0 32`) in a demand round (review C-2).
write("kb_demand_or_small.json", one(KBS, d_in, d_out,
    facts(kb=[(1, M ^ 255, 0)], db=[(4, M), (3, 0), (2, hi), (1, hi), (9, hi), (0, M >> 8)])))
write("kb_demand_mixed.json", one(KBS, add_in, add_out, facts(db=[(0, M)])))

# SCCP: a constant folded.
sc_in = snap("f", P, [], [(0, ["v1.i256 = add 96.i256 32.i256", "evm_mstore 64.i256 v1", "return"])], [[0, 1, 2]])
sc_out = snap("f", P, [], [(0, ["evm_mstore 64.i256 128.i256", "return"])], [[1, 2]])
write("sc_const.json", one(SCCP, sc_in, sc_out, facts(consts=[(1, 128)])))
# Rejected: a wrong claimed constant used; a claimed constant not used.
write("sc_const_bad_claim.json", one(SCCP, sc_in,
    snap("f", P, [], [(0, ["evm_mstore 64.i256 129.i256", "return"])], [[1, 2]]), facts(consts=[(1, 129)])))
write("sc_const_bad_use.json", one(SCCP, sc_in,
    snap("f", P, [], [(0, ["evm_mstore 64.i256 129.i256", "return"])], [[1, 2]]), facts(consts=[(1, 128)])))
# A phi constant on the executable edge only.
ph_in = snap("f", P, [], [(0, ["br 1.i256 block1 block2"]), (1, ["jump block3"]), (2, ["jump block3"]),
    (3, ["v2.i256 = phi (5.i256 block1) (7.i256 block2)", "evm_mstore 0.i256 v2", "return"])],
    [[0], [1], [2], [3, 4, 5]])
ph_out = snap("f", P, [], [(0, ["br 1.i256 block1 block2"]), (1, ["jump block3"]), (2, ["jump block3"]),
    (3, ["evm_mstore 0.i256 5.i256", "return"])], [[0], [1], [2], [4, 5]])
write("sc_phi.json", one(SCCP, ph_in, ph_out, facts(consts=[(2, 5)], dead=[(0, 1)])))
# Rejected: the taken slot claimed dead.
write("sc_phi_bad_dead.json", one(SCCP, ph_in, ph_out, facts(consts=[(2, 5)], dead=[(0, 0)])))
# Rejected: a dead edge out of a block whose condition is not constant.
phv_in = snap("f", P, [], [(0, ["br v0 block1 block2"]), (1, ["jump block3"]), (2, ["jump block3"]),
    (3, ["v2.i256 = phi (5.i256 block1) (7.i256 block2)", "evm_mstore 0.i256 v2", "return"])],
    [[0], [1], [2], [3, 4, 5]])
phv_out = snap("f", P, [], [(0, ["br v0 block1 block2"]), (1, ["jump block3"]), (2, ["jump block3"]),
    (3, ["evm_mstore 0.i256 5.i256", "return"])], [[0], [1], [2], [4, 5]])
write("sc_phi_bad_cond.json", one(SCCP, phv_in, phv_out, facts(consts=[(2, 5)], dead=[(0, 1)])))
# BuildIsZero: eq v0 0 replaced in place by is_zero v0.
iz_in = snap("f", P, R, [(0, ["v1.i256 = eq v0 0.i256", "return v1"])], [[0, 1]])
iz_out = snap("f", P, R, [(0, ["v1.i256 = is_zero v0", "return v1"])], [[0, 1]])
write("sc_is_zero.json", one(SCCP, iz_in, iz_out, facts(consts=[])))
# Rejected: replaced by something else.
write("sc_is_zero_bad.json", one(SCCP, iz_in,
    snap("f", P, R, [(0, ["v1.i256 = not v0", "return v1"])], [[0, 1]]), facts(consts=[])))
# Rejected: a constant of a parameter; clz deleted (review H-2).
write("sc_bad_param.json", one(SCCP, snap("f", P, R, [(0, ["return v0"])], [[0]]),
    snap("f", P, R, [(0, ["return 3.i256"])], [[0]]), facts(consts=[(0, 3)])))
cz_in = snap("f", P, R, [(0, ["v1.i256 = clz 0.i256", "return v1"])], [[0, 1]])
cz_out = snap("f", P, R, [(0, ["return 256.i256"])], [[1]])
write("sc_bad_clz.json", one(SCCP, cz_in, cz_out, facts(consts=[(1, 256)])))

# Rejected: and v0 255 -> v0 for an argument v0, with no fact (none can be derived).
arg_in = snap("f", P, R, [(0, ["v1.i256 = and v0 255.i256", "return v1"])], [[0, 1]])
arg_out = snap("f", P, R, [(0, ["return v0"])], [[1]])
write("kb_and_arg_nofact.json", one(KBS, arg_in, arg_out, facts()))
# Rejected: the same with a recorded fact that is no post-fixpoint (v2 = add v0 v9 is unknown).
bf_in = snap("f", ["v0.i256", "v9.i256"], R, [(0, ["v2.i256 = add v0 v9", "v1.i256 = and v2 255.i256", "return v1"])], [[0, 1, 2]])
bf_out = snap("f", ["v0.i256", "v9.i256"], R, [(0, ["v2.i256 = add v0 v9", "return v2"])], [[0, 2]])
write("kb_and_badfact.json", one(KBS, bf_in, bf_out, facts(kb=[(2, M ^ 255, 0)])))
# Rejected: an unknown fact key for the step's kind is not ignored.
write("kb_add0_unread.json", one(KBS, add_in, add_out, facts(gvn={"class": [[1, 2]]})))
write("sc_const_unread.json", one(SCCP, sc_in, sc_out, facts(consts=[(1, 128)], gvn={"class": [[1, 2]]})))
