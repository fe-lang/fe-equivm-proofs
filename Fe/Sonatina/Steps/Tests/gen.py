# Generates the hand-written step records of Steps/Tests.lean: python3 gen.py (in this directory).
import json

def func(name, params, rets, blocks):
    lines = [f"func private %{name}({', '.join(params)}){' -> ' + ', '.join(rets) if rets else ''} {{"]
    for b, stmts in blocks:
        lines.append(f"    block{b}:")
        lines += [f"        {s};" for s in stmts]
    lines.append("}")
    return "\n".join(lines) + "\n"

def snap(name, params, rets, blocks, insts):
    return {"func": name, "func_ref": 0, "text": func(name, params, rets, blocks), "insts": insts}

NOFACTS = {"known_bits": [], "demanded_bits": None, "sccp": None, "finite_loops": [], "gvn": None,
           "ranges": None}

def record(lowered, passes):
    return {"profile": "speed", "lowered": lowered, "passes": passes}

def one(kind, name, inp, out, facts=None):
    return record([inp], [{"kind": kind, "func_behavior": None,
        "steps": [{"kind": kind, "funcs": [{"out": out, "facts": facts or NOFACTS}]}]}])

def write(fn, r):
    with open(fn, "w") as f:
        json.dump(r, f, indent=1)

P, R = ["v0.i256"], ["i256"]

# edge_split: the critical edge block0 -> block2 gets block3.
es_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["evm_mstore 0.i256 v0", "jump block2"]),
    (2, ["v1.i256 = phi (1.i256 block0) (2.i256 block1)", "return v1"])],
    [[0], [1, 2], [3, 4]])
def es_out(b0="br v0 block1 block3", b1=("evm_mstore 0.i256 v0", "jump block2"),
           phi="v1.i256 = phi (1.i256 block3) (2.i256 block1)", b3="jump block2"):
    return snap("f", P, R, [(0, [b0]), (1, list(b1)), (2, [phi, "return v1"]), (3, [b3])],
                [[0], list(range(1, 1 + len(b1))), [3, 4], [5]])
write("edge_split.json", one("edge_split", "f", es_in, es_out()))
# Rejected: a wrong phi input, a dropped store, a changed instruction, a wrong split target,
# swapped branch targets.
write("edge_split_bad_phi.json", one("edge_split", "f", es_in,
    es_out(phi="v1.i256 = phi (2.i256 block3) (2.i256 block1)")))
write("edge_split_bad_store.json", one("edge_split", "f", es_in, es_out(b1=("jump block2",))))
write("edge_split_bad_inst.json", one("edge_split", "f", es_in,
    es_out(b1=("evm_mstore 32.i256 v0", "jump block2"))))
write("edge_split_bad_target.json", one("edge_split", "f", es_in, es_out(b3="jump block1")))
write("edge_split_bad_swap.json", one("edge_split", "f", es_in, es_out(b0="br v0 block3 block1")))

# A record with no steps: the lowered function alone.
def none_(inp):
    return record([inp], [])

# The edge split's lifted restriction: `br c a a` and an all-identical `br_table` with a
# default become `jump`, whatever the operand (here a parameter).
br_in = snap("g", P, R, [(0, ["br v0 block1 block1"]), (1, ["return v0"])], [[0], [1]])
jmp_out = snap("g", P, R, [(0, ["jump block1"]), (1, ["return v0"])], [[0], [1]])
write("es_br_same.json", one("edge_split", "g", br_in, jmp_out))
tab_in = snap("g", P, R, [(0, ["br_table v0 block1 (1.i256 block1) (2.i256 block1)"]),
    (1, ["return v0"])], [[0], [1]])
write("es_table_same.json", one("edge_split", "g", tab_in, jmp_out))
# Rejected: `br` to different blocks; a table with no default (review C-6), which the input
# runs stuck on a value no case has.
br2_in = snap("g", P, R, [(0, ["br v0 block1 block2"]), (1, ["return v0"]), (2, ["return v0"])],
    [[0], [1], [2]])
br2_out = snap("g", P, R, [(0, ["jump block1"]), (1, ["return v0"]), (2, ["return v0"])],
    [[0], [1], [2]])
write("es_br_differ.json", one("edge_split", "g", br2_in, br2_out))
nodef_in = snap("g", P, R, [(0, ["br_table v0 (1.i256 block1) (2.i256 block1)"]),
    (1, ["return v0"])], [[0], [1]])
write("es_table_nodefault.json", one("edge_split", "g", nodef_in, jmp_out))
# Duplicate table keys (review C-6): rejected by `wf`; distinct keys accepted.
def tab(keys):
    return snap("g", P, R, [(0, ["br_table v0 block2 " + " ".join(f"({k}.i256 block{b})" for k, b in keys)]),
        (1, ["return v0"]), (2, ["return v0"]), (3, ["return v0"])], [[0], [1], [2], [3]])
write("wf_table_dup.json", none_(tab([(1, 1), (1, 3)])))
write("wf_table_ok.json", none_(tab([(1, 1), (2, 3)])))
# Review H-1: an unreachable block (block5) jumping into reachable code, with a phi operand
# from it that nothing defines on a path from the entry, is accepted.
un_in = snap("h", [], R, [
    (0, ["v1.i256 = evm_calldata_size", "br v1 block1 block3"]),
    (1, ["jump block3"]),
    (3, ["v2.i256 = phi (v1 block0) (v1 block1) (v9 block5)", "return v2"]),
    (5, ["v9.i256 = add v1 1.i256", "jump block3"])],
    [[0, 1], [2], [3, 4], [5, 6]])
un_out = snap("h", [], R, [
    (0, ["v1.i256 = evm_calldata_size", "br v1 block1 block6"]),
    (1, ["jump block3"]),
    (3, ["v2.i256 = phi (v1 block6) (v1 block1) (v9 block5)", "return v2"]),
    (5, ["v9.i256 = add v1 1.i256", "jump block3"]),
    (6, ["jump block3"])],
    [[0, 1], [2], [3, 4], [5, 6], [7]])
write("es_unreachable.json", one("edge_split", "h", un_in, un_out))
# Rejected: the input is not in SSA form (block2 uses v1, which block1 defines).
ns_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["v1.i256 = add v0 1.i256", "jump block2"]),
    (2, ["v2.i256 = phi (1.i256 block0) (2.i256 block1)", "return v1"])],
    [[0], [1, 2], [3, 4]])
ns_out = snap("f", P, R, [
    (0, ["br v0 block1 block3"]),
    (1, ["v1.i256 = add v0 1.i256", "jump block2"]),
    (2, ["v2.i256 = phi (1.i256 block3) (2.i256 block1)", "return v1"]),
    (3, ["jump block2"])],
    [[0], [1, 2], [3, 4], [5]])
write("es_bad_ssa.json", one("edge_split", "f", ns_in, ns_out))
# Review 6 F-2: two slots of one table to one split block.
two_in = snap("g", P, R, [
    (0, ["br_table v0 block2 (1.i256 block1) (2.i256 block1)"]),
    (2, ["jump block1"]),
    (1, ["v1.i256 = phi (1.i256 block0) (2.i256 block2)", "return v1"])],
    [[0], [1], [2, 3]])
two_out = snap("g", P, R, [
    (0, ["br_table v0 block2 (1.i256 block3) (2.i256 block3)"]),
    (2, ["jump block1"]),
    (1, ["v1.i256 = phi (1.i256 block3) (2.i256 block2)", "return v1"]),
    (3, ["jump block1"])],
    [[0], [1], [2, 3], [4]])
write("es_two_slots.json", one("edge_split", "g", two_in, two_out))

# cfg_cleanup.
def cc(name, inp, out, fb=None, extra=()):
    """A record of one cfg_cleanup step of function `name`; `extra` are more lowered functions."""
    return record([inp, *extra], [{"kind": "cfg_cleanup", "func_behavior": fb,
        "steps": [{"kind": "cfg_cleanup", "funcs": [{"out": out, "facts": NOFACTS}]}]}])

# Merge and a trivial phi after pruning (design §4.3's example): block5 is unreachable, so
# v2 = phi (v1 block0) (v1 block5) is v1, and block0, block3, block4 merge.
mg_in = snap("f", [], R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block3"]),
    (3, ["v2.i256 = phi (v1 block0) (v1 block5)", "v3.i256 = add v2 1.i256", "jump block4"]),
    (4, ["return v3"]),
    (5, ["jump block3"])],
    [[0, 1], [2, 3, 4], [5], [6]])
def mg_out(add="v3.i256 = add v1 1.i256"):
    return snap("f", [], R, [(0, ["v1.i256 = evm_calldata_size", add, "return v3"])], [[0, 3, 5]])
write("cc_merge.json", cc("f", mg_in, mg_out()))
# Rejected: a changed instruction.
write("cc_bad_inst.json", cc("f", mg_in, mg_out("v3.i256 = add v1 2.i256")))

# A tunnel through block1 (only `jump block3`): block0's slot goes to block3, whose phi takes
# block1's operand from block0.
tn_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["jump block3"]),
    (2, ["v1.i256 = add v0 1.i256", "jump block3"]),
    (3, ["v2.i256 = phi (10.i256 block1) (v1 block2)", "return v2"])],
    [[0], [1], [2, 3], [4, 5]])
def tn_out(phi="v2.i256 = phi (10.i256 block0) (v1 block2)"):
    return snap("f", P, R, [
        (0, ["br v0 block3 block2"]),
        (2, ["v1.i256 = add v0 1.i256", "jump block3"]),
        (3, [phi, "return v2"])],
        [[0], [2, 3], [4, 5]])
write("cc_tunnel.json", cc("f", tn_in, tn_out()))
# Rejected: a wrong phi operand.
write("cc_bad_phi.json", cc("f", tn_in, tn_out("v2.i256 = phi (11.i256 block0) (v1 block2)")))

# Review C-4, first counterexample: block1 is tunnelled, and v5 = phi (v1 block1) (v2 block2)
# is taken for v2, as if block1 were no predecessor; it survives, so v5 is no trivial phi.
c41_in = snap("f", ["v0.i256", "v1.i256", "v2.i256"], R, [
    (0, ["br v0 block1 block2"]),
    (1, ["jump block3"]),
    (2, ["v9.i256 = add v2 0.i256", "jump block3"]),
    (3, ["v5.i256 = phi (v1 block1) (v2 block2)", "return v5"])],
    [[0], [1], [2, 3], [4, 5]])
c41_out = snap("f", ["v0.i256", "v1.i256", "v2.i256"], R, [
    (0, ["br v0 block3 block2"]),
    (2, ["v9.i256 = add v2 0.i256", "jump block3"]),
    (3, ["return v2"])],
    [[0], [2, 3], [5]])
write("cc_bad_c4_phi.json", cc("f", c41_in, c41_out))

# A forward bridge: block4 holds only a phi and a jump; block2 and block3 go to block6, whose phi
# takes block4's phi's operand from each.
br_in = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "br v0 block1 block5"]),
    (1, ["br v1 block2 block3"]),
    (2, ["jump block4"]),
    (3, ["jump block4"]),
    (4, ["v2.i256 = phi (1.i256 block2) (2.i256 block3)", "jump block6"]),
    (5, ["jump block6"]),
    (6, ["v3.i256 = phi (v2 block4) (3.i256 block5)", "return v3"])],
    [[0, 1], [2], [3], [4], [5, 6], [7], [8, 9]])
br_out = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "br v0 block1 block5"]),
    (1, ["br v1 block2 block3"]),
    (2, ["jump block6"]),
    (3, ["jump block6"]),
    (5, ["jump block6"]),
    (6, ["v3.i256 = phi (1.i256 block2) (2.i256 block3) (3.i256 block5)", "return v3"])],
    [[0, 1], [2], [3], [4], [7], [8, 9]])
write("cc_bridge.json", cc("f", br_in, br_out))

# An unreachable block deleted.
ur_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["return v0"]),
    (2, ["return 0.i256"]),
    (3, ["v5.i256 = add v0 1.i256", "jump block1"])],
    [[0], [1], [2], [3, 4]])
ur_out = snap("f", P, R, [(0, ["br v0 block1 block2"]), (1, ["return v0"]), (2, ["return 0.i256"])],
    [[0], [1], [2]])
write("cc_unreachable.json", cc("f", ur_in, ur_out))

# A trivial phi of a loop header: v2 = phi (v1 block0) (v2 block2) is v1.
tv_in = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block1"]),
    (1, ["v2.i256 = phi (v1 block0) (v2 block2)", "v3.i256 = lt v2 10.i256", "br v3 block2 block3"]),
    (2, ["jump block1"]),
    (3, ["return v2"])],
    [[0, 1], [2, 3, 4], [5], [6]])
tv_out = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block1"]),
    (1, ["v3.i256 = lt v1 10.i256", "br v3 block2 block3"]),
    (2, ["jump block1"]),
    (3, ["return v1"])],
    [[0, 1], [3, 4], [5], [6]])
write("cc_trivial.json", cc("f", tv_in, tv_out))

# Chained trivial phis: v3 = phi (v2 block1) (v3 block2) is v2, then v2 = phi (v1 block0)
# (v3 block2) is v1.
ch_in = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block1"]),
    (1, ["v2.i256 = phi (v1 block0) (v3 block2)", "br v0 block2 block3"]),
    (2, ["v3.i256 = phi (v2 block1) (v3 block2)", "br v1 block2 block1"]),
    (3, ["return v2"])],
    [[0, 1], [2, 3], [4, 5], [6]])
ch_out = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block1"]),
    (1, ["br v0 block2 block3"]),
    (2, ["br v1 block2 block1"]),
    (3, ["return v1"])],
    [[0, 1], [3], [5], [6]])
write("cc_chain.json", cc("f", ch_in, ch_out))

# Branch collapse: both slots of block0 tunnel to block3, a loop header, so the `br` becomes
# `jump block3` with its id; and the same with block3 merged into block0.
cl_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["jump block3"]),
    (2, ["jump block3"]),
    (3, ["br v0 block3 block4"]),
    (4, ["return v0"])],
    [[0], [1], [2], [3], [4]])
cl_out = snap("f", P, R, [(0, ["jump block3"]), (3, ["br v0 block3 block4"]), (4, ["return v0"])],
    [[0], [3], [4]])
write("cc_collapse.json", cc("f", cl_in, cl_out))
cm_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["jump block3"]),
    (2, ["jump block3"]),
    (3, ["return v0"])],
    [[0], [1], [2], [3]])
cm_out = snap("f", P, R, [(0, ["return v0"])], [[3]])
write("cc_collapse_merge.json", cc("f", cm_in, cm_out))

# Noreturn trims: %g does not return; f's code after `call %g` goes, and block1 with it.
G = snap("g", [], [], [(0, ["evm_revert 0.i256 0.i256"])], [[100]])
GR = snap("g", [], [], [(0, ["return"])], [[100]])
NR = [{"func": "g", "noreturn": True, "will_return": False, "reads": False, "writes": False,
       "mutates": True}]
nr_in = snap("f", P, R, [
    (0, ["call %g", "v1.i256 = add v0 1.i256", "jump block1"]),
    (1, ["return v1"])],
    [[0, 1, 2], [3]])
nr_out = snap("f", P, R, [(0, ["call %g", "unreachable"])], [[0, 7]])
write("cc_noret.json", cc("f", nr_in, nr_out, NR, [G]))
# Rejected: the table claims a function that returns does not; no table; the new
# `unreachable` with an input id.
write("cc_bad_noret_claim.json", cc("f", nr_in, nr_out, NR, [GR]))
write("cc_bad_noret_none.json", cc("f", nr_in, nr_out, None, [G]))
write("cc_bad_noret_id.json", cc("f", nr_in, snap("f", P, R, [(0, ["call %g", "unreachable"])],
    [[0, 2]]), NR, [G]))
# An existing `call %g; unreachable` tail keeps its id (here block2, unreachable, goes).
nk_in = snap("f", P, R, [
    (0, ["br v0 block1 block3"]),
    (1, ["call %g", "unreachable"]),
    (2, ["jump block3"]),
    (3, ["return v0"])],
    [[0], [1, 2], [3], [4]])
nk_out = snap("f", P, R, [
    (0, ["br v0 block1 block3"]),
    (1, ["call %g", "unreachable"]),
    (3, ["return v0"])],
    [[0], [1, 2], [4]])
write("cc_noret_kept.json", cc("f", nk_in, nk_out, NR, [G]))

# Review C-4, second counterexample: a deleted `evm_sstore`.
ss_in = snap("f", P, R, [(0, ["evm_sstore 0.i256 1.i256", "return v0"])], [[0, 1]])
ss_out = snap("f", P, R, [(0, ["return v0"])], [[1]])
write("cc_bad_sstore.json", cc("f", ss_in, ss_out))
# Review C-4, third counterexample: swapped branch targets; a changed entry.
sw_in = snap("f", P, R, [(0, ["br v0 block1 block2"]), (1, ["return 1.i256"]),
    (2, ["return 2.i256"])], [[0], [1], [2]])
write("cc_bad_swap.json", cc("f", sw_in, snap("f", P, R, [(0, ["br v0 block2 block1"]),
    (1, ["return 1.i256"]), (2, ["return 2.i256"])], [[0], [1], [2]])))
write("cc_bad_entry.json", cc("f", sw_in, snap("f", P, R, [(1, ["return 1.i256"]),
    (0, ["br v0 block1 block2"]), (2, ["return 2.i256"])], [[1], [0], [2]])))

# Rejected: block3, which block2 also enters, merged into block1.
mp_in = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["v1.i256 = add v0 1.i256", "jump block3"]),
    (2, ["jump block3"]),
    (3, ["v2.i256 = add v0 2.i256", "return v2"])],
    [[0], [1, 2], [3], [4, 5]])
mp_out = snap("f", P, R, [
    (0, ["br v0 block1 block2"]),
    (1, ["v1.i256 = add v0 1.i256", "v2.i256 = add v0 2.i256", "return v2"]),
    (2, ["jump block3"])],
    [[0], [1, 4, 5], [3]])
write("cc_bad_pred.json", cc("f", mp_in, mp_out))

# branch_canonicalize: is_zero peeling.
def bcr(inp, out, kind="branch_canonicalize"):
    return one(kind, "f", inp, out)

def bc_func(cond_lines, br, ret1="return 1.i256", ids=None):
    """block0: calldata size, the condition's statements, a branch; block1, block2 return."""
    body = ["v1.i256 = evm_calldata_size"] + cond_lines + [br]
    n = len(body)
    return snap("f", P, R, [(0, body), (1, [ret1]), (2, ["return 2.i256"])],
        ids or [list(range(n)), [n], [n + 1]])

# k = 1, 2, 3: br (is_zero^k v1) block1 block2 becomes br v1, swapped iff k is odd; the
# is_zeros are deleted.
for k in (1, 2, 3):
    cond = [f"v{2 + i}.i256 = is_zero v{1 + i}" for i in range(k)]
    inp = bc_func(cond, f"br v{1 + k} block1 block2")
    tgt = "block2 block1" if k % 2 else "block1 block2"
    out = bc_func([], f"br v1 {tgt}", ids=[[0, k + 1], [k + 2], [k + 3]])
    write(f"bc_peel{k}.json", bcr(inp, out))
    # Review M-3: the wrong parity.
    bad = "block1 block2" if k % 2 else "block2 block1"
    write(f"bc_bad_parity{k}.json", bcr(inp, bc_func([], f"br v1 {bad}", ids=[[0, k + 1], [k + 2], [k + 3]])))
# Peeling one of two is_zeros, the other kept: br (is_zero (is_zero v1)) → br (is_zero v1), swapped.
inp2 = bc_func(["v2.i256 = is_zero v1", "v3.i256 = is_zero v2"], "br v3 block1 block2")
write("bc_peel_partial.json", bcr(inp2, bc_func(["v2.i256 = is_zero v1"], "br v2 block2 block1",
    ids=[[0, 1, 3], [4], [5]])))
# The is_zero kept where the output still uses it.
inp_k = bc_func(["v2.i256 = is_zero v1"], "br v2 block1 block2", ret1="return v2")
write("bc_keep.json", bcr(inp_k, bc_func(["v2.i256 = is_zero v1"], "br v1 block2 block1",
    ret1="return v2")))
# Review M-3: a deleted is_zero the output still uses; a deleted instruction other than
# is_zero; a peel through `not` (bitwise, no negation).
write("bc_bad_live.json", bcr(inp_k, bc_func([], "br v1 block2 block1", ret1="return v2",
    ids=[[0, 2], [3], [4]])))
inp_s = bc_func(["evm_sstore 0.i256 v1", "v2.i256 = is_zero v1"], "br v2 block1 block2")
write("bc_bad_delete.json", bcr(inp_s, bc_func([], "br v1 block2 block1", ids=[[0, 3], [4], [5]])))
inp_n = bc_func(["v2.i256 = not v1"], "br v2 block1 block2")
write("bc_bad_not.json", bcr(inp_n, bc_func([], "br v1 block2 block1", ids=[[0, 2], [3], [4]])))
# The is_zero in a dominating block.
cr_in = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "v2.i256 = is_zero v1", "jump block3"]),
    (3, ["br v2 block1 block2"]),
    (1, ["return 1.i256"]), (2, ["return 2.i256"])],
    [[0, 1, 2], [3], [4], [5]])
cr_out = snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block3"]),
    (3, ["br v1 block2 block1"]),
    (1, ["return 1.i256"]), (2, ["return 2.i256"])],
    [[0, 2], [3], [4], [5]])
write("bc_cross.json", bcr(cr_in, cr_out))
# branch_conditions, the case k = 1.
write("bc_conditions.json", bcr(bc_func(["v2.i256 = is_zero v1"], "br v2 block1 block2"),
    bc_func([], "br v1 block2 block1", ids=[[0, 2], [3], [4]]), kind="branch_conditions"))
# Rejected: an unrelated condition; a changed target elsewhere.
write("bc_bad_cond.json", bcr(bc_func(["v2.i256 = is_zero v1"], "br v2 block1 block2"),
    bc_func(["v2.i256 = is_zero v1"], "br v0 block2 block1")))
write("bc_bad_target.json", bcr(cr_in, snap("f", P, R, [
    (0, ["v1.i256 = evm_calldata_size", "jump block1"]),
    (3, ["br v1 block2 block1"]),
    (1, ["return 1.i256"]), (2, ["return 2.i256"])],
    [[0, 2], [3], [4], [5]])))

# Facts (ruling R-11.3): a step of a kind that reads no facts is rejected if it carries any,
# known bits or a key no checker reads.
def with_facts(**kw):
    d = dict(NOFACTS); d.update(kw); return d
write("cc_bad_facts.json", one("cfg_cleanup", "f", mg_in, mg_out(),
    with_facts(known_bits=[[3, "0", "1"]])))
write("cc_bad_unread.json", one("cfg_cleanup", "f", mg_in, mg_out(),
    with_facts(ranges=[[3, "0", "5"]])))
# The reader keeps `"demanded_bits": []` (a demand round in which no value has a demanded bit).
write("rd_demand_empty.json", one("known_bits_simplify", "f", es_in, es_in, with_facts(demanded_bits=[])))
write("rd_demand_none.json", one("known_bits_simplify", "f", es_in, es_in))

# coalesce_copies.
def kc(blocks_in, blocks_out, params=(), rets=("i256",)):
    """blocks: list of (id, lines, ids)."""
    inp = snap("f", list(params), list(rets), [(b, ls) for b, ls, _ in blocks_in], [i for _, _, i in blocks_in])
    out = snap("f", list(params), list(rets), [(b, ls) for b, ls, _ in blocks_out], [i for _, _, i in blocks_out])
    return one("coalesce_copies", "f", inp, out)
def ids_from(n, k=0): return list(range(k, k + n))
L = lambda *xs: list(xs)
RET = "return 0.i256"
# Two words, constant ranges, all loads first (snapshot).
copy2 = ["v1.i256 = evm_mload 256.i256", "v2.i256 = evm_mload 288.i256",
         "evm_mstore 512.i256 v1", "evm_mstore 544.i256 v2"]
def run_in(lines): return [(0, lines + [RET], ids_from(len(lines) + 1))]
def run_out(lines, ids): return [(0, lines + [RET], ids)]
write("kc_const.json", kc(run_in(copy2), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [3, 4])))
# Interleaved, constant and disjoint.
inter = ["v1.i256 = evm_mload 256.i256", "evm_mstore 512.i256 v1",
         "v2.i256 = evm_mload 288.i256", "evm_mstore 544.i256 v2"]
write("kc_interleaved.json", kc(run_in(inter), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [3, 4])))
# Addresses through add chains, the adds deleted; three words.
arith = ["v1.i256 = evm_mload 256.i256", "v2.i256 = add 256.i256 32.i256",
         "v3.i256 = evm_mload v2", "v4.i256 = add v2 32.i256", "v5.i256 = evm_mload v4",
         "evm_mstore 512.i256 v1", "v6.i256 = add 512.i256 32.i256", "evm_mstore v6 v3",
         "v8.i256 = add v6 64.i256", "v7.i256 = sub v8 32.i256", "evm_mstore v7 v5"]
write("kc_arith.json", kc(run_in(arith), run_out(["evm_mcopy 512.i256 256.i256 96.i256"], [10, 11])))
# An add of the window used after it stays.
keep_in = [(0, copy2[:2] + ["v6.i256 = add 512.i256 32.i256"] + copy2[2:] + ["return v6"], ids_from(6))]
keep_out = [(0, ["v6.i256 = add 512.i256 32.i256", "evm_mcopy 512.i256 256.i256 64.i256", "return v6"], [2, 4, 5])]
write("kc_keep_add.json", kc(keep_in, keep_out))
# Two runs in one block and one in another block.
copyb = ["v11.i256 = evm_mload 1024.i256", "v12.i256 = evm_mload 1056.i256",
         "evm_mstore 2048.i256 v11", "evm_mstore 2080.i256 v12"]
copyc = ["v21.i256 = evm_mload 4096.i256", "v22.i256 = evm_mload 4128.i256",
         "evm_mstore 8192.i256 v21", "evm_mstore 8224.i256 v22"]
two_in = [(0, copy2 + copyb + ["jump block1"], ids_from(9)), (1, copyc + [RET], ids_from(5, 9))]
two_out = [(0, ["evm_mcopy 512.i256 256.i256 64.i256", "evm_mcopy 2048.i256 1024.i256 64.i256", "jump block1"], [3, 7, 8]),
           (1, ["evm_mcopy 8192.i256 4096.i256 64.i256", RET], [12, 13])]
write("kc_two_runs.json", kc(two_in, two_out))
# Base-relative, all loads first: one base, and a base for each range.
base = ["v1.i256 = evm_mload v0", "v2.i256 = add v0 32.i256", "v3.i256 = evm_mload v2",
        "evm_mstore 512.i256 v1", "evm_mstore 544.i256 v3"]
write("kc_base.json", kc([(0, base + [RET], ids_from(6))],
    [(0, ["evm_mcopy 512.i256 v0 64.i256", RET], [4, 5])], params=("v0.i256",)))
base2 = ["v2.i256 = evm_mload v0", "v3.i256 = add v0 32.i256", "v4.i256 = evm_mload v3",
         "evm_mstore v1 v2", "v5.i256 = add v1 32.i256", "evm_mstore v5 v4"]
write("kc_base2.json", kc([(0, base2 + [RET], ids_from(7))],
    [(0, ["evm_mcopy v1 v0 64.i256", RET], [5, 6])], params=("v0.i256", "v1.i256")))
# A constant range past 2^256, all loads first: the copy does not terminate there.
big = 2**256 - 32
past = [f"v1.i256 = evm_mload {big}.i256", f"v2.i256 = add {big}.i256 32.i256", "v3.i256 = evm_mload v2",
        "evm_mstore 512.i256 v1", "evm_mstore 544.i256 v3"]
write("kc_past.json", kc(run_in(past), run_out([f"evm_mcopy 512.i256 {big}.i256 64.i256"], [4, 5])))
# Rejected: interleaved and overlapping; a length other than 32 n; store i not storing load i;
# a load used twice; a store outside a run deleted; a changed copy operand; addresses not
# contiguous; another instruction in the window; one word; a kept add moved after the copy;
# interleaved and base-relative; interleaved with a range past 2^256; loads at two bases.
over = ["v1.i256 = evm_mload 256.i256", "evm_mstore 288.i256 v1",
        "v2.i256 = evm_mload 288.i256", "evm_mstore 320.i256 v2"]
write("kc_bad_overlap.json", kc(run_in(over), run_out(["evm_mcopy 288.i256 256.i256 64.i256"], [3, 4])))
write("kc_bad_len.json", kc(run_in(copy2), run_out(["evm_mcopy 512.i256 256.i256 96.i256"], [3, 4])))
swap = copy2[:2] + ["evm_mstore 512.i256 v2", "evm_mstore 544.i256 v1"]
write("kc_bad_order.json", kc(run_in(swap), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [3, 4])))
twouse = copy2[:2] + ["v9.i256 = add v1 0.i256"] + copy2[2:]
write("kc_bad_twouse.json", kc(run_in(twouse), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [4, 5])))
outside = copy2 + ["evm_mstore 768.i256 7.i256"]
write("kc_bad_store.json", kc(run_in(outside), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [3, 5])))
write("kc_bad_operand.json", kc(run_in(copy2), run_out(["evm_mcopy 512.i256 288.i256 64.i256"], [3, 4])))
gap = ["v1.i256 = evm_mload 256.i256", "v2.i256 = evm_mload 320.i256",
       "evm_mstore 512.i256 v1", "evm_mstore 544.i256 v2"]
write("kc_bad_gap.json", kc(run_in(gap), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [3, 4])))
other = copy2[:2] + ["evm_sstore 0.i256 1.i256"] + copy2[2:]
write("kc_bad_other.json", kc(run_in(other), run_out(["evm_mcopy 512.i256 256.i256 64.i256"], [4, 5])))
write("kc_bad_one.json", kc(run_in(copy2[:1] + copy2[2:3]), run_out(["evm_mcopy 512.i256 256.i256 32.i256"], [1, 2])))
base_inter = ["v1.i256 = evm_mload v0", "evm_mstore 512.i256 v1", "v2.i256 = add v0 32.i256",
              "v3.i256 = evm_mload v2", "evm_mstore 544.i256 v3"]
write("kc_bad_base_inter.json", kc([(0, base_inter + [RET], ids_from(6))],
    [(0, ["evm_mcopy 512.i256 v0 64.i256", RET], [4, 5])], params=("v0.i256",)))
past_inter = [f"v1.i256 = evm_mload {big}.i256", "evm_mstore 512.i256 v1", f"v2.i256 = add {big}.i256 32.i256",
              "v3.i256 = evm_mload v2", "evm_mstore 544.i256 v3"]
write("kc_bad_past_inter.json", kc(run_in(past_inter), run_out([f"evm_mcopy 512.i256 {big}.i256 64.i256"], [4, 5])))
two_base = ["v2.i256 = evm_mload v0", "v3.i256 = add v1 32.i256", "v4.i256 = evm_mload v3",
            "evm_mstore 512.i256 v2", "evm_mstore 544.i256 v4"]
write("kc_bad_two_base.json", kc([(0, two_base + [RET], ids_from(6))],
    [(0, ["evm_mcopy 512.i256 v0 64.i256", RET], [4, 5])], params=("v0.i256", "v1.i256")))
write("kc_bad_moved.json", kc(keep_in, [(0, ["evm_mcopy 512.i256 256.i256 64.i256", "v6.i256 = add 512.i256 32.i256", "return v6"], [4, 2, 5])]))
# Review 20 M-1: a run in an unreachable block (block1), its addresses through that block's own
# adds, which `addrNorm` does not follow; the compiler coalesces it (`copy.rs` visits every
# block).  Accepted, as is any body of an unreachable block (its statements are not checked).
# Rejected: the unreachable block's terminator changed; its new body uses a deleted value; the
# same arbitrary body in block1 reachable (block0 jumps to it).
unr_in = [(0, [RET], [0]), (1, base2 + [RET], ids_from(7, 1))]
unr = lambda b1, ids, b0="return 0.i256": kc([(0, [b0], [0])] + unr_in[1:], [(0, [b0], [0]), (1, b1, ids)],
    params=("v0.i256", "v1.i256"))
write("kc_unreach.json", unr(["evm_mcopy v1 v0 64.i256", RET], [6, 7]))
write("kc_unreach_any.json", unr(["evm_sstore 0.i256 1.i256", RET], [6, 7]))
write("kc_bad_unreach_term.json", unr(["evm_mcopy v1 v0 64.i256", "return 1.i256"], [6, 7]))
write("kc_bad_unreach_used.json", unr(["evm_mstore 0.i256 v3", RET], [6, 7]))
write("kc_bad_reach_any.json", unr(["evm_sstore 0.i256 1.i256", RET], [6, 7], b0="jump block1"))
