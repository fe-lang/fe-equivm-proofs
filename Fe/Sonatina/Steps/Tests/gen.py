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
