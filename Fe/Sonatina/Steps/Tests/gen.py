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
