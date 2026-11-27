# The step records of GvnPruneTests.lean.
#   python3 gen.py real SIDECAR SECTION FUNC NAME   one real gvn_prune step, from a corpus sidecar
#   python3 gen.py                                  the hand-written records and the mutants
import json, sys, copy, re

M = (1 << 256) - 1
BOOL = M ^ 1  # every bit but bit 0 known zero

def facts(gvn, kb=()):
    return {"gvn": gvn, "known_bits": [[v, str(z), str(o)] for v, z, o in kb],
            "demanded_bits": None, "sccp": None, "finite_loops": [], "ranges": None}

def gvn(cls=(), preds=(), dead=()):
    return {"dead_edges": [list(e) for e in dead], "class": [list(c) for c in cls],
            "preds": [list(p) for p in preds], "phis": [], "value_phis": []}

def one(inp, out, fs, kind="gvn_prune"):
    return {"profile": "speed", "lowered": [inp], "passes": [{"kind": "gvn", "func_behavior": None,
        "steps": [{"kind": kind, "funcs": [{"out": out, "facts": fs}]}]}]}

def write(fn, r):
    with open(fn, "w") as f:
        json.dump(r, f, indent=1)

def real(path, section, func, name):
    d = json.load(open(path))
    s = [s for s in d["sections"] if s["name"] == section][0]
    ms = s["lowering"]["machine_steps"]
    cur = {x["func"]: x for x in ms["lowered"]}
    for p in ms["passes"]:
        for st in p["steps"]:
            for fs in st["funcs"]:
                o = fs["out"]
                if st["kind"] == "gvn_prune" and o["func"] == func:
                    write(name + ".json", one(cur[func], o, fs["facts"]))
                    return
                cur[o["func"]] = o
    raise SystemExit("no such step")

def func(name, params, rets, blocks):
    lines = [f"func private %{name}({', '.join(params)}){' -> ' + ', '.join(rets) if rets else ''} {{"]
    for b, stmts in blocks:
        lines.append(f"    block{b}:")
        lines += [f"        {s};" for s in stmts]
    lines.append("}")
    return "\n".join(lines) + "\n"

def snap(params, rets, blocks):
    """Blocks as (id, [(inst id, line)])."""
    return {"func": "f", "func_ref": 0, "text": func("f", params, rets, [(b, [l for _, l in ls]) for b, ls in blocks]),
            "insts": [[i for i, _ in ls] for _, ls in blocks]}

V = lambda n: {"value": n}
I = lambda n: {"imm": str(n)}
P2, R = ["v0.i256", "v1.i256"], ["i256"]

def hand():
    # A branch on a boolean whose class has the condition of a dominating branch, taken nonzero:
    # `br v3` in block1 takes its nonzero slot; block4 is left unreachable and deleted.
    bi = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (1, [(2, "v3.i256 = lt v0 v1"), (3, "br v3 block3 block4")]),
          (2, [(4, "return 0.i256")]),
          (3, [(5, "return 1.i256")]),
          (4, [(6, "return 2.i256")])]
    bo = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (1, [(2, "v3.i256 = lt v0 v1"), (3, "jump block3")]),
          (2, [(4, "return 0.i256")]),
          (3, [(5, "return 1.i256")])]
    kb = [(2, BOOL, 0), (3, BOOL, 0)]
    good = gvn(cls=[(3, V(2))], preds=[(0, 0, V(2), I(1)), (0, 1, V(2), I(0)), (1, 0, V(3), I(1)), (1, 1, V(3), I(0))],
               dead=[(1, 1)])
    write("prune_br.json", one(snap(P2, R, bi), snap(P2, R, bo), facts(good, kb)))
    # Rejected: the predicates' polarity swapped (`v2 = 1` claimed of the zero edge, `v2 = 0` of
    # the nonzero edge).
    swap = gvn(cls=[(3, V(2))], preds=[(0, 1, V(2), I(1)), (0, 0, V(2), I(0))], dead=[(1, 1)])
    write("prune_bad_polarity.json", one(snap(P2, R, bi), snap(P2, R, bo), facts(swap, kb)))
    # Rejected: no class, and no predicate.
    write("prune_bad_noclass.json", one(snap(P2, R, bi), snap(P2, R, bo),
        facts(gvn(preds=good["preds"], dead=[(1, 1)]), kb)))
    write("prune_bad_nopred.json", one(snap(P2, R, bi), snap(P2, R, bo),
        facts(gvn(cls=[(3, V(2))], dead=[(1, 1)]), kb)))
    # Rejected: `c = 1` of a nonzero edge needs `c` boolean: here a word (`add`), and the same
    # with known bits that claim it boolean (not a post-fixpoint).
    wi = copy.deepcopy(bi); wi[0][1][0] = (0, "v2.i256 = add v0 v1"); wi[1][1][0] = (2, "v3.i256 = add v0 v1")
    wo = copy.deepcopy(bo); wo[0][1][0] = (0, "v2.i256 = add v0 v1"); wo[1][1][0] = (2, "v3.i256 = add v0 v1")
    write("prune_bad_word.json", one(snap(P2, R, wi), snap(P2, R, wo), facts(good)))
    write("prune_bad_word_kb.json", one(snap(P2, R, wi), snap(P2, R, wo), facts(good, kb)))
    # Rejected: the slot taken claimed dead (block1's zero slot taken, and the output jumps to
    # block4).
    bo2 = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
           (1, [(2, "v3.i256 = lt v0 v1"), (3, "jump block4")]),
           (2, [(4, "return 0.i256")]),
           (4, [(6, "return 2.i256")])]
    write("prune_bad_taken.json", one(snap(P2, R, bi), snap(P2, R, bo2),
        facts(gvn(cls=good["class"], preds=good["preds"], dead=[(1, 0)]), kb)))
    # Rejected: the right dead slot, the output jumps to the dead target.
    write("prune_bad_target.json", one(snap(P2, R, bi), snap(P2, R, bo2), facts(good, kb)))
    # Rejected: a predicate used where its target does not dominate: block1 and block2 join in
    # block5, which branches on `v3`.
    ji = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (1, [(2, "jump block5")]),
          (2, [(3, "jump block5")]),
          (5, [(4, "v3.i256 = lt v0 v1"), (5, "br v3 block3 block4")]),
          (3, [(6, "return 1.i256")]),
          (4, [(7, "return 2.i256")])]
    jo = copy.deepcopy(ji); jo[3] = (5, [(4, "v3.i256 = lt v0 v1"), (5, "jump block3")]); jo.pop()
    write("prune_bad_nodom.json", one(snap(P2, R, ji), snap(P2, R, jo),
        facts(gvn(cls=[(3, V(2))], preds=[(0, 0, V(2), I(1))], dead=[(5, 1)]), kb)))
    # Rejected: the predicate's target has another live slot into it (block2 also goes to block1).
    ti = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (2, [(2, "jump block1")]),
          (1, [(3, "v3.i256 = lt v0 v1"), (4, "br v3 block3 block4")]),
          (3, [(5, "return 1.i256")]),
          (4, [(6, "return 2.i256")])]
    to = copy.deepcopy(ti); to[2] = (1, [(3, "v3.i256 = lt v0 v1"), (4, "jump block3")]); to.pop()
    write("prune_bad_twoin.json", one(snap(P2, R, ti), snap(P2, R, to),
        facts(gvn(cls=[(3, V(2))], preds=[(0, 0, V(2), I(1))], dead=[(1, 1)]), kb)))
    # Rejected: GVN's old `not` peel on a word (`br (not v2)`'s nonzero edge does not make v2
    # zero), and the same predicate of the condition itself, which holds (`v3 = 0` on the zero
    # edge) but does not decide `br v2`.
    ni = [(0, [(0, "v2.i256 = evm_calldata_load 0.i256"), (1, "v3.i256 = not v2"), (2, "br v3 block1 block2")]),
          (1, [(3, "br v2 block3 block4")]),
          (2, [(4, "return 0.i256")]),
          (3, [(5, "return 1.i256")]),
          (4, [(6, "return 2.i256")])]
    no = copy.deepcopy(ni); no[1] = (1, [(3, "jump block4")]); del no[3]
    write("prune_bad_not.json", one(snap(P2, R, ni), snap(P2, R, no),
        facts(gvn(preds=[(0, 0, V(2), I(0))], dead=[(1, 0)]))))
    write("prune_bad_not2.json", one(snap(P2, R, ni), snap(P2, R, no),
        facts(gvn(preds=[(0, 1, V(3), I(0))], dead=[(1, 0)]))))
    # A phi left trivial: block4 goes, block3's phi takes `v0` alone and is replaced by it.
    pi = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (1, [(2, "v3.i256 = lt v0 v1"), (3, "br v3 block3 block4")]),
          (4, [(4, "jump block3")]),
          (3, [(5, "v5.i256 = phi (v0 block1) (v1 block4)"), (6, "return v5")]),
          (2, [(7, "return 0.i256")])]
    po = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
          (1, [(2, "v3.i256 = lt v0 v1"), (3, "jump block3")]),
          (3, [(6, "return v0")]),
          (2, [(7, "return 0.i256")])]
    write("prune_phi.json", one(snap(P2, R, pi), snap(P2, R, po), facts(good, kb)))
    # Rejected: a phi operand dropped from a live edge (the phi kept, its operand from block1
    # gone), and the dropped edge's operand kept.
    po2 = copy.deepcopy(po); po2[2] = (3, [(5, "v5.i256 = phi (v1 block4)"), (6, "return v5")])
    write("prune_bad_phi_live.json", one(snap(P2, R, pi), snap(P2, R, po2), facts(good, kb)))
    pi3 = copy.deepcopy(pi); pi3[1] = (1, [(2, "v3.i256 = lt v0 v1"), (3, "br v3 block3 block4")])
    pi3[3] = (3, [(5, "v5.i256 = phi (v0 block1) (v1 block4)"), (8, "evm_mstore 0.i256 v5"), (6, "return v5")])
    pi3[2] = (4, [(4, "jump block3")])
    po3 = [(0, [(0, "v2.i256 = lt v0 v1"), (1, "br v2 block1 block2")]),
           (1, [(2, "v3.i256 = lt v0 v1"), (3, "jump block3")]),
           (3, [(5, "v5.i256 = phi (v0 block1) (v1 block4)"), (8, "evm_mstore 0.i256 v5"), (6, "return v5")]),
           (2, [(7, "return 0.i256")])]
    write("prune_bad_phi_stale.json", one(snap(P2, R, pi3), snap(P2, R, po3), facts(good, kb)))
    # A phi equal to `0` through a `br_table` case predicate at its predecessor's end (as in
    # `lane_holds_before_halts`): `br v3` takes its zero slot.
    ci = [(0, [(0, "v2.i256 = evm_calldata_load 0.i256"), (1, "br_table v2 block2 (0.i256 block1)")]),
          (1, [(2, "jump block3")]),
          (2, [(3, "jump block3")]),
          (3, [(4, "v3.i256 = phi (v2 block1) (0.i256 block2)"), (5, "br v3 block4 block5")]),
          (4, [(6, "return 1.i256")]),
          (5, [(7, "return 0.i256")])]
    co = copy.deepcopy(ci); co[3] = (3, [(4, "v3.i256 = phi (v2 block1) (0.i256 block2)"), (5, "jump block5")]); del co[4]
    cg = gvn(cls=[(3, I(0))], preds=[(0, 1, V(2), I(0))], dead=[(3, 0)])
    write("prune_case.json", one(snap(P2, R, ci), snap(P2, R, co), facts(cg)))
    # Rejected: the case key `1`, the predicate claiming `v2 = 0` of it; and with the true
    # predicate `v2 = 1`, which makes the phi no constant.
    ci2 = copy.deepcopy(ci); ci2[0] = (0, [(0, "v2.i256 = evm_calldata_load 0.i256"), (1, "br_table v2 block2 (1.i256 block1)")])
    co2 = copy.deepcopy(co); co2[0] = ci2[0]
    write("prune_bad_case_key.json", one(snap(P2, R, ci2), snap(P2, R, co2), facts(cg)))
    write("prune_bad_case_phi.json", one(snap(P2, R, ci2), snap(P2, R, co2),
        facts(gvn(cls=[(3, I(0))], preds=[(0, 1, V(2), I(1))], dead=[(3, 0)]))))
    # Rejected: the default slot's target claimed equal to the key (slot 0 is the default).
    write("prune_bad_case_slot.json", one(snap(P2, R, ci), snap(P2, R, co),
        facts(gvn(cls=[(3, I(0))], preds=[(0, 0, V(2), I(0))], dead=[(3, 0)]))))
    # Rejected: a dead slot of a `br_table` (not pruned by this checker), and both slots of a `br`.
    write("prune_bad_table_slot.json", one(snap(P2, R, ci), snap(P2, R, ci), facts(gvn(dead=[(0, 0)]))))
    write("prune_bad_both.json", one(snap(P2, R, bi), snap(P2, R, bo),
        facts(gvn(cls=good["class"], preds=good["preds"], dead=[(1, 0), (1, 1)]), kb)))

def real_mutants():
    def gvn_of(r): return r["passes"][0]["steps"][0]["funcs"][0]["facts"]["gvn"]
    def nopreds(r): gvn_of(r)["preds"] = []
    def nocls(r): gvn_of(r)["class"] = []
    for name in ["prune_c", "prune_blob"]:
        for tag, fn in [("nopreds", nopreds), ("nocls", nocls)]:
            r = json.load(open(name + ".json")); fn(r); write(f"{name}_bad_{tag}.json", r)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "real":
        real(*sys.argv[2:6])
    elif len(sys.argv) > 1 and sys.argv[1] == "mutants":
        real_mutants()
    else:
        hand()
