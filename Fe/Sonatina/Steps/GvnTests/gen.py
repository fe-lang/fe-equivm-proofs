# The step records of GvnTests.lean.
#   python3 gen.py real SIDECAR SECTION FUNC NAME   one real gvn_rewrite step, from a corpus sidecar
#   python3 gen.py                                  the hand-written records and the mutants
import json, sys, copy, re

def facts(gvn, kb=()):
    return {"gvn": gvn, "known_bits": [[v, str(z), str(o)] for v, z, o in kb],
            "demanded_bits": None, "sccp": None, "finite_loops": [], "ranges": None}

def gvn(cls=(), preds=(), phis=(), vphis=(), dead=()):
    return {"dead_edges": [list(e) for e in dead], "class": [list(c) for c in cls],
            "preds": [list(p) for p in preds], "phis": list(phis), "value_phis": [list(v) for v in vphis]}

def one(inp, out, fs, kind="gvn_rewrite"):
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
                if st["kind"] == "gvn_rewrite" and o["func"] == func:
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

def mutate(src, dst, fn):
    r = json.load(open(src + ".json"))
    fn(r)
    write(dst + ".json", r)

def out_of(r): return r["passes"][0]["steps"][0]["funcs"][0]["out"]
def gvn_of(r): return r["passes"][0]["steps"][0]["funcs"][0]["facts"]["gvn"]

def hand():
    # Same key, commutative: `add v1 v0` in block1 is `add v0 v1` of block0, which dominates it.
    inp = snap(P2, R, [(0, [(0, "v2.i256 = add v0 v1"), (1, "br v0 block1 block2")]),
                       (1, [(2, "v3.i256 = add v1 v0"), (3, "evm_mstore 0.i256 v3"), (4, "jump block2")]),
                       (2, [(5, "return v2")])])
    out = snap(P2, R, [(0, [(0, "v2.i256 = add v0 v1"), (1, "br v0 block1 block2")]),
                       (1, [(3, "evm_mstore 0.i256 v2"), (4, "jump block2")]),
                       (2, [(5, "return v2")])])
    write("gvn_key.json", one(inp, out, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: the class pair claimed for an instruction of another key.
    inp2 = copy.deepcopy(inp); inp2["text"] = inp2["text"].replace("v3.i256 = add v1 v0", "v3.i256 = sub v1 v0")
    write("gvn_bad_key.json", one(inp2, out, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: no class pair and no schema.
    write("gvn_bad_noclass.json", one(inp2, out, facts(gvn())))
    # Rejected: a leader that does not dominate the use (block1 does not dominate block2).
    inp3 = snap(P2, R, [(0, [(0, "br v0 block1 block2")]),
                        (1, [(1, "v2.i256 = add v0 v1"), (2, "evm_mstore 0.i256 v2"), (3, "jump block2")]),
                        (2, [(4, "v3.i256 = add v0 v1"), (5, "return v3")])])
    out3 = snap(P2, R, [(0, [(0, "br v0 block1 block2")]),
                        (1, [(1, "v2.i256 = add v0 v1"), (2, "evm_mstore 0.i256 v2"), (3, "jump block2")]),
                        (2, [(5, "return v2")])])
    write("gvn_bad_nodom.json", one(inp3, out3, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: two loads merged across a store.
    inp4 = snap(P2, R, [(0, [(0, "v2.i256 = evm_mload v0"), (1, "evm_mstore v0 v1"), (2, "v3.i256 = evm_mload v0"),
                             (3, "return v3")])])
    out4 = snap(P2, R, [(0, [(0, "v2.i256 = evm_mload v0"), (1, "evm_mstore v0 v1"), (3, "return v2")])])
    write("gvn_bad_loads.json", one(inp4, out4, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: two `clz` merged (review H-2).
    inp5 = snap(P2, R, [(0, [(0, "v2.i256 = clz v0"), (1, "v3.i256 = clz v0"), (2, "v4.i256 = add v2 v3"),
                             (3, "return v4")])])
    out5 = snap(P2, R, [(0, [(0, "v2.i256 = clz v0"), (2, "v4.i256 = add v2 v2"), (3, "return v4")])])
    write("gvn_bad_clz.json", one(inp5, out5, facts(gvn(cls=[(3, V(2))]))))
    # Two phis of one block with operands of one class from each predecessor.
    ph_in = snap(P2, R, [(0, [(0, "br v0 block1 block2")]), (1, [(1, "jump block3")]), (2, [(2, "jump block3")]),
                         (3, [(3, "v2.i256 = phi (v0 block1) (v1 block2)"), (4, "v3.i256 = phi (v0 block1) (v1 block2)"),
                              (5, "v4.i256 = sub v2 v3"), (6, "return v4")])])
    ph_out = snap(P2, R, [(0, [(0, "br v0 block1 block2")]), (1, [(1, "jump block3")]), (2, [(2, "jump block3")]),
                          (3, [(3, "v2.i256 = phi (v0 block1) (v1 block2)"), (5, "v4.i256 = sub v2 v2"), (6, "return v4")])])
    write("gvn_phi.json", one(ph_in, ph_out, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: the phis differ on one predecessor.
    ph_bad = copy.deepcopy(ph_in); ph_bad["text"] = ph_bad["text"].replace("v3.i256 = phi (v0 block1) (v1 block2)", "v3.i256 = phi (v0 block1) (v0 block2)")
    write("gvn_bad_phi.json", one(ph_bad, ph_out, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: a predicate on an edge used as a class (the checker trusts no predicate).
    pr_in = snap(P2, R, [(0, [(0, "v2.i256 = eq v0 v1"), (1, "br v2 block1 block2")]),
                         (1, [(2, "v3.i256 = add v0 1.i256"), (3, "v4.i256 = add v1 1.i256"), (4, "v5.i256 = sub v3 v4"),
                              (5, "return v5")]),
                         (2, [(6, "return 0.i256")])])
    pr_out = snap(P2, R, [(0, [(0, "v2.i256 = eq v0 v1"), (1, "br v2 block1 block2")]),
                          (1, [(2, "v3.i256 = add v0 1.i256"), (4, "v5.i256 = sub v3 v3"), (5, "return v5")]),
                          (2, [(6, "return 0.i256")])])
    write("gvn_bad_pred.json", one(pr_in, pr_out, facts(gvn(cls=[(4, V(3))], preds=[(0, 0, V(0), V(1))]))))
    # ... and with the wrong polarity (the zero edge).
    pr2_in = copy.deepcopy(pr_in); pr2_in["text"] = pr2_in["text"].replace("br v2 block1 block2", "br v2 block2 block1")
    pr2_out = copy.deepcopy(pr_out); pr2_out["text"] = pr2_out["text"].replace("br v2 block1 block2", "br v2 block2 block1")
    write("gvn_bad_pred_polarity.json", one(pr2_in, pr2_out, facts(gvn(cls=[(4, V(3))], preds=[(0, 1, V(0), V(1))]))))
    # Two `sym_addr` of one symbol merged (as `EcrecoverPrecompile`'s `permute`), the second deleted.
    sy_in = snap(P2, R, [(0, [(0, "v2.i256 = sym_addr $g"), (1, "v3.i256 = sym_addr $g"), (2, "v4.i256 = add v2 v3"),
                              (3, "return v4")])])
    sy_out = snap(P2, R, [(0, [(0, "v2.i256 = sym_addr $g"), (2, "v4.i256 = add v2 v2"), (3, "return v4")])])
    write("gvn_sym.json", one(sy_in, sy_out, facts(gvn(cls=[(3, V(2))]))))
    # Rejected: of another symbol, or `sym_size` of the symbol.
    for tag, line in [("other", "v3.i256 = sym_addr $h"), ("size", "v3.i256 = sym_size $g")]:
        bad = copy.deepcopy(sy_in); bad["text"] = bad["text"].replace("v3.i256 = sym_addr $g", line)
        write(f"gvn_bad_sym_{tag}.json", one(bad, sy_out, facts(gvn(cls=[(3, V(2))]))))
    # A dead `sym_addr` deleted by `scalar_canonicalize`; rejected by `known_bits_simplify`.
    dd_in = snap(P2, R, [(0, [(0, "v2.i256 = sym_addr $g"), (1, "return v0")])])
    dd_out = snap(P2, R, [(0, [(1, "return v0")])])
    nof = {"gvn": None, "known_bits": [], "demanded_bits": None, "sccp": None, "finite_loops": [], "ranges": None}
    write("sc_sym_dead.json", one(dd_in, dd_out, nof, kind="scalar_canonicalize"))
    write("kb_bad_sym_dead.json", one(dd_in, dd_out, nof, kind="known_bits_simplify"))
    # Rejected: a rewrite step with dead edges.
    write("gvn_bad_dead.json", one(inp, out, facts(gvn(cls=[(3, V(2))], dead=[(0, 0)]))))
    # Nested value phis (gvn.rs `gvn_rewrite_lists_nested_value_phis_with_their_terms`).
    P4 = ["v0.i256", "v1.i256", "v2.i256", "v3.i256"]
    ne_in = snap(P4, R, [(0, [(0, "v4.i256 = lt v0 v1"), (1, "br v4 block1 block2")]),
                         (1, [(2, "v5.i256 = add v1 1.i256"), (3, "jump block6")]),
                         (2, [(4, "v6.i256 = lt v0 v2"), (5, "br v6 block3 block4")]),
                         (3, [(6, "v7.i256 = add v2 1.i256"), (7, "jump block5")]),
                         (4, [(8, "v8.i256 = add v3 1.i256"), (9, "jump block5")]),
                         (5, [(10, "v9.i256 = phi (v2 block3) (v3 block4)"), (11, "jump block6")]),
                         (6, [(12, "v10.i256 = phi (v1 block1) (v9 block5)"), (13, "v11.i256 = add v10 1.i256"),
                              (14, "return v11")])])
    ne_out = snap(P4, R, [(0, [(0, "v4.i256 = lt v0 v1"), (1, "br v4 block1 block2")]),
                          (1, [(2, "v5.i256 = add v1 1.i256"), (3, "jump block6")]),
                          (2, [(4, "v6.i256 = lt v0 v2"), (5, "br v6 block3 block4")]),
                          (3, [(6, "v7.i256 = add v2 1.i256"), (7, "jump block5")]),
                          (4, [(8, "v8.i256 = add v3 1.i256"), (9, "jump block5")]),
                          (5, [(15, "v12.i256 = phi (v7 block3) (v8 block4)"), (10, "v9.i256 = phi (v2 block3) (v3 block4)"),
                               (11, "jump block6")]),
                          (6, [(16, "v13.i256 = phi (v5 block1) (v12 block5)"), (12, "v10.i256 = phi (v1 block1) (v9 block5)"),
                               (14, "return v13")])])
    t = lambda phi: {"inst": {"inst": 13, "args": [V(phi), I(1)]}}
    ne_phis = [{"phi": 12, "block": 5, "term": t(9)}, {"phi": 13, "block": 6, "term": t(10)}]
    write("gvn_nested.json", one(ne_in, ne_out, facts(gvn(phis=ne_phis, vphis=[(11, 13)]))))
    # Rejected: an inserted phi with a wrong operand; with a wrong term; without a term; recorded
    # in another block; an inserted phi after a phi of the input.
    bad = copy.deepcopy(ne_out); bad["text"] = bad["text"].replace("v12.i256 = phi (v7 block3) (v8 block4)", "v12.i256 = phi (v7 block3) (v3 block4)")
    write("gvn_bad_phi_operand.json", one(ne_in, bad, facts(gvn(phis=ne_phis, vphis=[(11, 13)]))))
    bt = [{"phi": 12, "block": 5, "term": t(9)}, {"phi": 13, "block": 6, "term": {"inst": {"inst": 13, "args": [V(10), I(2)]}}}]
    write("gvn_bad_phi_term.json", one(ne_in, ne_out, facts(gvn(phis=bt, vphis=[(11, 13)]))))
    nt = [{"phi": 12, "block": 5, "term": t(9)}, {"phi": 13, "block": 6, "term": None}]
    write("gvn_bad_phi_noterm.json", one(ne_in, ne_out, facts(gvn(phis=nt, vphis=[(11, 13)]))))
    wb = [{"phi": 12, "block": 5, "term": t(9)}, {"phi": 13, "block": 5, "term": t(10)}]
    write("gvn_bad_phi_block.json", one(ne_in, ne_out, facts(gvn(phis=wb, vphis=[(11, 13)]))))
    late = copy.deepcopy(ne_out)
    late["text"] = late["text"].replace("        v13.i256 = phi (v5 block1) (v12 block5);\n        v10.i256 = phi (v1 block1) (v9 block5);",
                                        "        v10.i256 = phi (v1 block1) (v9 block5);\n        v13.i256 = phi (v5 block1) (v12 block5);")
    late["insts"][6] = [12, 16, 14]
    write("gvn_bad_phi_late.json", one(ne_in, late, facts(gvn(phis=ne_phis, vphis=[(11, 13)]))))

def real_mutants():
    # carry (Bn254Add): `v5 = shl 5 v3` and `v6 = add v1 v5` by the inserted `v50`, `v51` of block5.
    def phi_operand(r):
        o = out_of(r); o["text"] = o["text"].replace("v51.i256 = phi (v1 block0) (v15 block1)", "v51.i256 = phi (v1 block0) (v14 block1)")
    mutate("gvn_carry", "gvn_carry_bad_operand", phi_operand)
    def phi_term(r):
        g = gvn_of(r); g["phis"][0]["term"]["inst"]["args"][0] = I(6)
    mutate("gvn_carry", "gvn_carry_bad_term", phi_term)
    def wrong_phi(r):
        o = out_of(r); o["text"] = o["text"].replace("evm_mload v51", "evm_mload v50").replace("evm_mstore v51", "evm_mstore v50")
    mutate("gvn_carry", "gvn_carry_bad_use", wrong_phi)
    # from_slice (Builder): `v62 = add v9 64` by `v53`.
    def bad_rep(r):
        g = gvn_of(r); g["class"] = [[62, V(9)]]
        o = out_of(r); assert "v53 64.i256" not in o["text"]
        o["text"] = re.sub(r"\bv53\b(?!\.)", "v9", o["text"])
    mutate("gvn_from_slice", "gvn_from_slice_bad_rep", bad_rep)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "real":
        real(*sys.argv[2:6])
    else:
        hand()
        real_mutants()
