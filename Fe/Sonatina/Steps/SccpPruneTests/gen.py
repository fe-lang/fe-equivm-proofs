# The step records of SccpPruneTests.lean (`python3 gen.py`): hand-written `sccp_prune` steps
# and their mutants.  No corpus has an `sccp_prune` step.
import json, copy

def facts(consts=(), dead=(), kb=(), **other):
    f = {"known_bits": [[v, str(z), str(o)] for v, z, o in kb], "demanded_bits": None,
         "sccp": {"consts": [[v, str(c)] for v, c in consts], "dead_edges": [list(e) for e in dead]},
         "finite_loops": [], "gvn": None, "ranges": None}
    f.update(other)
    return f

def one(inp, out, fs):
    return {"profile": "speed", "lowered": [inp], "passes": [{"kind": "sccp", "func_behavior": None,
        "steps": [{"kind": "sccp_prune", "funcs": [{"out": out, "facts": fs}]}]}]}

def write(fn, r):
    with open(fn, "w") as f:
        json.dump(r, f, indent=1)

def func(name, params, rets, blocks):
    lines = [f"func private %{name}({', '.join(params)}){' -> ' + ', '.join(rets) if rets else ''} {{"]
    for b, stmts in blocks:
        lines.append(f"    block{b}:")
        lines += [f"        {s};" for s in stmts]
    lines.append("}")
    return "\n".join(lines) + "\n"

def snap(blocks, params=("v0.i256", "v1.i256"), rets=("i256",)):
    """Blocks as (id, [(inst id, line)])."""
    return {"func": "f", "func_ref": 0, "text": func("f", params, rets, [(b, [l for _, l in ls]) for b, ls in blocks]),
            "insts": [[i for i, _ in ls] for _, ls in blocks]}

def rec(name, bi, bo, fs):
    write(name + ".json", one(snap(bi), snap(bo), fs))

def hand():
    # A `br` on a constant: `v2 = lt 1 2` is 1, the zero slot is dead, block2 is left unreachable
    # and deleted, and with it block4, which only block2 reaches.
    bi = [(0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "br v2 block1 block2")]),
          (1, [(2, "return v0")]),
          (2, [(3, "jump block4")]),
          (4, [(4, "return v1")])]
    bo = [(0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "jump block1")]),
          (1, [(2, "return v0")])]
    good = facts(consts=[(2, 1)], dead=[(0, 1)])
    rec("prune_nz", bi, bo, good)
    # The other polarity: `v2 = lt 2 1` is 0, the nonzero slot is dead.
    zi = copy.deepcopy(bi); zi[0] = (0, [(0, "v2.i256 = lt 2.i256 1.i256"), (1, "br v2 block1 block2")])
    zo = [(0, [(0, "v2.i256 = lt 2.i256 1.i256"), (1, "jump block2")]),
          (2, [(3, "jump block4")]),
          (4, [(4, "return v1")])]
    rec("prune_z", zi, zo, facts(consts=[(2, 0)], dead=[(0, 0)]))
    # Rejected: the polarity swapped (the slot taken claimed dead, the output going the other way).
    zo2 = copy.deepcopy(zo); zo2[0] = (0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "jump block2")])
    rec("prune_bad_polarity", bi, zo2, facts(consts=[(2, 1)], dead=[(0, 0)]))
    # Rejected: the constant wrong (`v2 = 0` claimed of `lt 1 2`), with the matching dead slot.
    rec("prune_bad_const", bi, zo2, facts(consts=[(2, 0)], dead=[(0, 0)]))
    # Rejected: a constant of a value SCCP cannot know (`evm_calldata_load`), and no constant.
    ci = copy.deepcopy(bi); ci[0] = (0, [(0, "v2.i256 = evm_calldata_load 0.i256"), (1, "br v2 block1 block2")])
    co = copy.deepcopy(bo); co[0] = (0, [(0, "v2.i256 = evm_calldata_load 0.i256"), (1, "jump block1")])
    rec("prune_bad_unjustified", ci, co, facts(consts=[(2, 1)], dead=[(0, 1)]))
    rec("prune_bad_noconst", bi, bo, facts(dead=[(0, 1)]))
    # Rejected: both slots dead.
    rec("prune_bad_both", bi, bo, facts(consts=[(2, 1)], dead=[(0, 0), (0, 1)]))
    # Rejected: the right facts, and the output jumps to the dead slot's target, or keeps the `br`,
    # or deletes the live block1.
    rec("prune_bad_target", bi, zo2, good)
    rec("prune_bad_kept", bi, bi, good)
    rec("prune_bad_live_deleted", bi, [(0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "jump block1")])], good)
    # Rejected: facts of other steps: GVN's, ADCE's finite loops, demanded bits, ranges; and no
    # SCCP facts.
    gvn = {"dead_edges": [[0, 1]], "class": [], "preds": [], "phis": [], "value_phis": []}
    rec("prune_bad_gvn", bi, bo, facts(consts=[(2, 1)], dead=[(0, 1)], gvn=gvn))
    rec("prune_bad_loops", bi, bo, facts(consts=[(2, 1)], dead=[(0, 1)], finite_loops=[{"header": 1, "latch": 1, "iv": 3, "step": 4, "exit": 1}]))
    rec("prune_bad_demand", bi, bo, facts(consts=[(2, 1)], dead=[(0, 1)], demanded_bits=[]))
    rec("prune_bad_ranges", bi, bo, facts(consts=[(2, 1)], dead=[(0, 1)],
        ranges={"unreachable": [], "entry": [], "no_wrap": []}))
    nos = facts(); nos["sccp"] = None
    rec("prune_bad_nosccp", bi, bo, nos)

    # A `br_table` on a constant scrutinee (`v2 = add 1 0` is 1): slot 0 is the default (block3),
    # slot k + 1 case k.  Case `1` (slot 2) is taken; the other slots are dead, and the table
    # becomes a `jump`.
    ti = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "br_table v2 block3 (0.i256 block1) (1.i256 block2)")]),
          (1, [(2, "return 1.i256")]),
          (2, [(3, "return 2.i256")]),
          (3, [(4, "return 3.i256")])]
    to = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "jump block2")]),
          (2, [(3, "return 2.i256")])]
    rec("prune_table_case", ti, to, facts(consts=[(2, 1)], dead=[(0, 0), (0, 1)]))
    # Rejected: the taken case's slot claimed dead (as if the key were 0).
    to1 = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "jump block1")]),
           (1, [(2, "return 1.i256")])]
    rec("prune_bad_table_key", ti, to1, facts(consts=[(2, 1)], dead=[(0, 0), (0, 2)]))
    # The default: `v2 = add 5 0` matches no key.
    di = copy.deepcopy(ti); di[0] = (0, [(0, "v2.i256 = add 5.i256 0.i256"), (1, ti[0][1][1][1])])
    do = [(0, [(0, "v2.i256 = add 5.i256 0.i256"), (1, "jump block3")]),
          (3, [(4, "return 3.i256")])]
    rec("prune_table_default", di, do, facts(consts=[(2, 5)], dead=[(0, 1), (0, 2)]))
    # Rejected: the default claimed dead where no key matches.
    rec("prune_bad_table_default", di, to, facts(consts=[(2, 5)], dead=[(0, 0), (0, 1)]))
    # A table left a table: the default and case `1` go to block1, which `v2 = 1` takes; case `2`'s
    # slot is dead.
    ki = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "br_table v2 block1 (1.i256 block1) (2.i256 block2)")]),
          (1, [(2, "return 1.i256")]),
          (2, [(3, "return 2.i256")])]
    ko = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "br_table v2 block1 (1.i256 block1)")]),
          (1, [(2, "return 1.i256")])]
    rec("prune_table_keep", ki, ko, facts(consts=[(2, 1)], dead=[(0, 2)]))
    # Rejected (the compiler can emit it): the default dead with two cases left, both to block1;
    # `remove_edges_to_block` leaves a table without a default, which is not machine IR.
    ni = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "br_table v2 block3 (1.i256 block1) (2.i256 block1)")]),
          (1, [(2, "return 1.i256")]),
          (3, [(4, "return 3.i256")])]
    no = [(0, [(0, "v2.i256 = add 1.i256 0.i256"), (1, "br_table v2 (1.i256 block1) (2.i256 block1)")]),
          (1, [(2, "return 1.i256")])]
    rec("prune_bad_table_nodefault", ni, no, facts(consts=[(2, 1)], dead=[(0, 0)]))

    # A pruned edge into a block with phis: block0's zero slot to block3 is dead; block3's phi loses
    # its operand from block0 and keeps the two from block1 and block2, both live.
    pi = [(0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "br v2 block4 block3")]),
          (4, [(2, "br v0 block1 block2")]),
          (1, [(3, "jump block3")]),
          (2, [(4, "jump block3")]),
          (3, [(5, "v3.i256 = phi (7.i256 block0) (v0 block1) (v1 block2)"), (6, "return v3")])]
    po = copy.deepcopy(pi); po[0] = (0, [(0, "v2.i256 = lt 1.i256 2.i256"), (1, "jump block4")])
    po[4] = (3, [(5, "v3.i256 = phi (v0 block1) (v1 block2)"), (6, "return v3")])
    rec("prune_phi", pi, po, facts(consts=[(2, 1)], dead=[(0, 1)]))
    # Rejected: a phi operand dropped from a live edge (block2's), and the removed edge's operand
    # kept.
    po2 = copy.deepcopy(po); po2[4] = (3, [(5, "v3.i256 = phi (v0 block1)"), (6, "return v3")])
    rec("prune_bad_phi_live", pi, po2, facts(consts=[(2, 1)], dead=[(0, 1)]))
    po3 = copy.deepcopy(po); po3[4] = pi[4]
    rec("prune_bad_phi_stale", pi, po3, facts(consts=[(2, 1)], dead=[(0, 1)]))
    # A phi left trivial: block0's nonzero slot to block3 is dead, block3's phi keeps `v1` from
    # block2 alone and is replaced by it.
    qi = [(0, [(0, "v2.i256 = lt 2.i256 1.i256"), (1, "br v2 block3 block2")]),
          (2, [(2, "jump block3")]),
          (3, [(3, "v3.i256 = phi (v0 block0) (v1 block2)"), (4, "return v3")])]
    qo = [(0, [(0, "v2.i256 = lt 2.i256 1.i256"), (1, "jump block2")]),
          (2, [(2, "jump block3")]),
          (3, [(4, "return v1")])]
    rec("prune_phi_trivial", qi, qo, facts(consts=[(2, 0)], dead=[(0, 0)]))
    # Rejected: the trivial phi replaced by the removed edge's operand.
    qo2 = copy.deepcopy(qo); qo2[2] = (3, [(4, "return v0")])
    rec("prune_bad_phi_trivial", qi, qo2, facts(consts=[(2, 0)], dead=[(0, 0)]))
    # Rejected: a phi claimed constant from its executable edges where one operand is not (`v3 = 7`
    # with `v0` from block1 live), deciding a `br` on it.
    ri = [(0, [(0, "br v0 block1 block2")]),
          (1, [(1, "jump block3")]),
          (2, [(2, "jump block3")]),
          (3, [(3, "v3.i256 = phi (v0 block1) (7.i256 block2)"), (4, "v4.i256 = eq v3 7.i256"), (5, "br v4 block4 block5")]),
          (4, [(6, "return 1.i256")]),
          (5, [(7, "return 0.i256")])]
    ro = copy.deepcopy(ri); ro[3] = (3, [(3, "v3.i256 = phi (v0 block1) (7.i256 block2)"), (4, "v4.i256 = eq v3 7.i256"), (5, "jump block4")])
    del ro[5]
    rec("prune_bad_phi_const", ri, ro, facts(consts=[(3, 7), (4, 1)], dead=[(3, 1)]))
    # The same with block1's slot claimed dead too, where block0's condition is no constant.
    ro2 = copy.deepcopy(ro); ro2[0] = (0, [(0, "jump block2")]); del ro2[1]
    ro2[2] = (3, [(4, "v4.i256 = eq 7.i256 7.i256"), (5, "jump block4")])
    rec("prune_bad_unexec", ri, ro2, facts(consts=[(3, 7), (4, 1)], dead=[(0, 0), (3, 1)]))

    # A pruned loop back-edge: `v5 = lt 1 0` is 0, so block1 never loops; its phi keeps `v0` from
    # block0 alone and is replaced by it.
    li = [(0, [(0, "jump block1")]),
          (1, [(1, "v3.i256 = phi (v0 block0) (v4 block1)"), (2, "v4.i256 = add v3 1.i256"),
               (3, "v5.i256 = lt 1.i256 0.i256"), (4, "br v5 block1 block2")]),
          (2, [(5, "return v4")])]
    lo = [(0, [(0, "jump block1")]),
          (1, [(2, "v4.i256 = add v0 1.i256"), (3, "v5.i256 = lt 1.i256 0.i256"), (4, "jump block2")]),
          (2, [(5, "return v4")])]
    rec("prune_loop", li, lo, facts(consts=[(5, 0)], dead=[(1, 0)]))
    # Rejected: the back-edge claimed dead where the loop's condition is no constant (`lt v4 v1`).
    lbi = copy.deepcopy(li); lbi[1] = (1, li[1][1][:2] + [(3, "v5.i256 = lt v4 v1"), (4, "br v5 block1 block2")])
    lbo = copy.deepcopy(lo); lbo[1] = (1, [(2, "v4.i256 = add v0 1.i256"), (3, "v5.i256 = lt v4 v1"), (4, "jump block2")])
    rec("prune_bad_loop", lbi, lbo, facts(consts=[(5, 0)], dead=[(1, 0)]))

if __name__ == "__main__":
    hand()
