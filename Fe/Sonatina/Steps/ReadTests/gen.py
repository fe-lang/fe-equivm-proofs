# Writes the reader's test sidecars: mutations of the record of the runtime section of a real
# sidecar (`../SccpPruneTests/real_is_null_O1.sidecar.json`, Fe `a4c2ab6eb`, `-O1`), each with
# the error the reader gives it.
# `ReadTests.lean` reads `cases.txt`.  Run from this directory: `python3 gen.py`.
import copy, json

base = json.load(open("../SccpPruneTests/real_is_null_O1.sidecar.json"))

def low(d): return d["sections"][1]["lowering"]
def ms(d): return low(d)["machine_steps"]
def sccp_pass(d): return ms(d)["passes"][4]
def prune(d): return sccp_pass(d)["steps"][0]
def fstep(d): return prune(d)["funcs"][0]
def facts(d): return fstep(d)["facts"]

def gvn(**kw):
    g = {"dead_edges": [], "class": [], "preds": [], "phis": [], "value_phis": []}
    g.update(kw)
    return g

# name, mutation, the reader's error (a part of it), or None for a sidecar it reads.
cases = [
    ("v4_ok", lambda d: (d.update(version=4),
                         [s["lowering"].pop("machine_steps") for s in d["sections"]]), None),
    ("v5_no_steps", lambda d: low(d).pop("machine_steps"), "property not found: machine_steps"),
    ("v5_null_steps", lambda d: low(d).update(machine_steps=None), "machine_steps: not an object"),
    ("v4_steps", lambda d: d.update(version=4), "machine_steps in a version 4 sidecar"),
    ("passes_object", lambda d: ms(d).update(passes={}), "array"),
    ("unknown_kind", lambda d: prune(d).update(kind="sccp_prune_all"),
     "unknown step kind sccp_prune_all"),
    ("key_record", lambda d: ms(d).update(version=5), "machine_steps: unknown key version"),
    ("key_pass", lambda d: sccp_pass(d).update(foo=0), "pass: unknown key foo"),
    ("key_step", lambda d: prune(d).update(foo=0), "step: unknown key foo"),
    ("key_func_step", lambda d: fstep(d).update(func="contract_runtime_root_Probe"),
     "function step: unknown key func"),
    ("key_snapshot", lambda d: fstep(d)["out"].update(foo=0), "snapshot: unknown key foo"),
    ("key_lowered", lambda d: ms(d)["lowered"][0].update(foo=0), "snapshot: unknown key foo"),
    ("key_summary", lambda d: sccp_pass(d)["func_behavior"][0].update(foo=False),
     "func_behavior: unknown key foo"),
    ("key_facts_null", lambda d: facts(d).update(foo=None), "facts: unknown key foo"),
    ("missing_facts", lambda d: fstep(d).pop("facts"), "function step: no key facts"),
    ("null_facts", lambda d: fstep(d).update(facts=None), "facts: not an object"),
    ("missing_fact_key", lambda d: facts(d).pop("ranges"), "facts: no key ranges"),
    ("key_sccp", lambda d: facts(d)["sccp"].update(foo=[]), "sccp: unknown key foo"),
    ("missing_dead_edges", lambda d: facts(d)["sccp"].pop("dead_edges"),
     "sccp: no key dead_edges"),
    ("key_gvn", lambda d: facts(d).update(gvn=gvn(foo=[])), "gvn: unknown key foo"),
    ("gvn_operand", lambda d: facts(d).update(gvn=gvn(**{"class": [[0, {"value": 1, "imm": "2"}]]})),
     "gvn: not an operand"),
    ("key_gvn_phi", lambda d: facts(d).update(gvn=gvn(phis=[{"phi": 1, "block": 0}])),
     "gvn phi: no key term"),
    ("key_loop", lambda d: facts(d).update(finite_loops=[
        {"header": 1, "latch": 1, "iv": 0, "step": 1, "exit": 2, "foo": 0}]),
     "finite loop: unknown key foo"),
    ("dup_lowered", lambda d: ms(d)["lowered"].append(copy.deepcopy(ms(d)["lowered"][0])),
     "lowered: a function twice"),
    ("dup_step", lambda d: prune(d)["funcs"].append(copy.deepcopy(fstep(d))),
     "sccp_prune step of pass sccp: a function twice"),
]

with open("cases.txt", "w") as out:
    for name, mutate, why in cases:
        d = copy.deepcopy(base)
        mutate(d)
        with open(f"{name}.sidecar.json", "w") as f:
            json.dump(d, f)
        out.write(f"{name}\t{why or ''}\n")
