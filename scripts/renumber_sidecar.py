#!/usr/bin/env python3
"""Renumber the machine IR of a sidecar's sections, as a compiler change that only renumbers would:
the blocks of each function but its entry get their ids in reverse order and every value's id
grows by 1000, in the machine IR and in each hint that names them.  The bytes do not change.

Usage: scripts/renumber_sidecar.py <in.sidecar.json> <out.sidecar.json>

A test of a certificate's proofs: with the output in place of the fixture they read, the proofs of
the machine IR should build unchanged when they name no block or value (`Func.caseBlock` names a
dispatcher's arm by its selector).  Lake does not track the fixture, so make the module that reads
it (`sonatina_sidecar`, `sonatina_func`) rebuild, by a change to its text, and undo both after."""
import json, re, sys
s = json.load(open(sys.argv[1]))
pretty = open(sys.argv[1]).read().startswith("{\n")
VAL = re.compile(r"(?<![\w%@$&.])v(\d+)\b")
BLK = re.compile(r"\bblock(\d+)\b")
for sec in s["sections"]:
    low = sec["lowering"]
    ir = low["machine_ir"]
    # Per function: blocks in text order, the first (entry) kept.
    funcs = re.split(r"(?=^func )", ir, flags=re.M)
    out, bmaps = [], {}
    for chunk in funcs:
        m = re.match(r"func [^%]*%(\w+)", chunk)
        if not m:
            out.append(chunk); continue
        ids = [int(x) for x in re.findall(r"^\s*block(\d+):", chunk, flags=re.M)]
        rest = sorted(ids[1:])
        bmap = {ids[0]: ids[0], **dict(zip(rest, reversed(rest)))}
        bmaps[m.group(1)] = bmap
        chunk = BLK.sub(lambda x: f"block{bmap.get(int(x[1]), int(x[1]))}", chunk)
        out.append(VAL.sub(lambda x: f"v{int(x[1]) + 1000}", chunk))
    low["machine_ir"] = "".join(out)
    for f in low["funcs"]:
        bmap = bmaps.get(f["name"], {})
        for b in f["blocks"]:
            b["block"] = bmap.get(b["block"], b["block"])
            if b["alias"] is not None: b["alias"] = bmap.get(b["alias"], b["alias"])
            for slot in b["entry_stack"]:
                if isinstance(slot, dict) and "value" in slot: slot["value"] += 1000
        for sp in f["spills"]: sp["value"] += 1000
    for r in low["redirects"]:
        for end in ("from", "to"):
            lab = r[end]
            if isinstance(lab, dict) and "block" in lab:
                bm = bmaps.get(lab["block"]["func"], {})
                lab["block"]["block"] = bm.get(lab["block"]["block"], lab["block"]["block"])
    for name, bmap in bmaps.items():
        print(sec["name"], name, "blocks moved:", sum(a != b for a, b in bmap.items()))
with open(sys.argv[2], "w") as fh:
    fh.write(json.dumps(s, indent=2, ensure_ascii=False) if pretty else json.dumps(s))
