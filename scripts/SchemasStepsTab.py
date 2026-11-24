#!/usr/bin/env python3
"""Tabulate the output of scripts/SchemasSteps.lean: python3 scripts/SchemasStepsTab.py <tsv>.

Counts function steps by level (the `feproofs-*` directory of the sidecar, else `full`), kind,
verdict and reason, and sections by level and kind (a section is rejected if any of its steps
of that kind is)."""
import sys, collections

steps = collections.Counter()
secs = collections.defaultdict(lambda: collections.defaultdict(set))
for line in open(sys.argv[1]):
    p = line.rstrip("\n").split("\t")
    if len(p) < 6:
        print("unparsed:", line[:200])
        continue
    path, sec, kind, fn, v, why = p[:6]
    lvl = next((x for x in path.split("/") if x.startswith("feproofs-")), "full")
    steps[(lvl, kind, v, why if v == "REJECT" or why.startswith("skipped") else "")] += 1
    secs[(lvl, kind)][v].add((path, sec))
print("function steps:")
for k in sorted(steps):
    print(f"  {steps[k]:5}  " + "  ".join(k))
print("sections:")
for k in sorted(secs):
    rej = secs[k]["REJECT"]
    print(f"  {k[0]:12} {k[1]:20} accepted {len(secs[k]['ACCEPT'] - rej):4}  rejected {len(rej):4}")
