#!/usr/bin/env python3
"""Totals the differential-test lines of an export audit, which `Fe/EVM/Diff.lean` prints for
the calls of Fe tests and `Fe/EVM/Generate.lean` for generated calls."""
import re
import sys

totals = {"tests": 0, "agree": 0, "disagree": 0, "outOfGas": 0, "targets": 0, "covered": 0}
generated = {"contracts": 0, "sequences": 0, "deployed": 0, "agree": 0, "disagree": 0, "outOfGas": 0, "returned": 0}
files = 0
disagreements = []
unfinished = []
for line in open(sys.argv[1]):
    kind, _, rest = line.rstrip("\n").partition(" ")
    if kind == "DIFF":
        files += 1
        for key, value in re.findall(r"(\w+)=(\d+)", rest):
            totals[key] += int(value)
    elif kind == "GEN":
        generated["contracts"] += 1
        for key, value in re.findall(r"(\w+)=(\d+)", rest):
            generated[key] += int(value)
    elif kind == "DISAGREE":
        disagreements.append(rest)
    elif kind == "TEST" and " returns " not in rest and " reverts " not in rest:
        unfinished.append(rest)

print(
    f"differential: {files} files, {totals['tests']} tests, {totals['agree']} calls agree, "
    f"{totals['disagree']} disagree, {totals['outOfGas']} out of gas; "
    f"{totals['covered']} of {totals['targets']} contracts with tests compared"
)
print(
    f"generated: {generated['contracts']} contracts, {generated['deployed']} of "
    f"{generated['sequences']} sequences deployed, {generated['agree']} creations and calls agree "
    f"({generated['returned']} calls returned), {generated['disagree']} disagree, "
    f"{generated['outOfGas']} out of gas"
)
for line in disagreements[:60]:
    print("  DISAGREE", line[:300])
if len(disagreements) > 60:
    print(f"  ... and {len(disagreements) - 60} more")
for line in unfinished[:20]:
    print("  UNFINISHED", line[:200])
