#!/usr/bin/env python3
"""Totals the differential-test lines of an export audit, which `Fe/EVM/Diff.lean` prints for
the calls of Fe tests and `Fe/EVM/Generate.lean` for generated calls: the comparisons of model
and bytecode, then those of fe-spec's interpreter with both, with the distinct reasons the
interpreter gave up for (`SPEC`) and the targets it has no program for (`NOIR`)."""
import collections
import re
import sys

totals = collections.Counter()
generated = collections.Counter()
files = 0
disagreements = []
diff3 = []
pairs = collections.Counter()
spec = collections.Counter()
noir = []
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
    elif kind == "DIFF3":
        diff3.append(rest)
        for pair in re.findall(r"(?:^|; )(\w+≠\w+) \(", rest.partition(": ")[2]):
            pairs[pair] += 1
    elif kind == "SPEC":
        spec[rest.partition(": ")[2]] += 1
    elif kind == "NOIR":
        noir.append(rest)
    elif kind == "TEST" and " returns " not in rest and " reverts " not in rest:
        unfinished.append(rest)


def interp(c):
    return (
        f"interpreter: {c['agree3']} agree three ways, {c['interpDisagree']} disagree, "
        f"{c['spec']} where it gives up, {c['notRun']} not run, "
        f"{c['noModel']} on contracts without a model ({c['agree2']} agreeing with the bytecode)"
    )


print(
    f"differential: {files} files, {totals['tests']} tests, {totals['agree']} calls agree, "
    f"{totals['disagree']} disagree, {totals['outOfGas']} out of gas, "
    f"{totals['stackOverflow']} out of stack; "
    f"{totals['covered']} of {totals['targets']} contracts with tests compared; {interp(totals)}"
)
print(
    f"generated: {generated['contracts']} contracts, {generated['deployed']} of "
    f"{generated['sequences']} sequences deployed, {generated['agree']} creations and calls agree "
    f"({generated['returned']} calls returned), {generated['disagree']} disagree, "
    f"{generated['outOfGas']} out of gas, {generated['stackOverflow']} out of stack; "
    f"{interp(generated)}"
)
print(f"interpreter disagreements by pair: {dict(sorted(pairs.items()))}; targets without IR: {len(noir)}")
for line in disagreements[:60]:
    print("  DISAGREE", line[:300])
if len(disagreements) > 60:
    print(f"  ... and {len(disagreements) - 60} more")
for line in diff3[:60]:
    print("  DIFF3", line[:400])
if len(diff3) > 60:
    print(f"  ... and {len(diff3) - 60} more")
for reason, count in spec.most_common():
    print(f"  SPEC {count} {reason[:300]}")
for line in noir:
    print("  NOIR", line[:300])
for line in unfinished[:20]:
    print("  UNFINISHED", line[:200])
