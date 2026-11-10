#!/usr/bin/env python3
"""Tally the `BLOCK <ids>\\t<reason>` lines of an export corpus run by innermost reason.

usage: tally_blockers.py <blockers.txt>
"""
import collections
import re
import sys

tally = collections.Counter()
examples = {}
for line in open(sys.argv[1]):
    if not line.startswith("BLOCK "):
        continue
    ids, reason = line[6:].rstrip("\n").split("\t", 1)
    ids = ids.split(",")
    # Drop the chain of function names the reason is reported through.
    parts = re.split(r": (?=[a-z`A-Z])", reason)
    while len(parts) > 1 and re.fullmatch(r"[A-Za-z0-9_«»]+", parts[0]):
        parts.pop(0)
    key = ": ".join(parts)
    key = re.sub(r"TyId\(Id\(\w+\), PhantomData<fn\(\) -> &\(\)>\)", "T", key)
    key = re.sub(r"N(Value|Root|Block)Id\(\d+\)", "#", key)
    key = re.sub(r"ExprId\(\d+\)", "#", key)[:110]
    tally[key] += len(ids)
    examples.setdefault(key, []).extend(ids)
print("blocked:", sum(tally.values()))
for key, count in tally.most_common():
    print(f"{count:4}  {key}   [{', '.join(examples[key][:3])}]")
