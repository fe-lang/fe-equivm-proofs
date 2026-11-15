#!/usr/bin/env python3
"""Turn `simpa ... using h` into `simpa ... using! h` at each simpa that a build log reports as
"Type mismatch: After simplification".

usage: scripts/simpa_using_bang.py <build log>   (the output of `lake build`, run from the root)

Lean 4.35 checks the simplified `using` term against the simplified goal at reducible
transparency; 4.29 used the default transparency, which `using!` keeps.  Rerun after each build
until the log has no such error; a simpa that still fails with `using!` is reported, not edited.
"""
import pathlib
import re
import sys
import collections

root = str(pathlib.Path(__file__).resolve().parent.parent)
log = sys.argv[1]
errs=set(re.findall(r'^(?:error: )?([^:\n ]+\.lean):(\d+):(\d+): (?:error: )?Type mismatch: After simplification',open(log).read(),re.M))
byf=collections.defaultdict(list)
for f,l,c in errs: byf[f].append((int(l),int(c)))
n=0; miss=[]
block = re.compile(r'-- BEGIN fe-lean-export: [\w.]+\n.*?-- END fe-lean-export\n', re.S)
for f,ps in byf.items():
    if re.search(r'Blocks_\d+\.lean$', f):
        miss += [(f, l, c, 'generated block file') for l, c in ps]; continue
    p=root+'/'+f; s=open(p).read(); L=s.split('\n')
    spans=[m.span() for m in block.finditer(s)]
    offs=[0]
    for line in L: offs.append(offs[-1]+len(line)+1)
    for l,c in sorted(ps,reverse=True):
        o=offs[l-1]+c
        if any(a <= o < b for a, b in spans): miss.append((f,l,c,'exporter output')); continue
        if not s.startswith('simpa',o): miss.append((f,l,c,s[o:o+20])); continue
        m=re.compile(r'\busing\b').search(s,o)
        if not m: miss.append((f,l,c,'no using')); continue
        if s.startswith('!',m.end()): miss.append((f,l,c,'already using!')); continue
        s=s[:m.end()]+'!'+s[m.end():]; n+=1
    open(p,'w').write(s)
print(n,'using! edits'); [print('MISS',x) for x in miss]
