#!/usr/bin/env python3
"""Drop unused generated block summaries and rewrite the `*Blocks.index` line ranges.

usage: prune_blocks.py <contract dir> <unused.txt from scripts/Unused.lean> [--dry-run]
"""
import re, sys
from pathlib import Path

d, unused_file = Path(sys.argv[1]), sys.argv[2]
dry = '--dry-run' in sys.argv
unused = {l.split('\t')[1].strip().split('.')[-1] for l in open(unused_file) if l.startswith('  ') and '\t' in l}
decl = re.compile(r'^(?:theorem|def|abbrev)\s+(\S+)')

def items(lines):
    """Split into a header and items, each starting at a column-0 comment."""
    starts = [i for i, l in enumerate(lines) if l.startswith('/-')]
    ends = starts[1:] + [next((i for i in range(len(lines) - 1, -1, -1) if lines[i].startswith('end ')), len(lines))]
    out = []
    for s, e in zip(starts, ends):
        name = next((m.group(1) for l in lines[s:e] if (m := decl.match(l))), None)
        out.append((name, lines[s:e]))
    return lines[:starts[0]] if starts else lines, out, lines[ends[-1]:] if starts else []

removed = 0
for f in sorted(d.glob('*Blocks_*.lean')):
    lines = f.read_text().splitlines(keepends=True)
    head, its, tail = items(lines)
    keep = [(n, b) for n, b in its if n not in unused]
    removed += sum(len(b) for n, b in its if n in unused)
    if not dry:
        f.write_text(''.join(head + [l for _, b in keep for l in b] + tail))
print(f'removed {removed} lines')
if dry:
    sys.exit()

# Rewrite the index: entry N spans from its block group's first item to the end of N's item.
for idx in d.glob('*Blocks.index'):
    pos = {}
    for f in sorted(d.glob('*Blocks_*.lean')):
        lines = f.read_text().splitlines()
        cur = None
        for i, l in enumerate(lines, 1):
            if (m := decl.match(l)):
                pos[m.group(1)] = [f.name, i, i]
                cur = m.group(1)
            elif l.startswith(('/-', 'end ')):
                cur = None
            elif cur and l.strip():
                pos[cur][2] = i
    out = []
    for line in idx.read_text().splitlines():
        name, _, pcs = line.split('\t')
        if name not in pos:
            continue
        base = name.removesuffix('_packed')
        first = min((pos[n][1] for n in (base + '_stack', base + '_memory', base) if n in pos))
        fname, _, end = pos[name]
        out.append(f'{name}\t{fname}:{first - 1}-{end}\t{pcs}')
    idx.write_text('\n'.join(out) + '\n')
