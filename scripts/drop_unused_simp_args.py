#!/usr/bin/env python3
"""Remove the simp arguments Lean's linter reports as unused.

usage: drop_unused_simp_args.py <lake build log>   (run from the project root)

Reads `warning: <file>:<line>:<col>: This simp argument is unused:` entries, checks that the
reported argument starts at that position, and deletes it with its separating comma.
"""
import re, sys
from collections import defaultdict

log = open(sys.argv[1]).read().split('\n')
hits = defaultdict(set)
for i, l in enumerate(log):
    m = re.match(r'warning: (\S+\.lean):(\d+):(\d+): This simp argument is unused:', l)
    if m and m.group(1).startswith('FeProofs/') and i + 1 < len(log):
        hits[m.group(1)].add((int(m.group(2)), int(m.group(3)), log[i + 1].strip()))

ident = re.compile(r"[^\s,\]\[()]+")
removed = 0
for path, ps in hits.items():
    lines = open(path).read().split('\n')
    for ln, col, name in sorted(ps, reverse=True):
        s = lines[ln - 1]
        m = ident.match(s, col)
        if s.startswith(name, col):
            a, b = col, col + len(name)
        elif m and name.endswith('.' + m.group(0)):
            a, b = m.span()
        else:
            print(f'skip {path}:{ln}:{col} {name!r} found {s[col:col+40]!r}')
            continue
        rest = s[b:]
        if rest.startswith(', '):
            s = s[:a] + rest[2:]
        elif rest.startswith(',') and rest[1:].strip() == '':
            s = s[:a] + rest[1:]
        elif s[:a].endswith(', '):
            s = s[:a - 2] + rest
        elif s[:a].endswith('[') and rest.startswith(']'):
            s = s[:a - 1].rstrip() + rest[1:]
        elif s[:a].strip() == '' and rest.startswith(']'):
            # sole remaining argument on a continuation line: drop the comma ending the previous line
            prev = lines[ln - 2].rstrip()
            if prev.endswith(','):
                lines[ln - 2] = prev[:-1] + ']' + rest[1:]
                s = None
            else:
                print(f'skip {path}:{ln}:{col} {name!r} (layout)'); continue
        else:
            print(f'skip {path}:{ln}:{col} {name!r} (layout) {s.strip()[:60]!r}'); continue
        # a line left with only indentation held nothing but the argument: drop it
        lines[ln - 1] = None if s is None or s.strip() == '' else s
        removed += 1
    open(path, 'w').write('\n'.join(l for l in lines if l is not None))
print('removed', removed)
