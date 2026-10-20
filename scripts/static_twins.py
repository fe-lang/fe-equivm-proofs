#!/usr/bin/env python3
"""Add static-mode twins of generated runtime block summaries.

usage: static_twins.py <contract dir>...

For every block summary whose proof stores (`RD.sstore`) or logs (`RD.genLogN`), add
`<block>_static`: the same steps up to that instruction, which halts when `ee.perm = false`
(`RD.sstoreStatic` / `RD.logNStatic`), concluding `RDstatic code g s0`. `rd_run` uses these twins
when the context has `ee.perm = false`.
"""
import re, sys
from pathlib import Path

def args(s):
    """Split a run of space-separated, possibly parenthesized arguments."""
    out, i = [], 0
    while i < len(s):
        if s[i] == ' ':
            i += 1; continue
        if s[i] == '(':
            d, j = 0, i
            while True:
                d += {'(': 1, ')': -1}.get(s[j], 0)
                j += 1
                if d == 0: break
            out.append(s[i:j]); i = j
        else:
            j = s.find(' ', i); j = len(s) if j < 0 else j
            out.append(s[i:j]); i = j
    return out

sstore = re.compile(r'^  obtain ⟨_, _, r\d+⟩ := RD\.sstore (r\d+) hperm (.*)$')
log = re.compile(r'^  have r\d+ := RD\.genLog(\d) (r\d+) (.*)$')
total = 0
for d in map(Path, sys.argv[1:]):
    for f in sorted(d.glob('RuntimeBlocks_*.lean')):
        lines = f.read_text().split('\n')
        starts = [i for i, l in enumerate(lines) if l.startswith('theorem ')]
        twins, seen = [], set()
        for s in starts:
            name = lines[s].split()[1]
            if name.endswith('_packed'): continue
            base = re.sub(r'_(taken|fallthrough)$', '', name)
            twin = base + '_static'
            if twin in seen or any(l.startswith(f'theorem {twin} ') for l in lines): continue
            # header up to the conclusion, then the proof up to the next blank line
            c = next(i for i in range(s, len(lines)) if lines[i].startswith('    : '))
            e = next((i for i in range(c, len(lines)) if lines[i].strip() == ''), len(lines))
            proof = lines[c + 1:e]
            halt = next((k for k, l in enumerate(proof) if sstore.match(l) or log.match(l)), None)
            if halt is None: continue
            pre = proof[:halt]
            if m := sstore.match(proof[halt]):
                end = f'  exact RD.sstoreStatic {m.group(1)} hperm {m.group(2)}'
            else:
                m = log.match(proof[halt])
                dec, perm, ov = args(m.group(3))
                assert perm == 'hperm', proof[halt]
                end = f'  exact RD.log{m.group(1)}Static {m.group(2)} hperm {dec} {ov}'
            hyps = [l for l in lines[s + 1:c] if l.startswith('    (')]
            hline = next(l for l in hyps if l.startswith('    (h : RD '))
            code = re.match(r'    \(h : RD (\([^()]*\)|\S+) ', hline).group(1)
            body = '\n'.join(pre)
            keep = [l for l in hyps if l is not hline and not l.startswith('    (hperm ')
                    and (l.startswith('    (hstack ') or re.search(r'\b' + re.escape(l[5:].split()[0]) + r'\b', body))]
            twins.append('\n'.join(
                [f'/-- Static-mode twin of `{name}`: its steps up to the state change, which halts when',
                 '    `ee.perm = false`. -/', lines[s].replace(name, twin, 1)] + keep +
                ['    (hperm : ee.perm = false)', hline, f'    : RDstatic {code} g s0 := by'] + pre + [end]))
            seen.add(twin)
        if twins:
            endns = max(i for i, l in enumerate(lines) if l.startswith('end '))
            lines[endns:endns] = ['\n\n'.join(twins), '']
            f.write_text('\n'.join(lines))
            total += len(twins)
            print(f'{f}: {len(twins)} twins')
print('total', total)
