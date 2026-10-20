#!/usr/bin/env python3
"""Delete top-level declarations (with their docstrings) from Lean files.

usage: drop_decl.py <file>:<name> ...   (name without namespace prefix, as written after the keyword)
"""
import re, sys

for spec in sys.argv[1:]:
    path, name = spec.rsplit(':', 1)
    lines = open(path).read().split('\n')
    pat = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+' + re.escape(name) + r'(?=[\s:({\[]|$)')
    hits = [i for i, l in enumerate(lines) if pat.match(l)]
    if len(hits) != 1:
        sys.exit(f'{spec}: {len(hits)} matches')
    s = e = hits[0]
    # a preceding set_option ... in / attribute line, and the docstring right above
    while s > 0 and lines[s - 1].startswith('set_option ') and lines[s - 1].rstrip().endswith(' in'):
        s -= 1
    if s > 0 and lines[s - 1].rstrip().endswith('-/'):
        while not lines[s - 1].startswith('/--'):
            s -= 1
        s -= 1
    # body: until a blank line followed by a top-level line
    while e + 1 < len(lines) and not (lines[e + 1].strip() == '' and (e + 2 >= len(lines) or not lines[e + 2].startswith((' ', '\t')))):
        e += 1
    del lines[s:e + 2]
    open(path, 'w').write('\n'.join(lines))
    print(f'{spec}: removed lines {s + 1}-{e + 2}')
