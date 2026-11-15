#!/usr/bin/env python3
"""Pass selector facts to `simp` as equalities, for the files named.

usage: scripts/selector_eq_facts.py <file.lean> ...

EthLib, which EVMLean imports from Lean 4.35 on, declares `LawfulBEq ByteArray`, so `simp`
rewrites `(sel == cd.extract 0 4) = true` in a goal to `sel = cd.extract 0 4`, and a fact
`(sel == …) = true` or `= false` given to `simp` no longer matches it.  In each `simp […]`
argument list this wraps such facts: `show (a == b) = true from h` and `selN h` in `eq_of_beq`,
`show (a == b) = false from h`, `selN_not h` and the names of local facts
`have nK : (a == b) = false := …` or `have nK := miss K hK` in `ne_of_beq_false`.  A fact already
wrapped is left alone, so the script can be rerun.
"""
import re
import sys

show = re.compile(r'(?<![\w(])show \(([^()]*?) == ([^()]*?)\) = (true|false) from (\w+)')
selfact = re.compile(r'(?<![\w(])sel(\d+)(_not)? (h\w*)')


def wrap_args(args, falses):
    args = show.sub(lambda m: ('eq_of_beq' if m[3] == 'true' else 'ne_of_beq_false')
                    + f' ({m[0]})', args)
    args = selfact.sub(lambda m: ('ne_of_beq_false' if m[2] else 'eq_of_beq') + f' ({m[0]})', args)
    for name in falses:
        args = re.sub(r'(?<![\w(.])(?<!from )' + re.escape(name) + r'(?![\w\'.])',
                      f'ne_of_beq_false {name}', args)
    return args


for name in sys.argv[1:]:
    text = open(name).read()
    falses = set(re.findall(r'have (n\d+) : \([^()]*? == [^()]*?\) = false', text))
    falses |= set(re.findall(r'have (n\d+) := miss \d+ h\d+', text))
    out, pos = [], 0
    for m in re.finditer(r'\bsimp(?: only)? (?:\+\w+ )?\[', text):
        start = m.end()
        depth, j = 1, start
        while depth:
            depth += {'[': 1, ']': -1}.get(text[j], 0)
            j += 1
        out += [text[pos:start], wrap_args(text[start:j - 1], falses), ']']
        pos = j
    new = ''.join(out) + text[pos:]
    if new != text:
        open(name, 'w').write(new)
        print(f'wrapped {name}')
