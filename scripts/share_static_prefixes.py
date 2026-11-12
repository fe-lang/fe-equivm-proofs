#!/usr/bin/env python3
"""Share prefixes of generated runtime summaries and their static-mode twins.

usage: share_static_prefixes.py <contract dir>...
Run after static_twins.py and pruning; only retained summaries are changed.
"""
import re
import sys
from pathlib import Path


def declarations(source):
    start = re.compile(r'^theorem (\w+) ([^\n]+)\n', re.M)
    result = {}
    for match in start.finditer(source):
        end = source.find('\n\n', match.end())
        if end < 0:
            continue
        chunk = source[match.start():end]
        if ' := by\n' not in chunk:
            continue
        header, proof = chunk.split(' := by\n', 1)
        lines = header.splitlines()
        hstack = next((line for line in lines if line.startswith('    (hstack ')), None)
        hinput = next((line for line in lines if line.startswith('    (h : RD ')), None)
        if hstack and hinput:
            proof_start = match.start() + len(header) + len(' := by\n')
            result[match.group(1)] = (match, hstack, hinput, proof, proof_start)
    return result


def share(source):
    decls = declarations(source)
    edits = []
    count = 0
    for name, (static, stack, hinput, proof, static_start) in decls.items():
        if not name.endswith('_static'):
            continue
        base = name.removesuffix('_static')
        helper = base + '_before_static'
        if re.search(r'^private def ' + re.escape(helper) + r'\b', source, re.M):
            continue
        lines = proof.splitlines()
        if not lines or not re.match(r'  exact RD\.(?:sstoreStatic|log\dStatic)\b', lines[-1]):
            continue
        pre = lines[:-1]
        if len(pre) < 7 or pre[0] != '  let r0 := h':
            continue
        if any(not re.match(r'^  have r\d+ := ', line) for line in pre[1:]):
            continue
        cursor = re.match(r'^  have (r\d+) := ', pre[-1]).group(1)
        pretext = '\n'.join(pre)
        hypotheses = set(re.findall(r'\bh[A-Za-z0-9_]*\b', pretext))
        if hypotheses - {'h', 'have', 'hstack'}:
            continue
        consumers = []
        for candidate in (base, base + '_taken', base + '_fallthrough'):
            entry = decls.get(candidate)
            if entry and entry[0].group(2) == static.group(2) and entry[1:3] == (stack, hinput) and entry[3].startswith(pretext + '\n'):
                consumers.append(entry)
        if not consumers:
            continue
        helper_text = ('/- Shared prefix before the static-sensitive operation. -/\n'
                       + 'private def ' + helper + ' ' + static.group(2) + '\n'
                       + stack + '\n' + hinput + ' := by\n' + pretext + '\n  exact ' + cursor + '\n\n')
        first = min(consumers, key=lambda entry: entry[0].start())[0]
        doc = source.rfind('/-- Automatically generated RD summary', 0, first.start())
        if doc < 0 or '\n\n' in source[doc:first.start()]:
            doc = first.start()
        edits.append((doc, doc, helper_text))
        replacement = '  have ' + cursor + ' := ' + helper + ' hstack h'
        for entry in [*consumers, (static, stack, hinput, proof, static_start)]:
            pos = entry[4]
            edits.append((pos, pos + len(pretext), replacement))
        count += 1
    for start, end, replacement in sorted(edits, reverse=True):
        source = source[:start] + replacement + source[end:]
    return source, count


def main():
    total = 0
    for directory in map(Path, sys.argv[1:]):
        for path in sorted(directory.glob('RuntimeBlocks_*.lean')):
            original = path.read_text()
            result, count = share(original)
            if count:
                path.write_text(result)
                total += count
                print(f'{path}: {count} shared static prefixes')
    print('total', total)


if __name__ == '__main__':
    main()
