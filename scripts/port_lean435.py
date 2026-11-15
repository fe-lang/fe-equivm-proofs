#!/usr/bin/env python3
"""Rename what Lean 4.35, Mathlib v4.35.0 and Batteries deprecate or move, in the proofs.

usage: scripts/port_lean435.py [file ...]   (default: every tracked .lean file)

- `if_pos`, `if_neg`, `if_true`, `if_false`, `dif_pos`, `dif_neg` become `ite_eq_left`,
  `ite_eq_right`, `ite_true`, `ite_false`, `dite_eq_left`, `dite_eq_right`;
- Batteries' `RBMap`, `RBSet` and `RBNode` move from namespace `Batteries` to `RBTree`
  (`Batteries.Recycling.RBTree`), and `import Batteries.Data.RBMap` becomes that module.

The exporter's output, between `-- BEGIN fe-lean-export` and `-- END fe-lean-export`, is left
alone: it changes only by `scripts/sync_exported.py`. Generated block summaries
(`*Blocks_NNN.lean`) are left alone too: they change only by regenerating them. Idempotent, so it
can be rerun on merged files.
"""
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parent.parent
ITE = {'if_pos': 'ite_eq_left', 'if_neg': 'ite_eq_right', 'if_true': 'ite_true',
       'if_false': 'ite_false', 'dif_pos': 'dite_eq_left', 'dif_neg': 'dite_eq_right'}
ite = re.compile(r"(?<![\w.'])(" + '|'.join(ITE) + r")\b")
rb = re.compile(r'\bBatteries\.(RBMap|RBSet|RBNode)\b')
block = re.compile(r'(-- BEGIN fe-lean-export: [\w.]+\n.*?-- END fe-lean-export\n)', re.S)


def port(text):
    text = ite.sub(lambda m: ITE[m[1]], text)
    text = rb.sub(r'RBTree.\1', text)
    text = text.replace('import Batteries.Data.RBMap.Lemmas', 'import Batteries.Recycling.RBTree.Lemmas')
    text = text.replace('import Batteries.Data.RBMap', 'import Batteries.Recycling.RBTree')
    return re.sub(r'open Batteries \((RB[^)]*)\)', r'open RBTree (\1)', text)


files = sys.argv[1:] or subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=root, text=True).split()
for name in files:
    path = root / name
    if re.search(r'Blocks_\d+\.lean$', name):
        continue
    text = path.read_text()
    parts = block.split(text)
    new = ''.join(p if block.fullmatch(p) else port(p) for p in parts)
    if new != text:
        path.write_text(new)
        print(f'ported {name}')
