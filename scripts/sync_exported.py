#!/usr/bin/env python3
"""Copy `fe-lean-export` golden output into the `Exported.lean` files.

Usage: scripts/sync_exported.py <fe checkout>

Each target file holds the exporter's output between a `-- BEGIN fe-lean-export: <name>` line
and the next `-- END fe-lean-export` line.  `<name>` is the golden file
`crates/lean-export/tests/golden/<name>.lean` of the Fe checkout.  `lib` is the core and std
definitions the contracts and fixtures share; every other golden file starts with the `export`
of the ones it names, from a namespace `Lib`.

A changed export can rename what a proof names: build after syncing.
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
golden = pathlib.Path(sys.argv[1]) / "crates/lean-export/tests/golden"
block = re.compile(r"(-- BEGIN fe-lean-export: (\w+)\n).*?(-- END fe-lean-export\n)", re.S)

for path in sorted(root.glob("FeProofs/*/Exported.lean")):
    text = path.read_text()
    synced = block.sub(
        lambda m: m[1] + "\n" + (golden / f"{m[2]}.lean").read_text() + m[3], text
    )
    if synced != text:
        path.write_text(synced)
        print(f"updated {path.relative_to(root)}")
