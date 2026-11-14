#!/usr/bin/env python3
"""Copy `fe-lean-export` golden output into the `Exported.lean` files.

Usage: scripts/sync_exported.py <fe checkout>

Each `Exported.lean`, and each file of an `Exported/` directory (an ingot's exports: one file for
the definitions its contracts share, one for each contract), holds the exporter's output between a
`-- BEGIN fe-lean-export: <name>` line and the next `-- END fe-lean-export` line.  `<name>` is the
golden file `crates/lean-export/tests/golden/<name>.lean` of the Fe checkout, or that file itself
when `<name>` has an extension: `<name>.checks` has a check of each constant the compiler folded.
`lib` is the core and std definitions the contracts and fixtures share; every other golden file
starts with the `export` of the ones it names, from a namespace `Lib`, and a contract's of an
ingot with the `export` of the shared definitions it names, from a namespace `Shared`.

A `FeProofs/<dir>/<name>.trust` file is the golden file of that name, the trust ledger of
`<name>`: its unsafe code, raw accesses, externs, external calls and unexported constants.

A changed export can rename what a proof names: build after syncing.
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
golden = pathlib.Path(sys.argv[1]) / "crates/lean-export/tests/golden"
block = re.compile(r"(-- BEGIN fe-lean-export: ([\w.]+)\n).*?(-- END fe-lean-export\n)", re.S)


def source(name):
    return (golden / (name if "." in name else f"{name}.lean")).read_text()


exported = [*root.glob("FeProofs/*/Exported.lean"), *root.glob("FeProofs/*/Exported/*.lean")]
for path in sorted(exported):
    text = path.read_text()
    synced = block.sub(lambda m: m[1] + "\n" + source(m[2]) + m[3], text)
    if synced != text:
        path.write_text(synced)
        print(f"updated {path.relative_to(root)}")

for path in sorted(root.glob("FeProofs/*/*.trust")):
    synced = source(path.name)
    if synced != path.read_text():
        path.write_text(synced)
        print(f"updated {path.relative_to(root)}")
