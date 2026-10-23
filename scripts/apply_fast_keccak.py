#!/usr/bin/env python3
"""Apply the isolated, proved Keccak optimization to the pinned EVMLean checkout.

Run after Lake has downloaded dependencies and before `lake build`. The public
dependency pins stay unchanged. See docs/proof-performance.md for provenance.
"""

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys


PIN = "fd4f5e6d6d6b4a18eb73f5a71ae2df909ac2b542"
EXPECTED = {
    "Ethereum/SpongeHash/Keccak256.lean":
        "dcab497155672a9ca90d5dfacf58e9f331232e35f0cd7daa77232eff349134c6",
    "Ethereum/SpongeHash/Keccak256Tests.lean":
        "6c16db4ea0f05fa4d6f843a0a3c3b275d0d777e3c90fe28ce1df3b9683dd6e9b",
}


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    root = Path(__file__).resolve().parent.parent
    dependency = root / ".lake/packages/evmlean"
    patch = root / "patches/evmlean-fast-keccak.patch"
    if not dependency.is_dir():
        sys.exit("EVMLean checkout missing. Run `lake env true` first.")

    def git(*args):
        return subprocess.check_output(["git", "-C", str(dependency), *args], text=True).strip()

    if git("rev-parse", "HEAD") != PIN:
        sys.exit(f"Expected EVMLean {PIN}; refusing to patch another revision.")
    changed = set(git("diff", "--name-only", "HEAD").splitlines())

    def matches():
        return all((dependency / name).is_file() and
                   hashlib.sha256((dependency / name).read_bytes()).hexdigest() == digest
                   for name, digest in EXPECTED.items())

    if matches() and changed == set(EXPECTED):
        print("Fast Keccak patch already applied and verified.")
        return
    if changed:
        sys.exit("EVMLean has tracked changes; refusing to overwrite them.")
    git("apply", "--check", str(patch))
    git("apply", str(patch))
    if not matches() or set(git("diff", "--name-only", "HEAD").splitlines()) != set(EXPECTED):
        sys.exit("Patch verification failed; inspect the EVMLean checkout before building.")
    print("Applied and verified the two-file Keccak backport. Run `lake build`.")


if __name__ == "__main__":
    main()
