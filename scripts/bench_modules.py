#!/usr/bin/env python3
"""Recheck Lean modules with built imports, recording wall time and kernel profiles.

Run `lake build` first. Redirect JSON output to a file outside the source tree:
  python3 scripts/bench_modules.py --repeat 3 FeProofs.ERC20.Selectors

Every sample starts a fresh Lean process and checks the source even if its own
olean is current. Imported oleans are reused. Times include Lake startup and
imports; they are not clean-build timings. Include a new shared module in the
module list when comparing the total cost of checking shared facts and users.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent,
                        help="checkout to benchmark (default: this script's project)")
    parser.add_argument("modules", nargs="+", help="Lean module names, in dependency order")
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")

    root = args.root.resolve()
    files = [root / (name.replace(".", "/") + ".lean") for name in args.modules]
    for path in files:
        if not path.is_relative_to(root) or not path.is_file():
            parser.error(f"module source not found: {path}")

    def output(command):
        return subprocess.check_output(command, cwd=root, text=True).strip()

    result = {
        "revision": output(["git", "rev-parse", "HEAD"]),
        "tracked_changes": output(["git", "diff", "--name-only", "HEAD"]).splitlines(),
        "lean": output(["lake", "env", "lean", "--version"]),
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
        "manifest_sha256": hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest(),
        "keccak_sha256": hashlib.sha256(
            (root / ".lake/packages/evmlean/Ethereum/SpongeHash/Keccak256.lean").read_bytes()
        ).hexdigest(),
        "modules": [],
    }
    for name, path in zip(args.modules, files):
        command = ["lake", "env", "lean", "-Dprofiler=true", "-Dprofiler.threshold=100",
                   str(path.relative_to(root))]
        samples = []
        for run in range(args.repeat):
            print(f"{name}: check {run + 1}/{args.repeat}", file=sys.stderr, flush=True)
            start = time.perf_counter()
            check = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT)
            samples.append({"seconds": time.perf_counter() - start,
                            "exit_code": check.returncode, "profile": check.stdout})
            if check.returncode:
                print(check.stdout, file=sys.stderr)
                result["failed"] = {"module": name, "samples": samples}
                print(json.dumps(result, indent=2))
                return check.returncode
        result["modules"].append({
            "name": name,
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "command": command,
            "median_seconds": statistics.median(s["seconds"] for s in samples),
            "samples": samples,
        })
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
