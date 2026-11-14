"""ECDSARECOVER for EVMLean, by the exported model of fevm's secp256k1 code.

An EVMLean whose ECRECOVER (`Ethereum/EllipticCurves.lean`) runs in Python runs
`python3 Ethereum/EllipticCurvesPy/recover.py e v r s` in the working directory, which is this
repository's root when the export audit elaborates a file; the EVMLean this repository pins
computes it in Lean.  This file stands in for EVMLean's
script of that name, which needs the package `coincurve`: it prints what the program
`.lake/build/bin/ecrecover` (`FeProofs/Precompiles/Secp256k1/Main.lean`, built by `lake build ecrecover`)
prints, the key as 128 hex digits or `error`.  The program's diagnostics are shown only when it
fails: on every start, EVMLean's module initializers report precompiles they cannot run.
"""
import pathlib
import subprocess
import sys

program = pathlib.Path(__file__).resolve().parents[2] / ".lake/build/bin/ecrecover"
result = subprocess.run([str(program), *sys.argv[1:]], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, text=True)
if result.returncode != 0:
    sys.stderr.write(result.stderr)
    sys.exit(result.returncode)
print(result.stdout, end="")
