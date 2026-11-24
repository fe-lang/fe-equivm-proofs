#!/bin/sh
# Runs `fe-lean-export` over the Fe test contracts and this repository's, tallies the construct
# each unexported contract stopped at, and elaborates every export with Lean.  Elaborating a
# file also runs its Fe tests in EVMLean and compares each call they make on an exported
# contract with the contract's model (`Fe/EVM/Diff.lean`), and does the same for sequences of
# generated calls on each contract (`Fe/EVM/Generate.lean`).  Each comparison also runs fe-spec's
# interpreter (`../fe-spec-evm`) on the contract's IR, which the exporter's corpus driver writes
# next to each file, and compares it with the model and the bytecode (`Fe/EVM/SpecHost.lean`).
#
# Usage: scripts/audit_exports.sh <fe checkout> [regex over file paths]
#   NO_LEAN=1 skips elaboration.  AUDIT_JOBS sets how many files elaborate at once (default:
#   the number of CPUs), LEAN_TIMEOUT the seconds each may take (default 600).  Cargo builds in
#   the Fe checkout's target directory unless CARGO_TARGET_DIR names another.
# Output goes to a new directory .lake/export-corpus/<time>/, which `latest` then points at:
# one .lean file per Fe file with its .log, `blockers.txt`, `leanfail.txt` and `diff.txt`.
set -u
root=$(cd "$(dirname "$0")/.." && pwd -P)
fe=$(cd "$1" && pwd -P)
out=$root/.lake/export-corpus/$(date +%Y%m%d-%H%M%S)
mkdir -p "$out"
ln -sfn "$out" "$root/.lake/export-corpus/latest"
# A directory with an `fe.toml` is an ingot, and is exported as one.  Each group is sorted
# bytewise, so that the order does not depend on the locale or on where the checkouts are.
files=$( {
  ls -d "$fe"/crates/fe/tests/fixtures/fe_test/*.fe | LC_ALL=C sort
  ls -d "$root"/FeProofs/*/*.fe | LC_ALL=C sort
  for toml in "$root"/FeProofs/*/fe.toml; do dirname "$toml"; done | LC_ALL=C sort
} | grep -E "${2:-.}" | tr '\n' ':' | sed 's/:$//')
# The prelude modules an export may name: the call model too where this checkout has it.
imports="Fe.EVM.Storage Fe.EVM.Calls Fe.EVM.Generate"
(cd "$fe" && LEAN_EXPORT_CORPUS_OUT=$out LEAN_EXPORT_CORPUS="$files" LEAN_EXPORT_CORPUS_IMPORTS="$imports" \
  cargo test --release -p fe-lean-export --test corpus export_corpus -- --ignored --nocapture \
  2>"$out/cargo.err" >"$out/blockers.txt")
grep "^contracts:" "$out/blockers.txt" || tail -5 "$out/cargo.err"
python3 "$root/scripts/tally_blockers.py" "$out/blockers.txt"
[ -n "${NO_LEAN:-}" ] && exit 0
cd "$root" || exit 1
# EVMLean's ECRECOVER runs `python3 Ethereum/EllipticCurvesPy/recover.py` in the working
# directory, this one: that script runs the program `ecrecover`, which recovers keys by the
# exported model of fevm's secp256k1 code (`FeProofs/Precompiles/Secp256k1/Main.lean`).
# shellcheck disable=SC2086 # one module per word
lake build $imports ecrecover > "$out/lake.log" 2>&1 || { tail -20 "$out/lake.log"; exit 1; }
# The tests of some files reach the SHA-256 precompile, which EVMLean implements in C.
scripts/build_ffi.sh > /dev/null || echo "no FFI library: tests that reach SHA-256 or BLAKE2 will not run"
ls "$out"/*.lean | xargs -n 1 -P "${AUDIT_JOBS:-$(getconf _NPROCESSORS_ONLN)}" scripts/lean_check_one.sh \
  | LC_ALL=C sort > "$out/leanfail.txt"
echo "lean failures: $(wc -l < "$out/leanfail.txt" | tr -d ' ')"
# Without that library, a test that reaches such a precompile ends the interpreter.
while read -r _ name; do
  echo "LEANFAIL $name: $(grep -m1 -o "Could not find native implementation of external declaration '[^']*'" "$out/$name.log" || echo 'timed out or does not elaborate')"
done < "$out/leanfail.txt" | head -40
ls "$out"/*.lean.log | LC_ALL=C sort | xargs cat | grep -E "^(DIFF|DISAGREE|DIFF3|SPEC|NOIR|TEST|GEN) " > "$out/diff.txt"
python3 "$root/scripts/tally_diff.py" "$out/diff.txt"
