#!/bin/sh
# Runs the export audit (`scripts/audit_exports.sh`) on a Fe checkout and compares its results
# with scripts/expected/exports.txt: the totals, the constructs the exporter stopped at, the
# files that do not elaborate, then every differential-test line of each file, files in
# bytewise order.  Fails on any difference.  The results are in summary.txt of the audit's
# output directory, .lake/export-corpus/latest/.
#
# Usage: scripts/check_corpus.sh <fe checkout>
#   BLESS=1 first copies the results to the expected file.  EXPECTED names another expected
#   file: scripts/expected/exports3.txt holds the three-way audit's, with fe-spec at
#   ../fe-spec-evm and a Fe checkout whose exporter serializes the IR (README, "Differential
#   tests").
set -eu
root=$(cd "$(dirname "$0")/.." && pwd -P)
expected=${EXPECTED:-$root/scripts/expected/exports.txt}
"$root/scripts/audit_exports.sh" "$1"
out=$root/.lake/export-corpus/latest
{
  grep "^contracts:" "$out/blockers.txt" || echo "contracts: the exporter did not finish"
  python3 "$root/scripts/tally_blockers.py" "$out/blockers.txt"
  echo "lean failures: $(wc -l < "$out/leanfail.txt" | tr -d ' ')"
  cat "$out/leanfail.txt"
  python3 "$root/scripts/tally_diff.py" "$out/diff.txt" | sed -n 1,3p
  echo
  cat "$out/diff.txt"
} > "$out/summary.txt"
[ -n "${BLESS:-}" ] && cp "$out/summary.txt" "$expected"
if ! diff -u "$expected" "$out/summary.txt"; then
  echo "error: the export audit differs from $expected (- expected, + actual)."
  echo "Its output is in $(cd "$out" && pwd -P)."
  echo "If the change is intended, rerun with BLESS=1 and commit the expected file with it."
  exit 1
fi
