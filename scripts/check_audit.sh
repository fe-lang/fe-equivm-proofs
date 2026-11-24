#!/bin/sh
# Prints the axioms each capstone theorem depends on (`scripts/Audit.lean`, on a built project)
# to .lake/audit.txt and compares them with scripts/expected/audit.txt.  Fails on any
# difference: a new or missing capstone, a new axiom, or a changed count of `native_decide`
# facts.  Also fails if a capstone depends on an axiom other than `propext`, `Classical.choice`
# and `Quot.sound`, whatever the expected file says.
#
# Usage: scripts/check_audit.sh
#   BLESS=1 first copies the output to the expected file.
set -eu
cd "$(dirname "$0")/.."
expected=scripts/expected/audit.txt
actual=.lake/audit.txt
mkdir -p .lake
lake --log-level=error lean scripts/Audit.lean > "$actual"
[ -n "${BLESS:-}" ] && cp "$actual" "$expected"
status=0
std='(Classical\.choice|Quot\.sound|propext)'
if grep -vE "^[^ ]+: \[($std(, $std)*)?\] \+ [0-9]+ native_decide\$" "$actual"; then
  echo "error: the capstones above depend on other axioms"
  status=1
fi
if ! diff -u "$expected" "$actual"; then
  echo "error: the axioms of the capstones differ from $expected (- expected, + actual)."
  echo "If the change is intended, rerun with BLESS=1 and commit $expected with it."
  status=1
fi
exit $status
