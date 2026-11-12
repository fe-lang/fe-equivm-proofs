#!/bin/zsh
# Runs `fe-lean-export` over the Fe test contracts and this repository's, tallies the construct
# each unexported contract stopped at, and elaborates every export with Lean.  Elaborating a
# file also runs its Fe tests in EVMLean and compares each call they make on an exported
# contract with the contract's model (`Fe/EVM/Diff.lean`), and does the same for sequences of
# generated calls on each contract (`Fe/EVM/Generate.lean`).
#
# Usage: scripts/audit_exports.sh <fe checkout> [regex over file paths]
#   NO_LEAN=1 skips elaboration.
# Output goes to a new directory .lake/export-corpus/<time>/, which `latest` then points at:
# one .lean file per Fe file with its .log, `blockers.txt`, `leanfail.txt` and `diff.txt`.
set -u
root=${0:A:h:h}
fe=${1:A}
out=$root/.lake/export-corpus/$(date +%Y%m%d-%H%M%S)
mkdir -p $out
ln -sfn $out $root/.lake/export-corpus/latest
# A directory with an `fe.toml` is an ingot, and is exported as one.
files=$(ls -d $fe/crates/fe/tests/fixtures/fe_test/*.fe $root/FeProofs/*/*.fe $root/FeProofs/*/fe.toml(:h) | grep -E "${2:-.}" | tr '\n' ':' | sed 's/:$//')
# The prelude modules an export may name: the call model too where this checkout has it.
imports="Fe.EVM.Storage Fe.EVM.Calls Fe.EVM.Generate"
(cd $fe && LEAN_EXPORT_CORPUS_OUT=$out LEAN_EXPORT_CORPUS="$files" LEAN_EXPORT_CORPUS_IMPORTS="$imports" \
  cargo test --release -p fe-lean-export --test corpus export_corpus -- --ignored --nocapture \
  2>$out/cargo.err >$out/blockers.txt)
grep "^contracts:" $out/blockers.txt || tail -5 $out/cargo.err
python3 $root/scripts/tally_blockers.py $out/blockers.txt
[[ -n "${NO_LEAN:-}" ]] && exit 0
cd $root
# The tests of some files reach the SHA-256 precompile, which EVMLean implements in C.
scripts/build_ffi.sh > /dev/null || echo "no FFI library: tests that reach SHA-256 or BLAKE2 will not run"
ls $out/*.lean | xargs -n 1 -P 8 scripts/lean_check_one.sh | sort > $out/leanfail.txt
echo "lean failures: $(wc -l < $out/leanfail.txt | tr -d ' ')"
# Without that library, a test that reaches such a precompile ends the interpreter.
while read -r _ name; do
  echo "LEANFAIL $name: $(grep -m1 -o "Could not find native implementation of external declaration '[^']*'" $out/$name.log || echo 'timed out or does not elaborate')"
done < $out/leanfail.txt | head -40
cat $out/*.lean.log | grep -E "^(DIFF|DISAGREE|TEST|GEN) " > $out/diff.txt
python3 $root/scripts/tally_diff.py $out/diff.txt
