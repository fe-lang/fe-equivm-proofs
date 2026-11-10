#!/bin/zsh
# Runs `fe-lean-export` over the Fe test contracts and this repository's, tallies the construct
# each unexported contract stopped at, and elaborates every export with Lean.
#
# Usage: scripts/audit_exports.sh <fe checkout> [regex over file paths]
#   NO_LEAN=1 skips elaboration.
# Output goes to a new directory .lake/export-corpus/<time>/, which `latest` then points at:
# one .lean file per exported contract with its .log, `blockers.txt` and `leanfail.txt`.
set -u
root=${0:A:h:h}
fe=${1:A}
out=$root/.lake/export-corpus/$(date +%Y%m%d-%H%M%S)
mkdir -p $out
ln -sfn $out $root/.lake/export-corpus/latest
files=$(ls $fe/crates/fe/tests/fixtures/fe_test/*.fe $root/FeProofs/*/*.fe | grep -E "${2:-.}" | tr '\n' ':' | sed 's/:$//')
(cd $fe && LEAN_EXPORT_CORPUS_OUT=$out LEAN_EXPORT_CORPUS="$files" \
  cargo test --release -p fe-lean-export --test corpus export_corpus -- --ignored --nocapture \
  2>$out/cargo.err >$out/blockers.txt)
grep "^contracts:" $out/blockers.txt || tail -5 $out/cargo.err
python3 $root/scripts/tally_blockers.py $out/blockers.txt
[[ -n "${NO_LEAN:-}" ]] && exit 0
cd $root
ls $out/*.lean | xargs -n 1 -P 8 scripts/lean_check_one.sh | sort > $out/leanfail.txt
echo "lean failures: $(wc -l < $out/leanfail.txt | tr -d ' ')"
head -40 $out/leanfail.txt
