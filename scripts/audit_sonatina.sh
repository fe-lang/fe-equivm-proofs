#!/bin/zsh
# Compares the Sonatina IR of every contract of Fe's test fixtures and of this repository with the
# bytecode compiled from it (`Fe/Sonatina/Diff.lean`): Fe emits the sidecar of each contract
# (`fe build --emit sidecar`, from the corpus test `sonatina_corpus` of `fe-lean-export`), and
# Lean runs the IR as the contract's model on the calls each file's Fe tests make and on
# sequences of generated calls.
#
# Usage: scripts/audit_sonatina.sh <fe checkout with the sidecar emitter> [regex over file paths]
# Output goes to a new directory .lake/sonatina-corpus/<time>/, which `latest` then points at:
# per Fe file its sidecars, a .lean file and its .log, then `leanfail.txt`, `unsupported.txt`
# and `diff.txt`.
set -u
root=${0:A:h:h}
fe=${1:A}
out=$root/.lake/sonatina-corpus/$(date +%Y%m%d-%H%M%S)
mkdir -p $out
ln -sfn $out $root/.lake/sonatina-corpus/latest
files=$(ls -d $fe/crates/fe/tests/fixtures/fe_test/*.fe $root/FeProofs/*/*.fe $root/FeProofs/*/fe.toml(:h) | grep -E "${2:-.}" | tr '\n' ':' | sed 's/:$//')
(cd $fe && SONATINA_CORPUS_OUT=$out SONATINA_CORPUS="$files" \
  cargo test --release -p fe-lean-export --test corpus sonatina_corpus -- --ignored --nocapture \
  2>$out/cargo.err >$out/corpus.txt)
grep "^files skipped" $out/corpus.txt || tail -5 $out/cargo.err
cd $root
lake build Fe.Sonatina.Diff > /dev/null || exit 1
scripts/build_ffi.sh > /dev/null || echo "no FFI library: tests that reach SHA-256 or BLAKE2 will not run"
ls $out/*.lean | xargs -n 1 -P 8 scripts/lean_check_one.sh | sort > $out/leanfail.txt
echo "lean failures: $(wc -l < $out/leanfail.txt | tr -d ' ')"
cat $out/*.lean.log | grep "^UNSUPPORTED " > $out/unsupported.txt
echo "contracts whose IR is not read: $(wc -l < $out/unsupported.txt | tr -d ' ')"
sed -E 's/^UNSUPPORTED [^:]+::[^:]+: //' $out/unsupported.txt | sed -E 's/ v[0-9].*//' | sort | uniq -c | sort -rn | head -20
cat $out/*.lean.log | grep -E "^(DIFF|DISAGREE|TEST|GEN) " > $out/diff.txt
python3 $root/scripts/tally_diff.py $out/diff.txt
