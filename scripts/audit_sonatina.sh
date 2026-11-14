#!/bin/zsh
# Compares the Sonatina IR of every contract of Fe's test fixtures and of this repository with the
# bytecode compiled from it (`Fe/Sonatina/Diff.lean`): Fe emits the sidecar of each contract
# (`fe build --emit sidecar`, from the corpus test `sonatina_corpus` of `fe-lean-export`), and
# Lean runs the IR as the contract's model on the calls each file's Fe tests make and on
# sequences of generated calls.
#
# Usage: scripts/audit_sonatina.sh <fe checkout with the sidecar emitter> [regex over file paths]
#   SONATINA_LEVELS="post-opt source machine" runs each IR level in turn; post-opt by default.
# Output goes to a new directory .lake/sonatina-corpus/<time>/, which `latest` then points at:
# per Fe file its sidecars and a .lean file, and per level a directory of the .lean files and
# their logs, `leanfail.txt`, `unsupported.txt` and `diff.txt`.
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
# Each level runs the same files, from its own directory: the IR after optimization, the section
# IR after the backend's pipeline, or the machine IR (`SONATINA_LEVEL`, `Fe/Sonatina/Diff.lean`).
for level in ${=SONATINA_LEVELS:-post-opt}; do
  echo "== $level"
  dir=$out/$level
  mkdir -p $dir
  cp $out/*.lean $dir/
  ls $dir/*.lean | SONATINA_LEVEL=$level xargs -n 1 -P 8 scripts/lean_check_one.sh | sort \
    > $dir/leanfail.txt
  echo "lean failures: $(wc -l < $dir/leanfail.txt | tr -d ' ')"
  cat $dir/*.lean.log | grep "^UNSUPPORTED " > $dir/unsupported.txt
  echo "contracts whose IR is not read: $(wc -l < $dir/unsupported.txt | tr -d ' ')"
  sed -E 's/^UNSUPPORTED [^:]+::[^:]+: //' $dir/unsupported.txt | sed -E 's/ v[0-9].*//' \
    | sort | uniq -c | sort -rn | head -20
  cat $dir/*.lean.log | grep -E "^(DIFF|DISAGREE|TEST|GEN) " > $dir/diff.txt
  python3 $root/scripts/tally_diff.py $dir/diff.txt
done
