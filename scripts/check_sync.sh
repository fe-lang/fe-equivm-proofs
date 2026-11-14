#!/bin/sh
# Runs the exporter's golden test in a Fe checkout, then copies its golden files into the
# `Exported.lean` and `.trust` files (`scripts/sync_exported.py`).  Fails if the test fails or
# the copy changes a file, and shows the change: each file must hold that exporter's output.
#
# Usage: scripts/check_sync.sh <fe checkout>
set -eu
root=$(cd "$(dirname "$0")/.." && pwd -P)
fe=$(cd "$1" && pwd -P)
(cd "$fe" && cargo test --release --locked -p fe-lean-export --test golden)
before=$(mktemp -d)
(cd "$root" && tar -cf - FeProofs/*/Exported.lean FeProofs/*/Exported/*.lean FeProofs/*/*.trust) | tar -xf - -C "$before"
updated=$(python3 "$root/scripts/sync_exported.py" "$fe")
[ -z "$updated" ] && exit 0
for path in $(echo "$updated" | sed 's/^updated //'); do
  diff -u "$before/$path" "$root/$path" || true
done
echo "error: sync_exported.py changed the files above (- before, + after), so they do not hold"
echo "the golden output of the exporter at $fe."
echo "Commit the synced files and fix the proofs they break, or pin the Fe commit they come from."
exit 1
