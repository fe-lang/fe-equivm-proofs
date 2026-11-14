#!/bin/sh
# Checks out the Fe compiler at the commit `fe.pin` names, in <dir> (default .lake/fe), and
# prints the directory.  A checkout already there is moved to that commit.
#
# Usage: scripts/fetch_fe.sh [dir]
set -eu
root=$(cd "$(dirname "$0")/.." && pwd -P)
dir=${1:-$root/.lake/fe}
url=$(sed -n 's/^url=//p' "$root/fe.pin")
rev=$(sed -n 's/^rev=//p' "$root/fe.pin")
[ -d "$dir/.git" ] || git init -q "$dir"
if [ "$(git -C "$dir" rev-parse -q --verify HEAD || true)" != "$rev" ]; then
  git -C "$dir" fetch -q --depth 1 "$url" "$rev"
  git -C "$dir" -c advice.detachedHead=false checkout -q --detach "$rev"
fi
echo "$dir"
