#!/bin/sh
# Compiles each contract whose `*.build.json` names the Fe commit `fe.pin` names, with the `fe`
# of a checkout at that commit, and compares the bytes with the contract's pinned `creation.hex`
# and `runtime.hex`, ignoring a trailing newline.  Fails on any difference, and if no contract
# names that commit: the certificates are about the pinned bytecode, so it must be what the
# pinned compiler makes.
#
# Usage: scripts/check_bytecode.sh <fe checkout>
set -eu
root=$(cd "$(dirname "$0")/.." && pwd -P)
fe=$(cd "$1" && pwd -P)
rev=$(sed -n 's/^rev=//p' "$root/fe.pin")
(cd "$fe" && cargo build --release --locked -p fe)
out=$(mktemp -d)
status=0
checked=0
for json in "$root"/FeProofs/*/*.build.json; do
  dir=$(dirname "$json")
  # shellcheck disable=SC2046 # three words
  set -- $(python3 -c 'import json, sys
c = json.load(open(sys.argv[1]))
print(c["contract"], c["compiler"]["commit"], c["compiler"]["optimize"])' "$json")
  contract=$1 commit=$2 optimize=$3
  case $rev in "$commit"*) ;; *) continue ;; esac
  if [ -f "$dir/fe.toml" ]; then
    set -- "$dir"
  else
    set -- "$dir"/*.fe --standalone
  fi
  "$fe/target/release/fe" build "$@" --contract "$contract" -O "$optimize" \
    --out-dir "$out/$contract" --emit bytecode,runtime-bytecode > /dev/null
  for pair in "$contract.bin creation.hex" "$contract.runtime.bin runtime.hex"; do
    # shellcheck disable=SC2086 # two words
    set -- $pair
    if [ "$(cat "$out/$contract/$1")" != "$(cat "$dir/$2")" ]; then
      echo "error: ${dir#"$root"/}/$2 is not the $1 that Fe $rev compiles."
      status=1
    fi
  done
  checked=$((checked + 1))
done
if [ "$checked" -eq 0 ]; then
  echo "error: no *.build.json names the Fe commit fe.pin names ($rev)."
  exit 1
fi
echo "contracts whose pinned bytecode the pinned Fe compiles: $checked"
exit $status
