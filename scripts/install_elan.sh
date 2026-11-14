#!/bin/sh
# Installs elan, the Lean toolchain manager, on x86-64 Linux, with no default toolchain: `lake`
# then installs the toolchain `lean-toolchain` names.  For CI; elsewhere, see
# https://github.com/leanprover/elan.  Under GitHub Actions, adds ~/.elan/bin to the PATH of
# later steps.
set -eu
version=v4.2.2
sha256=40ec208731c4696ac80982ca29e7ad4c2c7c4fe410964d0131c581dd3240de79
[ "$(uname -s)-$(uname -m)" = Linux-x86_64 ] || { echo "install elan by hand on this platform" >&2; exit 1; }
tmp=$(mktemp -d)
curl -sSfL -o "$tmp/elan.tar.gz" \
  "https://github.com/leanprover/elan/releases/download/$version/elan-x86_64-unknown-linux-gnu.tar.gz"
echo "$sha256  $tmp/elan.tar.gz" | sha256sum -c -
tar -xzf "$tmp/elan.tar.gz" -C "$tmp"
"$tmp/elan-init" -y --no-modify-path --default-toolchain none
[ -n "${GITHUB_PATH:-}" ] && echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
"$HOME/.elan/bin/elan" --version
