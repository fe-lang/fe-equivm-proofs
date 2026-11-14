#!/bin/sh
# Fetches Mathlib's prebuilt files and builds the given targets (default: the whole project).
# The build fails on any error.
#
# Usage: scripts/check_build.sh [target...]
set -eu
cd "$(dirname "$0")/.."
lake exe cache get
lake build "$@"
