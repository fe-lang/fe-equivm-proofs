#!/bin/sh
# Elaborates one Lean file, writing its output to <file>.log and giving up after LEAN_TIMEOUT
# seconds (default half an hour: with fe-spec's interpreter the slowest files take more than ten
# minutes).  Prints `LEANFAIL <name>` if it does not elaborate.  Run from the project root.
# With the library `scripts/build_ffi.sh` builds, `#eval` can run the precompiles EVMLean
# implements in C.
#
# `lake lean` hands `lean` the location of each imported module: the `Fe` modules of this
# package and of fe-spec share the root `Fe`, which a search path (`lake env lean`) cannot split.
ffi=$(ls .lake/ffi/libfeffi.* 2> /dev/null | head -1)
( lake --log-level=error lean "$1" -- ${ffi:+--load-dynlib=$ffi} > "$1.log" 2>&1 ) & pid=$!
# `lake lean` runs `lean` as a child, so the watcher kills by command line, not by pid.
( sleep "${LEAN_TIMEOUT:-1800}"; pkill -f "lean $1" ) > /dev/null 2>&1 & watcher=$!
wait $pid || echo "LEANFAIL $(basename "$1")"
kill $watcher 2>/dev/null
