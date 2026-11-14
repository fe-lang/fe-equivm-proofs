#!/bin/sh
# Elaborates one Lean file, writing its output to <file>.log and giving up after LEAN_TIMEOUT
# seconds (default ten minutes).  Prints `LEANFAIL <name>` if it does not elaborate.  Run from
# the project root.  With the library `scripts/build_ffi.sh` builds, `#eval` can run the
# precompiles EVMLean implements in C.
ffi=$(ls .lake/ffi/libfeffi.* 2> /dev/null | head -1)
( lake env lean ${ffi:+--load-dynlib=$ffi} "$1" > "$1.log" 2>&1 ) & pid=$!
# `lake env` runs `lean` as a child, so the watcher kills by command line, not by pid.
( sleep "${LEAN_TIMEOUT:-600}"; pkill -f "lean ${ffi:+--load-dynlib=$ffi }$1" ) > /dev/null 2>&1 & watcher=$!
wait $pid || echo "LEANFAIL $(basename "$1")"
kill $watcher 2>/dev/null
