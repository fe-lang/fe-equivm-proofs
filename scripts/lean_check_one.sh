#!/bin/sh
# Elaborates one Lean file, writing its output to <file>.log and giving up after five minutes.
# Prints `LEANFAIL <name>` if it does not elaborate.  Run from the project root.
( lake env lean "$1" > "$1.log" 2>&1 ) & pid=$!
( sleep 300; pkill -f "lean $1" ) & watcher=$!
wait $pid || echo "LEANFAIL $(basename "$1")"
kill $watcher 2>/dev/null
