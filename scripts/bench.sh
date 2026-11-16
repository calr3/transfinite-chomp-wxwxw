#!/bin/sh
# Benchmark a solver on the hard positions from Ideas 1-3.
# usage: bench.sh SOLVER "FLAGS" TIMEOUT_SECONDS
SOLVER=$1; FLAGS=$2; T=$3
run() {
  name=$1; gens=$2
  out=$(timeout $((T + 30)) $SOLVER $FLAGS solve "$gens" 2>/dev/null | head -1)
  [ -z "$out" ] && out="(killed at $T s)"
  printf "%-28s %s\n" "$name" "$out"
}
run "omega x L(1,1)"          "0,1,1" &
run "slab3: floor+wall3"      "0,0,3 0,1,1" &
run "slab3: (0,1,2) option"   "0,0,3 0,1,2" &
run "slab3: (0,2,2) option"   "0,0,3 0,2,2" &
wait
run "L(1,2) x 3"              "0,0,3 1,2,0" &
run "L(2,2) x 3"              "0,0,3 2,2,0" &
run "3x3 x omega"             "3,0,0 0,3,0" &
run "U option B(1,2)"         "1,1,1 0,1,2" &
wait
run "U (after (1,1,1))"       "1,1,1" &
run "omega x omega x 3"       "0,0,3" &
run "omega^3"                 "" &
wait
