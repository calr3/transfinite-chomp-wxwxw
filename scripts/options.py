#!/usr/bin/env python3
"""Probe every option of a position separately: for each move m (up to a coordinate bound),
run `chomp3f why` on the child with a time limit and report N/P, the winning reply, and
whether the answer is exact. Runs several children in parallel.

usage: options.py CHOMP3F "gens" BOUND [ALPHA D TIMEOUT JOBS GLOBAL]
   gens:  the position as minimal eaten cells, e.g. "0,0,3"   (empty string = N^3)
   BOUND: try moves with every coordinate <= BOUND
Children equal up to a coordinate permutation are run once.
"""
import itertools
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def leq(a, b):
    return all(x <= y for x, y in zip(a, b))


def minimal(gs):
    gs = sorted(set(gs))
    return [g for g in gs if not any(h != g and leq(h, g) for h in gs)]


def canon(gs):
    best = None
    for p in itertools.permutations(range(3)):
        c = tuple(sorted(tuple(g[i] for i in p) for g in gs))
        if best is None or c < best:
            best = c
    return best


def main():
    binary, gstr, bound = sys.argv[1], sys.argv[2], int(sys.argv[3])
    alpha = sys.argv[4] if len(sys.argv) > 4 else "1"
    d = sys.argv[5] if len(sys.argv) > 5 else "3"
    timeout = float(sys.argv[6]) if len(sys.argv) > 6 else 120
    jobs = int(sys.argv[7]) if len(sys.argv) > 7 else 4
    glob = sys.argv[8] if len(sys.argv) > 8 else "1"
    gens = [tuple(map(int, t.split(","))) for t in gstr.split()] if gstr.strip() else []
    seen = {}
    for m in itertools.product(range(bound + 1), repeat=3):
        if m == (0, 0, 0) or any(leq(g, m) for g in gens):
            continue
        child = minimal(gens + [m])
        c = canon(child)
        seen.setdefault(c, []).append(m)

    def run(item):
        c, moves = item
        arg = " ".join("%d,%d,%d" % g for g in c)
        try:
            out = subprocess.run([binary, "-a", alpha, "-d", d, "-g", glob, "why", arg, "1"], capture_output=True,
                                 text=True, timeout=timeout).stdout.strip().splitlines()
        except subprocess.TimeoutExpired:
            return moves, arg, "timeout", ""
        status = out[0].rsplit(":", 1)[1].strip() if out else "?"
        reply = ""
        if len(out) >= 3 and "move" in out[1]:
            reply = out[1].strip().replace("move ", "") + " " + out[2].strip()
        return moves, arg, status, reply

    with ThreadPoolExecutor(jobs) as ex:
        for moves, arg, status, reply in ex.map(run, sorted(seen.items())):
            print("move %-10s child %-28s %-8s %s" % (",".join("(%d,%d,%d)" % m for m in moves[:1]), arg,
                                                     status, reply), flush=True)


main()
