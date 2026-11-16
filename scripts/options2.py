#!/usr/bin/env python3
"""Probe every option of a position with the hybrid df-pn solver (chomp3p with the rod oracle).

For each move m up to a coordinate bound (children equal up to a coordinate permutation are run
once), run `chomp3p why` on the child with a time limit and report N/P/unknown, exactness, and
for N the winning reply and the position it leads to.

usage: options2.py CHOMP3P "gens" BOUND [ALPHA D TIMEOUT JOBS]
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
    d = sys.argv[5] if len(sys.argv) > 5 else "2"
    timeout = float(sys.argv[6]) if len(sys.argv) > 6 else 120
    jobs = int(sys.argv[7]) if len(sys.argv) > 7 else 4
    gens = [tuple(map(int, t.split(","))) for t in gstr.split()] if gstr.strip() else []
    seen = {}
    for m in itertools.product(range(bound + 1), repeat=3):
        if m == (0, 0, 0) or any(leq(g, m) for g in gens):
            continue
        child = minimal(gens + [m])
        seen.setdefault(canon(child), []).append(m)

    def run(item):
        c, moves = item
        arg = " ".join("%d,%d,%d" % g for g in c)
        try:
            out = subprocess.run([binary, "-a", alpha, "-d", d, "-g", "1", "-t", str(timeout), "why", arg],
                                 capture_output=True, text=True, timeout=timeout + 60).stdout.strip().splitlines()
        except subprocess.TimeoutExpired:
            return moves, arg, "killed", ""
        if not out:
            return moves, arg, "?", ""
        head = out[0].split(" : ", 1)[1].split("[")[0].strip()
        reply = ""
        if len(out) >= 2 and out[1].strip().startswith("move"):
            reply = out[1].strip()[5:]
        return moves, arg, head, reply

    with ThreadPoolExecutor(jobs) as ex:
        for moves, arg, status, reply in ex.map(run, sorted(seen.items())):
            print("move %-10s child %-26s %-12s %s" % ("(%d,%d,%d)" % moves[0], arg, status, reply), flush=True)


main()
