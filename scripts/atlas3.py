#!/usr/bin/env python3
"""Atlas of the positions below 3x3xomega with three or more infinite columns.

Enumerates the plane partitions on the 3x3 base with entries in {0, ..., K, omega}, the poison
column infinite and at least MININF infinite columns, up to transposition, and runs the rod
solver on each. "N exact" means the solver found an exact P option (a finite position or a
certified two-wide stalk). Every other verdict leaves the position open: it is P, or it is N
only through a P option that has three or more infinite columns itself.

usage: atlas3.py RODF K TIMEOUT JOBS [MININF [EXTRA RODF ARGS...]]
       ATLAS_SHAPE=220 restricts the scan to one infinite shape (row lengths, up to transposition).
       Extra arguments are passed to the solver, for example "-A assumed.txt".
output: one line per position, heights in the order (0,0),(0,1),(0,2) | (1,0),... ; w = omega
"""
import os
import itertools
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

CELLS = [(x, y) for x in range(3) for y in range(3)]
W = 10 ** 6


def positions(K, mininf):
    vals = list(range(K + 1)) + [W]
    seen = set()
    for pos in itertools.product(vals, repeat=9):
        if pos[0] != W or sum(1 for v in pos if v == W) < mininf:
            continue
        if any((x < 2 and pos[k + 3] > pos[k]) or (y < 2 and pos[k + 1] > pos[k])
               for k, (x, y) in enumerate(CELLS)):
            continue
        tr = tuple(pos[y * 3 + x] for (x, y) in CELLS)
        key = min(pos, tr)
        if key in seen:
            continue
        seen.add(key)
        yield key


def fmt(pos):
    s = ["w" if v == W else str(v) for v in pos]
    return " | ".join(",".join(s[3 * x:3 * x + 3]) for x in range(3))


def shape(pos):
    """Row lengths of the infinite part, rows y = 0, 1, 2 (as in notes/17)."""
    return tuple(sum(1 for x in range(3) if pos[x * 3 + y] == W) for y in range(3))


def main():
    rodf, K, timeout, jobs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    mininf = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    extra = sys.argv[6:]
    cases = sorted(positions(K, mininf), key=lambda p: (sum(1 for v in p if v == W), p))
    want = os.environ.get("ATLAS_SHAPE")
    if want:
        def tshape(pos):
            return shape(tuple(pos[y * 3 + x] for (x, y) in CELLS))
        cases = [p for p in cases
                 if want in ("".join(map(str, shape(p))), "".join(map(str, tshape(p))))]

    def run(pos):
        cols = [sum(1 for y in range(3) if pos[x * 3 + y] > 0) for x in range(3)]
        cols = [c for c in cols if c > 0]
        hs = ",".join("w" if pos[x * 3 + y] == W else str(pos[x * 3 + y])
                      for x in range(len(cols)) for y in range(cols[x]))
        cmd = [rodf] + extra + ["-p", hs, "".join(map(str, cols))]
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).stdout
            res = [l for l in out.splitlines() if " : " in l]
            return pos, res[-1].split(" : ", 1)[1] if res else "no verdict"
        except subprocess.TimeoutExpired:
            return pos, "timeout"

    with ThreadPoolExecutor(jobs) as ex:
        for pos, res in ex.map(run, cases):
            sh = shape(pos)
            print("%s  shape %s  : %s" % (fmt(pos), "".join(map(str, sh)), res), flush=True)


if __name__ == "__main__":
    main()
