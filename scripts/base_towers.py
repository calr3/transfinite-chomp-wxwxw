#!/usr/bin/env python3
"""Towers of a rod S x omega, for any Young diagram S (column heights, e.g. 322).

S x omega is P iff it has no finite P cut and every tower T(b, g) is N: the columns above b
cut to height g, the rest infinite. This script runs the rod solver on each tower. A verdict
"N exact" settles the tower; anything else leaves it open.

usage: base_towers.py RODF COLS GMIN GMAX [ALPHA D TIMEOUT JOBS [EXTRA RODF ARGS...]]
       e.g. base_towers.py ./rodf 322 1 8 2 10 300 2 -Q 100
"""
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def cells(cols):
    return [(x, y) for x, c in enumerate(cols) for y in range(c)]


def heights(cols, b, g):
    return ",".join(str(g) if (x >= b[0] and y >= b[1]) else "w" for (x, y) in cells(cols))


def main():
    rodf, colstr, gmin, gmax = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    cols = [int(ch) for ch in colstr]
    a = sys.argv[5] if len(sys.argv) > 5 else "2"
    d = sys.argv[6] if len(sys.argv) > 6 else "10"
    timeout = float(sys.argv[7]) if len(sys.argv) > 7 else 120
    jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 2
    extra = sys.argv[9:]
    cases = [(b, g) for b in cells(cols)[1:] for g in range(gmin, gmax + 1)]

    def run(c):
        b, g = c
        cmd = [rodf, "-a", a, "-d", d] + extra + ["-p", heights(cols, b, g), colstr]
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).stdout
            res = [l for l in out.splitlines() if " : " in l]
            return c, res[-1].split(" : ", 1)[1] if res else "no verdict"
        except subprocess.TimeoutExpired:
            return c, "timeout"

    with ThreadPoolExecutor(jobs) as ex:
        for (b, g), res in ex.map(run, cases):
            print("T(%s, g=%d) = %s : %s" % (b, g, heights(cols, b, g), res), flush=True)


if __name__ == "__main__":
    main()
