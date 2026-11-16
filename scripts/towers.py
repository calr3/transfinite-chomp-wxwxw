#!/usr/bin/env python3
"""Gale's question: is 3x3xomega a first-player win?  It is iff some option ("tower")
T(b, g) is a P-position: the 3x3 base with the columns in up(b) cut to height g and the rest
infinite (b != (0,0)). Up to transposition, b in {(0,1),(0,2),(1,1),(1,2),(2,2)}.
For each tower, run the rod solver; exact N eliminates it for good.

usage: towers.py RODF GMAX [ALPHA D TIMEOUT JOBS]
"""
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def heights(b, g):
    hs = []
    for x in range(3):
        for y in range(3):
            hs.append(str(g) if (x >= b[0] and y >= b[1]) else "w")
    return ",".join(hs)


def main():
    rodf, gmax = sys.argv[1], int(sys.argv[2])
    a = sys.argv[3] if len(sys.argv) > 3 else "2"
    d = sys.argv[4] if len(sys.argv) > 4 else "10"
    timeout = float(sys.argv[5]) if len(sys.argv) > 5 else 120
    jobs = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    cases = [(b, g) for b in [(0, 1), (0, 2), (1, 1), (1, 2), (2, 2)] for g in range(1, gmax + 1)]

    def run(c):
        b, g = c
        try:
            out = subprocess.run([rodf, "-a", a, "-d", d, "-p", heights(b, g), "333"], capture_output=True,
                                 text=True, timeout=timeout).stdout.strip()
            return c, out.split(" : ")[1]
        except subprocess.TimeoutExpired:
            return c, "timeout"

    with ThreadPoolExecutor(jobs) as ex:
        for (b, g), res in ex.map(run, cases):
            print("T(%s, g=%d): %s" % (b, g, res), flush=True)


main()
