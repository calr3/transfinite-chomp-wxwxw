#!/usr/bin/env python3
"""Decide (heuristically) the L-prisms L(a,b) x c = N^3 minus up((0,0,c)) and up((a,b,0)).

If L(a,b) x c is P, then {(0,0,c), (a,b,0)} is a "P-pair": each of these first moves on
omega^3 is answered by the other, so both lose. Each prism has two infinite arms with finite
cross-sections (b x c along x, a x c along y) and no infinite slab.

usage: lprisms.py CHOMP3F MAXA MAXB C [ALPHA D TIMEOUT JOBS]
"""
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def main():
    binary, maxa, maxb, c = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    alpha = sys.argv[5] if len(sys.argv) > 5 else "1"
    d = sys.argv[6] if len(sys.argv) > 6 else "2"
    timeout = float(sys.argv[7]) if len(sys.argv) > 7 else 300
    jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 4
    cases = [(a, b) for a in range(1, maxa + 1) for b in range(a, maxb + 1)]

    def run(ab):
        a, b = ab
        arg = "0,0,%d %d,%d,0" % (c, a, b)
        try:
            out = subprocess.run([binary, "-a", alpha, "-d", d, "-g", "1", "why", arg, "1"],
                                 capture_output=True, text=True, timeout=timeout).stdout.strip().splitlines()
        except subprocess.TimeoutExpired:
            return ab, "timeout", ""
        status = out[0].rsplit(":", 1)[1].strip() if out else "?"
        reply = ""
        if len(out) >= 3 and "move" in out[1]:
            reply = out[1].strip().replace("move ", "") + " " + out[2].strip()
        return ab, status, reply

    with ThreadPoolExecutor(jobs) as ex:
        for (a, b), status, reply in ex.map(run, cases):
            print("L(%d,%d) x %d   %-8s %s" % (a, b, c, status, reply), flush=True)


main()
