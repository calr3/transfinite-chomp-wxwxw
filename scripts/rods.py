#!/usr/bin/env python3
"""Classify S x omega for small Young diagrams S (finite cross-sections, one infinite axis).

S x omega is a P-position iff the Huddleston-Shurman P-height h(S) equals omega.
Each S is given by its column heights c_0 >= c_1 >= ... > 0 (S and its transpose give the
same game, so only one of each pair is run). Runs the rodf solver with two cap settings and
reports whether the answers agree.

usage: rods.py RODF_BINARY MAX_CELLS [TIMEOUT_SECONDS] [MIN_CELLS]
"""
import subprocess
import sys


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def gens(cols):
    """Minimal eaten cells of N^2 x N for S x omega, S given by column heights."""
    g = [(0, cols[0], 0)]
    for x in range(1, len(cols)):
        if cols[x] < cols[x - 1]:
            g.append((x, cols[x], 0))
    g.append((len(cols), 0, 0))
    return " ".join("%d,%d,%d" % p for p in g)


def run(binary, cols, a, d, timeout):
    try:
        out = subprocess.run([binary, "-a", str(a), "-d", str(d), "".join(map(str, cols))],
                             capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return "timeout", ""
    w = out.split(":")[1].split()
    move = ""
    if "winning move:" in out:
        move = out.split("winning move:")[1].split("[")[0].strip()
    return w[0] + ("" if w[1] == "exact" else "?"), move


def main():
    binary, maxcells = sys.argv[1], int(sys.argv[2])
    timeout = float(sys.argv[3]) if len(sys.argv) > 3 else 120
    mincells = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    seen = set()
    for n in range(mincells, maxcells + 1):
        for cols in partitions(n):
            # transpose; S and its transpose give the same game
            t = tuple(sum(1 for c in cols if c > i) for i in range(cols[0]))
            if t in seen:
                continue
            seen.add(cols)
            if max(cols) > 9:
                continue
            r1, m1 = run(binary, cols, 2, 6, timeout)
            r2, m2 = run(binary, cols, 3, 10, timeout)
            flag = "" if r1 == r2 else "   <-- cap-dependent"
            print("%-10s n=%-2d  a2d6: %-8s a3d10: %-8s %s%s" % ("".join(map(str, cols)), n, r1, r2, m2 or m1,
                                                              flag), flush=True)


main()
