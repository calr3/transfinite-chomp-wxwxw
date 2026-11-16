#!/usr/bin/env python3
"""For each option m = (a,b,c) of the slab omega x omega x n, look for a reply that leaves a rod
(one unbounded axis) and is a P-position, decided by the rod solver.

Reply (j,0,0) leaves the rod along y with cross-section x < j, z < n; the column (x,z) has height
b if x >= a and z >= c, and omega otherwise. Reply (0,j,0) is the same along x with (y,z) and a.
At most one j works in each orientation (antichain lemma), so j = 1..JMAX is searched.

usage: rodreplies.py RODF N AMAX BMAX JMAX [TIMEOUT] [detail]
  detail: also print the status of every rod reply (N = exact, N? = heuristic, timeout)
"""
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def rod_query(binary, j, n, a, b, c, timeout):
    # cross-section: j columns (x or y), each with n cells (z); heights along the other axis
    cols = str(n) * j
    hs = []
    for x in range(j):
        for z in range(n):
            hs.append(str(b) if (x >= a and z >= c) else "w")
    if hs[0] != "w" and b == 0:
        return "skip"
    try:
        out = subprocess.run([binary, "-p", ",".join(hs), cols], capture_output=True, text=True,
                             timeout=timeout).stdout.strip()
    except subprocess.TimeoutExpired:
        return "timeout"
    w = out.split(" : ")[1].split()
    return w[0] + ("" if w[1].startswith("exact") else "?")


def main():
    binary, n, amax, bmax, jmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    timeout = float(sys.argv[6]) if len(sys.argv) > 6 else 60
    opts = [(a, b, c) for c in range(n) for a in range(amax + 1) for b in range(a, bmax + 1)
            if not (a == 0 and b == 0) and not (a == 0 and c == 0)]

    detail = len(sys.argv) > 7 and sys.argv[7] == "detail"

    def run(m):
        a, b, c = m
        found = []
        stats = []
        for j in range(1, jmax + 1):
            # reply (j,0,0): rod along y; columns x < j with height b where x >= a and z >= c
            r = rod_query(binary, j, n, a, b, c, timeout)
            if r.startswith("P"):
                found.append("(%d,0,0)->%s" % (j, r))
            # reply (0,j,0): rod along x; columns y < j with height a where y >= b and z >= c
            r2 = rod_query(binary, j, n, b, a, c, timeout)
            if r2.startswith("P"):
                found.append("(0,%d,0)->%s" % (j, r2))
            stats += [r, r2]
        if detail:
            found.append("[" + " ".join(stats) + "]")
        return m, found

    with ThreadPoolExecutor(4) as ex:
        for (a, b, c), found in ex.map(run, opts):
            print("option (%d,%d,%d): %s" % (a, b, c, ", ".join(found) if found else "no rod reply found"),
                  flush=True)


main()
