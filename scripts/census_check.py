#!/usr/bin/env python3
"""Check the census pass of tools/base3_table.cpp (-T) against a direct computation.

usage: census_check.py BASE3_TABLE H CAPS Z

Runs the tool with -P (all finite P-positions) and -T Z -O, then recomputes the census labels
from the definition, with no shortcuts: a position with an infinite column besides the poison
column is labelled P iff no cut of the poison column at a height <= H is P and no option is
labelled P, where infinite columns are cut at heights <= Z only.
"""
import subprocess
import sys
import tempfile
import os
from functools import lru_cache

tool, H, caps, Z = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
INF = 10 ** 6
CX = [0, 0, 1, 1, 1, 2, 2, 2]
CY = [1, 2, 0, 1, 2, 0, 1, 2]
cap9 = [H if t in "Hh" else min(H, int(t)) for t in caps.split(",")]
capxy = [[cap9[3 * x + y] for y in range(3)] for x in range(3)]
capxy[0][0] = H
for x in range(3):
    for y in range(3):
        if x > 0:
            capxy[x][y] = min(capxy[x][y], capxy[x - 1][y])
        if y > 0:
            capxy[x][y] = min(capxy[x][y], capxy[x][y - 1])
free = [capxy[CX[k]][CY[k]] == H for k in range(8)]
capk = [capxy[CX[k]][CY[k]] for k in range(8)]

d = tempfile.mkdtemp()
out = subprocess.run([tool, str(H), "-c", caps, "-P", d + "/fin.txt", "-T", str(Z), "-O", d + "/c"],
                     capture_output=True, text=True)
if out.returncode:
    sys.exit("tool failed: " + out.stderr)
finP = set()
for line in open(d + "/fin.txt"):
    a, p, q, u, v, w, dd, e, f = map(int, line.split())
    finP.add((a, p, q, u, v, w, dd, e, f))
toolP = set()
for line in open(d + "/c_P.txt"):
    if line.startswith("#"):
        continue
    t = line.replace("|", " ").split()
    toolP.add(tuple(INF if x == "w" else int(x) for x in t[1:]))


def bite(s, c, t):
    return tuple(min(s[k], t) if CX[k] >= CX[c] and CY[k] >= CY[c] else s[k] for k in range(8))


@lru_cache(maxsize=None)
def isP(s):
    if INF not in s:
        return False
    for a in range(1, H + 1):
        if (a,) + tuple(min(x, a) for x in s) in finP:
            return False
    for c in range(8):
        top = Z if s[c] == INF else s[c] - 1
        for t in range(top, -1, -1):
            if isP(bite(s, c, t)):
                return False
    return True


def states():
    def rec(k, s):
        if k == 8:
            yield tuple(s)
            return
        vals = list(range(0, (Z if free[k] else capk[k]) + 1)) + ([INF] if free[k] else [])
        for v in vals:
            ok = True
            for j in range(k):
                if CX[j] <= CX[k] and CY[j] <= CY[k] and s[j] < v:
                    ok = False
                if CX[j] >= CX[k] and CY[j] >= CY[k] and s[j] > v:
                    ok = False
            if ok:
                yield from rec(k + 1, s + [v])
    yield from rec(0, [])


sys.setrecursionlimit(100000)
mine = set()
n = 0
for s in sorted(states(), key=lambda s: sum(min(x, Z + 1) for x in s)):
    n += 1
    if isP(s):
        mine.add(s)
print("H=%d caps=%s Z=%d: %d positions, %d labelled P by the definition, %d by the tool: %s"
      % (H, caps, Z, n, len(mine), len(toolP), "identical" if mine == toolP else "DIFFERENT"))
if mine != toolP:
    print("  only definition:", sorted(mine - toolP)[:5])
    print("  only tool:", sorted(toolP - mine)[:5])
    sys.exit(1)
for f in os.listdir(d):
    os.remove(os.path.join(d, f))
os.rmdir(d)
