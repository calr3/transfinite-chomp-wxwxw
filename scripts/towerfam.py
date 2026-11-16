#!/usr/bin/env python3
"""Exact option families of the towers T(b, g) of 3x3xomega (see towers.py).

A tower is N as soon as one option is an exact P-position. Two kinds of options are decided
exactly by the rod solver however large the cut height z is:
  * cut the poison cell (0,0) at z: a finite position;
  * cut the cell that leaves exactly two infinite cells: a two-wide stalk, decided by the
    certified simulation. For b = (0,1) that cell is (2,0) (stalk (0,0),(1,0)); for b = (0,2)
    it is (1,0) (stalk (0,0),(0,1)). The other towers have no such cell.
This script runs those families for z <= ZMAX with `rodf -K cell -Z ZMAX`.

usage: towerfam.py RODF ZMAX TIMEOUT JOBS OUTDIR b0,b1:g[,g...] ...
Each family streams its per-height verdicts to OUTDIR/T<b0><b1>_g<g>_c<cell>.txt, so a run that
is cut short still leaves its partial results. Extra solver flags can be passed in the
environment, e.g. RODF_ARGS="-S 30000".
"""
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

STALK_CELL = {(0, 1): 6, (0, 2): 3}  # cell index x*3+y


def heights(b, g):
    return ",".join(str(g) if (x >= b[0] and y >= b[1]) else "w" for x in range(3) for y in range(3))


def main():
    rodf, zmax, timeout, jobs, outdir = (sys.argv[1], int(sys.argv[2]), float(sys.argv[3]),
                                         int(sys.argv[4]), sys.argv[5])
    os.makedirs(outdir, exist_ok=True)
    extra = os.environ.get("RODF_ARGS", "").split()
    cases = []
    for spec in sys.argv[6:]:
        bs, gs = spec.split(":")
        b = tuple(int(t) for t in bs.split(","))
        for g in gs.split(","):
            for cell in ([0] + ([STALK_CELL[b]] if b in STALK_CELL else [])):
                cases.append((b, int(g), cell))

    def run(c):
        b, g, cell = c
        path = os.path.join(outdir, "T%d%d_g%d_c%d.txt" % (b[0], b[1], g, cell))
        with open(path, "w") as fh:
            try:
                subprocess.run([rodf] + extra + ["-K", str(cell), "-Z", str(zmax), "-v", "1", "-p",
                                                 heights(b, g), "333"], stdout=fh, stderr=subprocess.DEVNULL,
                               timeout=timeout)
            except subprocess.TimeoutExpired:
                fh.write("(timeout)\n")
        lines = [l.strip() for l in open(path) if l.strip()]
        keep = [l for l in lines if ": P" in l or "N?" in l or "family" in l or "timeout" in l]
        if lines and "family" not in lines[-1]:
            keep.append("last decided: " + lines[-1].split("   reply")[0])
        return c, keep

    with ThreadPoolExecutor(jobs) as ex:
        for (b, g, cell), keep in ex.map(run, cases):
            print("T(%s, g=%d), cell (%d,%d):" % (b, g, cell // 3, cell % 3), flush=True)
            for l in keep:
                print("    " + l.split(" : ")[-1], flush=True)


main()
