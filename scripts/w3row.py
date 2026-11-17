#!/usr/bin/env python3
"""The closed class of the (0,1) towers: W(R) = the row y = 0 of the 3x3 base infinite (three
omega columns), with a finite 3x2 plane partition R on the cells (x,1), (x,2) above it.

Every option of W(R) is
  * a finite position (cut the poison column (0,0) at h),
  * N outright (cut (1,0): only the poison column stays infinite),
  * a two-wide stalk S(z,R) (cut (2,0) at z), or
  * W(R') with R' reached from R by one move inside R.
Let U = { R : no finite cut and no two-wide cut of W(R) is P }. Then W(R) is P iff R is in U and
W(R') is N for every R' one move below R. So if U is empty, every W(R) is N, and so is every
tower T((0,1),g) = W(g-box); a P tower needs its g-box in U.

For every R with entries <= M this script searches both exact families of W(R) (finite cuts up to
height HMAX, two-wide cuts up to height ZMAX) for a P option, and prints the R with none found:
the candidates for U.

usage: w3row.py RODF M HMAX ZMAX TIMEOUT JOBS OUTDIR
"""
import itertools
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def plane_partitions(m):
    # cells (x,y), x = 0..2, y = 1..2; non-increasing in x and in y
    for a in itertools.product(range(m + 1), repeat=6):
        r = {(x, y): a[2 * x + (y - 1)] for x in range(3) for y in (1, 2)}
        if all(r[(x, 1)] >= r[(x, 2)] for x in range(3)) and \
           all(r[(x, y)] >= r[(x + 1, y)] for x in range(2) for y in (1, 2)):
            yield r


def pos(r):
    return ",".join("w" if y == 0 else str(r[(x, y)]) for x in range(3) for y in range(3))


def name(r):
    return "%d%d.%d%d.%d%d" % tuple(r[(x, y)] for x in range(3) for y in (1, 2))


def main():
    rodf, m, hmax, zmax, timeout, jobs, outdir = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                                  int(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]),
                                                  sys.argv[7])
    os.makedirs(outdir, exist_ok=True)
    rs = list(plane_partitions(m))

    def fam(r, cell, top):
        path = os.path.join(outdir, "W%s_c%d.txt" % (name(r), cell))
        with open(path, "w") as fh:
            try:
                subprocess.run([rodf, "-K", str(cell), "-Z", str(top), "-v", "1", "-p", pos(r), "333"],
                               stdout=fh, stderr=subprocess.DEVNULL, timeout=timeout)
            except subprocess.TimeoutExpired:
                fh.write("(timeout)\n")
        lines = [l.strip() for l in open(path) if l.strip()]
        ps = [l for l in lines if l.endswith(": P")]
        last = [l for l in lines if l.startswith("cut")]
        return (ps[0].split(" at ")[1].split(":")[0] if ps else None,
                last[-1].split(" at ")[1].split(":")[0] if last else "-",
                any("timeout" in l for l in lines))

    def run(r):
        z = fam(r, 6, zmax)
        h = fam(r, 0, hmax) if z[0] is None else (None, "-", False)
        return r, z, h

    with ThreadPoolExecutor(jobs) as ex:
        for r, z, h in ex.map(run, rs):
            if z[0] is not None:
                print("%s  two-wide P at z = %s" % (name(r), z[0]), flush=True)
            elif h[0] is not None:
                print("%s  finite P at h = %s" % (name(r), h[0]), flush=True)
            else:
                print("%s  NONE FOUND (two-wide z <= %s%s, finite h <= %s%s)" %
                      (name(r), z[1], " timeout" if z[2] else "", h[1], " timeout" if h[2] else ""), flush=True)


main()
