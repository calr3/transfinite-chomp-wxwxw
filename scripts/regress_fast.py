#!/usr/bin/env python3
"""Regression for the fast certificate: on random two-wide stalks in 3x3, run the new solver in
check mode (-F 2: every member simulated both ways, abort on any difference) and compare its
verdict with a solver from before the fast path."""
import random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
NEW, OLD, seed, hmax, n, jobs = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
random.seed(seed)
def rand_pos():
    h = [[0]*3 for _ in range(3)]
    for x in range(3):
        for y in range(3):
            lim = hmax
            if x > 0: lim = min(lim, h[x-1][y])
            if y > 0: lim = min(lim, h[x][y-1])
            h[x][y] = random.randint(max(0, lim - 3), lim)
    h[0][0] = 99
    if random.random() < 0.5: h[1][0] = 99
    else: h[0][1] = 99
    # re-impose monotonicity below the omega cells is automatic; finite cells already monotone
    return ",".join("w" if h[x][y] == 99 else str(h[x][y]) for x in range(3) for y in range(3))
poss = [rand_pos() for _ in range(n)]
def run(p):
    a = subprocess.run([NEW, "-F", "2", "-p", p, "333"], capture_output=True, text=True, timeout=3000)
    b = subprocess.run([OLD, "-p", p, "333"], capture_output=True, text=True, timeout=3000)
    va = a.stdout.split(":")[1].split()[:2] if a.stdout else ["ERR", str(a.returncode)]
    vb = b.stdout.split(":")[1].split()[:2] if b.stdout else ["ERR", str(b.returncode)]
    return p, va, vb, a.returncode
bad = 0
with ThreadPoolExecutor(jobs) as ex:
    for p, va, vb, rc in ex.map(run, poss):
        ok = va == vb and rc == 0
        bad += not ok
        print(("ok  " if ok else "BAD ") + p, va, vb, rc, flush=True)
print("mismatches:", bad, "of", n)
