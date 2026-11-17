#!/usr/bin/env python3
# Finite 3D Chomp on a 2x2 base: heights u=(0,0), v=(0,1), y=(1,0), z=(1,1) (a plane partition).
# Check Huddleston-Shurman PA1 (z = y, all finite: P iff u = v + z + 1, taking v >= y) and
# PB1 (z < y: the P-positions are u = v = y = z+1), with the symmetry v >= y.
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
M = int(sys.argv[1]) if len(sys.argv) > 1 else 14
@lru_cache(None)
def P(u, v, y, z):
    h = {(0,0):u, (0,1):v, (1,0):y, (1,1):z}
    for (i,j), H in h.items():
        for t in range(H):
            if (i,j) == (0,0) and t == 0: continue
            g = dict(h)
            for (a,b) in g:
                if a >= i and b >= j: g[(a,b)] = min(g[(a,b)], t)
            if P(g[(0,0)], g[(0,1)], g[(1,0)], g[(1,1)]): return False
    return True
badA = badB = nA = nB = 0
for u in range(1, M+1):
    for v in range(0, u+1):
        for y in range(0, v+1):          # symmetry: v >= y
            for z in range(0, y+1):
                p = P(u, v, y, z)
                if z == y:
                    nA += 1
                    if p != (u == v + z + 1): badA += 1
                else:
                    nB += 1
                    if p != (u == v == y == z + 1): badB += 1
print("heights <= %d: PA1 %d positions, %d mismatches; PB1 %d positions, %d mismatches" % (M, nA, badA, nB, badB))
