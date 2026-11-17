#!/usr/bin/env python3
"""Statistics of the 2D side class from `side3row` output: density, the error eps(x) =
tau(x) - x - #(side <= x), discrepancy against (sqrt2 - 1)(x + 1), gaps, and images of tau.
usage: side_analyze.py FILE"""
import sys, math
from collections import Counter
fn = sys.argv[1]
side = []; tau = {}
for l in open(fn):
    p = l.split()
    if p[0] == 'side': side.append(int(p[1]))
    else: tau[int(p[1])] = int(p[2])
X = max(max(side), max(tau))
S = set(side)
r = math.sqrt(2) - 1
cnt = 0; eps = Counter(); disc_min = 1e9; disc_max = -1e9; cnts = [0]*(X+2)
for x in range(X + 1):
    if x in S: cnt += 1
    cnts[x] = cnt
    if x in tau: eps[tau[x] - x - cnt] += 1
    d = cnt - r * (x + 1)
    disc_min = min(disc_min, d); disc_max = max(disc_max, d)
print("X =", X, "side count", len(side), "density %.5f" % (len(side) / (X + 1)))
print("eps = tau(x) - x - #side<=x:", sorted(eps.items()))
print("discrepancy #side<=x - (sqrt2-1)(x+1): min %.3f max %.3f" % (disc_min, disc_max))
# gaps between consecutive side elements
g = Counter(side[i+1] - side[i] for i in range(len(side) - 1))
print("gaps:", sorted(g.items()))
# tau(x) - sqrt2 x
dt = [tau[x] - math.sqrt(2) * x for x in tau]
print("tau(x) - sqrt2*x: min %.3f max %.3f" % (min(dt), max(dt)))
img = set(tau.values())
print("images in side:", len(img & S), "of", len([v for v in img if v <= X]), "(images <= X)")
# is the image set plus something complementary? check which values are neither side, nor non-side-with-tau ... all x <= X are one or the other
# complement structure: values that are images vs not
nonimg_nonside = [v for v in range(1, X+1) if v not in img and v not in S]
print("values <= X neither side nor an image:", len(nonimg_nonside), nonimg_nonside[:20])
