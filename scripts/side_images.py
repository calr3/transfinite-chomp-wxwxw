#!/usr/bin/env python3
"""Compare the counting functions of the 2D side class and of the image set tau(non-side).
usage: side_images.py FILE (side3row output)"""
import sys
from collections import Counter
fn = sys.argv[1]
side = []; tau = {}
for l in open(fn):
    p = l.split()
    if p[0] == 'side': side.append(int(p[1]))
    else: tau[int(p[1])] = int(p[2])
S = set(side); X = max(max(side), max(tau))
img = set(tau.values())
# compare counting functions of the side set and of the image set tau(non-side), up to X
cs = ci = 0; dmin = dmax = 0; worst = None
for v in range(X + 1):
    cs += v in S; ci += v in img
    d = ci - cs
    if d < dmin: dmin = d
    if d > dmax: dmax = d
print("#images<=v - #side<=v over v <= %d: min %d max %d" % (X, dmin, dmax))
# a natural matching: k-th side element with k-th image
imgs = sorted(v for v in img if v <= X)
pairs = list(zip(side, imgs))
print("k-th image - k-th side element:", sorted(Counter(b - a for a, b in pairs).items()))
both = S & img; print("values that are both side and image:", len([v for v in both if v <= X]), "side only:", len([v for v in S if v not in img and v <= X]), "image only:", len([v for v in imgs if v not in S]))
