#!/usr/bin/env python3
"""Is the 2D side class a Beatty/Sturmian sequence? Compares s_n - (1+sqrt2)n and
tau(x) - sqrt2 x with the phase frac(n sqrt2): a Sturmian rule would make the within-bin spread
small. usage: side_beatty.py FILE"""
import sys, math
fn = sys.argv[1]
side = []; tau = {}
for l in open(fn):
    p = l.split()
    if p[0] == 'side': side.append(int(p[1]))
    else: tau[int(p[1])] = int(p[2])
r2 = math.sqrt(2)
# side elements s_n (n = 0,1,...) against (1+sqrt2) n
dev = [s - (1 + r2) * n for n, s in enumerate(side)]
print("s_n - (1+sqrt2)n: min %.3f max %.3f" % (min(dev), max(dev)))
B = 50
def binstats(keys, vals, name):
    bins = [[] for _ in range(B)]
    for k, v in zip(keys, vals): bins[min(B - 1, int(k * B))].append(v)
    spread = [max(b) - min(b) for b in bins if b]
    print("%s: mean within-bin spread %.3f, max %.3f (total spread %.3f)" % (name, sum(spread) / len(spread), max(spread), max(vals) - min(vals)))
binstats([(n * r2) % 1 for n in range(len(side))], dev, "s_n dev vs frac(n sqrt2)")
binstats([(n * (1 + r2)) % 1 for n in range(len(side))], dev, "s_n dev vs frac(n(1+sqrt2))")
xs = sorted(tau); dt = [tau[x] - r2 * x for x in xs]
binstats([(x * r2) % 1 for x in xs], dt, "tau(x)-sqrt2 x vs frac(x sqrt2)")
# exact integer offsets
from collections import Counter
print("tau(x) - floor(sqrt2 x):", sorted(Counter(tau[x] - math.floor(r2 * x) for x in xs).items()))
print("s_n - floor((1+sqrt2) n):", sorted(Counter(s - math.floor((1 + r2) * n) for n, s in enumerate(side)).items()))
