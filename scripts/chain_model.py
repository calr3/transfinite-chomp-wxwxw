#!/usr/bin/env python3
"""The pool model for the end of a chain, computed exactly.

usage: chain_model.py DELTA EPS [K0] [HMAX]

State: the size k of the pool (K0 at height 1, default 1). At every row:
  with probability 1 - DELTA^k the row finds a partner, nothing changes;
  with probability DELTA^k it finds none; then the chain ends with probability EPS (the
  diagonal cell is eligible), and otherwise the pool grows by one.
The script iterates the distribution of k over the chains still alive and prints, at
heights 10, 20, 40, ...: the probability S(h) to be alive, h^gamma * S(h) for
gamma = ln(1/(1-EPS)) / ln(1/DELTA), and the local exponent between successive heights.

What is proved about the model (notes/28): h^gamma * S(h) stays between two positive
constants. So the chain ends with probability 1, and its expected length is infinite when
gamma <= 1.
"""
import math
import sys

delta, eps = float(sys.argv[1]), float(sys.argv[2])
k0 = int(sys.argv[3]) if len(sys.argv) > 3 else 1
hmax = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 6
gamma = math.log(1 / (1 - eps)) / math.log(1 / delta)
K = k0 + int(math.log(hmax) / math.log(1 / delta)) + 25
dk = [delta ** k for k in range(K + 1)]
p = [0.0] * (K + 1)
p[k0] = 1.0
print("delta = %g, eps = %g, start pool %d: gamma = %.4f" % (delta, eps, k0, gamma))
print("%9s  %12s  %14s  %s" % ("h", "S(h)", "h^gamma S(h)", "local exponent"))
marks, h = [], 10
while h <= hmax:
    marks.append(h)
    h *= 2
prev = None
t = 1
for m in marks:
    while t < m:
        q = [0.0] * (K + 1)
        for k in range(K):
            if p[k]:
                q[k] += p[k] * (1 - dk[k])
                q[k + 1] += p[k] * dk[k] * (1 - eps)
        p = q
        t += 1
    S = sum(p)
    loc = "" if prev is None else "%.3f" % (math.log(prev / S) / math.log(2))
    print("%9d  %12.6g  %14.4f  %s" % (m, S, m ** gamma * S, loc))
    prev = S
