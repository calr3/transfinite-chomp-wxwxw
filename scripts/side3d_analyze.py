#!/usr/bin/env python3
"""The law tau(z) - z - #side ~ const for the 3D side sets, from `rodf -I 2 -K 6 -v 1` output.
usage: side3d_analyze.py FILE..."""
import sys, re, math
from collections import Counter
# parse "rodf -I 2 -K 6 -v 1" output: side elements "z", others "[z:h]"
for fn in sys.argv[1:]:
    txt = open(fn).read().split(':', 1)[1] if ':' in open(fn).read() else ''
    body = open(fn).read()
    body = body[body.index(']:') + 2:] if ']:' in body else body
    side = []; tau = {}
    for tok in body.split():
        m = re.match(r'\[(\d+):(\d+)\]', tok)
        if m: tau[int(m.group(1))] = int(m.group(2))
        elif tok.isdigit(): side.append(int(tok))
    allz = sorted(side + list(tau)); lo, hi = allz[0], allz[-1]
    S = set(side); cnt = 0; eps = Counter(); ratios = []
    for z in range(lo, hi + 1):
        if z in S: cnt += 1
        if z in tau:
            eps[tau[z] - z - cnt] += 1
            ratios.append(tau[z] / z)
    print("%s: z in [%d,%d], side %d (density %.3f), tau(z)/z last 10 avg %.3f" % (fn.split('/')[-1], lo, hi, len(side), len(side) / (hi - lo + 1), sum(ratios[-10:]) / 10))
    print("   tau(z) - z - #side in [lo,z]:", sorted(eps.items()))
    print("   tau pairs (last 8):", [(z, tau[z]) for z in sorted(tau)[-8:]])
