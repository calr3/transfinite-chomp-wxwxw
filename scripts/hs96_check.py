#!/usr/bin/env python3
"""Check Huddleston-Shurman's two-column formula (9-6) as a mex recursion, on random positions
with heights below (omega^omega)^J.

An ordinal below (omega^omega)^J is a list of J digits d[0], ..., d[J-1], each an ordinal below
omega^omega (a dict as in tools/hs_oracle.py); its value is the sum of Omega^j * d[j] with
Omega = omega^omega. With j the top digit of h, write h = Omega^j*u + a and k = Omega^j*v + b.
The formula (notes/21) is

    G(h,k) = Omega^j * G(u,v) + (G(a,b) if u = v else a nim-sum b),

with G(u,v) from (9-1)-(9-5). For each sampled position the script checks that
  (1) no option has the value G(h,k);
  (2) every ordinal w < G(h,k) on a grid of small coefficients is the value of some option.
Options are (t,t) for t <= k, t < h; (t,k) for k < t < h; (h,t) for t < k, with t on a larger
grid. The digits have degree at most 1 to keep the grids small.

usage: hs96_check.py [SAMPLES] [J] [SEED]      (J = 2 or 3)
"""
import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_oracle as H  # noqa: E402


def okey(x):
    return tuple(H.key(d) for d in reversed(x))


def ocmp(x, y):
    for dx, dy in zip(reversed(x), reversed(y)):
        c = H.cmp(dx, dy)
        if c:
            return c
    return 0


def top(x):
    for j in range(len(x) - 1, -1, -1):
        if x[j]:
            return j
    return -1


def G(h, k):
    """two-column value by (9-1)-(9-6); h >= k, both lists of J digits"""
    J = len(h)
    j = top(h)
    if j <= 0:
        return [H.G2(h[0], k[0])] + [{}] * (J - 1)
    u, v = h[j], k[j]
    a = h[:j] + [{}] * (J - j)
    b = k[:j] + [{}] * (J - j)
    if H.cmp(u, v) == 0:
        lowpart = G(a, b)
    else:
        lowpart = [H.nim(x, y) for x, y in zip(a, b)]
    res = lowpart[:j] + [H.G2(u, v)] + [{}] * (J - j - 1)
    return res


def digits_below(d, B1, B0):
    """ordinals below the digit d (degree <= 1), coefficient of omega <= B1 unless forced,
    finite part <= B0 unless forced"""
    c1, c0 = d.get(1, 0), d.get(0, 0)
    for f in range(c0):
        yield H.O((1, c1), (0, f))
    for c in range(c1):
        for f in range(B0 + 1):
            yield H.O((1, c), (0, f))


def grid(B1, B0):
    return [H.O((1, c), (0, f)) for c in range(B1 + 1) for f in range(B0 + 1)]


def lowgrid_for(L1, L0, WC, WF):
    """digits for the part of an option below the changed digit. A value omega*c + n on the
    diagonal needs a height omega^2*c + ..., so some digits of degree 2 are included."""
    return grid(L1, L0) + [H.O((2, c2), (1, c1), (0, f))
                           for c2 in range(1, WC + 1) for c1 in range(3) for f in range(WF + 3)]


def below(h, B1, B0, lowgrid):
    """ordinals t < h: equal to h above some digit, smaller at that digit, on a grid below"""
    J = len(h)
    for j in range(J - 1, -1, -1):
        for d in digits_below(h[j], B1, B0):
            for lows in itertools.product(lowgrid, repeat=j):
                yield list(lows) + [d] + h[j + 1:]


def rand_digit(rng, c1max, c0max):
    return H.O((1, rng.randint(0, c1max) if rng.random() < 0.7 else 0),
               (0, rng.randint(0, c0max) if rng.random() < 0.7 else 0))


def show(x):
    parts = []
    for j in range(len(x) - 1, -1, -1):
        if x[j]:
            parts.append(("W^%d*(%s)" % (j, H.show(x[j]))) if j else H.show(x[j]))
    return " + ".join(parts) if parts else "0"


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    J = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 11)
    if J == 2:
        C1, C0, B1, B0, L1, L0, WC, WF = 3, 9, 7, 30, 7, 30, 2, 6
    else:
        C1, C0, B1, B0, L1, L0, WC, WF = 2, 5, 4, 8, 4, 8, 1, 3
    wgrid = grid(WC, WF)
    lowgrid = lowgrid_for(L1, L0, WC, WF)
    ok = bad1 = bad2 = 0
    t0 = time.time()
    for _ in range(samples):
        h = [rand_digit(rng, C1, C0) for _ in range(J)]
        k = [rand_digit(rng, C1, C0) for _ in range(J)]
        mode = rng.random()
        if mode < 0.4:      # equal top digits: the case u = v
            k[J - 1] = dict(h[J - 1])
        if mode < 0.15:     # equal in the two top digits
            k[J - 2] = dict(h[J - 2])
        if ocmp(h, k) < 0:
            h, k = k, h
        if top(h) < 1:
            continue
        g = G(h, k)
        vals = set()
        for t in below(h, B1, B0, lowgrid):
            if ocmp(t, k) <= 0:
                vals.add(okey(G(t, t)))
            else:
                vals.add(okey(G(t, k)))
        for t in below(k, B1, B0, lowgrid):
            vals.add(okey(G(h, t)))
        if okey(g) in vals:
            bad1 += 1
            print("OPTION WITH EQUAL VALUE:", show(h), "|", show(k), "G =", show(g), flush=True)
            continue
        miss = None
        for w in itertools.product(wgrid, repeat=J):
            w = list(w)
            if ocmp(w, g) < 0 and okey(w) not in vals:
                miss = w
                break
        if miss is not None:
            bad2 += 1
            print("MISSING VALUE:", show(h), "|", show(k), "G =", show(g), "e.g.", show(miss), flush=True)
        else:
            ok += 1
    print("J = %d: %d positions consistent, %d with an option of equal value, %d with a missing smaller value; %.0fs"
          % (J, ok, bad1, bad2, time.time() - t0))
    return 0 if bad1 == 0 and bad2 == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
