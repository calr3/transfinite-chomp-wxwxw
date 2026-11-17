#!/usr/bin/env python3
"""Check Huddleston-Shurman's two-column Grundy formulas (9-1)-(9-5) (tools/hs_oracle.G2) as a
mex recursion, locally, on random positions (h, k), h >= k, heights < omega^(MAXDEG+1).

G(h,k) = mex of the values of the options (t, min(k,t)) for t < h and (h, t) for t < k (the
empty position has value 0). For each position:
  (1) no option may have the value G(h,k);
  (2) every ordinal w < G(h,k) with small coefficients (<= WC, finite part <= WF) must be the
      value of some option. Options are enumerated as in hs_check2 (coefficients <= B1, finite
      parts <= B0).
(9-1), the finite case, is checked by brute force separately.

usage: hs_check_two.py [SAMPLES] [MAXDEG] [SEED]
"""
import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_oracle as H  # noqa: E402


def cands(h, B1, B0):
    terms = H.key(h)
    for idx, (k, hk) in enumerate(terms):
        prefix = dict(terms[:idx])
        lows = list(range(k - 1, 0, -1))
        for c in range(hk):
            base = dict(prefix)
            if c:
                base[k] = c
            if k == 0:
                yield base
                continue
            for cs in itertools.product(range(B1 + 1), repeat=len(lows)):
                mid = dict(base)
                for e, cc in zip(lows, cs):
                    if cc:
                        mid[e] = cc
                for f in range(B0 + 1):
                    t = dict(mid)
                    if f:
                        t[0] = f
                    yield t


def below(g, WC, WF):
    """ordinals w < g with coefficients <= WC (exponents >= 1) and finite part <= WF"""
    d = max(H.deg(g), 0)
    for cs in itertools.product(range(WC + 1), repeat=d):
        for f in range(WF + 1):
            w = {e: c for e, c in zip(range(d, 0, -1), cs) if c}
            if f:
                w[0] = f
            if H.cmp(w, g) < 0:
                yield w


def rand_ord(maxdeg, rng):
    return {e: rng.randint(1, 3 if e else 10) for e in range(maxdeg, -1, -1) if rng.random() < 0.6}


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    maxdeg = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
    B1, B0, WC, WF = (8, 400, 3, 40) if maxdeg <= 2 else (6, 60, 2, 12)
    bad1 = bad2 = ok = 0
    t0 = time.time()
    for _ in range(samples):
        h, k = sorted([rand_ord(maxdeg, rng), rand_ord(maxdeg, rng)], key=H.key, reverse=True)
        if rng.random() < 0.35:  # equal leading parts: the cases (9-2) and (9-4)
            k = {e: c for e, c in h.items() if e > 0}
            if rng.random() < 0.7:
                k[0] = rng.randint(0, 10)
                k = {e: c for e, c in k.items() if c}
            if H.cmp(k, h) > 0:
                h, k = k, h
        if not h:
            continue
        g = H.G2(h, k)
        vals = set()
        for t in cands(h, B1, B0):
            vals.add(H.key(H.G2(t, t if H.cmp(k, t) > 0 else k)))
        for t in cands(k, B1, B0) if k else []:
            vals.add(H.key(H.G2(h, t)))
        if H.key(g) in vals:
            bad1 += 1
            print("OPTION WITH EQUAL VALUE:", H.show(h), H.show(k), "G =", H.show(g), flush=True)
            continue
        miss = [w for w in below(g, WC, WF) if H.key(w) not in vals]
        if miss:
            bad2 += 1
            print("MISSING VALUE:", H.show(h), H.show(k), "G =", H.show(g), "e.g.", H.show(miss[0]), flush=True)
        else:
            ok += 1
    print("two-column positions: %d consistent, %d with an option of equal value, %d with a missing smaller value; %.0fs"
          % (ok, bad1, bad2, time.time() - t0))


if __name__ == "__main__":
    main()
