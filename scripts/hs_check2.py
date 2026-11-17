#!/usr/bin/env python3
"""A deeper local-consistency check of Huddleston-Shurman's three-column P-criterion
(tools/hs_oracle.py: Side-Top Theorem and criterion (10-1)).

The criterion is correct (by induction on the ordinal) iff
  (a) no position it calls P has an option it calls P, and
  (b) every position it calls N has an option it calls P.
hs_check.py sampled options with tiny coefficients and left 83 of ~400 N-positions without a
P option found. Here the options of column j at height h are enumerated systematically:
  t = (terms of h above exponent k) + w^k * c + L,   c < h_k,  L < w^k,
with L's coefficients bounded by B1 (exponents >= 1) and B0 (finite part). Every ordinal
t < h has exactly one such form, so the search is complete up to those bounds.

The side class comes from data/side-class/side2d_x_le_50000.txt.gz (exact: tau(x) <= 2x+1).

usage: hs_check2.py [SAMPLES] [MAXDEG] [SEED] [B1] [B0]
"""
import gzip
import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_oracle as H  # noqa: E402

# ---- exact side class from the stored table ----
SIDE = set()
TAU = {}
with gzip.open(os.path.join(HERE, "..", "data", "side-class", "side2d_x_le_50000.txt.gz"), "rt") as fh:
    for line in fh:
        w = line.split()
        if w[0] == "side":
            SIDE.add(int(w[1]))
        elif w[0] == "tau":
            TAU[int(w[1])] = int(w[2])
SIDE_MAX = 50000
SIDE_LIST = sorted(SIDE)
SIDE_INDEX = {x: i for i, x in enumerate(SIDE_LIST)}


def in_side_class(x):
    if x > SIDE_MAX:
        raise RuntimeError("side class beyond table: %d" % x)
    return x in SIDE


def G_side(x):
    return SIDE_INDEX[x]


H.in_side_class = in_side_class
H.G_side = G_side


# ---- finite three-column positions via the first-row table A(b,c) ----
class Finite3:
    """A[c][b] = the unique a >= max(b,1) with [a,b,c] P, or -1 (rows b <= BMAX, c <= CMAX)."""

    def __init__(self, BMAX, CMAX):
        self.BMAX, self.CMAX = BMAX, CMAX
        A = [[-1] * (BMAX + 1) for _ in range(CMAX + 1)]
        for c in range(CMAX + 1):
            tau = None  # the b > c with [b,b,c] P, once found
            for b in range(c, BMAX + 1):
                if tau is not None:
                    break  # every [a,b,c] with b > tau(c) has the P option [tau,tau,c]
                blocked = set()
                for c2 in range(c):
                    blocked.add(A[c2][b])
                for b2 in range(b):
                    blocked.add(A[min(c, b2)][b2] if b2 >= c else A[b2][b2])
                a = max(b, 1)
                while a in blocked:
                    a += 1
                A[c][b] = a
                if a == b and b > c:
                    tau = b
        self.A = A

    def P(self, u, v, x):
        if u == v == x and u >= 1:
            return False  # rectangles are N (strategy stealing)
        if u == v and x < v and x <= SIDE_MAX:
            return TAU.get(x) == u  # [t,t,x] is P iff t = tau(x)
        if x > self.CMAX or v > self.BMAX:
            raise RuntimeError("finite position beyond table: [%d,%d,%d]" % (u, v, x))
        return self.A[x][v] == u


FIN = None


def is_P3_finite(u, v, x):
    return FIN.P(u, v, x)


def cands(h, B1, B0):
    """all t < h with lower coefficients bounded (see module doc), smallest-ish first"""
    terms = H.key(h)  # descending (exp, coef)
    out = []
    for idx, (k, hk) in enumerate(terms):
        prefix = dict(terms[:idx])
        lows = list(range(k - 1, 0, -1))  # exponents strictly between 0 and k
        for c in range(hk):
            base = dict(prefix)
            if c:
                base[k] = c
            if k == 0:
                out.append(base)
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
                    out.append(t)
    return out


def options(cols, B1, B0):
    for j in range(len(cols)):
        for t in cands(cols[j], B1, B0):
            if j == 0 and H.is_zero(t):
                continue
            c = [dict(x) for x in cols]
            for jj in range(j, len(c)):
                if H.cmp(c[jj], t) > 0:
                    c[jj] = dict(t)
            c = [x for x in c if not H.is_zero(x)]
            yield j, t, c


def rand_ord(maxdeg, rng, cmax=3, fmax=12):
    d = {}
    for e in range(maxdeg, -1, -1):
        if rng.random() < 0.6:
            d[e] = rng.randint(1, cmax if e else fmax)
    return d


def rand_pos(maxdeg, rng):
    cols = sorted([rand_ord(maxdeg, rng) for _ in range(3)], key=H.key, reverse=True)
    r = rng.random()
    # bias towards the shapes where the decomposition cases (i)-(iii) and Side-Top occur
    if r < 0.25:
        cols[1] = dict(cols[0])
        for e in list(cols[1]):
            if e == 0:
                cols[1][0] = rng.randint(0, cols[0][0])
                if not cols[1][0]:
                    del cols[1][0]
    elif r < 0.45 and H.deg(cols[0]) >= 1:
        # same leading coefficients at the degree of the third column
        i = max(H.deg(cols[2]), 1)
        for j in (1, 2):
            cols[j] = {e: c for e, c in cols[j].items() if e < i}
            cols[j][i] = cols[0].get(i, 1)
    cols = sorted(cols, key=lambda a: H.key(a), reverse=True)
    return [c for c in cols if c]


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    maxdeg = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    B1 = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    B0 = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    global FIN
    FIN = Finite3(300, 40)
    # cross-check the table against brute force on small positions
    for u in range(1, 9):
        for v in range(0, u + 1):
            for x in range(0, v + 1):
                assert FIN.P(u, v, x) == H.P3_finite(u, v, x), (u, v, x)
    H.P3_finite = is_P3_finite
    counts = {"P ok": 0, "N ok": 0, "N unverified": 0, "INCONSISTENT": 0, "skipped": 0}
    kinds = {}
    seen = set()
    replies = {}
    t0 = time.time()
    n = 0
    while n < samples:
        cols = rand_pos(maxdeg, rng)
        k = tuple(H.key(c) for c in cols)
        if not cols or k in seen:
            continue
        seen.add(k)
        n += 1
        try:
            p = H.is_P(cols)
        except (AssertionError, ValueError, RuntimeError):
            counts["skipped"] += 1
            continue
        name = [H.show(c) for c in cols]
        if p:
            bad = None
            for j, t, o in options(cols, B1, B0):
                if H.is_P(o):
                    bad = (j, t, o)
                    break
            if bad:
                counts["INCONSISTENT"] += 1
                print("INCONSISTENT P:", name, "bite", bad[0], H.show(bad[1]), "->", [H.show(c) for c in bad[2]], flush=True)
            else:
                counts["P ok"] += 1
                print("P", name, flush=True)
        else:
            hit = None
            for j, t, o in options(cols, B1, B0):
                if H.is_P(o):
                    hit = (j, t, o)
                    break
            if not hit:  # second pass: few middle coefficients, long finite parts
                for j, t, o in options(cols, 4, 20000):
                    if H.is_P(o):
                        hit = (j, t, o)
                        print("N (deep reply):", name, "bite", j, H.show(t), flush=True)
                        break
            if hit:
                replies[tuple(H.key(c) for c in hit[2])] = hit[2]
                counts["N ok"] += 1
                kinds[hit[0]] = kinds.get(hit[0], 0) + 1
            else:
                counts["N unverified"] += 1
                print("N UNVERIFIED:", name, flush=True)
    print("positions: %d, heights < w^%d, B1=%d, B0=%d: %s; winning bite column counts %s; %.0fs"
          % (samples, maxdeg + 1, B1, B0, counts, kinds, time.time() - t0))
    # (a) on the P replies found: no option may be claimed P
    PMAX = int(os.environ.get("PMAX", "100000"))
    B1p, B0p = int(os.environ.get("B1P", "4")), int(os.environ.get("B0P", "100"))
    t0 = time.time()
    good = bad = 0
    for k in sorted(replies)[:PMAX]:
        cols = replies[k]
        if not cols:
            continue
        if len(cols) == 1 and cols[0] == H.O(1):
            continue  # the poison alone
        hit = None
        for j, t, o in options(cols, B1p, B0p):
            if o and H.is_P(o):
                hit = (j, t, o)
                break
        if hit:
            bad += 1
            print("INCONSISTENT P reply:", [H.show(c) for c in cols], "bite", hit[0], H.show(hit[1]), "->",
                  [H.show(c) for c in hit[2]], flush=True)
        else:
            good += 1
    print("P replies checked: %d consistent, %d inconsistent (B1=%d, B0=%d); %.0fs" % (good, bad, B1p, B0p, time.time() - t0))


if __name__ == "__main__":
    main()
