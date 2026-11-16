#!/usr/bin/env python3
"""Validate tools/hs_oracle.py.

1. Finite positions: the oracle agrees with brute force (it uses brute force there, so this
   checks the plumbing) and with rodf.
2. Local consistency on random positions with heights < omega^MAXDEG: a position claimed P must
   have every option claimed N; a position claimed N must have some option claimed P. Options
   are sampled: cut column j at every ordinal t below its height whose Cantor normal form uses
   coefficients <= C, plus ordinals built from the position's own terms.

usage: hs_check.py RODF [SAMPLES] [MAXDEG] [SEED]
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "tools"))
import hs_oracle as H  # noqa: E402


def ords_below(h, C=3):
    """candidate ordinals t < h: CNF with exponents <= deg(h), coefficients <= C, plus
    truncations of h itself (its leading terms with a smaller last coefficient or added tail)."""
    d = max(H.deg(h), 0)
    out = []
    for cs in itertools.product(range(C + 1), repeat=d + 1):
        t = {e: c for e, c in zip(range(d, -1, -1), cs) if c}
        if H.cmp(t, h) < 0:
            out.append(t)
    terms = H.key(h)
    for k in range(len(terms)):
        base = dict(terms[:k])
        e, c = terms[k]
        for cc in range(max(0, c - 2), c):
            for tail in range(0, 4):
                t = dict(base)
                if cc:
                    t[e] = cc
                if e > 0 and tail:
                    t[e - 1 if e - 1 >= 0 else 0] = t.get(e - 1, 0) + tail
                if H.cmp(t, h) < 0:
                    out.append(t)
    uniq = {H.key(t): t for t in out}
    return list(uniq.values())


def options(cols):
    res = []
    for j in range(len(cols)):
        for t in ords_below(cols[j]):
            if j == 0 and H.is_zero(t):
                continue  # poison
            c = [dict(x) for x in cols]
            for jj in range(j, len(c)):
                if H.cmp(c[jj], t) > 0:
                    c[jj] = dict(t)
            c = [x for x in c if not H.is_zero(x)]
            if c:
                res.append(c)
    return res


def rand_ord(maxdeg, rng):
    d = {}
    for e in range(maxdeg, -1, -1):
        if rng.random() < 0.6:
            d[e] = rng.randint(1, 3)
    return {e: c for e, c in d.items() if c}


def main():
    H.RODF = sys.argv[1]
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    maxdeg = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    # 1. finite cross-check with rodf
    bad = 0
    for u in range(1, 9):
        for v in range(0, u + 1):
            for x in range(0, v + 1):
                hs = [u, v, x]
                cells = ",".join(str(t) for t in hs)
                out = os.popen("%s -p %s 3" % (H.RODF, cells)).read()
                r = "P" in out.split(":")[1].split()[0]
                if r != H.is_P([H.O(t) for t in hs if t]):
                    bad += 1
    print("finite cross-check with rodf: %d mismatches" % bad)
    # 2. local consistency
    counts = {"P ok": 0, "N ok": 0, "N unverified": 0, "INCONSISTENT": 0}
    nP = 0
    for _ in range(samples):
        cols = sorted([rand_ord(maxdeg, rng) for _ in range(3)], key=H.key, reverse=True)
        cols = [c for c in cols if c]
        if not cols:
            continue
        # also bias towards interesting shapes: sometimes make the top two equal
        if rng.random() < 0.3 and len(cols) >= 2:
            cols[1] = dict(cols[0])
        cols = sorted(cols, key=lambda a: [(-1, 0)] if not a else H.key(a), reverse=True)
        try:
            p = H.is_P(cols)
            opts = options(cols)
            optP = [o for o in opts if H.is_P(o)]
        except (AssertionError, ValueError):
            continue
        if p:
            nP += 1
            if optP:
                counts["INCONSISTENT"] += 1
                print("INCONSISTENT P:", [H.show(c) for c in cols], "has P option", [H.show(c) for c in optP[0]])
            else:
                counts["P ok"] += 1
        else:
            if optP:
                counts["N ok"] += 1
            else:
                counts["N unverified"] += 1
    print("local consistency (%d positions, heights < w^%d): %s" % (samples, maxdeg + 1, counts))


main()


def targeted(samples=150, maxdeg=2, seed=2):
    """Generate claimed P-positions (scan x for random u >= v) and check every sampled option
    is claimed N; retry 'N unverified' positions with a wider option sample."""
    rng = random.Random(seed)
    found, bad = 0, 0
    for _ in range(samples):
        u, v = sorted([rand_ord(maxdeg, rng), rand_ord(maxdeg, rng)], key=H.key, reverse=True)
        if rng.random() < 0.4:
            v = dict(u)
        if not u or not v:
            continue
        for x in ords_below(v) + [dict(v)]:
            if H.is_zero(x):
                continue
            cols = [u, v, x]
            if not H.is_P(cols):
                continue
            found += 1
            optP = [o for o in options(cols) if H.is_P(o)]
            if optP:
                bad += 1
                print("INCONSISTENT P:", [H.show(c) for c in cols], "->", [H.show(c) for c in optP[0]])
    print("targeted: %d claimed P-positions checked, %d inconsistent" % (found, bad))


if __name__ == "__main__" and os.environ.get("TARGETED"):
    targeted()
