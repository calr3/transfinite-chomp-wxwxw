#!/usr/bin/env python3
"""A machine check of Huddleston-Shurman's classification of the P-positions over a 2x2 base
("Transfinite Chomp", section 11) for heights above omega (notes/32).

The classification is correct, by induction on the position, iff
  (a) no position it calls P has an option it calls P, and
  (b) every position it calls N has an option it calls P.
Each part below samples positions of one kind, enumerates their options completely up to bounds
on the coefficients (hs22_lib.cuts), and tests (a) and (b) against the statements of the paper
as implemented in hs22_lib.claim.

usage: hs22_audit.py [PART ...] [-n SAMPLES] [-s SEED]
  parts: examples pa2 pd1 pd23 pd1proof pc2 pc3 tallc pf1 c1 c2      (default: all)
"""
import random
import sys
import time

import hs22_lib as L
from hs22_lib import (O, W1, W2, W3, G2, G2f, cmp, coef, finite, high, lsub, oadd, parse, pshow, show, val)


def rnd_ord(rng, maxdeg, cmax, fmax):
    d = {}
    for e in range(maxdeg, 0, -1):
        c = rng.choice([0, 0, 1, 1, 2] if cmax >= 2 else [0, 1])
        c = min(c, cmax)
        if c:
            d[e] = c
    f = rng.randint(0, fmax)
    if f:
        d[0] = f
    return d


def check(p, B1, B0, stats, retry=((1, 4), (2, 12)), allow_none=False):
    """test (a) or (b) at p; returns a list of problems"""
    st, why = L.claim(p)
    assert st is not None, pshow(p)
    probs = []
    if st == "P":
        n = 0
        for col, k, q in L.options(p, B1, B0):
            n += 1
            s2, w2 = L.claim(q)
            if s2 == "P":
                probs.append("P with P option: %s -(%d,%s)-> %s [%s]" % (pshow(p), col, show(k), pshow(L.norm(q)), w2))
            elif s2 is None:
                stats["open options of P"] = stats.get("open options of P", 0) + 1
                if not allow_none:
                    probs.append("P with an option of no stated status: %s -(%d,%s)-> %s" % (pshow(p), col, show(k), pshow(L.norm(q))))
        stats["P positions"] = stats.get("P positions", 0) + 1
        stats["options of P checked"] = stats.get("options of P checked", 0) + n
        return probs
    stats["N positions"] = stats.get("N positions", 0) + 1
    tries = [(B1, B0)] + [(B1 + a, B0 * m) for a, m in retry]
    for b1, b0 in tries:
        for col, k, q in L.options(p, b1, b0):
            if L.claim(q)[0] == "P":
                return probs
        stats["N: wider search needed"] = stats.get("N: wider search needed", 0) + 1
    probs.append("N with no P option found (bounds %s): %s [%s]" % (tries[-1], pshow(p), why))
    return probs


def report(name, stats, probs, t0):
    print("== %s: %s; %d problems (%.0f s)" % (name, ", ".join("%s %d" % kv for kv in sorted(stats.items())), len(probs), time.time() - t0))
    for q in probs[:12]:
        print("   " + q)
    return len(probs)


# ---------------------------------------------------------------------------------------------

def part_examples(rng, n):
    ex = ["1,1;3,1", "2,2;5,2", "3,2;6,2", "2,1;2,2", "3,2;3,3", "w,0;w,0", "w,1;w+1,1", "w,w;w*2,w", "w+1,w;w*2+1,w",
          "w^2,w^2;w^2+w,w^2", "w^2+1,w^2;w^2+w+1,w^2", "w^2,w;w^2,w", "w^2,w;w^2+1,w+1", "w^2*2,w^2;w^2*2,w^2",
          "w^2,w;w^2*2,w^2", "w^2*2,w^2;w^2*3,w^2*2", "w^2*2,w;w^2*2,w*2", "w^3,w;w^3,w^2", "w^3,w^2;w^3,w^2*2", "w^3,w^3;w^3,w^3"]
    t0 = time.time(); probs = []; stats = {}
    for s in ex:
        top, bot = s.split(";"); v, z = top.split(","); u, y = bot.split(",")
        p = tuple(parse(t) for t in (u, v, y, z))
        st = top_claim(p)
        stats[str(st)] = stats.get(str(st), 0) + 1
        if st != "P":
            probs.append("example not P by the stated rules: %s" % pshow(p))
    return report("the paper's examples of P-positions (types A to D, F)", stats, probs, t0)


def top_claim(p):
    """claim, with PC1 applied to tall type C: the status of the short position with the same top"""
    st, why = L.claim(p)
    if st is None and L.ptype(p) == "C":
        h, top = L.decompC(p)
        st, why = L.claim(tuple(oadd(W1, t) for t in top))
    return st


def part_pa2(rng, n):
    """types A and B (z finite): closed under options"""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        v = rnd_ord(rng, rng.choice([1, 1, 2, 3]), 2, 6)
        if finite(v):
            continue
        top = rnd_ord(rng, rng.choice([0, 0, 1, 1, 2]), 2, 6)
        u = oadd(v, top) if rng.random() < 0.7 else rnd_ord(rng, 3, 2, 6)
        if cmp(u, v) < 0:
            continue
        g = G2(lsub(W1, u), lsub(W1, v))
        if finite(g) and val(g) <= 40 and rng.random() < 0.8:      # a P-position, or near one
            zf = val(g) if rng.random() < 0.6 else max(0, val(g) + rng.choice([-2, -1, 1, 2]))
            yf = zf if rng.random() < 0.8 else zf + rng.randint(1, 3)
        else:
            zf = rng.randint(0, 5)
            yf = zf if rng.random() < 0.7 else zf + rng.randint(1, 3)
        p = (u, v, O(yf), O(zf))
        k = pshow(p)
        if k in seen:
            continue
        seen.add(k)
        probs += check(p, 3, max(14, 2 * zf + 6), stats)
    return report("PA2 (types A and B, v infinite)", stats, probs, t0)


def rnd_typeD(rng):
    while True:
        z = rnd_ord(rng, 2, 2, 3)
        if finite(z):
            continue
        v = rnd_ord(rng, 3, 2, 3)
        if cmp(high(v, 2), high(z, 2)) <= 0:
            continue
        y = z if rng.random() < 0.25 else rnd_ord(rng, 3, 2, 3)
        if cmp(y, z) < 0 or cmp(y, v) > 0:
            continue
        u = v if rng.random() < 0.3 else rnd_ord(rng, 3, 2, 3)
        if cmp(u, v) < 0:
            continue
        return (u, v, y, z)


def solveD(rng, p):
    """move the top column so that G(F) = G(T), if a suitable u exists among the candidates"""
    u, v, y, z = p
    f, _ = L.FT(p)
    for k in L.cuts(oadd(oadd(u, W3), W3), 2, 6):
        if cmp(k, v) >= 0:
            q = (k, v, y, z)
            if L.ptype(q) == "D" and L.FT(q)[1] == f:
                return q
    return None


def part_pd1(rng, n):
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        p = rnd_typeD(rng)
        if rng.random() < 0.5:
            q = solveD(rng, p)
            if q is None:
                continue
            p = q
        k = pshow(p)
        if k in seen:
            continue
        seen.add(k)
        probs += check(p, 3, 8, stats)
    return report("PD1 (type D)", stats, probs, t0)


def inv_square(k):
    """the c with G(c, c) = k (k finite): c = w*j + a"""
    j = 0
    while True:
        base = (3 ** j - 1) // 2
        if k >= base and (k - base) % 3 ** j == 0:
            m = (k - base) // 3 ** j
            for a in range(0, m + 2):
                if (3 * a + 1) // 2 == m:
                    return L.nat_add(O((1, j)), O(a))
        j += 1
        assert 3 ** j <= 2 * k + 3


def rnd_typeC(rng, equal):
    """type C with u-hat = v-hat and u1 = v1 (equal), or with u-hat > v-hat or u1 > v1"""
    while True:
        m = rng.choice([0, 0, 1, 2])
        zl = rnd_ord(rng, 1, 3, 4)
        if m == 0 and finite(zl):
            continue
        hh = {2: m} if m else {}
        z = L.nat_add(hh, zl)
        y = L.nat_add(hh, rnd_ord(rng, 1, 3, 4))
        v = L.nat_add(hh, rnd_ord(rng, 1, 3, 4))
        if cmp(y, z) < 0 or cmp(v, y) < 0:
            continue
        if equal:
            u = L.nat_add(L.nat_add(hh, O((1, coef(v, 1)))), O(rng.randint(coef(v, 0), coef(v, 0) + 5)))
        elif rng.random() < 0.5:
            u = L.nat_add(L.nat_add(hh, O((1, coef(v, 1) + rng.randint(1, 3)))), O(rng.randint(0, 6)))
        else:
            u = rnd_ord(rng, 3, 2, 4)
            if cmp(u, v) < 0 or (high(u, 2) == high(v, 2) and coef(u, 1) == coef(v, 1)):
                continue
        return (u, v, y, z)


def part_pc2(rng, n):
    """the winning bite named in the proof of PC2"""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        p = rnd_typeC(rng, True)
        if pshow(p) in seen:
            continue
        seen.add(pshow(p))
        u, v, y, z = p
        h, (tu, tv, ty, tz) = L.decompC(p)
        k = G2(tu, tv)
        assert finite(k), pshow(p)
        if h == W1:
            height = O(val(k)); kind = "short"
        else:
            m = coef(h, 2)
            h1 = {2: m - 1} if m > 1 else {}
            height = oadd(oadd(W1, h1), inv_square(val(k))); kind = "tall"
        stats[kind] = stats.get(kind, 0) + 1
        if cmp(height, y) >= 0:
            # the named bite is not a bite: the column (1,0) is not taller than its height
            stats[kind + ": named height not below y"] = stats.get(kind + ": named height not below y", 0) + 1
            # is there any P option then?
            pr = check(p, 3, 12, {})
            if pr:
                probs.append("PC2: named bite (1,0,%s) is not available in %s, and no P option found" % (show(height), pshow(p)))
            else:
                stats[kind + ": another P option exists"] = stats.get(kind + ": another P option exists", 0) + 1
            continue
        q = L.bite(p, 2, height)
        if L.claim(q)[0] != "P":
            probs.append("PC2: bite (1,0,%s) of %s leaves %s, not P by %s" % (show(height), pshow(p), pshow(q), L.claim(q)[1]))
    return report("PC2 (type C with u-hat = v-hat, u1 = v1 is N by the named bite)", stats, probs, t0)


def part_pc3(rng, n):
    """every bite that meets the base of a type C position of PC3 leaves an N-position"""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        p = rnd_typeC(rng, False)
        if pshow(p) in seen:
            continue
        seen.add(pshow(p))
        h, _ = L.decompC(p)
        u, v, y, z = p
        case = "u-hat > v-hat" if high(u, 2) != high(v, 2) else "u-hat = v-hat, u1 > v1"
        case += ", short" if h == W1 else ", tall"
        stats["positions with " + case] = stats.get("positions with " + case, 0) + 1
        bad = False
        for col, k, q in L.options(p, 3, 6):
            if cmp(k, h) >= 0:
                continue
            stats["bites into the base"] = stats.get("bites into the base", 0) + 1
            st, why = L.claim(q)
            if st == "P":
                bad = True
                key = "P after a bite of %s into the base, %s" % (("(0,0)", "(0,1)", "(1,0)", "(1,1)")[col], case)
                stats[key] = stats.get(key, 0) + 1
                if high(u, 2) == high(v, 2) or len(probs) < 4:
                    probs.append("PC3: %s -(%d,%s)-> %s is P by %s" % (pshow(p), col, show(k), pshow(L.norm(q)), why))
            elif st is None:
                stats["no stated status"] = stats.get("no stated status", 0) + 1
        if bad:
            stats["positions with a P bite, " + case] = stats.get("positions with a P bite, " + case, 0) + 1
    return report("PC3 (bites into the base of the other type C positions)", stats, probs, t0)


def small_ords(maxdeg, cmax, fmax):
    import itertools
    for cs in itertools.product(range(cmax + 1), repeat=maxdeg):
        for f in range(fmax + 1):
            d = {e: c for e, c in zip(range(maxdeg, 0, -1), cs) if c}
            if f:
                d[0] = f
            yield d


def part_pd23(rng, n):
    """PD2 and PD3 as statements about the two decompositions, on all small type D positions"""
    t0 = time.time(); probs = []; stats = {}
    zs = [z for z in small_ords(2, 1, 1) if not finite(z)]
    ys = list(small_ords(3, 2, 1)); vs = list(small_ords(3, 2, 1)); us = list(small_ords(3, 2, 2))
    first = []
    for z in zs:
        for y in ys:
            if cmp(y, z) < 0:
                continue
            for v in vs:
                if cmp(v, y) < 0 or cmp(high(z, 2), high(v, 2)) >= 0:
                    continue
                for u in us:
                    if cmp(u, v) < 0:
                        continue
                    p = (u, v, y, z)
                    f, t = L.FT(p)
                    if high(u, 2) == high(v, 2) == high(y, 2):
                        stats["PD2: positions"] = stats.get("PD2: positions", 0) + 1
                        if f == t:
                            probs.append("PD2: %s is P by PD1" % pshow(p))
                    if cmp(high(z, 2), high(y, 2)) < 0 and cmp(high(v, 2), high(u, 2)) < 0:
                        f2, t2 = G2(lsub(W1, v), lsub(W1, z)), G2(lsub(W2, u), lsub(W2, y))
                        rel = "y-hat = v-hat" if high(y, 2) == high(v, 2) else "y-hat < v-hat"
                        a, b = f == t, f2 == t2
                        res = "both" if a and b else "neither" if not a and not b else "PD1 only" if a else "other direction only"
                        key = "PD3, %s: %s" % (rel, res)
                        stats[key] = stats.get(key, 0) + 1
                        if a != b:
                            first.append((a, p))
    first.sort(key=lambda ap: (L.key(ap[1][0]), L.key(ap[1][1])))
    for a, p in first[:3]:
        u, v, y, z = p
        probs.append("PD3 fails: %s: G(F)=%s G(T)=%s; other direction G=%s and %s" % (pshow(p), show(L.FT(p)[0]), show(L.FT(p)[1]),
                     show(G2(lsub(W1, v), lsub(W1, z))), show(G2(lsub(W2, u), lsub(W2, y)))))
    # which of the two criteria is consistent with the game, on the positions where they differ
    st = {}; pr = []
    for a, p in first:
        pr += check(p, 3, 6, st)
    stats["PD3 disagreements: PD1 consistent with the game"] = len(first) - len(pr)
    probs += pr
    return report("PD2 and PD3", stats, probs, t0)


def part_pd1proof(rng, n):
    """the step of the proof of PD1 that quotes PD3: a bite (0,1,h) with z-hat < h-hat < v-hat and
    h < y from a type D position with G(F) = G(T). Claimed: G(F') < G(F) + w^2 <= G(T')."""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        p = rnd_typeD(rng)
        q = solveD(rng, p)
        if q is None or pshow(q) in seen:
            continue
        seen.add(pshow(q))
        u, v, y, z = q
        f, t = L.FT(q)
        for h in L.cuts(v, 3, 3):
            if finite(h) or cmp(h, y) >= 0:
                continue
            if not (cmp(high(z, 2), high(h, 2)) < 0 and cmp(high(h, 2), high(v, 2)) < 0):
                continue
            case = "y-hat < v-hat" if high(y, 2) != high(v, 2) else "y-hat = v-hat"
            stats["bites, " + case] = stats.get("bites, " + case, 0) + 1
            r = L.norm(L.bite(q, 1, h))                  # (u, y, h, min(z,h))
            f2, t2 = L.FT(r)
            bound = oadd(f, W2)
            okF, okT = cmp(f2, bound) < 0, cmp(t2, oadd(t, W2)) >= 0
            if not okF:
                stats["G(F') < G(F) + w^2 fails, " + case] = stats.get("G(F') < G(F) + w^2 fails, " + case, 0) + 1
            if not okT:
                stats["G(T') >= G(T) + w^2 fails, " + case] = stats.get("G(T') >= G(T) + w^2 fails, " + case, 0) + 1
            if not (okF and okT) and case == "y-hat < v-hat":
                shown = stats.get("_shown", 0)
                if shown < 3:
                    stats["_shown"] = shown + 1
                    probs.append("proof of PD1: %s -(0,1,%s)-> %s: G(F)=G(T)=%s, G(F')=%s, G(T')=%s" % (pshow(q), show(h), pshow(r), show(t), show(f2), show(t2)))
            if L.claim(r)[0] != "N":
                probs.append("the option is P: %s -(0,1,%s)-> %s" % (pshow(q), show(h), pshow(r)))
    stats.pop("_shown", None)
    return report("the step of the proof of PD1 that quotes PD3", stats, probs, t0)


def part_tallc(rng, n):
    """type C through PC1, for tops with z finite: tall and short, u-hat = v-hat or u-hat > v-hat"""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        m = rng.choice([0, 1, 1, 2])
        hh = {2: m} if m else W1
        y1 = rng.choice([0, 0, 1, 2]); v1 = rng.choice([y1, y1, y1 + 1])
        z0 = rng.randint(0, 4)
        y0 = rng.randint(z0 if y1 == 0 else 0, 6)
        v0 = rng.randint(max(y0, z0) if v1 == y1 else 0, 6)
        r = rng.random()
        if r < 0.25:
            tu = rnd_ord(rng, 3, 2, 5)                       # u-hat > v-hat mostly
            if not high(tu, 2):
                continue
        else:
            u1 = v1 + y1 + 1 if r < 0.75 else rng.randint(v1 + 1, v1 + y1 + 4)
            tu = O((1, u1), (0, rng.randint(0, 9)))
        top = (tu, O((1, v1), (0, v0)), O((1, y1), (0, y0)), O(z0))
        p = tuple(oadd(hh, t) for t in top)
        if not L.valid(p) or L.ptype(p) != "C":
            continue
        if r >= 0.25 and r < 0.75:                           # steer to a P-position
            for a in range(0, 64):
                q = (oadd(hh, O((1, coef(tu, 1)), (0, a))), p[1], p[2], p[3])
                if L.claim(q)[0] == "P":
                    p = q
                    break
        if pshow(p) in seen:
            continue
        seen.add(pshow(p))
        u = p[0]
        kind = ("short" if m == 0 else "tall") + (", u-hat > v-hat" if high(lsub(hh, u), 2) else ", u-hat = v-hat")
        st = {}
        pr = check(p, max(4, coef(p[1], 1) + coef(p[2], 1) + 1), 14, st)
        for k2, v2 in st.items():
            stats[kind + ": " + k2] = stats.get(kind + ": " + k2, 0) + v2
        probs += pr
    return report("type C through PC1 (tops with z finite)", stats, probs, t0)


def part_pf1(rng, n):
    """2x2xw^3: every option is N; the replies named in the paper, as printed and as corrected"""
    t0 = time.time(); probs = []; stats = {}
    box = (W3, W3, W3, W3)
    assert L.claim(box)[0] == "P"
    hs = [k for k in L.cuts(W3, 3, 5) if not finite(k)]
    for h in hs:
        for col in range(4):
            q = L.bite(box, col, h)
            st = L.claim(q)[0]
            stats["options"] = stats.get("options", 0) + 1
            if st != "N":
                probs.append("option of the box not N: bite (%d,%s) -> %s: %s" % (col, show(h), pshow(L.norm(q)), L.claim(q)))
            small, mid = cmp(h, W2) < 0, cmp(h, {2: 2}) < 0
            # replies as printed
            if col == 0:
                printed = (2, G2(lsub(W1, h), lsub(W1, h))) if small else (2, oadd(W1, lsub(W1, h))) if mid else (2, lsub(W1, h))
                fixed = printed if small else (2, oadd(W1, lsub(W2, h))) if mid else (2, lsub(W2, h))
            elif col == 3:
                printed = (2, oadd(W2, h)); fixed = (2, oadd(W2, lsub(W1, h)))
            else:
                printed = (0, oadd(W2, h)); fixed = (0, oadd(W2, lsub(W1, h)))
            for name, (c2, k2) in (("printed", printed), ("corrected", fixed)):
                if cmp(k2, q[c2]) >= 0:
                    ok = False
                else:
                    ok = L.claim(L.bite(q, c2, k2))[0] == "P"
                key = "%s reply to a bite of %s: %s" % (name, ("(0,0)", "(0,1)", "(1,0)", "(1,1)")[col], "P" if ok else "fails")
                stats[key] = stats.get(key, 0) + 1
                if name == "corrected" and not ok:
                    probs.append("corrected reply fails: bite (%d,%s), reply (%d,%s)" % (col, show(h), c2, show(k2)))
    return report("PF1 (the box 2x2xw^3)", stats, probs, t0)


def part_c1(rng, n):
    """short type C with z1 = 1: the rule u1 = v1 + y1, pieces with nim sum 0"""
    t0 = time.time(); probs = []; stats = {}
    seen = set()
    while len(seen) < n:
        y1 = rng.choice([1, 1, 2, 3]); v1 = rng.choice([y1, y1, y1 + 1, y1 + 2])
        z0 = rng.randint(0, 5)
        y0 = rng.randint(z0 if y1 == 1 else 0, 7)
        v0 = rng.randint(max(y0, z0) if v1 == y1 else (z0 if v1 == 1 else 0), 7) if v1 == y1 else rng.randint(0, 7)
        if v1 == 1 and v0 < z0:
            continue
        u1 = v1 + y1 if rng.random() < 0.7 else rng.randint(v1 + 1, v1 + y1 + 2)
        u0 = rng.randint(0, 9)
        p = (O((1, u1), (0, u0)), O((1, v1), (0, v0)), O((1, y1), (0, y0)), O((1, 1), (0, z0)))
        if not L.valid(p):
            continue
        if rng.random() < 0.5 and u1 == v1 + y1:      # steer to a P-position
            for a in range(0, 64):
                q = (O((1, u1), (0, a)), p[1], p[2], p[3])
                if L.claimC1(q):
                    p = q
                    break
        if pshow(p) in seen:
            continue
        seen.add(pshow(p))
        probs += check(p, 6, 16, stats)
    return report("short type C with z1 = 1", stats, probs, t0)


def part_c2(rng, n):
    """the statements on z1 = 2: the set Q, the power-of-two criterion, and the taller column"""
    t0 = time.time(); probs = []; stats = {}
    M = 12
    inQ = lambda a, b, c: (a ^ b) % 3 == 1 and (a ^ c) % 3 == 1
    # number theory: some a with a^b = a^c = 1 (mod 3) exists iff b^c is not a power of 2
    for b in range(64):
        for c in range(64):
            ex = any(inQ(a, b, c) for a in range(4096))
            pw = (b ^ c) != 0 and ((b ^ c) & ((b ^ c) - 1)) == 0
            stats["pairs (b,c) < 64"] = stats.get("pairs (b,c) < 64", 0) + 1
            if ex == pw:
                probs.append("power-of-two criterion fails for b=%d c=%d" % (b, c))
    # The restricted game on Q. A top [b d; w+a c] over the base of height w*2 has restricted
    # value 0 iff a = sol(b,c,d): the least a with inQ(a,b,c) that is not the solution of a
    # piece obtained from (b,c,d) by one bite (for a fixed piece at most one a has value 0).
    solm = {}
    ABOUND = 200000
    def sol(b, c, d):
        k = (b, c, d)
        if k not in solm:
            E = set()
            for b2 in range(b): E.add(sol(b2, c, min(d, b2)))
            for c2 in range(c): E.add(sol(b, c2, min(d, c2)))
            for d2 in range(d): E.add(sol(b, c, d2))
            pw = (b ^ c) != 0 and ((b ^ c) & ((b ^ c) - 1)) == 0
            r = None
            if not pw:
                for a in range(ABOUND):
                    if inQ(a, b, c) and a not in E:
                        r = a
                        break
            solm[k] = r
        return solm[k]
    def P3(a, b, c, d):
        return sol(b, c, d) == a
    p3 = {}
    amax = 0
    for b in range(M + 1):
        for c in range(M + 1):
            for d in range(min(b, c) + 1):
                r = sol(b, c, d)
                p3[(b, c, d)] = [] if r is None else [r]
                pw = (b ^ c) != 0 and ((b ^ c) & ((b ^ c) - 1)) == 0
                stats["triples (b,c,d)"] = stats.get("triples (b,c,d)", 0) + 1
                if (r is None) != pw:
                    probs.append("u1 = 3: no solution below %d for b=%d c=%d d=%d (b^c a power of two: %s)" % (ABOUND, b, c, d, pw))
                if r is not None:
                    amax = max(amax, r)
    stats["largest a with u1 = 3 (b,c <= %d)" % M] = amax
    # the taller column: for b^c a power of 2 the P-position has u1 = 5
    m5 = {}
    def mu5(b, c, d):
        k = (b, c, d)
        if k not in m5:
            s = set()
            for b2 in range(b):
                if not p3[(b2, c, min(d, b2))]: s.add(mu5(b2, c, min(d, b2)))
            for c2 in range(c):
                if not p3[(b, c2, min(d, c2))]: s.add(mu5(b, c2, min(d, c2)))
            for d2 in range(d):
                if not p3[(b, c, d2)]: s.add(mu5(b, c, d2))
            g = 0
            while g in s: g += 1
            m5[k] = g
        return m5[k]
    def stat2(p):
        """status of a position with v1 = y1 = z1 = 2 and u1 in 3..5, by the rules above"""
        u, v, y, z = L.norm(p)
        u1, a, b, c, d = coef(u, 1), coef(u, 0), coef(v, 0), coef(y, 0), coef(z, 0)
        if u1 == 3:
            return P3(a, b, c, d)
        if u1 == 4:
            return False
        return (not p3[(b, c, d)]) and a == mu5(b, c, d)
    def claim2(p):
        u, v, y, z = L.norm(p)
        if (not high(u, 2)) and coef(v, 1) == coef(y, 1) == coef(z, 1) == 2 and not high(v, 2) and 3 <= coef(u, 1) <= 5:
            return "P" if stat2((u, v, y, z)) else "N"
        return L.claim(p)[0]
    cnt = 0
    while cnt < n:
        b, c = rng.randint(0, 7), rng.randint(0, 7)
        d = rng.randint(0, min(b, c))
        u1 = rng.choice([3, 3, 4, 5])
        a = rng.randint(0, 20)
        if rng.random() < 0.6:
            if u1 == 3 and p3[(b, c, d)]: a = p3[(b, c, d)][0]
            if u1 == 5 and not p3[(b, c, d)]: a = mu5(b, c, d)
        p = (O((1, u1), (0, a)), O((1, 2), (0, b)), O((1, 2), (0, c)), O((1, 2), (0, d)))
        cnt += 1
        st = claim2(p)
        if st == "P":
            stats["P positions"] = stats.get("P positions", 0) + 1
            for col, k, q in L.options(p, 6, max(40, 2 * a + 8)):
                stats["options of P checked"] = stats.get("options of P checked", 0) + 1
                s2 = claim2(q)
                if s2 == "P":
                    probs.append("z1 = 2: P with P option: %s -(%d,%s)-> %s" % (pshow(p), col, show(k), pshow(L.norm(q))))
                elif s2 is None:
                    stats["open options of P"] = stats.get("open options of P", 0) + 1
        else:
            stats["N positions"] = stats.get("N positions", 0) + 1
            if not any(claim2(q) == "P" for col, k, q in L.options(p, 6, max(60, amax + 8))):
                probs.append("z1 = 2: N with no P option found: %s" % pshow(p))
    return report("type C with z1 = 2 (v1 = y1 = 2)", stats, probs, t0)


PARTS = {"examples": part_examples, "pa2": part_pa2, "pd1": part_pd1, "pd23": part_pd23, "pd1proof": part_pd1proof, "pc2": part_pc2, "pc3": part_pc3, "tallc": part_tallc, "pf1": part_pf1, "c1": part_c1, "c2": part_c2}


def main():
    args = sys.argv[1:]
    n, seed = 300, 1
    parts = []
    i = 0
    while i < len(args):
        if args[i] == "-n": n = int(args[i + 1]); i += 2
        elif args[i] == "-s": seed = int(args[i + 1]); i += 2
        else: parts.append(args[i]); i += 1
    total = 0
    for name in parts or list(PARTS):
        total += PARTS[name](random.Random(seed), n)
    print("total problems: %d" % total)


if __name__ == "__main__":
    main()
