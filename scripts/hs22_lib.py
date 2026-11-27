#!/usr/bin/env python3
"""Huddleston-Shurman, "Transfinite Chomp", section 11: the P-positions over a 2x2 base, as the
paper states them (notes/32). Used by hs22_audit.py.

A position is (u, v, y, z): the heights of the columns (0,0), (0,1), (1,0), (1,1), ordinals
below omega^omega (dicts {exponent: coefficient}, as in tools/hs_oracle.py), with
u >= v, u >= y, min(v, y) >= z. The paper's bird's-eye matrix [v z; u y] is the same thing.
Type E (y >= omega^omega) is out of range.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_oracle as H  # noqa: E402

O, cmp, key, deg, coef, high, low, finite, val, G2, show, parse, nim, nat_add = (
    H.O, H.cmp, H.key, H.deg, H.coef, H.high, H.low, H.finite, H.val, H.G2, H.show, H.parse, H.nim, H.nat_add)
G2f = H.G2_finite

W1, W2, W3 = {1: 1}, {2: 1}, {3: 1}


def oadd(a, b):
    """ordinal addition a + b"""
    if not b:
        return dict(a)
    e = deg(b)
    r = {k: c for k, c in a.items() if k > e}
    r[e] = a.get(e, 0) + b[e]
    for k, c in b.items():
        if k < e:
            r[k] = c
    return r


def lsub(b, z):
    """b\\z: the t with b + t = z (b <= z)"""
    assert cmp(b, z) <= 0, (show(b), show(z))
    for e in sorted(set(b) | set(z), reverse=True):
        cb, cz = b.get(e, 0), z.get(e, 0)
        if cb != cz:
            assert cz > cb
            t = {e: cz - cb}
            t.update({k: c for k, c in z.items() if k < e})
            return t
    return {}


def omin(a, b):
    return a if cmp(a, b) <= 0 else b


def norm(p):
    """reflect so that v >= y"""
    u, v, y, z = p
    if cmp(v, y) < 0:
        v, y = y, v
    return (u, v, y, z)


def valid(p):
    u, v, y, z = p
    return bool(u) and cmp(u, v) >= 0 and cmp(u, y) >= 0 and cmp(v, z) >= 0 and cmp(y, z) >= 0


def pshow(p):
    return "[%s %s; %s %s]" % (show(p[1]), show(p[3]), show(p[0]), show(p[2]))


def ptype(p):
    """the paper's type of a position (after reflection): A, B, C, D or F"""
    u, v, y, z = norm(p)
    if finite(z):
        return "A" if z == y else "B"
    if cmp(z, W3) >= 0:
        return "F"
    return "C" if high(z, 2) == high(v, 2) else "D"


def decompC(p):
    """type C: base height h and top piece (h\\u, h\\v, h\\y, h\\z)"""
    u, v, y, z = norm(p)
    zh = high(z, 2)
    h = dict(zh) if zh else W1
    return h, tuple(lsub(h, x) for x in (u, v, y, z))


def FT(p):
    """type D: the values G(F) and G(T) of the decomposition before PD1"""
    u, v, y, z = norm(p)
    return G2(lsub(W1, y), lsub(W1, z)), G2(lsub(W2, u), lsub(W2, v))


# ---- short type C with z < omega*2 (z_1 = 1): the rule stated after the proof of PD1 ----

_lam = {}


def lam(b, c, d):
    """Grundy value of three finite stacks b, c, d over the cells (0,1), (1,0), (1,1) of one
    level, every cell free to be taken; a cut of (0,1) or (1,0) at n also cuts (1,1)."""
    if b < c:
        b, c = c, b
    k = (b, c, d)
    if k not in _lam:
        s = set()
        for n in range(b):
            s.add(lam(n, c, min(d, n)))
        for n in range(c):
            s.add(lam(b, n, min(d, n)))
        for n in range(d):
            s.add(lam(b, c, n))
        g = 0
        while g in s:
            g += 1
        _lam[k] = g
    return _lam[k]


def claimC1(p):
    """short type C with z_1 = 1 and u_1 > v_1: P iff u_1 = v_1 + y_1 and the pieces have nim sum 0"""
    u, v, y, z = norm(p)
    u1, v1, y1 = coef(u, 1), coef(v, 1), coef(y, 1)
    u0, v0, y0, z0 = coef(u, 0), coef(v, 0), coef(y, 0), coef(z, 0)
    if u1 != v1 + y1:
        return False
    if v1 > y1:
        rest = v0 ^ (G2f(y0, z0) if y1 == 1 else y0 ^ z0)
    elif y1 > 1:
        rest = v0 ^ y0 ^ z0
    else:
        rest = lam(v0, y0, z0)
    return u0 == rest


def claim(p, use_c1=True):
    """(status, reason): status 'P', 'N', or None where the paper gives no closed form."""
    u, v, y, z = norm(p)
    assert valid((u, v, y, z)), pshow(p)
    if finite(z):
        zf = val(z)
        if finite(y):
            yf = val(y)
            if finite(v):
                if not finite(u):
                    return "N", "one tall column"
                uf, vf = val(u), val(v)
                if yf == zf:
                    return ("P" if uf == vf + zf + 1 else "N"), "PA1"
                return ("P" if uf == vf == yf == zf + 1 else "N"), "PB1"
            if yf == zf:
                return ("P" if G2(lsub(W1, u), lsub(W1, v)) == O(zf) else "N"), "PA2"
            return "N", "PB1"
        return "N", "PB1"
    if cmp(z, W3) >= 0:
        return ("P" if u == W3 and v == W3 and y == W3 and z == W3 else "N"), "PF1"
    if high(z, 2) == high(v, 2):
        h, (tu, tv, ty, tz) = decompC((u, v, y, z))
        if high(tu, 2):
            return "N", "PC1 (top with u-hat > 0)"
        if coef(tu, 1) == coef(tv, 1):
            return "N", "PC2"
        if use_c1 and finite(tz):
            # PC1: the status depends on the top piece only; for a top with z finite it is the
            # rule for short positions with z1 = 1
            short = tuple(oadd(W1, t) for t in (tu, tv, ty, tz))
            return ("P" if claimC1(short) else "N"), ("C, z1 = 1" if h == W1 else "PC1 with the rule for z1 = 1")
        return None, "PC1 (restricted value)"
    f, t = FT((u, v, y, z))
    return ("P" if f == t else "N"), "PD1"


# ---- options ----

def cuts(h, B1, B0):
    """the t < h of the form (terms of h above exponent k) + w^k*c + L with c < h_k and L < w^k
    whose coefficients are at most B1 (exponents >= 1) and B0 (finite part). Every t < h has
    exactly one such form, so the list is complete up to the bounds."""
    import itertools
    terms = key(h)
    out = []
    for idx, (k, hk) in enumerate(terms):
        prefix = dict(terms[:idx])
        for c in range(hk):
            base = dict(prefix)
            if c:
                base[k] = c
            if k == 0:
                out.append(base)
                continue
            lows = list(range(k - 1, 0, -1))
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


def bite(p, col, k):
    u, v, y, z = p
    if col == 0:
        return (omin(u, k), omin(v, k), omin(y, k), omin(z, k))
    if col == 1:
        return (u, omin(v, k), y, omin(z, k))
    if col == 2:
        return (u, v, omin(y, k), omin(z, k))
    return (u, v, y, omin(z, k))


def options(p, B1, B0):
    """(col, k, position) for the bites at heights k given by cuts(); col 0..3 = (0,0),(0,1),(1,0),(1,1)"""
    for col in range(4):
        for k in cuts(p[col], B1, B0):
            if col == 0 and not k:
                continue
            yield col, k, bite(p, col, k)
