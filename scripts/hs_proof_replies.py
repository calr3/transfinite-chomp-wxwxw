#!/usr/bin/env python3
"""The constructive half of the proof of the three-wide criterion in notes/16: for a position
(u, v, x), omega <= x < omega^omega, that is not in the families A, B, the proof names a move
to a member (or to a Side-Top P-position). This script implements exactly those moves and checks
with the oracle (tools/hs_oracle.py) that each named option is P. It also checks the families
against the oracle, and that every family member has no option in the families (sampled).

Ordinals u, v may be large (u, v < omega^D for D up to 7), so that U = u / omega^(i+1) can be
infinite.

usage (from the repository root): hs_proof_replies.py [SAMPLES] [SEED]
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_check2 as C  # noqa: E402
import hs_oracle as H  # noqa: E402
from hs_tall_box import inv_G2_equal  # noqa: E402

O, add, nim, G2 = H.O, H.nat_add, H.nim, H.G2


def split(h, i):
    """h = w^(i+1) * Q + w^i * h_i + rest: returns (Q as {exp - (i+1): coef}, h_i, rest)"""
    Q = {e - (i + 1): c for e, c in h.items() if e >= i + 1}
    return Q, h.get(i, 0), H.low(h, i)


def times_w(Q, i):
    """w^(i+1) * Q for Q given as returned by split"""
    return {e + i + 1: c for e, c in Q.items()}


def family(u, v, x):
    i = H.deg(x)
    xi, c = H.lead(x), H.low(x, i)
    U, ui, a = split(u, i)
    V, vi, b = split(v, i)
    if U != V or H.deg(U) > 0:
        return None
    m = U.get(0, 0)
    if m == 0:
        if ui != vi + xi:
            return None
        return "A" if (a == G2(b, c) if vi == xi else not nim(nim(a, b), c)) else None
    if xi != m + ui - vi:
        return None
    if ui == vi:
        return "B" if c == G2(add(O((i, ui)), a), add(O((i, vi)), b)) else None
    return "B" if not nim(nim(a, b), c) else None


def nim_fix(vals):
    """vals = [a, b, c] with nonzero nim-sum s: (index k, new value) with vals[k] ^ s < vals[k]"""
    s = nim(nim(vals[0], vals[1]), vals[2])
    e = H.deg(s)
    bit = 1 << (s[e].bit_length() - 1)
    for k, t in enumerate(vals):
        if t.get(e, 0) & bit:
            return k, nim(t, s)
    raise AssertionError


def option_with_value(h, k, target):
    """an option of the two-column position (h, k) with value target: ('col0', s) or ('col1', s).
    It exists whenever target < G(h, k) (mex); the search widens until it is found."""
    for B1, B0 in ((6, 200), (12, 3000), (40, 20000)):
        for s in C.cands(h, B1, B0):
            if G2(s, s if H.cmp(k, s) > 0 else k) == target:
                return "col0", s
        for s in C.cands(k, B1, B0) if k else []:
            if G2(h, s) == target:
                return "col1", s
    raise AssertionError("no option of value %s found for (%s, %s)" % (H.show(target), H.show(h), H.show(k)))


def reply(u, v, x):
    """(column, height) of the move named in the proof, for (u, v, x) not in the families"""
    i = H.deg(x)
    xi, c = H.lead(x), H.low(x, i)
    U, ui, a = split(u, i)
    V, vi, b = split(v, i)
    wi = lambda k: O((i, k))  # noqa: E731
    Vfin = H.deg(V) <= 0
    m = V.get(0, 0) if Vfin else None

    def both_down(mm):  # cut column 0 to t with t / w^(i+1) = mm and G(t', t') = c: Y = (t, t, x)
        return 0, add(times_w(O(mm), i), inv_G2_equal(c))

    def equal_branch(mm):  # x_i = mm = m >= 1: reply via the position Q = (w^i(v_i+1), w^i v_i + b)
        h, k = O((i, vi + 1)), add(wi(vi), b)
        kind, s = option_with_value(h, k, c)
        if kind == "col0":
            return 0, add(times_w(O(mm), i), s)
        raise AssertionError("value only on column 1")

    if not (U == V and Vfin):
        if Vfin and m == 0:  # Ib, V = 0: family A
            top = G2(b, c) if vi == xi else nim(b, c)
            return 0, add(wi(vi + xi), top)
        if Vfin and H.cmp(U, V) > 0:  # Ib, V = m >= 1 finite
            if xi > m:
                return 0, add(add(times_w(O(m), i), wi(vi + xi - m)), nim(b, c))
            if xi == m:
                return equal_branch(m)
            return both_down(xi)
        return both_down(xi)  # V infinite (Ia, or U > V infinite)
    if m == 0:
        if ui > vi + xi:
            top = G2(b, c) if vi == xi else nim(b, c)
            return 0, add(wi(vi + xi), top)
        if ui < vi + xi:
            if ui > vi:
                return 2, add(wi(ui - vi), nim(a, b))
            # u_i = v_i: drop the degree of the third column
            if i >= 2:
                ai, bi = a.get(i - 1, 0), b.get(i - 1, 0)
                at, bt = H.low(a, i - 1), H.low(b, i - 1)
                top = G2(add(O((i - 1, ai)), at), add(O((i - 1, bi)), bt)) if ai == bi else nim(at, bt)
                return 2, add(O((i - 1, ui + ai - bi)), top)
            T = G2(H.omega_left_sub(u), H.omega_left_sub(v))
            return 2, O(C.SIDE_LIST[H.val(T)])  # the side element of index T
        # top fails, family A
        if vi == xi:
            g = G2(b, c)
            if H.cmp(a, g) > 0:
                return 0, add(wi(ui), g)
            kind, s = option_with_value(b, c, a)
            return (1, add(wi(vi), s)) if kind == "col0" else (2, add(wi(xi), s))
        k, new = nim_fix([a, b, c])
        return k, add(wi([ui, vi, xi][k]), new)
    # m >= 1
    if xi > m + ui - vi:
        top = G2(add(wi(ui), a), add(wi(vi), b)) if ui == vi else nim(a, b)
        return 2, add(wi(m + ui - vi), top)
    if xi < m + ui - vi:
        if xi > m:
            return 0, add(add(times_w(O(m), i), wi(vi + xi - m)), nim(b, c))
        if xi == m:
            return equal_branch(m)
        return both_down(xi)
    hi = times_w(O(m), i)
    if ui == vi:
        g = G2(add(wi(ui), a), add(wi(vi), b))
        if H.cmp(c, g) > 0:
            return 2, add(wi(xi), g)
        kind, s = option_with_value(add(wi(ui), a), add(wi(vi), b), c)
        return (0, add(hi, s)) if kind == "col0" else (1, add(hi, s))
    k, new = nim_fix([a, b, c])
    return k, add(add(hi if k < 2 else {}, wi([ui, vi, xi][k])), new)


def apply(cols, j, t):
    c = [dict(x) for x in cols]
    for jj in range(j, 3):
        if H.cmp(c[jj], t) > 0:
            c[jj] = dict(t)
    return c


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 11)
    C.FIN = C.Finite3(300, 40)
    H.P3_finite = C.is_P3_finite

    def ro(lo, hi_):
        return {e: rng.randint(1, 4 if e else 12) for e in range(hi_, lo - 1, -1) if rng.random() < 0.6}

    stats = {"N, named reply P": 0, "family mismatch": 0, "BAD reply": 0, "P": 0}
    n = 0
    while n < samples:
        i = rng.randint(1, 3)
        x = add(O((i, rng.randint(1, 4))), ro(0, i - 1))
        D = rng.choice([i, i + 1, i + 1, i + 2, i + 4])
        u = add(ro(i, D), {})
        v = add(ro(i, D), {})
        if rng.random() < 0.5:
            v = {e: cc for e, cc in u.items() if e >= i + 1}
            v[i] = rng.randint(0, 5)
            v = {e: cc for e, cc in v.items() if cc}
            v = add(v, ro(0, i - 1))
        if rng.random() < 0.3:  # bottom relations of the families
            Q, ui, a = split(u, i)
            u = add(add(times_w(Q, i), O((i, max(v.get(i, 0) + x[i] - (Q.get(0, 0) if H.deg(Q) <= 0 else 0), 0)))), a)
        u, v, x = sorted([u, v, x], key=H.key, reverse=True)
        if H.deg(x) < 1 or not v:
            continue
        n += 1
        cols = [u, v, x]
        p = H.is_P(cols) if H.deg(u) < 30 else None
        f = family(u, v, x)
        if p is not None and p != (f is not None):
            stats["family mismatch"] += 1
            print("FAMILY MISMATCH", [H.show(t) for t in cols], p, f, flush=True)
            continue
        if f is not None:
            stats["P"] += 1
            continue
        j, t = reply(u, v, x)
        Y = [y for y in apply(cols, j, t) if y]
        if H.cmp(t, cols[j]) >= 0 or not H.is_P(Y):
            stats["BAD reply"] += 1
            print("BAD REPLY", [H.show(s) for s in cols], "->", j, H.show(t), [H.show(s) for s in Y], flush=True)
        else:
            stats["N, named reply P"] += 1
    print(stats)


if __name__ == "__main__":
    main()
