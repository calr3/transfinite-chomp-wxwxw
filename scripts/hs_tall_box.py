#!/usr/bin/env python3
"""Huddleston-Shurman's proof that the tall box 3 x w^w is P (section 10, last part): for
every bite (e, z), z < w^w, they name an answering bite that leaves a P-position. This script
computes their named reply for every z < w^(D+1) with coefficients <= C and finite part <= F,
and checks with the oracle (tools/hs_oracle.py, exact side class from data/side-class) that
the reply really is P.

  e = 2 (third column cut to z):  reply (0,u), leaving (u, u, z);
     z finite, z not in S: u = tau(z);  z in S: u = w + a with G(2 x a) = G_S(z);
     z = w^i x_i + c (i >= 1):        u = w^(i+1) x_i + a with G(2 x a) = c.
  e = 1 (last two columns cut to z): reply (0,u), leaving (u, z, z);
     z finite: the finite u with [u,z,z] P;  z = w^i x_i + c: u = w^i 2x_i + G(2 x c).
  e = 0 (rectangle 3 x z):
     z finite: some finite P option (Sheiner: exactly one);
     w <= z < w^2, z = w(n+1) + c: reply (2,x), x finite with G_S(x) = G(2 x (w n + c));
     z = w^(i+1) z_{i+1} + c (i >= 1, c < w^(i+1)): reply (2,x), x = w^i z_{i+1} + G(2 x c).

G(2 x a) is the two-column value G2(a, a). "a with G(2 x a) = c" is solved by inverting the
formulas (9-1), (9-2), (9-4).

usage: hs_tall_box.py [D] [C] [F]
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_check2 as C2  # noqa: E402  (exact side class, finite tables)
import hs_oracle as H  # noqa: E402


def inv_G2_equal(c):
    """the ordinal a with G2(a, a) = c (c < w^w), or None. G2(a,a) for a = w^i u + a' (i >= 2)
    is w^(i-1) u + G2(a',a'); for a = w u + a0 it is 3^u G2(a0,a0) + (3^u - 1)/2; finite:
    (3a+1)//2."""
    if H.is_zero(c):
        return {}
    i = H.deg(c)
    if i >= 1:
        rest = inv_G2_equal(H.low(c, i))
        if rest is None or H.deg(rest) >= i + 1:
            return None
        return H.nat_add(H.O((i + 1, H.lead(c))), rest)
    n = H.val(c)
    k = 0
    while n % 3 == 1:  # n = 3^k m + (3^k - 1)/2 with m != 1 (mod 3)
        n = (n - 1) // 3
        k += 1
    if n % 3 == 1:
        return None
    a0 = next(a for a in range(n + 1) if (3 * a + 1) // 2 == n)
    a = H.O((1, k)) if k else {}
    return H.nat_add(a, H.O(a0))


def ords(D, Cmax, F):
    for cs in itertools.product(range(Cmax + 1), repeat=D):
        for f in range(F + 1):
            z = {e: c for e, c in zip(range(D, 0, -1), cs) if c}
            if f:
                z[0] = f
            if z:
                yield z


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    Cmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    F = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    C2.FIN = C2.Finite3(300, 40)
    H.P3_finite = C2.is_P3_finite
    # check the inversion against G2
    for z in ords(3, 3, 40):
        a = inv_G2_equal(z)
        assert a is not None and H.G2(a, a) == z, (H.show(z), a)
    ok = {0: 0, 1: 0, 2: 0}
    bad = 0
    for z in ords(D, Cmax, F):
        # e = 2
        if H.finite(z):
            x = H.val(z)
            if x in C2.TAU:
                rep = [H.O(C2.TAU[x]), H.O(C2.TAU[x]), z]
            else:
                a = inv_G2_equal(H.O(C2.G_side(x)))
                u = H.nat_add(H.O((1, 1)), a)
                rep = [u, u, z]
        else:
            i = H.deg(z)
            a = inv_G2_equal(H.low(z, i))
            u = H.nat_add(H.O((i + 1, H.lead(z))), a)
            rep = [u, u, z]
        if H.is_P(rep):
            ok[2] += 1
        else:
            bad += 1
            print("e=2 z=%s: named reply %s is not P" % (H.show(z), [H.show(c) for c in rep]))
        # e = 1
        if H.finite(z):
            x = H.val(z)
            u = C2.FIN.A[x][x] if x <= 40 else None
            rep = [H.O(u), z, z] if u is not None else None
        else:
            i = H.deg(z)
            u = H.nat_add(H.O((i, 2 * H.lead(z))), H.G2(H.low(z, i), H.low(z, i)))
            rep = [u, z, z]
        if rep is not None:
            if H.is_P(rep):
                ok[1] += 1
            else:
                bad += 1
                print("e=1 z=%s: named reply %s is not P" % (H.show(z), [H.show(c) for c in rep]))
        # e = 0
        if H.finite(z):
            continue  # finite rectangles: N by strategy stealing
        if H.deg(z) == 1:
            n1, c = H.lead(z), H.low(z, 1)
            g = H.G2(H.nat_add(H.O((1, n1 - 1)), c), H.nat_add(H.O((1, n1 - 1)), c))
            gv = H.val(g)
            x = C2.SIDE_LIST[gv]
            rep = [z, z, H.O(x)]
        else:
            i = H.deg(z) - 1
            c = H.low(z, i + 1)
            x = H.nat_add(H.O((i, H.lead(z))), H.G2(c, c))
            rep = [z, z, x]
        if H.is_P(rep):
            ok[0] += 1
        else:
            bad += 1
            print("e=0 z=%s: named reply %s is not P" % (H.show(z), [H.show(c) for c in rep]))
    print("bites (e,z), z < w^%d, coefficients <= %d, finite part <= %d: named replies P: e=2 %d, e=1 %d, e=0 %d; failures %d"
          % (D + 1, Cmax, F, ok[2], ok[1], ok[0], bad))


if __name__ == "__main__":
    main()
