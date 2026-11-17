#!/usr/bin/env python3
"""Does Huddleston-Shurman's proof of criterion (10-1) prescribe the right reply?

For a three-column position (u, v, x) with omega <= x < omega^omega that (10-1) calls N, their
proof (section 10) names the kind of winning bite:
  case "=" : G(Ub) = G(Xb), tops do not cancel -> a bite into exactly one top component;
  case "<" : G(Ub) < G(Xb)                    -> a bite (2, z) touching Xb (z < w^i x_i);
  case ">" : G(Ub) > G(Xb)                    -> a bite (0, z) touching Ub but not Xb.
For each random N-position this script searches (with the bounds of hs_check2) for a P reply of
the prescribed kind, and separately for any P reply. A position with a P reply but none of the
prescribed kind is a gap in the written proof, not in the criterion.

usage: hs_proofcheck.py [SAMPLES] [MAXDEG] [SEED] [B1] [B0]
"""
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import hs_check2 as C  # noqa: E402  (installs the exact side class and finite tables)
import hs_oracle as H  # noqa: E402


def decomp(cols):
    """(case name, G(Ub), G(Xb), top value, i, height of Ub's columns, height of Xb)"""
    u, v, x = cols
    i = H.deg(x)
    xi, c = H.lead(x), H.low(x, i)
    uh, ui, a = H.high(u, i + 1), H.coef(u, i), H.low(u, i)
    vh, vi, b = H.high(v, i + 1), H.coef(v, i), H.low(v, i)
    oxi = H.O((i, xi))
    if not uh and not vh and ui == vi == xi:
        return "i", H.G2(H.O((i, ui)), H.O((i, ui))), oxi, None, i
    if not vh and vi == xi and (uh or ui > vi):
        return "ii", H.G2(H.nat_add(uh, H.O((i, ui))), H.O((i, vi))), oxi, H.nim(a, H.G2(b, c)), i
    if uh and uh == vh and ui == vi:
        return "iii", H.G2(uh, uh), oxi, H.nim(H.G2(H.nat_add(H.O((i, ui)), a), H.nat_add(H.O((i, vi)), b)), c), i
    return "iv", H.G2(H.nat_add(uh, H.O((i, ui))), H.nat_add(vh, H.O((i, vi)))), oxi, H.nim(H.nim(a, b), c), i


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    maxdeg = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    B1 = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    B0 = int(sys.argv[5]) if len(sys.argv) > 5 else 600
    C.FIN = C.Finite3(300, 40)
    H.P3_finite = C.is_P3_finite
    stats = {}
    seen = set()
    t0 = time.time()
    n = 0
    while n < samples:
        cols = C.rand_pos(maxdeg, rng)
        if len(cols) < 3 or H.deg(cols[2]) < 1:
            continue
        k = tuple(H.key(c) for c in cols)
        if k in seen:
            continue
        seen.add(k)
        n += 1
        if H.is_P(cols):
            continue
        case, gu, gx, top, i = decomp(cols)
        rel = "=" if gu == gx else ("<" if H.cmp(gu, gx) < 0 else ">")
        xb = H.O((i, H.lead(cols[2])))
        any_hit, pres_hit = None, None
        for j, t, o in C.options(cols, B1, B0):
            if not H.is_P(o):
                continue
            if any_hit is None:
                any_hit = (j, t)
            if rel == "<":
                ok = j == 2 and H.cmp(t, xb) < 0
            elif rel == ">":
                ok = j == 0 and H.cmp(t, xb) >= 0
            else:
                # a bite into one top component leaves both bottoms: compare the decompositions
                ok = len(o) == 3 and H.deg(o[2]) == i and H.lead(o[2]) == H.lead(cols[2]) and \
                    decomp(o)[0] == case and decomp(o)[1] == gu
            if ok:
                pres_hit = (j, t)
                break
        key = (case, rel)
        s = stats.setdefault(key, [0, 0, 0])
        s[0] += 1
        if pres_hit:
            s[1] += 1
        elif any_hit:
            s[2] += 1
            print("other reply only:", [H.show(c) for c in cols], "case", case, rel,
                  "G(Ub)=%s G(Xb)=%s" % (H.show(gu), H.show(gx)), "reply: bite", any_hit[0], H.show(any_hit[1]), flush=True)
        else:
            print("NO REPLY FOUND:", [H.show(c) for c in cols], "case", case, rel, flush=True)
    for key in sorted(stats):
        s = stats[key]
        print("case %-3s G(Ub) %s G(Xb): %4d N-positions, %4d with the prescribed reply, %d with another reply only"
              % (key[0], key[1], s[0], s[1], s[2]))
    print("%.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
