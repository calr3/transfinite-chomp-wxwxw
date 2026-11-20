#!/usr/bin/env python3
"""The matching lemma (notes/20, Lemma 6) in the cube family of three-row Chomp.

usage: cube_matching_check.py [N]      (default 600; about 25 s for N = 1200)

[p,q,r | cube] is P iff the three-row position [p,q,r] has restricted Grundy value 1. The table
f1 of this family obeys the recurrence of Brouwer et al. with one more blocked value per cell,
the 2D value f0(q,r). The script
  * compares both tables with brute-force Grundy values for rows up to 15;
  * checks, for every row x that dies at p = tau1(x) and every older row b alive at p, that
    b has exactly one level j in (b,p) with f1(j,b) = p, or tau0(b) = p (the cube-removal
    option), and that the levels are distinct;
  * lists the rows that survive a time p only because of the cube block ("free passes").
"""
import collections
import sys
from functools import lru_cache


def build(n, extra=None):
    rowused = [set() for _ in range(n + 1)]
    diag = set()
    tau = [None] * (n + 1)
    picks = [dict() for _ in range(n + 1)]
    d = [0] * (n + 1)
    for r in range(n + 1):
        if r >= 1:
            diag.add(d[r - 1])
        col = set()
        ex = extra[r] if extra is not None else {}
        for q in range(r, n + 1):
            v = max(q, 1)
            ru = rowused[q]
            e = ex.get(q)
            while v in ru or v in col or v in diag or v == e:
                v += 1
            picks[r][q] = v
            ru.add(v)
            col.add(v)
            if q == r:
                d[r] = v
            if v == q and q > r:
                tau[r] = q
                break
    return picks, tau, d


def brute_mismatches(p0, t0, p1, t1, m=16):
    @lru_cache(maxsize=None)
    def g(p, q, r):
        s = set()
        for j in range(1, p):
            s.add(g(j, min(q, j), min(r, j)))
        for j in range(0, q):
            s.add(g(p, j, min(r, j)))
        for j in range(0, r):
            s.add(g(p, q, j))
        v = 0
        while v in s:
            v += 1
        return v

    bad = 0
    for r in range(m):
        for q in range(r, m):
            for p in range(max(q, 1), m):
                val = g(p, q, r)
                e0 = p0[r].get(q) == p
                e1 = p1[r].get(q) == p
                if (val == 0) != e0 or (val == 1) != e1:
                    bad += 1
    return bad


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    p0, t0, d0 = build(n)
    p1, t1, d1 = build(n, p0)
    print("brute-force mismatches (rows < 16):", brute_mismatches(p0, t0, p1, t1))
    lim = int(n / 2.1)
    mortal = [x for x in range(lim) if t1[x] is not None]
    print("rows <", lim, "; with a partner:", len(mortal), "; without:", lim - len(mortal))
    inv1 = [{v: q for q, v in p1[b].items()} for b in range(n + 1)]
    diag1 = {d1[a]: a for a in range(n + 1)}
    partner1 = {t1[x]: x for x in range(n + 1) if t1[x] is not None}

    cnt = collections.Counter()
    for x in mortal:
        p = t1[x]
        levels = set()
        for b in range(x):
            if t1[b] is not None and t1[b] < p:
                continue
            j = inv1[b].get(p)
            has = j is not None and b < j < p
            cube = t0[b] == p
            cnt["level only" if has and not cube else
                "level and cube" if has else
                "cube only" if cube else "NEITHER"] += 1
            if has:
                if j in levels:
                    cnt["LEVEL CLASH"] += 1
                levels.add(j)
    print("older rows alive at a death time:", dict(cnt))
    ok = cnt["NEITHER"] == 0 and cnt["LEVEL CLASH"] == 0
    print(("ok   " if ok else "FAIL ") + "matching lemma with the cube exception")

    fates = []
    for b in range(lim):
        p = t0[b]
        if p is None or (t1[b] is not None and t1[b] <= p):
            continue
        j = inv1[b].get(p)
        if j is not None and j < p:
            continue
        if (p in diag1 and diag1[p] < b) or (p in partner1 and partner1[p] < b):
            continue
        fates.append((b, p, t1[b]))
    print("free passes (row, time, later partner or None):", fates)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
