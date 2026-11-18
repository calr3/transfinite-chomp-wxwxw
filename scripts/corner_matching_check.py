#!/usr/bin/env python3
"""Checks for notes/20 on the table of f(q,r) of three-row Chomp.

usage: corner_matching_check.py [N]      (default 600; about 30 s for N = 1500)

Builds f(q,r) for r <= q <= N by the recurrence of Brouwer et al. and checks, for rows
x < 2N/3 (whose partners, if any, are below N):
  * Theorem 1 and Theorem 5: tau(x) >= x+2 for x >= 2, tau(x) >= x+3 for x >= 4;
  * Lemma 4: f(q,2) = q+2;
  * Lemma 6: when x dies at p, every older row alive at p has exactly one level j in (b,p)
    with f(j,b) = p, and the levels are distinct;
  * Corollary 7: #{b < x alive at p} <= I(p), with its least slack;
  * f(a,a) <= 2a for a >= 2;
and reports whether tau is increasing and the first three consecutive diagonal values.
"""
import bisect
import sys


def build(n):
    rowused = [set() for _ in range(n + 1)]
    diag = set()
    tau = [None] * (n + 1)
    picks = [dict() for _ in range(n + 1)]
    d = [0] * (n + 1)
    for r in range(n + 1):
        if r >= 1:
            diag.add(d[r - 1])
        col = set()
        for q in range(r, n + 1):
            v = max(q, 1)
            ru = rowused[q]
            while v in ru or v in col or v in diag:
                v += 1
            picks[r][q] = v
            ru.add(v)
            col.add(v)
            if q == r:
                d[r] = v
            if v == q and q > r:
                tau[r] = q
                for q2 in range(q + 1, n + 1):
                    rowused[q2].add(q)
                break
    return picks, tau, d


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    picks, tau, d = build(n)
    lim = 2 * n // 3
    mortal = [x for x in range(lim) if tau[x] is not None]
    ok = True

    def report(name, cond):
        nonlocal ok
        ok = ok and cond
        print(("ok   " if cond else "FAIL ") + name)

    report("tau(x) >= x+2 for x >= 2", all(tau[x] - x >= 2 for x in mortal if x >= 2))
    report("tau(x) >= x+3 for x >= 4", all(tau[x] - x >= 3 for x in mortal if x >= 4))
    report("f(q,2) = q+2", all(picks[2][q] == q + 2 for q in range(2, n + 1)))
    report("f(a,a) <= 2a for a >= 2", all(d[a] <= 2 * a for a in range(2, n + 1)))

    taus = sorted(tau[x] for x in mortal)
    matching_ok = True
    slack = None
    for x in mortal:
        p = tau[x]
        levels = set()
        alive = 0
        for b in range(x):
            if tau[b] is not None and tau[b] < p:
                continue
            alive += 1
            js = [j for j, v in picks[b].items() if v == p and b < j < p]
            if len(js) != 1 or js[0] in levels:
                matching_ok = False
            levels.update(js)
        dead_by_p = bisect.bisect_right(taus, p)
        s = dead_by_p - alive
        slack = s if slack is None else min(slack, s)
    report("Lemma 6: one level per alive older row, all distinct", matching_ok)
    report("Corollary 7: #alive older rows <= I(tau(x)); least slack %d" % slack, slack >= 0)

    inc = all(tau[mortal[i]] < tau[mortal[i + 1]] for i in range(len(mortal) - 1))
    print("info tau increasing on non-side rows below %d: %s" % (lim, inc))
    ds = set(d)
    triple = next((v for v in range(1, lim) if v in ds and v + 1 in ds and v + 2 in ds), None)
    print("info first three consecutive diagonal values start at:", triple)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
