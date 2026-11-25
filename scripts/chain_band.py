#!/usr/bin/env python3
"""Where the eligible cells of a chain sit, and whether the pool of usable columns grows.

usage: chain_band.py STALKS REPORT ZMAX [--chains]

  STALKS, REPORT, ZMAX as for chain_survival.py.

Notation of chain_matching.py: S(u,v) is the position X after cutting the chain cell at u and
(1,1) at v <= u. Three things are measured on every chain whose diagonal sometimes needs a
partner, up to its first P member.

* The life of a column. If S(u,v) has a P cut of the poison column at a height h <= u, the
  position left does not depend on u, so every S(u',v) with u' >= u has the same cut: column
  v is dead from row u on. death(v) is the first such row; death(v) - v is the life of the
  column. Columns that are still alive at ZMAX are counted as censored.
* The pool. In row u the live columns are the v < u with death(v) > u. The script counts the
  live ones, the live ones that no earlier row has taken, and among those the eligible ones
  (the slack of chain_matching.py).
* Persistence. For each chain, the share of rows without a partner in two successive ranges
  of heights. If chains differ durably, the two shares are correlated across chains.
* The pool model. A row with k live unused columns has no partner with probability delta^k,
  and on such a row the diagonal is eligible with probability eps. The script fits both and
  prints the exponent gamma = ln(1/(1-eps)) / ln(1/delta) of the law "alive at height h with
  probability proportional to h^-gamma". (If all candidate cells were independent with the
  same probability q of being eligible, delta = 1 - q = 1 - eps and gamma = 1.)

A world that is symmetric under transposition contains every chain twice (the chain of (1,0)
of X is the chain of (0,1) of the transpose of X). The counts printed here are not halved.

With --chains the per-chain numbers are printed as well.
"""
import collections
import sys

from chain_matching import INF, cell_state, cut, load, parse

BANDS = [(5, 9), (10, 19), (20, 39), (40, 69), (70, 99), (100, 10 ** 6)]


def band_of(u):
    for b in BANDS:
        if b[0] <= u <= b[1]:
            return b
    return None


def analyse(data, X, cx, cy, zmax):
    """Rows of one chain: dict u -> (diag eligible, has partner, live, live unused, slack, isP)."""
    ctag = "(%d,%d)" % (cx, cy)
    death = {}
    used = set()
    rows = {}
    for u in range(zmax + 1):
        Yu = cut(X, cx, cy, u)
        if Yu not in data:
            break
        live = unused = slack = 0
        partner = None
        dist = []
        for v in range(u):
            s = cut(Yu, 1, 1, v)
            h = data[s][0]
            if v not in death and 0 < h <= u:
                death[v] = u
            if v in death:
                continue
            live += 1
            e, f, isP = cell_state(data, s, ctag)
            if e:
                dist.append(u - v)
            if v not in used:
                unused += 1
                if e:
                    slack += 1
            if isP:
                partner = v
        if partner is not None:
            used.add(partner)
        h, isP, opts = data[Yu]
        att = [o for o in opts if o not in (ctag, "(1,1)")]
        diag = (h == 0 and not att)
        rows[u] = (diag, partner is not None, live, unused, slack, bool(isP), dist,
                   None if partner is None else u - partner)
        if isP:
            break
    return rows, death


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    stalks, report, zmax = args[0], args[1], int(args[2])
    data = load(stalks)
    tops = [parse(l.split("  :")[0].replace("|", " ").split())
            for l in open(report) if l.startswith(" w") and "no P cut" in l]
    agg = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0])   # rows, live, unused, slack, nopartner, diag
    life = collections.defaultdict(lambda: [0, 0, 0])            # columns, sum of lives, censored
    lifehist = collections.Counter()
    chains = []
    for X in tops:
        start = max(5, max(v for v in X if v < INF))
        for (cx, cy) in ((1, 0), (0, 1)):
            rows, death = analyse(data, X, cx, cy, zmax)
            rs = {u: r for u, r in rows.items() if u >= start}
            if not rs or not any(r[0] for r in rs.values()):
                continue
            last = max(rows)
            ended = rows[last][5]
            chains.append((X, (cx, cy), start, last, ended, rs))
            for u, r in rs.items():
                b = band_of(u)
                a = agg[b]
                a[0] += 1
                a[1] += r[2]
                a[2] += r[3]
                a[3] += r[4]
                a[4] += not r[1]
                a[5] += r[0]
            for v in range(start, last):
                b = band_of(v)
                if b is None:
                    continue
                if v in death:
                    life[b][0] += 1
                    life[b][1] += death[v] - v
                    lifehist[min(death[v] - v, 30)] += 1
                else:
                    life[b][2] += 1
    print("chains: %d" % len(chains))
    print("rows by height: live columns, live and unused, of those eligible (slack), share of rows without a partner")
    print("heights    rows   live  unused  slack  no partner  diagonal eligible")
    for b in BANDS:
        a = agg[b]
        if a[0]:
            print("%3d-%-4s %6d  %5.2f  %5.2f  %5.2f  %8.1f%%  %8.1f%%"
                  % (b[0], "" if b[1] > 10 ** 5 else b[1], a[0], a[1] / a[0], a[2] / a[0], a[3] / a[0],
                     100 * a[4] / a[0], 100 * a[5] / a[0]))
    print("life of a column (death(v) - v), by the height v of the column:")
    print("heights  columns  mean life  still alive at the end of the data")
    for b in BANDS:
        l = life[b]
        if l[0] + l[2]:
            print("%3d-%-4s %6d  %8.2f  %d" % (b[0], "" if b[1] > 10 ** 5 else b[1], l[0],
                                             l[1] / l[0] if l[0] else 0.0, l[2]))
    print("distribution of the life (30 = 30 or more): "
          + " ".join("%d:%d" % (k, lifehist[k]) for k in sorted(lifehist)))

    # persistence: share of rows without a partner in [10,20) and [20,40), chains alive at 40
    for (lo, mid, hi) in ((10, 20, 40), (20, 40, 70)):
        pts = []
        for X, c, start, last, ended, rs in chains:
            if last < hi or start > lo:
                continue
            a = [not rs[u][1] for u in range(lo, mid)]
            b = [not rs[u][1] for u in range(mid, hi)]
            pts.append((sum(a) / len(a), sum(b) / len(b)))
        if len(pts) >= 3:
            n = len(pts)
            mx = sum(p[0] for p in pts) / n
            my = sum(p[1] for p in pts) / n
            sxx = sum((p[0] - mx) ** 2 for p in pts)
            syy = sum((p[1] - my) ** 2 for p in pts)
            sxy = sum((p[0] - mx) * (p[1] - my) for p in pts)
            r = sxy / (sxx * syy) ** 0.5 if sxx > 0 and syy > 0 else float("nan")
            print("chains alive at %d: %d; share of rows without a partner in %d-%d: %.3f, in %d-%d: %.3f; "
                  "correlation across chains %.2f" % (hi, n, lo, mid - 1, mx, mid, hi - 1, my, r))

    # does the pool at a given height predict the end? rows with the diagonal eligible, by slack
    by_slack = collections.defaultdict(lambda: [0, 0])
    by_unused = collections.defaultdict(lambda: [0, 0])
    for X, c, start, last, ended, rs in chains:
        for u, r in rs.items():
            if u >= 10:
                by_unused[min(r[3], 8)][0] += 1
                by_unused[min(r[3], 8)][1] += not r[1]
    print("rows at height 10 or more, by the number of live unused columns (8 = 8 or more): rows, share without a partner")
    for k in sorted(by_unused):
        n, m = by_unused[k]
        print("  %d: %5d  %5.1f%%" % (k, n, 100.0 * m / n))

    # the pool model: every candidate cell (a live unused column, or the diagonal) is eligible with
    # the same probability q, independently. A row with k live unused columns then has no partner
    # with probability (1-q)^k and ends the chain with probability q(1-q)^k.
    cand = elig = 0
    for X, c, start, last, ended, rs in chains:
        for u, r in rs.items():
            if u >= 10:
                cand += r[3] + 1
                elig += r[4] + r[0]
    q = elig / cand if cand else 0.0
    print("pool model: share of eligible cells among the candidates at height 10 or more: q = %.3f "
          "(live unused columns %.3f, diagonal %.3f)"
          % (q, sum(a[3] for b, a in agg.items() if b[0] >= 10) / max(1, sum(a[2] for b, a in agg.items() if b[0] >= 10)),
             sum(a[5] for b, a in agg.items() if b[0] >= 10) / max(1, sum(a[0] for b, a in agg.items() if b[0] >= 10))))
    model = collections.defaultdict(lambda: [0, 0, 0.0, 0.0, 0])
    for X, c, start, last, ended, rs in chains:
        for u, r in rs.items():
            m = model[band_of(u)]
            m[0] += not r[1]
            m[1] += r[5]
            m[2] += (1 - q) ** r[3]
            m[3] += q * (1 - q) ** r[3]
            m[4] += (not r[1]) and r[0]
    print("heights   rows without a partner: observed, model   chain ends: observed, model   "
          "diagonal eligible among the rows without a partner")
    for b in BANDS:
        m = model[b]
        if agg[b][0]:
            print("%3d-%-4s  %5d  %7.1f   %5d  %7.1f   %s"
                  % (b[0], "" if b[1] > 10 ** 5 else b[1], m[0], m[2], m[1], m[3],
                     ("%d of %d" % (m[4], m[0]))))
    tot = [sum(model[b][i] for b in BANDS if b[0] >= 10) for i in range(5)]
    print("from 10 on  %5d  %7.1f   %5d  %7.1f   %d of %d" % (tot[0], tot[2], tot[1], tot[3], tot[4], tot[0]))

    # two parameters: no partner with probability delta^k (fitted by maximum likelihood on the rows at
    # height 10 or more), and the diagonal eligible with probability eps on a row without a partner.
    # Then the chance to be alive at height h falls like h^-gamma, gamma = ln(1/(1-eps)) / ln(1/delta).
    import math
    obs = [(r[3], not r[1]) for X, c, start, last, ended, rs in chains for u, r in rs.items() if u >= 10 and r[3] >= 1]

    def loglik(d):
        t = 0.0
        for k, nop in obs:
            pk = d ** k
            t += math.log(pk) if nop else math.log(1.0 - pk)
        return t
    if obs and tot[0]:
        delta = max((i / 200.0 for i in range(20, 180)), key=loglik)
        eps = tot[4] / tot[0]
        print("fit: delta = %.3f, eps = %.3f (%d of %d), gamma = %.2f; with independent cells delta would be 1 - q = %.3f"
              % (delta, eps, tot[4], tot[0], math.log(1 / (1 - eps)) / math.log(1 / delta), 1 - q))
        exp_np = collections.defaultdict(float)
        for X, c, start, last, ended, rs in chains:
            for u, r in rs.items():
                exp_np[band_of(u)] += delta ** r[3]
        print("rows without a partner, observed and delta^k: "
              + "; ".join("%d-%s: %d, %.1f" % (b[0], "" if b[1] > 10 ** 5 else b[1], model[b][0], exp_np[b])
                          for b in BANDS if agg[b][0]))

    # how far below the diagonal the eligible cells and the partners sit (rows at height 20 or more)
    de, dp = collections.Counter(), collections.Counter()
    sl = collections.defaultdict(collections.Counter)
    for X, c, start, last, ended, rs in chains:
        for u, r in rs.items():
            if u >= 20:
                for d in r[6]:
                    de[min(d, 20)] += 1
                if r[7] is not None:
                    dp[min(r[7], 20)] += 1
            if u >= 10:
                sl[min(r[3], 8)][r[4]] += 1
    print("distance u - v at height 20 or more (20 = 20 or more): eligible cells "
          + " ".join("%d:%d" % (k, de[k]) for k in sorted(de)))
    print("  partners " + " ".join("%d:%d" % (k, dp[k]) for k in sorted(dp)))
    print("rows at height 10 or more with k live unused columns: how many of the k are eligible, "
          "observed and for independent cells with the same mean")
    for k in sorted(sl):
        if k == 0:
            continue
        n = sum(sl[k].values())
        mean = sum(j * c for j, c in sl[k].items()) / n
        pk = mean / k
        binom = [math.comb(k, j) * pk ** j * (1 - pk) ** (k - j) * n for j in range(k + 1)]
        print("  k = %d (%d rows): " % (k, n)
              + " ".join("%d:%d/%.0f" % (j, sl[k][j], binom[j]) for j in range(k + 1)))

    if "--chains" in sys.argv:
        print("chains alive at 40 or more: position, chain cell, last row, ended; rows without a partner; "
              "mean live unused in 10-39 and from 40")
        for X, c, start, last, ended, rs in chains:
            if last < 40:
                continue
            nop = [u for u in sorted(rs) if not rs[u][1]]
            e1 = [rs[u][3] for u in rs if 10 <= u < 40]
            e2 = [rs[u][3] for u in rs if u >= 40]
            pos = " ".join("w" if v >= INF else str(v) for v in X)
            print("  %s  (%d,%d)  %3d %s  %s  %.2f %.2f"
                  % (pos, c[0], c[1], last, "P" if ended else "-", nop,
                     sum(e1) / max(1, len(e1)), sum(e2) / max(1, len(e2))))


if __name__ == "__main__":
    main()
