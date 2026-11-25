#!/usr/bin/env python3
"""How chains of cuts end: statistics over all block positions of one or more census worlds.

usage: chain_survival.py STALKS REPORT ZMAX [STALKS REPORT ZMAX ...]

  STALKS  prefix_stalks.txt of "STALKS=1 base3_table ... -T Z -O prefix"
  REPORT  the standard output of the same run (the positions with every free cell infinite)
  ZMAX    the largest cut height to use (at most Z)

For every position without a P cut of the poison column and for both chains "cut (1,0) at u"
and "cut (0,1) at u", the rows are followed up to the first P member (see chain_matching.py).
A chain is called regular if its diagonal cell is never eligible, that is, no member ever
needs a partner. For the other chains the script prints, by height band: how often the
diagonal cell is eligible, how often no partner is available, and how often the row is a P
member (the chain ends). It also prints how many chains are still alive at each height,
next to the prediction of the law "a chain ends at height u with probability G/u".
"""
import collections
import sys

from chain_matching import INF, chain_rows, load, parse

BANDS = [(5, 9), (10, 19), (20, 39), (40, 69), (70, 99), (100, 10 ** 6)]


def main():
    rows = collections.defaultdict(lambda: [0, 0, 0, 0, 0.0])
    lives = []        # (start height, first P member or None, last height seen)
    nreg = 0
    zmin = min(map(int, sys.argv[3::3]))
    for stalks, report, zmax in zip(sys.argv[1::3], sys.argv[2::3], map(int, sys.argv[3::3])):
        data = load(stalks)
        tops = [parse(l.split("  :")[0].replace("|", " ").split())
                for l in open(report) if l.startswith(" w") and "no P cut" in l]
        for X in tops:
            start = max(5, max(v for v in X if v < INF))
            for (cx, cy) in ((1, 0), (0, 1)):
                rs = [r for r in chain_rows(data, X, cx, cy, zmax, window=60) if r[0] >= start]
                if not rs:
                    continue
                if not any(r[1] in ("partner", "P") for r in rs):
                    nreg += 1
                    continue
                first = rs[-1][0] if rs[-1][1] == "P" else None
                lives.append((start, first, rs[-1][0]))
                for u, state, partner, elig, free, pool in rs:
                    for b in BANDS:
                        if b[0] <= u <= b[1]:
                            r = rows[b]
                            r[0] += 1
                            r[1] += state in ("partner", "P")
                            r[2] += not free
                            r[3] += state == "P"
                            r[4] += 1.0 / u
    print("chains whose diagonal sometimes needs a partner: %d (regular chains left out: %d)" % (len(lives), nreg))
    print("heights    rows  needs a partner  no partner available  chain ends   ends x height")
    ends = wsum = 0
    for b in BANDS:
        r = rows[b]
        if r[0]:
            print("%3d-%-4s %6d  %14.1f%%  %19.1f%%  %4d = %4.1f%%   %.2f"
                  % (b[0], "" if b[1] > 10 ** 5 else b[1], r[0], 100 * r[1] / r[0], 100 * r[2] / r[0], r[3],
                     100 * r[3] / r[0], r[3] / r[4]))
            ends += r[3]
            wsum += r[4]
    G = ends / wsum if wsum else 0.0
    print("fitted law: a row at height u ends its chain with probability G/u, G = %.2f (%d ends)" % (G, ends))
    print("chains alive (no P member up to that height), observed and predicted by the law:")
    for h in (10, 20, 40, 70, 100, 120):
        if h > zmin:
            continue
        # chains that started at or below h and whose fate at h is known
        started = [l for l in lives if l[0] <= h and ((l[1] is not None and l[1] <= h) or l[2] >= h)]
        if not started:
            continue
        obs = sum(1 for l in started if l[1] is None or l[1] > h)
        pred = 0.0
        for l in started:
            p = 1.0
            for u in range(l[0], h + 1):
                p *= max(0.0, 1.0 - G / u)
            pred += p
        print("  height %3d: %4d of %4d alive, predicted %.1f" % (h, obs, len(started), pred))


if __name__ == "__main__":
    main()
