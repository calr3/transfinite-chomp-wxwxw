#!/usr/bin/env python3
"""The matching behind a chain of cuts, read off a census dump.

usage: chain_matching.py STALKS_FILE "POSITION" CELL [ZMAX] [--grid W | --pool]

  STALKS_FILE  prefix_stalks.txt of "STALKS=1 base3_table ... -T Z -O prefix"
  POSITION     nine entries, w = omega, for example "w w 2 | w w 2 | 2 2 0"
  CELL         the infinite column that is cut: 1,0 or 0,1 (the other one stays infinite)
  --grid W     draw the W cells below the diagonal of every row
  --pool       per row: the number of unused columns among the last 40 and the slack

Let X be the position and c the cell. Write S(u,v) for X after cutting c at u and then (1,1)
at v <= u. S(u,u) is the chain member "cut c at u". S(u,v) has two infinite columns, and

  S(u,v) is P  iff  it is eligible, its column is free and its row is free, where
    eligible:    no P cut of the poison column, and no P option by a bite in an attachment
    column free: no S(t,v) with v <= t < u is P, and no chain member S(t,t) with t < v is P
    row free:    no S(u,t) with t < v is P.

So row u takes the smallest v < u that is eligible with a free column (its "partner"). The
first P chain member is S(u,u) for the first u where the diagonal cell is eligible and no
partner is available. The number of unused columns grows by exactly one at every row without
a partner. The script prints, for every row: the state of the diagonal cell, the partner, the
eligible cells and how many of them have a free column (the slack).

The dump comes from the census, so everything here holds up to its two truncations.
"""
import sys

INF = 10 ** 6
CELLS = [(x, y) for x in range(3) for y in range(3)]


def parse(tokens):
    return tuple(INF if t == "w" else int(t) for t in tokens)


def load(fn):
    data = {}
    for line in open(fn):
        if line.startswith("#"):
            continue
        t = line.replace("|", " ").split()
        data[parse(t[:9])] = (int(t[9]), int(t[10]), t[11:])
    return data


def cut(pos, cx, cy, z):
    return tuple(min(v, z) if (x >= cx and y >= cy) else v for (x, y), v in zip(CELLS, pos))


def cell_state(data, s, ctag):
    """(eligible, column free, labelled P) of a position with two infinite columns."""
    h, isP, opts = data[s]
    att = [o for o in opts if o not in (ctag, "(1,1)")]
    return (h == 0 and not att), (ctag not in opts), bool(isP)


def chain_rows(data, X, cx, cy, zmax, window=None):
    """Rows of the chain up to its first P member: (u, diagonal state, partner, eligible, free, pool)."""
    ctag = "(%d,%d)" % (cx, cy)
    rows = []
    for u in range(zmax + 1):
        Yu = cut(X, cx, cy, u)
        if Yu not in data:
            break
        elig, free, partner, pool = [], [], None, 0
        for v in range(0 if window is None else max(0, u - window), u):
            e, f, isP = cell_state(data, cut(Yu, 1, 1, v), ctag)
            pool += f
            if e:
                elig.append(v)
                if f:
                    free.append(v)
            if isP:
                partner = v
        h, isP, opts = data[Yu]
        att = [o for o in opts if o not in (ctag, "(1,1)")]
        if isP:
            state = "P"
        elif h:
            state = "cut %d" % h
        elif att:
            state = "blocked " + ",".join(att)
        elif "(1,1)" in opts:
            state = "partner"
        else:
            state = "option " + ",".join(opts)
        rows.append((u, state, partner, elig, free, pool))
        if isP:
            break
    return rows


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    fn, postxt, cell = args[:3]
    zmax = int(args[3]) if len(args) > 3 else 10 ** 9
    data = load(fn)
    X = parse(postxt.replace("|", " ").split())
    cx, cy = map(int, cell.split(","))
    ctag = "(%d,%d)" % (cx, cy)
    print("# %s, chain: cut (%d,%d) at u" % (postxt, cx, cy))
    if "--grid" in sys.argv:
        W = int(sys.argv[sys.argv.index("--grid") + 1])
        print("# row u: the cells v = u-%d .. u-1, then the diagonal cell. P partner, E eligible and free,\n"
              "# e eligible but column used, c finite P cut, b blocked by a P-position with a smaller attachment;\n"
              "# diagonal: P chain member, p has a partner, c finite P cut, b blocked" % W)
        for u in range(zmax + 1):
            Yu = cut(X, cx, cy, u)
            if Yu not in data:
                break
            out = []
            for v in range(max(0, u - W), u):
                s = cut(Yu, 1, 1, v)
                e, f, isP = cell_state(data, s, ctag)
                out.append("P" if isP else "c" if data[s][0] else "b" if not e else "E" if f else "e")
            e, f, isP = cell_state(data, Yu, ctag)
            d = "P" if isP else "c" if data[Yu][0] else "b" if not e else "p"
            print("%3d  %s %s" % (u, "".join(out).rjust(W), d))
            if isP:
                break
        return
    if "--pool" in sys.argv:
        rows = chain_rows(data, X, cx, cy, zmax, window=40)
        print("# u:pool/slack   pool = unused columns among the last 40, slack = those eligible in this row")
        print(" ".join("%d:%d/%d" % (r[0], r[5], len(r[4])) for r in rows))
        return
    rows = chain_rows(data, X, cx, cy, zmax)
    print("# u  diagonal        partner  slack  eligible v (free ones marked *)")
    for u, state, partner, elig, free, pool in rows:
        fs = set(free)
        cells = " ".join(("%d*" % v) if v in fs else str(v) for v in elig[-12:])
        print("%3d  %-14s  %-7s  %-5d  %s%s" % (u, state, "-" if partner is None else partner, len(free),
                                              "... " if len(elig) > 12 else "", cells))
    need = [r for r in rows if r[1] in ("partner", "P")]
    first = rows[-1][0] if rows and rows[-1][1] == "P" else None
    print("# rows: %d; diagonal has a finite cut: %d; needs a partner: %d; first P member: %s"
          % (len(rows), sum(1 for r in rows if r[1].startswith("cut")), len(need), first))
    sl = [len(r[4]) for r in need]
    if sl:
        print("# slack on the rows that need a partner: min %d, mean %.2f, max %d" % (min(sl), sum(sl) / len(sl), max(sl)))


if __name__ == "__main__":
    main()
