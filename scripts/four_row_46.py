#!/usr/bin/env python3
"""Where the table of sides puts a value g, from the death levels written by four_row_values.

usage: four_row_46.py X GM OUT [g] [A0]

X, GM and OUT are those of the run `four_row_values X GM T 0 OUT`. The script recomputes the
values of the sides (x,y) under the assumption that no row alive at the end dies later, and
reports for the value g (default GM) and the rows a >= A0 (default 150) of that table:
  * the rows that do not contain g, and how far below the diagonal g sits in the others;
  * the number of free columns (columns within 60 of the diagonal that do not yet hold g);
  * how many of them are usable, i.e. have a living row (a,y,g);
  * the rows with no usable column, and whether the diagonal row (a,a,g) is alive.
The diagonal side (a,a) gets the value g iff no column is usable and the diagonal row lives.
Once a diagonal side has the value g, no later side can have it, so the statistics stop there.
"""
import collections
import sys

import numpy as np


def main():
    X, GM, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    G = int(sys.argv[4]) if len(sys.argv) > 4 else GM
    A0 = int(sys.argv[5]) if len(sys.argv) > 5 else 150
    d = np.fromfile(fn, dtype=np.int32).reshape(-1, GM)

    def si(x, y):
        return x * (x + 1) // 2 + y

    diagused = np.zeros(GM + 2, bool)
    colused = np.zeros((X + 1, GM + 2), bool)
    usedby = {}
    offsets = collections.Counter()
    missing, zero, pools, usable_hist = [], [], [], collections.Counter()
    diag_hits = []
    for x in range(X + 1):
        rowused = np.zeros(GM + 2, bool)
        usable = 0
        placed = None
        for y in range(x + 1):
            if x == y:
                colused[y] = diagused
            alive = d[si(x, y), G - 1] == -1
            if y < x and y >= x - 60 and alive and not colused[y][G]:
                usable += 1
            seen = rowused | colused[y]
            seen[1:GM + 1] |= d[si(x, y)] != -1
            seen[0] = True
            nz = np.flatnonzero(~seen[:GM + 1])
            v = int(nz[0]) if len(nz) else GM + 1
            if v <= GM:
                rowused[v] = True
                colused[y][v] = True
                if x == y:
                    diagused[v] = True
            if v == G:
                placed = y
                usedby[y] = x
        if placed == x:
            diag_hits.append(x)
        if x >= A0 and (not diag_hits or x <= diag_hits[0]):
            free = sum(1 for y in range(x - 60, x) if y not in usedby or usedby[y] == x)
            pools.append((x, free))
            usable_hist[usable] += 1
            if placed is None:
                missing.append(x)
            elif placed < x:
                offsets[x - placed] += 1
            if usable == 0:
                zero.append((x, bool(d[si(x, x), G - 1] == -1)))
    last = diag_hits[0] if diag_hits else X
    print("value %d, rows %d..%d" % (G, A0, last))
    print("diagonal side with this value:", diag_hits[0] if diag_hits else None)
    print("rows without the value:", missing)
    print("distance below the diagonal, histogram:", sorted(offsets.items()))
    changes = [pools[0]] + [pools[i] for i in range(1, len(pools)) if pools[i][1] != pools[i - 1][1]]
    print("free columns (row from which the count holds, count):", changes)
    print("usable columns per row, histogram:", sorted(usable_hist.items()))
    tot = sum(usable_hist.values())
    print("mean usable: %.2f" % (sum(k * c for k, c in usable_hist.items()) / tot))
    print("rows with no usable column (row, diagonal row alive):", zero)


if __name__ == "__main__":
    main()
