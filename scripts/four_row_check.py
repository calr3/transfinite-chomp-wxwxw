#!/usr/bin/env python3
"""Check of the four-row recurrence of notes/23 (tools/four_row_values.cpp).

usage: four_row_check.py X GM T [BINARY]

Runs the recurrence for the rows (x,y,g), y <= x <= X, g <= GM, up to level T in plain Python,
compares it with brute-force unrestricted Grundy values of all positions [a,b,x,y] with a <= 8,
prints the values of (omega,omega,x,y) that result if no row alive at level T dies later, and,
if BINARY (the compiled four_row_values) is given, compares the death levels row by row.
A row (x,y,g) takes at level b >= x the value A = the a >= b with G[a,b,x,y] = g; it dies at
level b if A = b.
"""
import struct
import subprocess
import sys
import tempfile
from functools import lru_cache


def run(X, GM, T):
    pick, death = {}, {}
    rows = [(x, y, g) for x in range(X + 1) for y in range(x + 1) for g in range(1, GM + 1)]
    for r in rows:
        pick[r] = {}
        death[r] = None                    # None alive, -1 stillborn, else the level of death
    for b in range(0, T + 1):
        for (x, y, g) in rows:             # older rows first
            if x > b:
                continue
            r = (x, y, g)
            if b == x and any(death[(j, min(y, j), g)] == j for j in range(1, x)):
                death[r] = -1
            if death[r] is not None:
                continue
            blocked = set(pick[r].values())
            for j in range(0, x):
                t = (j, min(y, j), g)
                for lvl in (j, b):         # its birth value, and its value at this level
                    v = pick[t].get(lvl)
                    if v is not None:
                        blocked.add(v)
            for j in range(0, y):
                v = pick[(x, j, g)].get(b)
                if v is not None:
                    blocked.add(v)
            for g2 in range(1, g):
                v = pick[(x, y, g2)].get(b)
                if v is not None:
                    blocked.add(v)
            a = max(b, 1)
            while a in blocked:
                a += 1
            pick[r][b] = a
            if a == b:
                death[r] = b
    return pick, death


def brute():
    @lru_cache(maxsize=None)
    def G(a, b, x, y):
        if a == 0:
            return 0
        s = {0}                            # taking the poison
        for j in range(1, a):
            s.add(G(j, min(b, j), min(x, j), min(y, j)))
        for j in range(0, b):
            s.add(G(a, j, min(x, j), min(y, j)))
        for j in range(0, x):
            s.add(G(a, b, j, min(y, j)))
        for j in range(0, y):
            s.add(G(a, b, x, j))
        v = 0
        while v in s:
            v += 1
        return v
    return G


def main():
    X, GM, T = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    pick, death = run(X, GM, T)
    ok = True
    G = brute()
    m = 9
    bad = tot = 0
    for x in range(min(X, m - 1) + 1):
        for y in range(x + 1):
            for b in range(x, m):
                for a in range(max(b, 1), m):
                    g = G(a, b, x, y)
                    tot += 1
                    if g <= GM and pick[(x, y, g)].get(b) != a:
                        bad += 1
    print("brute force: %d positions, %d mismatches" % (tot, bad))
    ok = ok and bad == 0
    gv = {}
    for x in range(X + 1):
        for y in range(x + 1):
            s = {gv[(x, j)] for j in range(y)} | {gv[(j, min(y, j))] for j in range(x)}
            s |= {g for g in range(1, GM + 1) if death[(x, y, g)] is not None}
            v = 1
            while v in s:
                v += 1
            gv[(x, y)] = v if v <= GM else None
    for x in range(X + 1):
        print(x, [gv[(x, y)] for y in range(x + 1)])
    if len(sys.argv) > 4:
        with tempfile.NamedTemporaryFile() as f:
            subprocess.run([sys.argv[4], str(X), str(GM), str(T + 1), "0", f.name],
                           stdout=subprocess.DEVNULL, check=True)
            raw = open(f.name, "rb").read()
        d = struct.unpack("%di" % (len(raw) // 4), raw)
        i = diff = 0
        for x in range(X + 1):
            for y in range(x + 1):
                for g in range(1, GM + 1):
                    a = death[(x, y, g)]
                    a = -1 if a is None else (-2 if a == -1 else a)
                    diff += a != d[i]
                    i += 1
        print("compared with %s: %d rows, %d differences" % (sys.argv[4], i, diff))
        ok = ok and diff == 0
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
