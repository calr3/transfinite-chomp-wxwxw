#!/usr/bin/env python3
"""Turn the exact replies found by the rod solver into a query file for the census.

usage: solver_replies.py COLS [-p POSITION] FILE [FILE ...] > queries.txt

FILE: output of scripts/option_runs.py, lines of the form
    cut (x,y) at z = h0,h1,... : N exact   move: cell (a,b) at height t
or, with -p POSITION (heights of the cells of COLS, w = omega), output of "rodf -K c -v 1",
lines of the form
    cut (x,y) at z: N   reply: cell (a,b) at t
COLS: the base of those positions by column heights (322, 333, ...).

Prints the position after the reply, nine entries in the order (0,0),(0,1),(0,2) | (1,0),...,
w = omega, for every exact verdict whose reply is not a cut of the poison column. Feed the
result to "base3_table ... -T Z -U queries.txt": every such position is a P-position (the
solver certified it), so the census must label it P, as far as it lies inside the census.
"""
import re
import sys

cols = sys.argv[1]
args = sys.argv[2:]
base = None
if args[0] == "-p":
    base = args[1].split(",")
    args = args[2:]
cells = [(x, y) for x, c in enumerate(cols) for y in range(int(c))]
pat = re.compile(r"cut \((\d),(\d)\) at (\d+) = (\S+) : N exact\s+move: cell \((\d),(\d)\) at height (\d+)")
pat2 = re.compile(r"cut \((\d),(\d)\) at (\d+): N\s+reply: cell \((\d),(\d)\) at (\d+)\s*$")
seen = set()
for fn in args:
    for line in open(fn):
        m = pat.search(line)
        if m:
            hs = m.group(4).split(",")
            ax, ay, t = int(m.group(5)), int(m.group(6)), int(m.group(7))
        else:
            m = pat2.search(line) if base else None
            if not m:
                continue
            cx, cy, z = int(m.group(1)), int(m.group(2)), int(m.group(3))
            hs = [str(z) if (x >= cx and y >= cy and (v == "w" or int(v) > z)) else v
                  for (x, y), v in zip(cells, base)]
            ax, ay, t = int(m.group(4)), int(m.group(5)), int(m.group(6))
        if (ax, ay) == (0, 0):
            continue
        grid = {(x, y): "0" for x in range(3) for y in range(3)}
        for c, v in zip(cells, hs):
            grid[c] = v
        for (x, y) in grid:
            if x >= ax and y >= ay and (grid[(x, y)] == "w" or int(grid[(x, y)]) > t):
                grid[(x, y)] = str(t)
        q = " | ".join(" ".join(grid[(x, y)] for y in range(3)) for x in range(3))
        if q not in seen:
            seen.add(q)
            print(q)
