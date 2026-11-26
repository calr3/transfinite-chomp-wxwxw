#!/usr/bin/env python3
"""Death levels against birth values in the four-row system of notes/23 (section 8).

usage: four_row_h4.py X GM OUT BIRTHS [XMIN]
  OUT and BIRTHS are the files written by tools/four_row_values.cpp (OUT argument and the
  BIRTHS environment variable) for the same X and GM. Rows with x >= XMIN (default 32) that die
  after their birth level are compared with three reference values: their own birth value, the
  birth value of the diagonal row (x,x,g), and the largest birth value of the rows (x,y',g).
"""
import sys
import numpy as np

X, GM = int(sys.argv[1]), int(sys.argv[2])
XMIN = int(sys.argv[5]) if len(sys.argv) > 5 else 32
nside = (X + 1) * (X + 2) // 2
death = np.fromfile(sys.argv[3], dtype=np.int32).reshape(nside, GM)
birth = np.fromfile(sys.argv[4], dtype=np.int32).reshape(nside, GM)
xs = np.repeat(np.arange(X + 1), np.arange(1, X + 2))
start = np.arange(X + 1) * (np.arange(X + 1) + 1) // 2
died = (death >= 0) & (death != xs[:, None]) & (xs[:, None] >= XMIN)
n = int(died.sum())
print("rows with x >= %d that die after their birth level: %d" % (XMIN, n))

def report(name, bad):
    rows = bad.any(axis=1)
    print("  die after %s: %d%s" % (name, int(bad.sum()), ("; largest x = %d" % int(xs[rows].max())) if rows.any() else ""))

report("their own birth value", died & (death > birth))
diag = start + np.arange(X + 1)
ref = np.where(death[diag] == -2, np.iinfo(np.int32).max, birth[diag])
report("the birth value of the diagonal row (x,x,g)", died & (death > ref[xs]))
mx = np.zeros((X + 1, GM), dtype=np.int64)
for x in range(X + 1):
    seg = slice(start[x], start[x] + x + 1)
    mx[x] = np.where(death[seg] == -2, 0, birth[seg]).max(axis=0)
report("the largest birth value of the rows (x,y',g)", died & (death > mx[xs]))
report("level 2x", died & (death > 2 * xs[:, None]))
born = death != -2
print("largest birth value: %d; largest death level: %d" % (int(birth[born].max()), int(death.max())))
big = died & (xs[:, None] >= 400)
if big.any():
    r = death[big] / np.broadcast_to(xs[:, None], death.shape)[big]
    print("x >= 400: largest death level / x = %.3f; largest birth value / x = %.3f" % (r.max(), (mx[400:] / np.arange(400, X + 1)[:, None]).max()))
