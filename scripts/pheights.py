#!/usr/bin/env python3
"""Exact finite P-heights: for each Young diagram S (up to transpose), the least t <= T such
that the finite box-like position S x t is a P-position. By uniqueness this t is the
Huddleston-Shurman P-height h(S). Rectangles other than 1x1 are skipped (S x t has a top cell
other than the poison, so it is N by strategy stealing; their P-height is infinite).

usage: pheights.py RODF_BINARY MAX_CELLS T [TIMEOUT_SECONDS]
"""
import subprocess
import sys


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def main():
    binary, maxcells, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    timeout = float(sys.argv[4]) if len(sys.argv) > 4 else 300
    seen = set()
    for n in range(1, maxcells + 1):
        for cols in partitions(n):
            t = tuple(sum(1 for c in cols if c > i) for i in range(cols[0]))
            if t in seen or max(cols) > 9:
                continue
            seen.add(cols)
            name = "".join(map(str, cols))
            if cols == (1,):
                print("%-10s n=%-2d h = 1 (the poison alone)" % (name, n), flush=True)
                continue
            if len(set(cols)) == 1:
                print("%-10s n=%-2d rectangle (no finite h)" % (name, n), flush=True)
                continue
            try:
                out = subprocess.run([binary, "-H", str(T), name], capture_output=True, text=True,
                                     timeout=timeout).stdout.strip()
                res = out.split(":")[1].split("[")[0].strip()
            except subprocess.TimeoutExpired:
                res = "timeout"
            print("%-10s n=%-2d %s" % (name, n, res), flush=True)


main()
