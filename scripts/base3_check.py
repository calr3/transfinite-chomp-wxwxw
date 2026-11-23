#!/usr/bin/env python3
"""Check tools/base3_table.cpp against a brute-force search.

usage: base3_check.py BINARY H [TRIALS]

Runs the binary with all caps H and with TRIALS random caps, and compares its list of
P-positions (option -P) with the P-positions found by a direct recursion over all plane
partitions on the 3x3 base with the same caps. Use small H (up to 5 or 6).
"""
import itertools
import os
import random
import subprocess
import sys
import tempfile
from functools import lru_cache

CELLS = [(x, y) for x in range(3) for y in range(3)]


@lru_cache(maxsize=None)
def is_p(pos):
    """pos: heights in x-major order. True iff the player to move loses."""
    for k, (x, y) in enumerate(CELLS):
        for t in range(pos[k]):
            if k == 0 and t == 0:
                continue  # the poison
            new = tuple(min(pos[j], t) if (CELLS[j][0] >= x and CELLS[j][1] >= y) else pos[j]
                        for j in range(9))
            if is_p(new):
                return False
    return True


def brute(H, cap):
    out = set()
    rng = [range(min(H, cap[k]) + 1) for k in range(9)]
    for pos in itertools.product(*rng):
        if pos[0] < 1:
            continue
        ok = True
        for k, (x, y) in enumerate(CELLS):
            if x < 2 and pos[k + 3] > pos[k]:
                ok = False
                break
            if y < 2 and pos[k + 1] > pos[k]:
                ok = False
                break
        if ok and is_p(pos):
            out.add(pos)
    return out


def monotone(cap):
    cap = list(cap)
    for k, (x, y) in enumerate(CELLS):
        if x > 0:
            cap[k] = min(cap[k], cap[k - 3])
        if y > 0:
            cap[k] = min(cap[k], cap[k - 1])
    return cap


def run(binary, H, cap):
    with tempfile.TemporaryDirectory() as tmp:
        dump = os.path.join(tmp, "p.txt")
        subprocess.run([binary, str(H), "-c", ",".join(map(str, cap)), "-P", dump],
                       check=True, capture_output=True)
        got = set()
        for line in open(dump):
            a, p, q, u, v, w, d, e, f = map(int, line.split())
            got.add((a, p, q, u, v, w, d, e, f))
    return got


def main():
    binary, H = sys.argv[1], int(sys.argv[2])
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    random.seed(1)
    caps = [[H] * 9]
    for _ in range(trials):
        caps.append(monotone([H] + [random.choice([0, 1, 2, H, H, random.randint(0, H)])
                                    for _ in range(8)]))
    bad = 0
    for cap in caps:
        want = brute(H, cap)
        got = run(binary, H, cap)
        status = "ok" if want == got else "DIFFERENT"
        if want != got:
            bad += 1
            print("  only brute force:", sorted(want - got)[:5])
            print("  only binary     :", sorted(got - want)[:5])
        print("caps %s: %d P-positions, %s" % (cap, len(want), status))
    print("all agree" if bad == 0 else "%d cap settings differ" % bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
