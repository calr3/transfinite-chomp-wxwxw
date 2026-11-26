#!/usr/bin/env python3
"""Restricted Grundy values of the finite attachments of the brick 1x2xomega over the 3x3 base,
and the P-ordinals they give (notes/31).

A position here has the columns (0,0) and (0,1) of height at least omega and a finite attachment
F on the other seven columns. F is given by its heights in the order
(0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2), non-increasing in both coordinates.

H(F) is the height of the finite P cut of brick + F, or infinite if there is none; it is decided
exactly by `rodf -I 1` (certified, notes/07). The restricted value is
    G_F(F) = mex { G_F(F') : F' an option of F with H(F') infinite },
defined when H(F) is infinite. By the Base-Top Theorem, brick + F + T (T a two-wide position on
top of the brick) is P iff H(F) is infinite and G_F(F) = G(T).

usage: brick_values.py M RODF OUT [JOBS]
  M: largest height of an attachment column. RODF: path of the rodf binary. OUT: table.
"""
import itertools, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

CELLS = [(0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
IDX = {c: i for i, c in enumerate(CELLS)}
BRICK = {(0, 0), (0, 1)}

def valid(F):
    h = lambda x, y: 10**9 if (x, y) in BRICK else F[IDX[(x, y)]]
    for (x, y) in CELLS:
        if x > 0 and h(x - 1, y) < h(x, y): return False
        if y > 0 and h(x, y - 1) < h(x, y): return False
    return True

def options(F):
    out = set()
    for (x, y) in CELLS:
        for t in range(F[IDX[(x, y)]]):
            G = list(F)
            for (a, b) in CELLS:
                if a >= x and b >= y: G[IDX[(a, b)]] = min(G[IDX[(a, b)]], t)
            out.add(tuple(G))
    return out

def rodf_H(rodf, F, timeout):
    # order of rodf -p for the base 333: (0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)
    p = "w,w," + ",".join(str(v) for v in F)
    try:
        r = subprocess.run([rodf, "-I", "1", "-p", p, "333"], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    line = [l for l in r.stdout.splitlines() if "poison cuts decided" in l]
    if not line: return None
    if "no P-position" in line[0]: return 0            # infinite
    return int(line[0].split("P at height")[1].split()[0])

def two_row_height(k):
    """The alpha with G(2 x alpha) = k (unrestricted two-wide values, notes/15), as a string."""
    # G(2 x (omega*j + a)) = 3^j * floor((3a+1)/2) + (3^j - 1)/2
    j = 0
    while True:
        base = (3**j - 1) // 2
        if k >= base and (k - base) % 3**j == 0:
            m = (k - base) // 3**j                      # m = floor((3a+1)/2)
            for a in (2 * m // 3, 2 * m // 3 + 1):
                if (3 * a + 1) // 2 == m and (j == 0 or True):
                    if j == 0 and a == 0 and k != 0: break
                    return j, a
        j += 1
        if 3**j > 2 * k + 3: return None

def ordinal(j, a):
    """omega + omega*j + a = omega*(j+1) + a, written with w for omega."""
    s = "w" if j == 0 else "w*%d" % (j + 1)
    return s + ("+%d" % a if a else "")

def main():
    M = int(sys.argv[1]); rodf = sys.argv[2]; out = sys.argv[3]
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    Fs = [F for F in itertools.product(range(M + 1), repeat=7) if valid(F)]
    Fs.sort(key=lambda F: (sum(F), F))
    print("attachments with heights <= %d: %d" % (M, len(Fs)), flush=True)
    with ThreadPoolExecutor(jobs) as ex:
        Hs = list(ex.map(lambda F: rodf_H(rodf, F, 600), Fs))
    H = dict(zip(Fs, Hs))
    G = {}
    for F in Fs:
        if H[F] != 0: continue
        if any(H.get(o) is None for o in options(F)): G[F] = None; continue
        s = set(G[o] for o in options(F) if H[o] == 0)
        if None in s: G[F] = None; continue
        g = 0
        while g in s: g += 1
        G[F] = g
    und = [F for F in Fs if H[F] is None]
    with open(out, "w") as f:
        f.write("# brick 1x2xomega over the 3x3 base with a finite attachment; heights of (0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)\n")
        f.write("# H = height of the finite P cut, or inf; G = restricted value; box = the height of the two brick columns at which brick + attachment is P (w = omega)\n")
        for F in Fs:
            if H[F] is None: f.write("%s H=? \n" % " ".join(map(str, F))); continue
            if H[F] != 0: f.write("%s H=%d box=%d\n" % (" ".join(map(str, F)), H[F], H[F])); continue
            g = G[F]
            if g is None: f.write("%s H=inf G=?\n" % " ".join(map(str, F))); continue
            ja = two_row_height(g)
            f.write("%s H=inf G=%d box=%s\n" % (" ".join(map(str, F)), g, ordinal(*ja) if ja else "?"))
    ninf = sum(1 for F in Fs if H[F] == 0)
    print("H infinite: %d, finite: %d, undecided: %d" % (ninf, len(Fs) - ninf - len(und), len(und)))
    hist = {}
    for F in Fs:
        if H[F] == 0 and G[F] is not None: hist[G[F]] = hist.get(G[F], 0) + 1
    print("restricted values:", sorted(hist.items()))

if __name__ == "__main__":
    main()
