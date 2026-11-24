#!/usr/bin/env python3
"""Machine proof (Z3) for candidate A of notes/24: a set S of finite positions is closed under
replies, up to one hypothesis.

Positions are finite Chomp positions over the cells (0,0),(0,1),(1,0),(1,1) (heights a,b,c,d),
(0,2),(1,2) (heights e,f, at most 1) and (2,0) (height k, at most 2); the poison is (0,0,0).
A bite at a cell at height t cuts that cell and every cell above it in both coordinates to t.

S is the union of
  pure   the P-positions with e = f = k = 0:  b+c = a-1, d = min(b,c);  or  (a; a, a; a-1)
  2D     the P-positions in one layer: [2,2,1], [3,1,1] and [c+2, c, 2]
  G      (c+2; d+2, c, d) with e = f = 1, k = 0            (the top layer is the bottom one lowered by 2)
  F1-F4  (m+1; m+1, m, m), (m+1; m, m+1, m), (m+2; m+2, m+2, m), (m+2; m+1, m+1, m) with e = f = 1, k = 2
  K1-K4  the same four shapes with e = 1, f = 0, k = 1
  TW1-3  (m+2; 1, m, 1) and (m+2; m, 1, 1) with e = 1, f = 0, k = 1;  (m+3; m, 1, 1) with e = f = k = 1
  SMALL  106 positions of height at most 8.
H is the hypothesis family W(m) = (m+1; m, m+1, m) with e = f = 1, k = 0, m >= 1.

Claim. For every X in S and every option Y of X: Y is in H, or Y has an option in S.

Consequence (induction on the number of cells): if every position in H is an N-position, then
every position in S is a P-position. In particular F1(z), F2(z), F3(z) are P for all z, and
by the proposition of notes/24 the position A = (w,w,1 | w,w,1 | 2,0,0) is P.

The claim is a sentence of Presburger arithmetic. For each family and each cell, Z3 refutes
"some X in the family has an option at this cell that is not in H and has no option in S".
The 106 small positions are checked by enumeration, and the whole claim is also checked by
enumeration for all positions of height at most CHECK (default 14).

The script proves three things in order.
  1. The part S0 = S without F1-F4 is closed without any hypothesis, so it consists of
     P-positions. This includes the two-parameter family G.
  2. Lemma: every W(m) is an N-position. For m >= 2 this is a strategy-stealing argument on
     the top cell of the column (1,1); the four positions it leaves over are N by replies
     in S0 (see prove_lemma).
  3. The claim above for all of S. With 1 and 2, every position of S is a P-position.

usage: candidate_A_closure_z3.py [CHECK]
"""
import itertools
import sys
import time

import z3

SMALL = [
    (1, 1, 1, 0, 1, 0, 1), (1, 1, 1, 1, 0, 0, 1), (1, 1, 1, 1, 1, 0, 0), (2, 1, 1, 1, 1, 0, 1), (2, 1, 2, 0, 1, 0, 0), (3, 2, 1, 0, 1, 0, 0),
    (3, 2, 2, 2, 1, 0, 2), (3, 2, 2, 2, 1, 1, 1), (3, 2, 3, 1, 1, 0, 2), (3, 2, 3, 1, 1, 1, 0), (3, 3, 2, 1, 1, 0, 2), (3, 3, 2, 1, 1, 1, 1),
    (3, 3, 3, 0, 1, 0, 0), (3, 3, 3, 2, 1, 0, 2), (3, 3, 3, 2, 1, 1, 1), (4, 1, 1, 0, 1, 0, 0), (4, 1, 3, 1, 1, 0, 2), (4, 1, 4, 1, 1, 1, 0),
    (4, 2, 2, 0, 1, 0, 0), (4, 2, 2, 1, 1, 1, 1), (4, 2, 3, 2, 1, 1, 1), (4, 3, 2, 2, 1, 1, 1), (4, 3, 3, 1, 1, 1, 1), (4, 3, 4, 1, 1, 0, 2),
    (4, 4, 4, 1, 1, 1, 1), (4, 4, 4, 3, 1, 0, 2), (5, 1, 1, 1, 1, 1, 0), (5, 1, 2, 1, 1, 0, 2), (5, 1, 2, 1, 1, 1, 1), (5, 2, 2, 1, 1, 1, 0),
    (5, 2, 3, 0, 1, 0, 0), (5, 2, 4, 2, 1, 0, 2), (5, 2, 5, 2, 1, 1, 0), (5, 3, 1, 0, 1, 0, 0), (5, 3, 2, 2, 1, 1, 0), (5, 3, 3, 3, 1, 1, 1),
    (5, 4, 2, 0, 1, 0, 0), (5, 4, 4, 1, 1, 0, 2), (5, 4, 4, 4, 1, 1, 1), (5, 4, 5, 1, 1, 1, 0), (5, 4, 5, 3, 1, 1, 1), (5, 5, 5, 1, 1, 0, 2),
    (5, 5, 5, 4, 1, 1, 1), (6, 1, 2, 1, 1, 1, 0), (6, 1, 3, 1, 1, 1, 1), (6, 1, 5, 1, 1, 0, 2), (6, 2, 1, 1, 1, 1, 0), (6, 2, 3, 1, 1, 0, 1),
    (6, 2, 3, 2, 1, 0, 2), (6, 2, 4, 0, 1, 0, 0), (6, 2, 4, 1, 1, 1, 1), (6, 2, 5, 2, 1, 1, 1), (6, 3, 2, 0, 1, 0, 0), (6, 3, 2, 2, 1, 0, 2),
    (6, 3, 3, 1, 1, 0, 2), (6, 3, 3, 2, 1, 1, 0), (6, 3, 3, 3, 1, 0, 1), (6, 3, 6, 3, 1, 1, 0), (6, 4, 1, 0, 1, 0, 0), (6, 4, 2, 2, 1, 1, 1),
    (6, 4, 3, 1, 1, 1, 0), (6, 5, 6, 1, 1, 1, 0), (6, 5, 6, 3, 1, 1, 1), (6, 5, 6, 4, 1, 0, 2), (6, 6, 6, 2, 1, 1, 0), (6, 6, 6, 5, 1, 0, 2),
    (6, 6, 6, 5, 1, 1, 1), (7, 1, 3, 1, 1, 1, 0), (7, 1, 4, 1, 1, 0, 2), (7, 1, 4, 1, 1, 1, 1), (7, 2, 2, 2, 1, 1, 0), (7, 2, 3, 1, 1, 1, 1),
    (7, 2, 6, 2, 1, 0, 2), (7, 2, 6, 2, 1, 1, 1), (7, 3, 3, 3, 1, 0, 2), (7, 3, 4, 2, 1, 1, 0), (7, 3, 5, 3, 1, 1, 1), (7, 4, 2, 1, 1, 1, 0),
    (7, 4, 2, 2, 1, 0, 2), (7, 4, 3, 1, 1, 0, 2), (7, 4, 4, 3, 1, 1, 0), (7, 4, 7, 4, 1, 1, 0), (7, 5, 1, 0, 1, 0, 0), (7, 5, 2, 2, 1, 1, 1),
    (7, 5, 4, 1, 1, 1, 0), (7, 6, 3, 3, 1, 1, 1), (7, 6, 7, 1, 1, 1, 0), (7, 6, 7, 4, 1, 0, 2), (7, 7, 7, 3, 1, 1, 0), (7, 7, 7, 6, 1, 0, 2),
    (7, 7, 7, 6, 1, 1, 1), (8, 1, 7, 1, 1, 0, 2), (8, 2, 3, 2, 1, 1, 0), (8, 2, 5, 2, 1, 0, 2), (8, 3, 4, 3, 1, 0, 2), (8, 3, 5, 2, 1, 1, 0),
    (8, 4, 3, 3, 1, 0, 2), (8, 4, 5, 3, 1, 1, 0), (8, 5, 2, 0, 1, 0, 0), (8, 5, 2, 2, 1, 0, 2), (8, 5, 3, 1, 1, 1, 0), (8, 5, 4, 2, 1, 1, 0),
    (8, 5, 5, 4, 1, 1, 0), (8, 5, 8, 5, 1, 1, 0), (8, 7, 8, 4, 1, 0, 2), (8, 8, 8, 7, 1, 0, 2),
]


CELL_NAMES = ["(0,0)", "(0,1)", "(1,0)", "(1,1)", "(0,2)", "(1,2)", "(2,0)"]
# index of the coordinates of X = (a, b, c, d, e, f, k) cut by a bite at each cell
CUTS = [(0, 1, 2, 3, 4, 5, 6),  # (0,0): everything
        (1, 3, 4, 5),           # (0,1): b, d, e, f
        (2, 3, 5, 6),           # (1,0): c, d, f, k
        (3, 5),                 # (1,1): d, f
        (4, 5),                 # (0,2): e, f
        (5,),                   # (1,2): f
        (6,)]                   # (2,0): k
HEIGHT_OF = [0, 1, 2, 3, 4, 5, 6]  # the coordinate that is the height of each cell


class IntLogic:
    And = staticmethod(lambda *xs: all(xs))
    Or = staticmethod(lambda *xs: any(xs))
    mn = staticmethod(min)


class Z3Logic:
    And = staticmethod(z3.And)
    Or = staticmethod(z3.Or)
    mn = staticmethod(lambda x, y: z3.If(x <= y, x, y))


def cut(L, X, cell, t):
    return tuple(L.mn(v, t) if i in CUTS[cell] else v for i, v in enumerate(X))


def valid(L, X):
    a, b, c, d, e, f, k = X
    return L.And(a >= 1, d >= 0, f >= 0, k >= 0, a >= b, a >= c, b >= d, c >= d, b >= e, e >= f,
                 d >= f, c >= k, e <= 1, k <= 2)


def families(L):
    """name -> predicate on X = (a, b, c, d, e, f, k)."""
    def shapes(e0, f0, k0, lo):
        deco = lambda X: L.And(X[4] == e0, X[5] == f0, X[6] == k0)
        return [
            lambda X: L.And(deco(X), X[1] == X[0], X[2] == X[0] - 1, X[3] == X[0] - 1, X[0] >= lo[0]),
            lambda X: L.And(deco(X), X[1] == X[0] - 1, X[2] == X[0], X[3] == X[0] - 1, X[0] >= lo[1]),
            lambda X: L.And(deco(X), X[1] == X[0], X[2] == X[0], X[3] == X[0] - 2, X[0] >= lo[2]),
            lambda X: L.And(deco(X), X[1] == X[0] - 1, X[2] == X[0] - 1, X[3] == X[0] - 2, X[0] >= lo[3]),
        ]
    fam = {}
    fam["pure"] = lambda X: L.And(X[4] == 0, X[5] == 0, X[6] == 0, L.Or(
        L.And(X[1] + X[2] == X[0] - 1, X[3] == L.mn(X[1], X[2])),
        L.And(X[1] == X[0], X[2] == X[0], X[3] == X[0] - 1)))
    fam["2D"] = lambda X: L.Or(
        L.And(X[2] == 0, X[3] == 0, X[5] == 0, X[6] == 0, X[4] == 1,
              L.Or(L.And(X[0] == 2, X[1] == 2), L.And(X[0] == 3, X[1] == 1))),
        L.And(X[1] == 0, X[3] == 0, X[4] == 0, X[5] == 0, X[6] == 1,
              L.Or(L.And(X[0] == 2, X[2] == 2), L.And(X[0] == 3, X[2] == 1))),
        L.And(X[1] == 0, X[3] == 0, X[4] == 0, X[5] == 0, X[6] == 2, X[0] == X[2] + 2, X[2] >= 2))
    fam["G"] = lambda X: L.And(X[4] == 1, X[5] == 1, X[6] == 0, X[0] == X[2] + 2, X[1] == X[3] + 2,
                               X[3] >= 1)
    for name, s in zip(["F1", "F2", "F3", "F4"], shapes(1, 1, 2, (3, 2, 3, 3))):
        fam[name] = s
    for name, s in zip(["K1", "K2", "K3", "K4"], shapes(1, 0, 1, (3, 3, 3, 3))):
        fam[name] = s
    fam["TW1"] = lambda X: L.And(X[4] == 1, X[5] == 0, X[6] == 1, X[1] == 1, X[3] == 1,
                                 X[0] == X[2] + 2, X[2] >= 2)
    fam["TW2"] = lambda X: L.And(X[4] == 1, X[5] == 0, X[6] == 1, X[2] == 1, X[3] == 1,
                                 X[0] == X[1] + 2, X[1] >= 2)
    fam["TW3"] = lambda X: L.And(X[4] == 1, X[5] == 1, X[6] == 1, X[2] == 1, X[3] == 1,
                                 X[0] == X[1] + 3, X[1] >= 1)
    fam["SMALL"] = lambda X: L.Or(*[L.And(*[X[i] == p[i] for i in range(7)]) for p in SMALL])
    return fam


ACTIVE = None  # names of the families in use (None: all)
USE_H = True


def in_S(L, X):
    return L.Or(False, *[p(X) for n, p in families(L).items() if ACTIVE is None or n in ACTIVE])


def in_H(L, X):
    if not USE_H:
        return False
    return L.And(X[4] == 1, X[5] == 1, X[6] == 0, X[1] == X[0] - 1, X[2] == X[0], X[3] == X[0] - 1,
                 X[0] >= 2)


def options(X):
    """Integer positions: all options of X as (cell, t, position)."""
    out = []
    for cell in range(7):
        for t in range(1 if cell == 0 else 0, X[HEIGHT_OF[cell]]):
            out.append((cell, t, cut(IntLogic, X, cell, t)))
    return out


def closed_at(X):
    """Integer check of the claim at X. Returns None, or an option without a reply."""
    for cell, t, Y in options(X):
        if in_H(IntLogic, Y):
            continue
        if not any(in_S(IntLogic, R) for (_, _, R) in options(Y)):
            return (cell, t, Y)
    return None


def enumerate_positions(top):
    for a in range(1, top + 1):
        for b in range(0, a + 1):
            for c in range(0, a + 1):
                for d in range(0, min(b, c) + 1):
                    for e in range(0, min(b, 1) + 1):
                        for f in range(0, min(e, d, 1) + 1):
                            for k in range(0, min(c, 2) + 1):
                                yield (a, b, c, d, e, f, k)


def shrink_to_closed(check):
    """Without the hypothesis: drop families and small positions until the rest is closed
    (by enumeration up to height check)."""
    global ACTIVE, USE_H, SMALL
    USE_H = False
    ACTIVE = set(families(IntLogic))
    while True:
        fam = families(IntLogic)
        bad_fam, bad_small = set(), set()
        for X in enumerate_positions(check):
            if in_S(IntLogic, X) and closed_at(X):
                if X in SMALL:
                    bad_small.add(X)
                else:
                    bad_fam.update(n for n in ACTIVE if n != "SMALL" and fam[n](X))
        if not bad_fam and not bad_small:
            break
        ACTIVE -= bad_fam
        SMALL = [p for p in SMALL if p not in bad_small]


def prove_closed(check, label):
    """Enumeration up to height check, then Z3 for every active family and every cell."""
    ok = True
    n = 0
    for X in enumerate_positions(check):
        if in_S(IntLogic, X):
            n += 1
            bad = closed_at(X)
            if bad:
                ok = False
                print("NOT closed at", X, ": option", CELL_NAMES[bad[0]], "at", bad[1], "->", bad[2])
    print("  enumeration: %d positions of height <= %d, %s" % (n, check, "closed" if ok else "NOT closed"))
    a, b, c, d, e, f, k, t, s = z3.Ints("a b c d e f k t s")
    X = (a, b, c, d, e, f, k)
    t0 = time.time()
    done = []
    for name, pred in families(Z3Logic).items():
        if name == "SMALL" or (ACTIVE is not None and name not in ACTIVE):
            continue  # SMALL: finitely many, covered by the enumeration
        for cell in range(7):
            Y = cut(Z3Logic, X, cell, t)
            reply = z3.Or([z3.Exists([s], z3.And(s >= (1 if c2 == 0 else 0), s < Y[HEIGHT_OF[c2]],
                                                 in_S(Z3Logic, cut(Z3Logic, Y, c2, s))))
                           for c2 in range(7)])
            solver = z3.Solver()
            solver.add(valid(Z3Logic, X), pred(X), t >= (1 if cell == 0 else 0), t < X[HEIGHT_OF[cell]],
                       z3.Not(in_H(Z3Logic, Y)), z3.Not(reply))
            r = solver.check()
            if r != z3.unsat:
                ok = False
                print("  family %-5s bite at %s: %s" % (name, CELL_NAMES[cell], r),
                      solver.model() if r == z3.sat else "")
        done.append(name)
    print("  Z3: families %s, all seven cells each, %.0f s" % (" ".join(done), time.time() - t0))
    print("  %s: %s" % (label, "PROVED" if ok else "NOT PROVED"), flush=True)
    return ok


def prove_lemma(check):
    """W(m) = (m+1; m, m+1, m | e = f = 1, k = 0) is an N-position for every m >= 1.

    For m >= 2 let W' be W(m) without the top cell u = (1,1,m-1) of the column (1,1), which is a
    maximal cell. If W(m) were P, W' would be N by a bite p with W' minus up(p) in P. If
    p <= u, that position is also an option of W(m): impossible. The bites p not below u are
    the top cells of the columns (0,0) and (1,0) and the two wing cells. Each of the four
    positions they leave has an option in the closed part S0, so none of them is P."""
    ok = True
    m, = z3.Ints("m")
    Wp = (m + 1, m, m + 1, m - 1, 1, 1, 0)
    L = Z3Logic
    four = [("top of (0,0)", cut(L, Wp, 0, m), 4, 0),   # then take the wing (0,2,0): pure (m; m, m; m-1)
            ("top of (1,0)", cut(L, Wp, 2, m), 1, 0),   # then take (0,1,0): two rows [m+1, m]
            ("wing (0,2,0)", cut(L, Wp, 4, 0), 2, 0),   # then take (1,0,0): two rows [m+1, m]
            ("wing (1,2,0)", cut(L, Wp, 5, 0), 0, 1)]   # then cut (0,0) at 1: the 2D position [3,2]
    for name, pos, cell, t in four:
        solver = z3.Solver()
        solver.add(m >= 2, z3.Not(z3.And(t < pos[HEIGHT_OF[cell]], in_S(L, cut(L, pos, cell, t)))))
        r = solver.check()
        if r != z3.unsat:
            ok = False
            print("  lemma, bite at the %s: reply not in S0 (%s)" % (name, r))
    # the same by enumeration, including the list of bites that are not below u
    for mm in range(2, check):
        W = (mm + 1, mm, mm + 1, mm, 1, 1, 0)
        Wp_i = (mm + 1, mm, mm + 1, mm - 1, 1, 1, 0)
        outside = 0
        for cell, t, Y in options(Wp_i):
            below_u = cell in (0, 1, 2, 3) and t <= mm - 1
            if below_u:
                assert cut(IntLogic, W, cell, t) == Y  # the same option of W(m)
                continue
            outside += 1
            if not any(in_S(IntLogic, R) for (_, _, R) in options(Y)):
                ok = False
                print("  lemma fails at m =", mm, "bite", CELL_NAMES[cell], t)
        assert outside == 4
    W1 = (2, 1, 2, 1, 1, 1, 0)
    if not any(in_S(IntLogic, R) for (_, _, R) in options(W1)):
        ok = False
        print("  W(1) has no option in S0")
    print("  lemma (W(m) is N for all m >= 1): %s" % ("PROVED" if ok else "NOT PROVED"), flush=True)
    return ok


def main():
    global ACTIVE, USE_H, SMALL
    check = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    for X in SMALL:
        assert valid(IntLogic, X) and X[0] <= check, X
    small_all = list(SMALL)

    print("1. The part S0 of S that is closed without any hypothesis")
    shrink_to_closed(check)
    print("  families: %s; small positions: %d of %d" % (" ".join(sorted(ACTIVE - {"SMALL"})), len(SMALL), len(small_all)))
    ok1 = prove_closed(check, "every position of S0 is a P-position")

    print("2. The lemma, using S0")
    ok2 = prove_lemma(check)

    print("3. All of S, with the positions W(m) of the lemma allowed as options")
    ACTIVE, USE_H, SMALL = None, True, small_all
    ok3 = prove_closed(check, "every position of S is a P-position (given 1 and 2)")

    ok = ok1 and ok2 and ok3
    print("THEOREM PROVED: F1(z), F2(z), F3(z) are P-positions for all z" if ok else "NOT PROVED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
