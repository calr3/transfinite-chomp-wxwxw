#!/usr/bin/env python3
"""Exact P-positions of 2D Chomp with at most three columns of ordinal height < omega^omega,
following Huddleston-Shurman, "Transfinite Chomp" (MSRI 42, 2002), sections 8-10.

Conventions are theirs: UNRESTRICTED Grundy values (the empty position has value 0, the poison
alone has value 1, P-positions have value 1). A position is a list of column heights
u >= v >= x (column 0 holds the poison).

  * One column: G = height.
  * Two columns (section 9): closed formulas (9-1)-(9-5) for G(h, k).
  * Three columns (section 10): x = 0 is two-wide; x finite and v finite: finite computation
    (or N by the Beanstalk Lemma if u is infinite); x finite and v infinite: the Side-Top
    Theorem 8.1; omega <= x < omega^omega: the decomposition (i)-(iv) and criterion (10-1).
    (Heights >= omega^omega are out of range here.)

The Side-Top Theorem needs, for a side column of finite height x, whether some finite h makes
(h, h, x) a P-position. That is decided exactly by the rod solver's certified analysis
(`rodf -I 1 -p w,w,x 3`); its answers are cached.

Ordinals are dicts {exponent: coefficient} with finite exponents and positive coefficients.
"""
import functools
import subprocess
import sys

RODF = None  # path to the rodf binary, set by main() or the caller


# ---------------- ordinals below omega^omega ----------------

def O(*terms):
    """O((e1,c1),(e2,c2),...) -> ordinal; O(n) for a natural number n."""
    if len(terms) == 1 and isinstance(terms[0], int):
        return {0: terms[0]} if terms[0] else {}
    d = {}
    for e, c in terms:
        if c:
            d[e] = d.get(e, 0) + c
    return d


def key(a):
    return tuple(sorted(a.items(), reverse=True))


def cmp(a, b):
    ka, kb = key(a), key(b)
    # compare lexicographically by (exponent, coefficient) from the top
    for (ea, ca), (eb, cb) in zip(ka, kb):
        if ea != eb:
            return 1 if ea > eb else -1
        if ca != cb:
            return 1 if ca > cb else -1
    return (len(ka) > len(kb)) - (len(ka) < len(kb))


def is_zero(a):
    return not a


def deg(a):
    return max(a) if a else -1


def lead(a):
    return a[deg(a)] if a else 0


def low(a, i):
    """terms with exponent < i"""
    return {e: c for e, c in a.items() if e < i}


def high(a, i):
    """terms with exponent >= i"""
    return {e: c for e, c in a.items() if e >= i}


def coef(a, i):
    return a.get(i, 0)


def nat_add(a, b):
    d = dict(a)
    for e, c in b.items():
        d[e] = d.get(e, 0) + c
    return {e: c for e, c in d.items() if c}


def nim(a, b):
    """ordinal nim-sum: coefficientwise XOR (binary expansion of each coefficient)"""
    d = {}
    for e in set(a) | set(b):
        c = a.get(e, 0) ^ b.get(e, 0)
        if c:
            d[e] = c
    return d


def finite(a):
    return deg(a) <= 0


def val(a):
    assert finite(a)
    return a.get(0, 0)


def omega_left_sub(u):
    """the ordinal t with omega + t = u (requires u >= omega)"""
    assert deg(u) >= 1
    if deg(u) >= 2:
        return dict(u)
    t = dict(u)
    t[1] -= 1
    if not t[1]:
        del t[1]
    return t


def show(a):
    if not a:
        return "0"
    parts = []
    for e, c in key(a):
        if e == 0:
            parts.append(str(c))
        else:
            w = "w" if e == 1 else "w^%d" % e
            parts.append(w if c == 1 else "%s*%d" % (w, c))
    return "+".join(parts)


def parse(s):
    """parse 'w^2*3+w*2+5' style ordinals"""
    s = s.replace(" ", "")
    if s in ("", "0"):
        return {}
    d = {}
    for t in s.split("+"):
        c = 1
        if "*" in t:
            t, cs = t.split("*")
            c = int(cs)
        if t.startswith("w"):
            e = int(t[2:]) if t.startswith("w^") else 1
        else:
            e, c = 0, int(t) * c
        d[e] = d.get(e, 0) + c
    return {e: c for e, c in d.items() if c}


# ---------------- two-wide Grundy values (section 9) ----------------

def G2_finite(u, v):
    """(9-1): two columns of finite heights u >= v (unrestricted)."""
    if u == 0:
        return 0
    d = u - v
    if d % 2 == 0:
        return d + (3 * v + 1) // 2
    return min(d + v // 2, (3 * d - 1) // 2)


def G2(h, k):
    """Unrestricted Grundy value of two columns of heights h >= k (ordinals < omega^omega)."""
    assert cmp(h, k) >= 0
    if is_zero(h):
        return {}
    i = deg(h)
    if i == 0:
        return O(G2_finite(val(h), val(k)))
    u, a = lead(h), low(h, i)
    v, b = coef(k, i), low(k, i)
    if i == 1:
        if u == v:  # (9-2)
            g = val(G2(a, b))
            return O(3 ** u * g + (3 ** u - 1) // 2)
        return nat_add(O((1, u - v)), nim(a, b))  # (9-3)
    if u == v:  # (9-4)
        return nat_add(O((i - 1, u)), G2(a, b))
    return nat_add(O((i, u - v)), nim(a, b))  # (9-5)


# ---------------- finite three-column positions ----------------

@functools.lru_cache(maxsize=None)
def P3_finite(u, v, x):
    """finite three-column Chomp: is (u, v, x) a P-position? (poison move excluded)"""
    cols = (u, v, x)
    for j in range(3):
        for t in range(cols[j]):
            if j == 0 and t == 0:
                continue
            c = list(cols)
            for jj in range(j, 3):
                c[jj] = min(c[jj], t)
            if P3_finite(*c):
                return False
    return True


# ---------------- side-top data for a side column of finite height x ----------------

@functools.lru_cache(maxsize=None)
def in_side_class(x):
    """x in S: no finite h makes (h, h, x) a P-position (H(box S, 2) infinite)."""
    if x == 0:
        return True
    out = subprocess.run([RODF, "-I", "1", "-p", "w,w,%d" % x, "3"], capture_output=True, text=True).stdout
    if "UNDECIDED" in out:
        raise RuntimeError("side class undecided for x=%d" % x)
    return "no P-position" in out


@functools.lru_cache(maxsize=None)
def G_side(x):
    """restricted Grundy value of the side column x within the class S"""
    vals = {G_side(y) for y in range(x) if in_side_class(y)}
    m = 0
    while m in vals:
        m += 1
    return m


# ---------------- three-wide P-criterion (section 10) ----------------

def is_P(cols):
    """cols: list of up to three ordinals, non-increasing. Exact P/N (heights < omega^omega)."""
    cols = [c for c in cols if not is_zero(c)]
    if not cols:
        raise ValueError("empty position")
    for a, b in zip(cols, cols[1:]):
        assert cmp(a, b) >= 0, "heights must be non-increasing"
    if len(cols) == 1:
        return cols[0] == O(1)
    if len(cols) == 2:
        return G2(cols[0], cols[1]) == O(1)
    u, v, x = cols
    if finite(x):
        xv = val(x)
        if finite(v):
            if finite(u):
                return P3_finite(val(u), val(v), xv)
            return False  # Beanstalk Lemma: one infinite column plus finite part has infinite G
        # Side-Top Theorem: U = (2 x omega) + S@(2,0) + T@(0,omega), S = column x
        if not in_side_class(xv):
            return False
        T = G2(omega_left_sub(u), omega_left_sub(v))
        return finite(T) and val(T) == G_side(xv)
    # omega <= x < omega^omega: decomposition (i)-(iv) and criterion (10-1)
    i = deg(x)
    xi, c = lead(x), low(x, i)
    uh, ui, a = high(u, i + 1), coef(u, i), low(u, i)
    vh, vi, b = high(v, i + 1), coef(v, i), low(v, i)
    oxi = O((i, xi))
    if not uh and not vh and ui == vi == xi:  # case (i)
        Ub = G2(O((i, ui)), O((i, ui)))
        return Ub == oxi and False  # (10-1) would need G(Ut) = 0, i.e. an empty top; never P
    if not vh and vi == xi and (uh or ui > vi):  # case (ii)
        Ub = G2(nat_add(uh, O((i, ui))), O((i, vi)))
        top = nim(a, G2(b, c))
        return Ub == oxi and not top
    if uh and uh == vh and ui == vi:  # case (iii)
        Ub = G2(uh, uh)
        top = nim(G2(nat_add(O((i, ui)), a), nat_add(O((i, vi)), b)), c)
        return Ub == oxi and not top
    # case (iv)
    Ub = G2(nat_add(uh, O((i, ui))), nat_add(vh, O((i, vi))))
    top = nim(nim(a, b), c)
    return Ub == oxi and not top


def main():
    global RODF
    RODF = sys.argv[1]
    for arg in sys.argv[2:]:
        cols = [parse(t) for t in arg.split(",")]
        print("%-30s %s" % (arg, "P" if is_P(cols) else "N"))


if __name__ == "__main__":
    main()
