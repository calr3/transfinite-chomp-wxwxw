#!/usr/bin/env python3
"""Machine proof of Huddleston-Shurman's formula (9-1) for two-column Chomp.

G(u,v), u >= v >= 0 finite, is the Grundy value of the two-column position with heights u, v in
which every cell may be taken (the empty position has value 0). Its options are (t,t) for
t <= v, t < u (bite both columns at t), (t,v) for v < t < u, and (u,t) for t < v. (9-1) says
G = F with
    F(u,v) = d + floor((3v+1)/2)                    if d = u - v is even,
             min(d + floor(v/2), (3d-1)/2)          if d is odd.
F(0,0) = 0. G is the unique function satisfying G(u,v) = mex(option values), so (9-1) holds iff F
satisfies the same recursion for all u >= v >= 0:
  (i)  F(u,v) is not the value of an option;
  (ii) every n < F(u,v) is the value of some option.
Both are statements of Presburger arithmetic (linear integer arithmetic with floor by 2), which
Z3 decides here by refuting their negations. Two consequences used in notes/18 are proved the
same way:
  (D0) the diagonal values G(e,e) are exactly the n with n mod 3 != 1;
  (B0) for every b, the values G(e,e) (e <= b) and G(e,b) (e > b) together cover all of N.

usage: hs91_z3.py
"""
import z3


def F(u, v):
    d = u - v
    even = (d % 2) == 0
    return z3.If(even, d + (3 * v + 1) / 2, z3.If(d + v / 2 <= (3 * d - 1) / 2, d + v / 2, (3 * d - 1) / 2))


def is_option_value(n, u, v):
    t = z3.Int("t")
    return z3.Exists([t], z3.Or(
        z3.And(t >= 0, t <= v, t < u, F(t, t) == n),
        z3.And(t > v, t < u, F(t, v) == n),
        z3.And(t >= 0, t < v, F(u, t) == n)))


def prove(name, claim):
    s = z3.Solver()
    s.set("timeout", 600000)
    s.add(z3.Not(claim))
    r = s.check()
    label = "PROVED (negation unsat)" if r == z3.unsat else ("FALSE" if r == z3.sat else "unknown")
    print("%-60s %s" % (name, label), flush=True)
    if r == z3.sat:
        print("  counterexample:", s.model())
    return r == z3.unsat


def main():
    u, v, n = z3.Ints("u v n")
    dom = z3.And(u >= v, v >= 0)
    ok = True
    ok &= prove("F(0,0) = 0", F(z3.IntVal(0), z3.IntVal(0)) == 0)
    ok &= prove("(i)  F(u,v) is not an option value", z3.ForAll([u, v], z3.Implies(dom, z3.Not(is_option_value(F(u, v), u, v)))))
    ok &= prove("(ii) every n < F(u,v) is an option value",
                z3.ForAll([u, v, n], z3.Implies(z3.And(dom, n >= 0, n < F(u, v)), is_option_value(n, u, v))))
    e, b = z3.Ints("e b")
    ok &= prove("(D0) {G(e,e)} = {n : n mod 3 != 1}",
                z3.ForAll([n], z3.Implies(n >= 0, (n % 3 != 1) == z3.Exists([e], z3.And(e >= 0, F(e, e) == n)))))
    ok &= prove("(B0) {G(e,e): e <= b} u {G(e,b): e > b} = N",
                z3.ForAll([b, n], z3.Implies(z3.And(b >= 0, n >= 0), z3.Exists([e], z3.Or(
                    z3.And(e >= 0, e <= b, F(e, e) == n), z3.And(e > b, F(e, b) == n))))))
    print("(9-1), (D0), (B0) proved" if ok else "NOT all proved")


if __name__ == "__main__":
    main()
