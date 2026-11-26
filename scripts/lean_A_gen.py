#!/usr/bin/env python3
"""Generate the Lean proof that A = (w,w,1 | w,w,1 | 2,0,0) is a P-position.

usage: lean_A_gen.py [--check-only]

Writes lean/Chomp/BlockFamilies.lean and lean/Chomp/BlockA.lean. The hand-written part
(positions, moves, the closure principle, the Fundamental Theorem) is lean/Chomp/Block.lean.

What is generated, and how.

* A set S of finite positions over the seven columns of A: 27 families given by linear
  conditions (some with a parity), and a list of small positions. It is the set of
  notes/25 together with what the three positions with two infinite columns in the proof
  of A need (notes/29).
* For every family and every column, a lemma: a bite of a member in that column leaves a
  position of the exceptional family W, or a position with a bite back into S. The reply is
  given explicitly, as a short list of candidates (column, height as a linear expression,
  target family), each with the region where it applies. The candidates are found by search
  on small cases and completed with Z3 until Z3 finds no uncovered case. Z3 is only used to
  find them: Lean checks every case with `omega`.
* For the small positions, a table of replies that Lean checks by evaluation (`decide`).
* The positions with infinite columns: A, its options, and the 33 positions with two
  infinite columns under them, each with its reply.

Requires z3 (pip install z3-solver). The table of finite P-positions used for the search is
computed here (heights up to TOP); it is not part of the proof.
"""
import itertools
import os
import sys
import time

import z3

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.argv_saved = list(sys.argv)
sys.argv = [sys.argv[0]]
import candidate_A_closure_z3 as cz   # for the list of small positions of notes/25
sys.argv = sys.argv_saved

FIELDS = "abcdefk"
CUTS = [(0, 1, 2, 3, 4, 5, 6), (1, 3, 4, 5), (2, 3, 5, 6), (3, 5), (4, 5), (5,), (6,)]
CELLS = ["(0,0)", "(0,1)", "(1,0)", "(1,1)", "(0,2)", "(1,2)", "(2,0)"]


# ---------------------------------------------------------------- expressions
class E:
    """Linear expressions with min over the variables a..k, t."""

    def __init__(self, kind, *args):
        self.kind, self.args = kind, args

    def __add__(self, o):
        o = lift(o)
        if o.kind == "const" and o.args[0] == 0:
            return self
        if o.kind == "const" and o.args[0] < 0:
            return E("sub", self, E("const", -o.args[0]))
        return E("add", self, o)

    def __sub__(self, o):
        o = lift(o)
        if o.kind == "const" and o.args[0] == 0:
            return self
        return E("sub", self, o)

    def ev(self, env):
        k, a = self.kind, self.args
        if k == "var":
            return env[a[0]]
        if k == "const":
            return a[0]
        if k == "add":
            return a[0].ev(env) + a[1].ev(env)
        if k == "sub":
            return a[0].ev(env) - a[1].ev(env)
        if k == "min":
            return min(a[0].ev(env), a[1].ev(env))
        raise ValueError(k)

    def z(self, env):
        k, a = self.kind, self.args
        if k == "var":
            return env[a[0]]
        if k == "const":
            return z3.IntVal(a[0])
        if k == "add":
            return a[0].z(env) + a[1].z(env)
        if k == "sub":
            return a[0].z(env) - a[1].z(env)
        if k == "min":
            x, y = a[0].z(env), a[1].z(env)
            return z3.If(x <= y, x, y)
        raise ValueError(k)

    def lean(self, top=True):
        k, a = self.kind, self.args
        if k == "var":
            return a[0]
        if k == "const":
            return str(a[0])
        if k == "add":
            s = "%s + %s" % (a[0].lean(False), a[1].lean(False))
        elif k == "sub":
            s = "%s - %s" % (a[0].lean(False), a[1].lean(False))
        else:
            return "min %s %s" % (atomic(a[0]), atomic(a[1])) if top else "(min %s %s)" % (atomic(a[0]), atomic(a[1]))
        return s if top else "(" + s + ")"

    def py(self):
        k, a = self.kind, self.args
        if k == "var":
            return a[0]
        if k == "const":
            return str(a[0])
        if k == "add":
            return "(%s + %s)" % (a[0].py(), a[1].py())
        if k == "sub":
            return "(%s - %s)" % (a[0].py(), a[1].py())
        return "min(%s, %s)" % (a[0].py(), a[1].py())

    def has_sub(self):
        return self.kind == "sub" or any(isinstance(x, E) and x.has_sub() for x in self.args)


def atomic(e):
    return e.lean(True) if e.kind in ("var", "const") else "(" + e.lean(True) + ")"


def lift(x):
    return x if isinstance(x, E) else E("const", int(x))


def V(n):
    return E("var", n)


def mn(x, y):
    x, y = lift(x), lift(y)
    return E("min", x, y)


class Atom:
    """lhs op rhs with op in == <= < ; or lhs % 2 == r."""

    def __init__(self, op, l, r):
        self.op, self.l, self.r = op, lift(l), lift(r)

    def ev(self, env):
        l, r = self.l.ev(env), self.r.ev(env)
        return {"==": l == r, "<=": l <= r, "<": l < r, "mod": l % 2 == r}[self.op]

    def z(self, env):
        l, r = self.l.z(env), self.r.z(env)
        return {"==": l == r, "<=": l <= r, "<": l < r, "mod": l % 2 == r}[self.op]

    def py(self):
        if self.op == "mod":
            return "%s %% 2 == %s" % (self.l.py(), self.r.py())
        return "%s %s %s" % (self.l.py(), self.op, self.r.py())

    def lean(self):
        if self.op == "mod":
            return "%s %% 2 = %s" % (atomic(self.l), self.r.lean())
        return "%s %s %s" % (self.l.lean(), {"==": "=", "<=": "≤", "<": "<"}[self.op], self.r.lean())


def eq(l, r):
    return Atom("==", l, r)


def le(l, r):
    return Atom("<=", l, r)


def lt(l, r):
    return Atom("<", l, r)


def mod2(l, r):
    return Atom("mod", l, r)


def conj_lean(atoms):
    return " ∧ ".join(a.lean() for a in atoms)


# ---------------------------------------------------------------- positions
def cut(X, cell, t):
    """X: 7 expressions or ints."""
    if all(isinstance(v, int) for v in X) and isinstance(t, int):
        return tuple(min(v, t) if i in CUTS[cell] else v for i, v in enumerate(X))
    return tuple(mn(v, t) if i in CUTS[cell] else lift(v) for i, v in enumerate(X))


def legal_atoms(X, cell, t):
    t = lift(t)
    out = [lt(t, X[cell])]
    if cell == 0:
        out = [le(1, t)] + out
    return out


def valid_atoms(X):
    a, b, c, d, e, f, k = X
    return [le(1, a), le(b, a), le(c, a), le(d, b), le(d, c), le(e, b), le(f, e), le(f, d), le(k, c),
            le(e, 1), le(k, 2)]


def deco(X, e0, f0, k0):
    return [eq(X[4], e0), eq(X[5], f0), eq(X[6], k0)]


def fam_defs():
    """name -> function X (7 expressions) -> list of atoms (validity included)."""
    F = {}

    def add(name, fn):
        F[name] = lambda X, fn=fn: valid_atoms(X) + fn(*X)

    add("pureA", lambda a, b, c, d, e, f, k: [eq(e, 0), eq(f, 0), eq(k, 0), eq(b + c + 1, a), eq(d, mn(b, c))])
    add("pureB", lambda a, b, c, d, e, f, k: [eq(e, 0), eq(f, 0), eq(k, 0), eq(b, a), eq(c, a), eq(d + 1, a)])
    add("flat2", lambda a, b, c, d, e, f, k: [eq(b, 0), eq(d, 0), eq(e, 0), eq(f, 0), eq(k, 2), eq(a, c + 2), le(2, c)])
    add("G", lambda a, b, c, d, e, f, k: [eq(e, 1), eq(f, 1), eq(k, 0), eq(a, c + 2), eq(b, d + 2), le(1, d)])
    shapes = [lambda a, b, c, d: [eq(b, a), eq(c + 1, a), eq(d + 1, a)],
              lambda a, b, c, d: [eq(b + 1, a), eq(c, a), eq(d + 1, a)],
              lambda a, b, c, d: [eq(b, a), eq(c, a), eq(d + 2, a)],
              lambda a, b, c, d: [eq(b + 1, a), eq(c + 1, a), eq(d + 2, a)]]
    for pre, (e0, f0, k0), lows in (("F", (1, 1, 2), (3, 2, 3, 3)), ("K", (1, 0, 1), (3, 3, 3, 3))):
        for i in range(4):
            add("%s%d" % (pre, i + 1),
                lambda a, b, c, d, e, f, k, i=i, e0=e0, f0=f0, k0=k0, lo=lows[i]:
                [eq(e, e0), eq(f, f0), eq(k, k0)] + shapes[i](a, b, c, d) + [le(lo, a)])
    add("TW1", lambda a, b, c, d, e, f, k: [eq(e, 1), eq(f, 0), eq(k, 1), eq(b, 1), eq(d, 1), eq(a, c + 2), le(2, c)])
    add("TW2", lambda a, b, c, d, e, f, k: [eq(e, 1), eq(f, 0), eq(k, 1), eq(c, 1), eq(d, 1), eq(a, b + 2), le(2, b)])
    add("TW3", lambda a, b, c, d, e, f, k: [eq(e, 1), eq(f, 1), eq(k, 1), eq(c, 1), eq(d, 1), eq(a, b + 3), le(1, b)])
    # the families of notes/29: type (b, d, e, f, k), a - c by the parity of c, lowest c
    new = [("N1e", (1, 1, 1, 0, 2), 0, 3, 2), ("N1o", (1, 1, 1, 0, 2), 1, 1, 3),
           ("N2", (1, 1, 1, 1, 1), None, 3, 1),
           ("N3e", (2, 1, 1, 0, 1), 0, 1, 2), ("N3o", (2, 1, 1, 0, 1), 1, 3, 1),
           ("N4e", (2, 1, 1, 1, 1), 0, 2, 2), ("N4o", (2, 1, 1, 1, 1), 1, 4, 1),
           ("N5e", (2, 2, 1, 0, 2), 0, 1, 2), ("N5o", (2, 2, 1, 0, 2), 1, 3, 3),
           ("N6e", (3, 3, 1, 1, 1), 0, 2, 6), ("N6o", (3, 3, 1, 1, 1), 1, 4, 7)]
    for name, (b0, d0, e0, f0, k0), par, delta, c0 in new:
        add(name, lambda a, b, c, d, e, f, k, b0=b0, d0=d0, e0=e0, f0=f0, k0=k0, par=par, delta=delta, c0=c0:
            [eq(b, b0), eq(d, d0), eq(e, e0), eq(f, f0), eq(k, k0)] + ([] if par is None else [mod2(c, par)])
            + [eq(a, c + delta), le(c0, c)])
    return F


def reduce_atoms(fn):
    """Drop the atoms of fn(X) that follow from the remaining ones (and the variables being >= 0)."""
    zenv = {n: z3.Int(n) for n in FIELDS}
    atoms = fn(tuple(V(n) for n in FIELDS))
    keep = list(range(len(atoms)))
    for i in range(len(atoms)):
        rest = [j for j in keep if j != i]
        solver = z3.Solver()
        solver.add([zenv[n] >= 0 for n in FIELDS] + [atoms[j].z(zenv) for j in rest] + [z3.Not(atoms[i].z(zenv))])
        if solver.check() == z3.unsat:
            keep = rest
    return lambda X, fn=fn, keep=tuple(keep): [fn(X)[j] for j in keep]


FAM = {n: reduce_atoms(fn) for n, fn in fam_defs().items()}
FAM_NAMES = list(FAM)


def w_atoms(X):
    a, b, c, d, e, f, k = X
    return [eq(e, 1), eq(f, 1), eq(k, 0), eq(b + 1, a), eq(c, a), eq(d + 1, a), le(2, a)]


SMALL0 = list(cz.SMALL) + [(2, 2, 0, 0, 1, 0, 0), (3, 1, 0, 0, 1, 0, 0), (2, 0, 2, 0, 0, 0, 1), (3, 0, 1, 0, 0, 0, 1)]
EXTRA_SMALL = [(9, 3, 4, 3, 1, 1, 1), (8, 2, 4, 2, 1, 1, 1), (5, 3, 4, 1, 1, 1, 1), (9, 3, 3, 3, 1, 1, 0)]
SMALL = []
for p in SMALL0 + EXTRA_SMALL:
    if p not in SMALL:
        SMALL.append(p)
SMALL_SET = set(SMALL)


def ienv(X, t=0):
    env = dict(zip(FIELDS, X))
    env["t"] = t
    return env


XV = tuple(V(n) for n in FIELDS)
TV = V("t")
_fam_atoms = {n: FAM[n](XV) for n in FAM_NAMES}


def compile_atoms(atoms, args="a, b, c, d, e, f, k"):
    return eval("lambda %s: %s" % (args, " and ".join(a.py() for a in atoms) or "True"))


_fam_fn = {n: compile_atoms(_fam_atoms[n]) for n in FAM_NAMES}


def in_fam(name, X):
    return _fam_fn[name](*X)


def fam_of(X):
    """A family containing the integer position X, or 'small', or None."""
    for n in FAM_NAMES:
        if in_fam(n, X):
            return n
    return "small" if X in SMALL_SET else None


_w_fn = compile_atoms(w_atoms(XV))


def is_W(X):
    return _w_fn(*X)


def options(X):
    return [(cell, t, cut(X, cell, t)) for cell in range(7) for t in range(1 if cell == 0 else 0, X[cell])]


# ---------------------------------------------------------------- the table (search only)
def build_table(N):
    pi = {}
    rs = [(b, c, d, e, f, k) for b in range(N + 1) for c in range(N + 1) for d in range(min(b, c) + 1)
          for e in range(min(b, 1) + 1) for f in range(min(e, d, 1) + 1) for k in range(min(c, 2) + 1)]
    rs.sort(key=sum)
    for r in rs:
        M = max(r)
        if any(pi.get(tuple(min(v, a2) for v in r)) == a2 for a2 in range(1, M)):
            pi[r] = None
            continue
        blocked = set()
        X = (10 ** 9,) + r
        for cell in range(1, 7):
            for t in range(X[cell]):
                p = pi[cut(X, cell, t)[1:]]
                if p is not None:
                    blocked.add(p)
        a = max(M, 1)
        while a in blocked:
            a += 1
        pi[r] = a
    return pi


# ---------------------------------------------------------------- reply problems
class Problem:
    """Prove: for all values of the variables with the hypotheses, the position POS has a
    legal bite into S. hyps: list of atoms; neg: a list of atoms whose conjunction is denied
    (or None); pos: 7 expressions; samples: list of environments (ints)."""

    def __init__(self, name, hyps, neg, pos, samples, doc, names=("t", "a", "b", "c", "d")):
        self.name, self.hyps, self.neg, self.pos, self.samples, self.doc = name, hyps, neg, pos, samples, doc
        self.names = list(names)
        self.cands = []      # (cell, s expression, target, region atoms)

    def holds(self, env):
        if not hasattr(self, "_h"):
            self._h = compile_atoms(self.hyps, "a, b, c, d, e, f, k, t")
            self._n = compile_atoms(self.neg, "a, b, c, d, e, f, k, t") if self.neg is not None else None
        v = [env[n] for n in "abcdefkt"]
        return self._h(*v) and not (self._n is not None and self._n(*v))


def shifted(base, k, exact):
    """base + k as an expression of natural numbers, with the atoms that make it exact."""
    if k >= 0:
        e = base + k
        e.exact = list(exact)
    else:
        e = base - (-k)
        e.exact = list(exact) + [le(lift(-k), base)] if not exact else [le(exact[0].l + (-k), exact[0].r)]
    return e


def templates(env, s0, names):
    """Candidate expressions for the height s0 of a reply: (priority, expression)."""
    out = []
    if s0 <= 4:
        c = E("const", s0)
        c.exact = []
        out.append((2, c))
    for v in names:
        kdiff = s0 - env[v]
        if -6 <= kdiff <= 6:
            out.append((0, shifted(V(v), kdiff, [])))
    for u in names:
        for v in names:
            if u == v:
                continue
            kdiff = s0 - (env[u] - env[v])
            if -3 <= kdiff <= 3 and env[u] >= env[v]:
                out.append((1, shifted(V(u) - V(v), kdiff, [le(V(v), V(u))])))
    for i, u in enumerate(names):
        for v in names[i + 1:]:
            kdiff = s0 - (env[u] + env[v])
            if -3 <= kdiff <= 3:
                out.append((1, shifted(V(u) + V(v), kdiff, [])))
    return out


def cand_atoms(pos, cell, s, target):
    """The atoms that say: the bite (cell, s) of pos is legal and lands in target."""
    Z = cut(pos, cell, s)
    atoms = list(getattr(s, "exact", [])) + legal_atoms(pos, cell, s)
    if isinstance(target, tuple):
        atoms += [eq(Z[i], target[i]) for i in range(7)]
    else:
        atoms += FAM[target](Z)
    return atoms


def solve(pr, verbose=False):
    """Fill pr.cands: greedy cover of the samples, then Z3 until nothing is uncovered."""
    zenv = {n: z3.Int(n) for n in FIELDS + "t"}
    hyp_z = [a.z(zenv) for a in pr.hyps] + [zenv[n] >= 0 for n in zenv]
    if pr.neg is not None:
        hyp_z.append(z3.Not(z3.And([a.z(zenv) for a in pr.neg])))
    samples = [env for env in pr.samples if pr.holds(env)]
    chosen = []          # (cell, s, target)
    _cov = {}

    def covered(env, c):
        key = (c[0], c[1].lean(), c[2])
        if key not in _cov:
            _cov[key] = compile_atoms(cand_atoms(pr.pos, c[0], c[1], c[2]), "a, b, c, d, e, f, k, t")
        return _cov[key](*[env[n] for n in "abcdefkt"])
    rounds = 0
    while True:
        rounds += 1
        todo = [env for env in samples if not any(covered(env, c) for c in chosen)]
        while todo:
            # candidates from the uncovered samples
            score = {}
            for env in todo[:400]:
                Y = tuple(p.ev(env) for p in pr.pos)
                for cell, s0, Z in options(Y):
                    tg = fam_of(Z)
                    if tg is None:
                        continue
                    target = Z if tg == "small" else tg
                    for pri, s in templates(env, s0, pr.names):
                        key = (cell, s.lean(), target if isinstance(target, str) else tuple(target))
                        if key not in score:
                            score[key] = [0, pri + (2 if tg == "small" else 0), cell, s, target]
            if not score:
                env = todo[0]
                raise RuntimeError("%s: no reply in S for %s -> %s" % (pr.name, env, tuple(p.ev(env) for p in pr.pos)))
            for key, rec in score.items():
                c = (rec[2], rec[3], rec[4])
                rec[0] = sum(1 for env in todo if covered(env, c))
            best = max(score.values(), key=lambda r: (r[0], -r[1]))
            if best[0] == 0:
                raise RuntimeError("%s: candidates cover nothing" % pr.name)
            chosen.append((best[2], best[3], best[4]))
            todo = [env for env in todo if not covered(env, chosen[-1])]
        # Z3: anything uncovered?
        solver = z3.Solver()
        solver.add(hyp_z)
        for c in chosen:
            solver.add(z3.Not(z3.And([a.z(zenv) for a in cand_atoms(pr.pos, *c)])))
        r = solver.check()
        if r == z3.unsat:
            break
        assert r == z3.sat, r
        m = solver.model()
        env = {n: m.eval(zenv[n], model_completion=True).as_long() for n in zenv}
        samples.append(env)
        if rounds > 60:
            raise RuntimeError("%s: no convergence" % pr.name)
    # drop candidates made redundant by the others
    for c in list(chosen):
        rest = [x for x in chosen if x is not c]
        solver = z3.Solver()
        solver.add(hyp_z)
        for x in rest:
            solver.add(z3.Not(z3.And([a.z(zenv) for a in cand_atoms(pr.pos, *x)])))
        if rest and solver.check() == z3.unsat:
            chosen = rest
    pr.cands = chosen
    pr.tree = build_tree(pr, zenv, hyp_z, samples)
    if verbose:
        print("  %-12s %d candidates, tree with %d leaves: %s" % (pr.name, len(pr.cands), count_leaves(pr.tree), "; ".join(
            "%s@%s->%s" % (CELLS[c[0]], c[1].lean(), c[2] if isinstance(c[2], str) else "pt") for c in pr.cands)))
    return pr


def guard_vocabulary(samples, names):
    """Simple conditions on the variables that take more than one value in the samples."""
    active = [v for v in names if len({env[v] for env in samples}) > 1]
    out = []
    if "t" in active:
        out += [eq(TV, n) for n in range(0, 10)] + [lt(TV, n) for n in range(1, 11)] + [mod2(TV, 0)]
    for v in active:
        if v == "t":
            continue
        out += [eq(V(v), n) for n in range(0, 11)] + [lt(V(v), n) for n in range(1, 12)] + [mod2(V(v), 0)]
        if "t" in active:
            out += [eq(TV + n, V(v)) for n in range(0, 7)] + [lt(TV + n, V(v)) for n in range(0, 7)]
            out += [eq(V(v) + n, TV) for n in range(1, 4)] + [lt(V(v) + n, TV) for n in range(0, 4)]
    par = [v for v in active if v != "t"]
    for x in range(len(par)):
        for y in range(x + 1, len(par)):
            u, v = V(par[x]), V(par[y])
            out += [eq(u + n, v) for n in range(0, 4)] + [lt(u + n, v) for n in range(0, 4)]
            out += [eq(v + n, u) for n in range(1, 4)] + [lt(v + n, u) for n in range(0, 4)]
            if "t" in active:
                out += [eq(TV + u + n, v) for n in range(0, 3)] + [lt(TV + u + n, v) for n in range(0, 3)]
                out += [eq(TV + v + n, u) for n in range(0, 3)] + [lt(TV + v + n, u) for n in range(0, 3)]
    return out


def count_leaves(tree):
    return 1 if tree[0] != "split" else count_leaves(tree[2]) + count_leaves(tree[3])


def build_tree(pr, zenv, hyp_z, samples):
    """A decision tree: ("leaf", candidate index) | ("absurd",) | ("split", atom, yes, no).
    At a leaf, the hypotheses and the conditions on the path imply that the candidate is a
    legal bite into its target (checked with Z3 here, and by omega in Lean)."""
    samples = list(samples)
    vocab = guard_vocabulary(samples, pr.names)
    args = "a, b, c, d, e, f, k, t"
    vfn = [compile_atoms([g], args) for g in vocab]
    cfn = [compile_atoms(cand_atoms(pr.pos, *c), args) for c in pr.cands]
    cz_ = [z3.And([a.z(zenv) for a in cand_atoms(pr.pos, *c)]) for c in pr.cands]
    vals = lambda env: [env[n] for n in "abcdefkt"]

    def rec(path_z, path_fn, here, depth):
        # here: samples that satisfy the path
        for _ in range(40):
            solver = z3.Solver()
            solver.add(hyp_z + path_z)
            if not here:
                if solver.check() == z3.unsat:
                    return ("absurd",)
                m = solver.model()
                here = [{n: m.eval(zenv[n], model_completion=True).as_long() for n in zenv}]
            # a candidate that covers all the samples here?
            full = [j for j in range(len(pr.cands)) if all(cfn[j](*vals(env)) for env in here)]
            done = None
            for j in full:
                solver = z3.Solver()
                solver.add(hyp_z + path_z + [z3.Not(cz_[j])])
                r = solver.check()
                if r == z3.unsat:
                    done = j
                    break
                m = solver.model()
                here.append({n: m.eval(zenv[n], model_completion=True).as_long() for n in zenv})
            if done is not None:
                return ("leaf", done)
            if full:
                continue      # new samples were added: look again
            break
        if depth > 14:
            raise RuntimeError("%s: tree too deep" % pr.name)
        # choose a guard
        best = None
        cover = [[cfn[j](*vals(env)) for env in here] for j in range(len(pr.cands))]
        for gi, g in enumerate(vocab):
            side = [vfn[gi](*vals(env)) for env in here]
            nt = sum(side)
            if nt == 0 or nt == len(here):
                continue
            st = max(sum(1 for x, y in zip(cov, side) if x and y) for cov in cover)
            sf = max(sum(1 for x, y in zip(cov, side) if x and not y) for cov in cover)
            score = (st == nt) + (sf == len(here) - nt), st + sf
            if best is None or score > best[0]:
                best = (score, gi, side)
        if best is None:
            raise RuntimeError("%s: no guard separates %s" % (pr.name, here[:4]))
        _, gi, side = best
        g = vocab[gi]
        yes = rec(path_z + [g.z(zenv)], path_fn + [vfn[gi]], [e for e, sd in zip(here, side) if sd], depth + 1)
        no = rec(path_z + [z3.Not(g.z(zenv))], path_fn, [e for e, sd in zip(here, side) if not sd], depth + 1)
        return ("split", g, yes, no)

    return rec([], [], [env for env in samples], 0)


def pos_lean(X):
    return "⟨" + ", ".join(lift(v).lean() for v in X) + "⟩"


XP = tuple(V("X." + n) for n in FIELDS)


def or_chain(i, n, h="h"):
    """The proof of the i-th disjunct of an n-fold right-nested disjunction."""
    t = h if i == n - 1 else "Or.inl " + h
    for _ in range(i):
        t = "Or.inr (%s)" % t
    return t


def reply_term(c, indent):
    cell, s, target = c[0], c[1], c[2]
    leg = "by simp only [F7.cut, F7.legal] <;> omega"
    if isinstance(target, tuple):
        mem = "inS_pt (p := %s) (by decide) (by simp only [F7.cut, F7.mk.injEq] <;> omega)" % pos_lean(target)
    else:
        mem = "inS_%s (by simp only [F7.cut, fam%s] <;> omega)" % (target, target)
    return "⟨%d, %s, %s,\n%s%s⟩" % (cell, s.lean(), leg, indent, mem)


def proof_lean(pr):
    """The tactic block that proves `Reply inS POS` from the hypotheses in context."""
    L = []

    def rec(tree, ind, depth):
        pad = "  " * ind
        if tree[0] == "absurd":
            L.append(pad + "exfalso; omega")
        elif tree[0] == "leaf":
            L.append(pad + "exact " + reply_term(pr.cands[tree[1]], pad + "  "))
        else:
            L.append(pad + "by_cases g%d : %s" % (depth, tree[1].lean()))
            L.append(pad + "·")
            rec(tree[2], ind + 1, depth + 1)
            L.append(pad + "·")
            rec(tree[3], ind + 1, depth + 1)

    rec(pr.tree, 1, 0)
    # join "·" lines with the first line of their block
    out = []
    for line in L:
        if out and out[-1].strip() == "·":
            out[-1] = out[-1] + " " + line.strip()
        else:
            out.append(line)
    return "\n".join(out)


def closure_lemma(pr):
    X7 = "⟨a, b, c, d, e, f, k⟩"
    head = ("/-- %s -/\ntheorem %s (a b c d e f k t : Nat)\n    (hF : %s)\n    (hl : %s)\n    (hW : ¬ (%s)) :\n"
            "    Reply inS (F7.cut %s %d t) := by\n"
            % (pr.doc, pr.name, conj_lean(FAM[pr.fam](XV)), conj_lean(legal_atoms(XV, pr.cell, TV)),
               conj_lean(pr.neg), X7, pr.cell))
    if pr.empty:
        return head + "  omega"
    return head + proof_lean(pr)


def small_rows():
    """For every small position, the replies to all its options: (i, t, j, s)."""
    rows = []
    for X in SMALL:
        ws = []
        for cell, t, Y in options(X):
            if is_W(Y):
                ws.append((cell, t, 0, 0))
                continue
            best = None
            for j, s0, Z in options(Y):
                tg = fam_of(Z)
                if tg is not None:
                    best = (cell, t, j, s0)
                    if tg != "small":
                        break
            assert best is not None, (X, cell, t, Y)
            ws.append(best)
        rows.append((X, ws))
    return rows


def emit_families(problems):
    L = []
    w = L.append
    w("import Chomp.Block\n")
    w("/-!\n# The closed set `S` of finite positions under `A`\n\n"
      "GENERATED by `scripts/lean_A_gen.py`. Do not edit.\n\n"
      "`inS X`: the position `X` belongs to one of %d families given by linear conditions, or to a\n"
      "list of %d small positions. `S_closed`: every bite of a position of `S` leaves a position of\n"
      "the exceptional family `isW`, or a position with a bite back into `S`. Each case is an explicit\n"
      "reply checked by `omega`; the small positions are checked by evaluation.\n-/\n" % (len(FAM_NAMES), len(SMALL)))
    w("namespace Chomp\n\nopen F7\n")
    for n in FAM_NAMES:
        w("/-- The family `%s`. -/\ndef fam%s (X : F7) : Prop :=\n  %s\n" % (n, n, conj_lean(FAM[n](XP))))
        w("instance (X : F7) : Decidable (fam%s X) := by unfold fam%s; infer_instance\n" % (n, n))
    w("/-- The exceptional family `W(m) = (m+1; m, m+1, m | 1, 1 | 0)`, `m ≥ 1`. -/\ndef isW (X : F7) : Prop :=\n  %s\n"
      % conj_lean(w_atoms(XP)))
    w("instance (X : F7) : Decidable (isW X) := by unfold isW; infer_instance\n")
    rows = small_rows()
    CH = 6
    chunks = [rows[i:i + CH] for i in range(0, len(rows), CH)]
    w("/-! The small positions of `S`, each with a reply `(i, t, j, s)` to every bite `(i, t)`: the bite\n"
      "`(j, s)` of the position left (the entry is not used if that position is in `W`). -/\n")
    for ci, ch in enumerate(chunks):
        w("def smallChunk%d : List (F7 × List (Nat × Nat × Nat × Nat)) :=\n  [%s]\n"
          % (ci, ",\n   ".join("(%s, [%s])" % (pos_lean(X), ", ".join("(%d, %d, %d, %d)" % e for e in ws))
                                for X, ws in ch)))
    w("/-- The small positions with their replies. -/\ndef smallTable : List (F7 × List (Nat × Nat × Nat × Nat)) :=\n  %s\n"
      % " ++ ".join("smallChunk%d" % ci for ci in range(len(chunks))))
    w("/-- The small positions of `S`. -/\ndef small : List F7 := smallTable.map (·.1)\n")
    n = len(FAM_NAMES) + 1
    w("/-- The set `S`. -/\ndef inS (X : F7) : Prop :=\n  %s ∨\n  X ∈ small\n"
      % " ∨ ".join("fam%s X" % m for m in FAM_NAMES))
    w("instance (X : F7) : Decidable (inS X) := by unfold inS; infer_instance\n")
    for i, m in enumerate(FAM_NAMES):
        w("theorem inS_%s {X : F7} (h : fam%s X) : inS X := %s" % (m, m, or_chain(i, n)))
    w("theorem inS_small {X : F7} (h : X ∈ small) : inS X := %s" % or_chain(n - 1, n))
    w("theorem inS_pt {X p : F7} (hp : p ∈ small) (h : X = p) : inS X := by subst h; exact inS_small hp\n")
    w("/-! ## The families -/\n")
    for pr in problems:
        w(closure_lemma(pr) + "\n")
    # the small positions
    w("/-! ## The small positions -/\n")
    w("/-- `F7.legal` as a boolean. -/\ndef legalB (X : F7) : Nat → Nat → Bool\n"
      "  | 0, t => decide (1 ≤ t ∧ t < X.a)\n  | 1, t => decide (t < X.b)\n  | 2, t => decide (t < X.c)\n"
      "  | 3, t => decide (t < X.d)\n  | 4, t => decide (t < X.e)\n  | 5, t => decide (t < X.f)\n"
      "  | 6, t => decide (t < X.k)\n  | _, _ => false\n")
    w("theorem legalB_sound {X : F7} {i t : Nat} (h : legalB X i t = true) : X.legal i t := by\n"
      "  match i, h with\n"
      + "  | 0, h => exact of_decide_eq_true (p := 1 ≤ t ∧ t < X.a) h\n"
      + "".join("  | %d, h => exact of_decide_eq_true (p := t < X.%s) h\n" % (i, FIELDS[i]) for i in range(1, 7))
      + "  | _ + 7, h => exact absurd h (by simp [legalB])\n")
    w("/-- The entry `(i, t, j, s)`: the bite `(i, t)` of `X` leaves a position of `W`, or one with the\n"
      "legal bite `(j, s)` into `S`. -/\n"
      "def okEntry (X : F7) (w : Nat × Nat × Nat × Nat) : Bool :=\n"
      "  decide (isW (X.cut w.1 w.2.1)) ||\n"
      "    (legalB (X.cut w.1 w.2.1) w.2.2.1 w.2.2.2 && decide (inS ((X.cut w.1 w.2.1).cut w.2.2.1 w.2.2.2)))\n")
    w("/-- Every height `lo ≤ t < h` of the column `i` has an entry in the table. -/\n"
      "def covers (X : F7) (ws : List (Nat × Nat × Nat × Nat)) (i h lo : Nat) : Bool :=\n"
      "  (List.range h).all fun t => decide (t < lo) || ws.any fun w => w.1 == i && w.2.1 == t && okEntry X w\n")
    w("def checkRow (X : F7) (ws : List (Nat × Nat × Nat × Nat)) : Bool :=\n"
      "  covers X ws 0 X.a 1 && covers X ws 1 X.b 0 && covers X ws 2 X.c 0 && covers X ws 3 X.d 0 &&\n"
      "  covers X ws 4 X.e 0 && covers X ws 5 X.f 0 && covers X ws 6 X.k 0\n")
    w("theorem covers_sound {X : F7} {ws : List (Nat × Nat × Nat × Nat)} {i h lo : Nat}\n"
      "    (hc : covers X ws i h lo = true) {t : Nat} (ht : t < h) (hlo : lo ≤ t) :\n"
      "    isW (X.cut i t) ∨ Reply inS (X.cut i t) := by\n"
      "  have h1 := List.all_eq_true.mp hc t (List.mem_range.mpr ht)\n"
      "  have h2 : (ws.any fun w => w.1 == i && w.2.1 == t && okEntry X w) = true := by\n"
      "    rcases Bool.or_eq_true _ _ |>.mp h1 with h | h\n"
      "    · exact absurd (of_decide_eq_true h) (by omega)\n"
      "    · exact h\n"
      "  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp h2\n"
      "  have hw' := Bool.and_eq_true _ _ |>.mp hw\n"
      "  have hw'' := Bool.and_eq_true _ _ |>.mp hw'.1\n"
      "  have e1 : w.1 = i := by simpa using hw''.1\n"
      "  have e2 : w.2.1 = t := by simpa using hw''.2\n"
      "  have hok := hw'.2\n"
      "  unfold okEntry at hok\n"
      "  rw [e1, e2] at hok\n"
      "  rcases Bool.or_eq_true _ _ |>.mp hok with h | h\n"
      "  · exact Or.inl (of_decide_eq_true h)\n"
      "  · have h3 := Bool.and_eq_true _ _ |>.mp h\n"
      "    exact Or.inr ⟨_, _, legalB_sound h3.1, of_decide_eq_true h3.2⟩\n")
    w("theorem checkRow_sound {X : F7} {ws : List (Nat × Nat × Nat × Nat)} (hc : checkRow X ws = true)\n"
      "    {i t : Nat} (hl : X.legal i t) : isW (X.cut i t) ∨ Reply inS (X.cut i t) := by\n"
      "  simp only [checkRow, Bool.and_eq_true] at hc\n"
      "  obtain ⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc\n"
      "  match i, hl with\n"
      "  | 0, hl => exact covers_sound c0 hl.2 hl.1\n"
      + "".join("  | %d, hl => exact covers_sound c%d hl (Nat.zero_le _)\n" % (i, i) for i in range(1, 7))
      + "  | _ + 7, hl => exact absurd hl (by simp [F7.legal])\n")
    for ci in range(len(chunks)):
        w("set_option maxRecDepth 100000 in\ntheorem smallChunk%d_ok : smallChunk%d.all (fun p => checkRow p.1 p.2) = true := by decide\n"
          % (ci, ci))
    pat = "h"
    for ci in range(1, len(chunks)):
        pat = "(%s | h)" % pat
    cases = "".join("  · exact List.all_eq_true.mp smallChunk%d_ok p h\n" % ci for ci in range(len(chunks)))
    w("theorem smallTable_ok : ∀ p ∈ smallTable, checkRow p.1 p.2 = true := by\n"
      "  intro p hp\n"
      "  simp only [smallTable, List.mem_append] at hp\n"
      "  rcases hp with %s\n%s" % (pat, cases))
    w("theorem small_closed {X : F7} (hX : X ∈ small) {i t : Nat} (hl : X.legal i t) :\n"
      "    isW (X.cut i t) ∨ Reply inS (X.cut i t) := by\n"
      "  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hX\n"
      "  exact checkRow_sound (smallTable_ok p hp) hl\n")
    # the closure theorem
    w("/-! ## `S` is closed -/\n")
    w("/-- Every bite of a position of `S` leaves a position of `W`, or one with a bite back into `S`. -/\n"
      "theorem S_closed (X : F7) (hX : inS X) (i t : Nat) (hl : X.legal i t) :\n"
      "    isW (X.cut i t) ∨ Reply inS (X.cut i t) := by\n"
      "  by_cases hW : isW (X.cut i t)\n"
      "  · exact Or.inl hW\n"
      "  refine Or.inr ?_\n"
      "  rcases hX with %s\n" % " | ".join(["h"] * n))
    for m in FAM_NAMES:
        w("  · match i, hl with\n"
          + "".join("    | %d, hl => exact cl_%s_%d X.a X.b X.c X.d X.e X.f X.k t h hl hW\n" % (c, m, c) for c in range(7))
          + "    | _ + 7, hl => exact absurd hl (by simp [F7.legal])")
    w("  · rcases small_closed h hl with h' | h'\n    · exact absurd h' hW\n    · exact h'\n")
    w("end Chomp")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------- main
def main():
    t0 = time.time()
    TOP = 30
    pi = build_table(TOP + 8)
    isP = lambda X: pi.get(tuple(X[1:])) == X[0]
    # sanity: the members of S within the table are P-positions, the W are not
    members = {n: [] for n in FAM_NAMES}
    for a in range(1, TOP + 1):
        for b in range(a + 1):
            for c in range(a + 1):
                for d in range(min(b, c) + 1):
                    for e in range(min(b, 1) + 1):
                        for f in range(min(e, d, 1) + 1):
                            for k in range(min(c, 2) + 1):
                                X = (a, b, c, d, e, f, k)
                                for n in FAM_NAMES:
                                    if in_fam(n, X):
                                        members[n].append(X)
                                        assert isP(X), (n, X)
                                assert not (is_W(X) and isP(X))
    for X in SMALL:
        assert isP(X), X
    print("families: %d, members up to height %d: %d; small positions: %d; all P in the table (%.0f s)"
          % (len(FAM_NAMES), TOP, sum(map(len, members.values())), len(SMALL), time.time() - t0))

    # closure problems: family x cell
    problems = []
    for n in FAM_NAMES:
        for cell in range(7):
            hyps = FAM[n](XV) + legal_atoms(XV, cell, TV)
            Y = cut(XV, cell, TV)
            samples = []
            for X in members[n]:
                if X[0] > 26:
                    continue
                for t in range(1 if cell == 0 else 0, X[cell]):
                    samples.append(ienv(X, t))
            if len(samples) > 3000:
                samples = samples[::len(samples) // 3000 + 1]
            pr = Problem("cl_%s_%d" % (n, cell), hyps, w_atoms(Y), Y, samples,
                         "A bite of a member of `%s` in the column `%s`." % (n, CELLS[cell]))
            pr.fam, pr.cell = n, cell
            if not samples:
                # no legal bite at all in this column (the column is empty in this family)?
                solver = z3.Solver()
                zenv = {m: z3.Int(m) for m in FIELDS + "t"}
                solver.add([a.z(zenv) for a in hyps] + [zenv[m] >= 0 for m in zenv])
                pr.empty = solver.check() == z3.unsat
                assert pr.empty, pr.name
            else:
                pr.empty = False
                solve(pr, verbose=True)
            problems.append(pr)
    print("closure lemmas: %d (%.0f s)" % (len(problems), time.time() - t0))
    out = os.path.join(ROOT, "lean", "Chomp", "BlockFamilies.lean")
    open(out, "w").write(emit_families(problems))
    print("wrote", out)
    return problems, members, pi


if __name__ == "__main__":
    main()
