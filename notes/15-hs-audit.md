# Huddleston–Shurman's three-wide theory: an audit

[notes/13](13-side-class-theorem.md) proves that the side class `𝒮` of three-wide Chomp is
infinite. Huddleston and Shurman ("Transfinite Chomp", MSRI 42, 2002) use that fact without proof
in showing that the tall box `3×ω^ω` is a P-position. This note checks the rest of their §8–§10
argument as far as computation can, and records exactly where `𝒮` enters.

The exact oracle `tools/hs_oracle.py` (notes/12, Step 1a) decides every position with at most
three columns of height `< ω^ω` by their formulas. The checks below test those formulas against
the game's definition. They use the exact side class to `x = 50000` from
`data/side-class/` (exact because `τ(x) ≤ 2x+1`, notes/13 Step A) and exact finite tables. The
convention is theirs: unrestricted Grundy values, so the empty position has value 0 and
P-positions have value 1.

## The parts of the argument

| part | content | status |
| --- | --- | --- |
| §9, (9-1) | two finite columns: closed formula | checked by brute force for heights `< 120` |
| §9, (9-2)–(9-5) | two columns of height `< ω^ω` | checked as a mex recursion (below) |
| Prop 6.1 | Beanstalk Lemma: one infinite column plus a finite part has infinite value | proved in the paper; sharpened in notes/09 |
| Thm 8.1 | Side-Top Theorem: `(ω+a, ω+b, x)`, `x` finite | the proof is complete; it uses only the mex definition of `G_𝒮` |
| §10, (10-1) | three columns, `ω ≤ x < ω^ω`: decomposition (i)–(iv) | the proof is a sketch; checked locally (below) |
| §10, end | the tall box `3×ω^ω`: a named reply to every bite | every named reply checked P (below) |
| — | `𝒮` is infinite | **notes/13** |

## Where `𝒮` enters

1. **The tall box, bite `(0,z)`, `ω ≤ z < ω²`.** The reply is a side `x` with
   `G_𝒮(x) = G(2×(ω·n+c))`, where `z = ω·(n+1)+c`. These targets are unbounded. This is the
   use noted in notes/13.
2. **Criterion (10-1) itself.** (10-1) says that no position in case (i) is P. Already for
   the simplest such positions, this is equivalent to `𝒮` being infinite:

   > **Proposition.** Let `B_a = (ω+a, ω, ω)`, the three columns of heights `ω+a`, `ω`, `ω`.
   > Given the Side-Top Theorem and the Beanstalk Lemma, `B_a` is N iff `𝒮` has an element
   > `s_a` of index `a`. Its only winning move is then the cut of the third column to `s_a`.
   > Hence (10-1) holds for every `B_a` iff `𝒮` is infinite.

   *Proof.* The options of `B_a` are:
   * `B_{a′}` for `a′ < a` (cut the first column to `ω+a′`; `B_0 = (ω,ω,ω)` is the cut at `ω`);
   * rectangles `(t,t,t)` with `t` finite, which are N;
   * `(ω+a, t, t)` with `t` finite, which is N by the Beanstalk Lemma;
   * Side-Top positions `(ω+a, ω, x)` with `x` finite.

   By the Side-Top Theorem, `(ω+a, ω, x)` is P iff `x ∈ 𝒮` and `G_𝒮(x) = G(a, 0) = a`, i.e.
   `x = s_a`. Induction on `a`: if `s_0, …, s_a` all exist, every `B_{a′}` with `a′ < a` is N and
   `B_a` is N by the cut to `s_a`. If `𝒮` has exactly `m` elements, `B_0, …, B_{m−1}` are N, and
   `B_m` has no P option, so it is P. That contradicts (10-1). ∎

   The search confirms this: the only P option of `B_a` is the cut to `s_a` (for example
   `a = 100`, `s_a = 241`; options searched with coefficients `≤ 8`, finite parts `≤ 600`).

   The same happens throughout case (i), `A = (ω·n+a, ω·n+b, ω·n+c)`:
   * for odd `n` the only P option is a Side-Top cut to the side element of index
     `G(ω·(n−1)+a, ω·(n−1)+b) = 3^{n−1}·G(a,b) + (3^{n−1}−1)/2`;
   * for example, the only P option of `(ω·3+12, ω·3+3, ω·3)` is the cut to `227`, the side
     element of index 94;
   * for even `n` there can also be a cut of the second column, e.g.
     `(ω·2+5, ω·2+3, ω·2) → (ω·2+5, ω+3, ω+3)`.

   So the proof of (10-1) in §10 cannot be complete without `𝒮` infinite. Where it says "the
   needed bite has `z = ω^j·z_j + c′` with `ω^j·z_j = G(U_b′)`", the case of finite `G(U_b′)` is
   a finite `z`, i.e. a Side-Top reply. Its existence is exactly an element of `𝒮` of the
   required index. With notes/13 this step is now justified.

## The criterion in closed form

Unwinding the decomposition (i)–(iv) with the two-column formulas gives an explicit list.
Write `i = deg x ≥ 1` and

`u = ω^{i+1}·U + ω^i·u_i + a`, `v = ω^{i+1}·V + ω^i·v_i + b`, `x = ω^i·x_i + c`,

with `u_i, v_i, x_i` finite, `x_i ≥ 1`, and `a, b, c < ω^i`. Here `U` and `V` are arbitrary
ordinals. Then `(u, v, x)` is P iff `U = V = m` is finite and one of the following holds:

| family | bottom condition | top condition | (10-1) case |
| --- | --- | --- | --- |
| A, `v_i = x_i` | `m = 0`, `u_i = 2x_i` | `a = G(b, c)` | (ii) |
| A, `v_i > x_i` | `m = 0`, `u_i = v_i + x_i` | `a ⊕ b ⊕ c = 0` | (iv) |
| B, `u_i = v_i` | `m = x_i ≥ 1` | `c = G(ω^i·u_i + a, ω^i·u_i + b)` | (iii) |
| B, `u_i > v_i` | `m ≥ 1`, `x_i = m + u_i − v_i` | `a ⊕ b ⊕ c = 0` | (iv) |

`G` is the two-column value and `⊕` is the coefficientwise nim-sum.
* **Bottom.** In every family the two left columns' bottom part has value `ω^i·x_i`, the value
  of the right column's bottom part. For example, `G(ω^{i+1}·m + ω^i·u_i, ω^{i+1}·m + ω^i·v_i)
  = ω^i·(m + u_i − v_i)`.
* **Top.** When two adjacent columns have equal coefficients at `ω^i`, their tops merge into a
  two-column piece.
* **Never P.** Case (i), and every position with `U ≠ V` or with `U` infinite.
* **Check.** `scripts/hs_families.py` compares this list with the oracle on 200000 random
  positions with `ω ≤ x < ω⁴`, biased toward the boundary relations. There are 1227 P-positions
  among them, and no mismatch.

The tall box's replies are instances:
* `(ω^{i+1}·x_i + a, ω^{i+1}·x_i + a, ω^i·x_i + c)` is family B with `u_i = v_i = 0`;
* `(ω^i·2x_i + G(c,c), ω^i·x_i + c, ω^i·x_i + c)` is family A.

A complete proof of (10-1) ([notes/16](16-three-wide-proof.md)) amounts to checking, for this list together with the Side-Top
positions, that no P-position has a P option and that every other position has one. The checks
below do this on samples.

## Checks

**Two columns** (`scripts/hs_check_two.py`). `G(h,k)` must be the mex of its options' values.
For random `(h,k)`:
* no option has the same value;
* every smaller value with small coefficients is the value of some option.

Results: 300 positions below `ω³` and 150 below `ω⁴`, none inconsistent. (9-1) agrees with brute
force for all heights `< 120`.

**Three columns, local consistency** (`scripts/hs_check2.py`). The criterion is correct (by
induction on the position) iff no position it calls P has an option it calls P, and every
position it calls N has one. Options of a column of height `h` are enumerated completely in the
form `t = (terms of h above ω^k) + ω^k·c + L` with `c < h_k`, up to bounds on `L`'s coefficients.
The earlier check (`scripts/hs_check.py`) used tiny coefficients and left 83 N-positions
unverified. With wider bounds:

| positions | heights | N with a P option | N unverified | P consistent | inconsistent |
| --- | --- | --- | --- | --- | --- |
| 3000 random | `< ω³` | 2991 | 0 | 9 | 0 |
| the 1176 distinct P replies found | `< ω³` | – | – | 1176 | 0 |
| 225 P replies from another sample, finite parts of options `≤ 1500` | `< ω³` | – | – | 225 | 0 |

Some replies are deep:
* `(ω·3+12, ω·3+3, ω·3)` → `(…, 227)`;
* `(ω²+ω·3+11, ω²+ω·3+9, ω²+ω·2)` → third column cut to `ω+445`.

Both depths come from (9-2): `G(ω·u+a, ω·u+b) = 3^u·G(a,b) + (3^u−1)/2`.

**The written proof's replies** (`scripts/hs_proofcheck.py`). For an N-position with
`ω ≤ x`, §10 prescribes the kind of winning bite from the two bottom values:
* `G(U_b) = G(X_b)`: a bite into one top component;
* `G(U_b) < G(X_b)`: a bite `(2,z)` into `X_b`;
* `G(U_b) > G(X_b)`: a bite `(0,z)` into `U_b` but not `X_b`.

In 397 random N-positions below `ω³`, a P reply of the prescribed kind exists every time:

| case | `G(U_b) < G(X_b)` | `=` | `>` |
| --- | --- | --- | --- |
| (i) | 44 | – | – |
| (ii) | 13 | 8 | 100 |
| (iii) | 17 | 17 | 27 |
| (iv) | 56 | 13 | 102 |

In case (i) `G(U_b) = G(2×ω^i·u)` is always below `G(X_b) = ω^i·u`, so only `<` occurs.

**The tall box** (`scripts/hs_tall_box.py`). For every bite `(e,z)` with `z < ω⁴` (coefficients
`≤ 3`, finite part `≤ 30`) and `z < ω³` (coefficients `≤ 6`, finite part `≤ 40`), the reply named
in §10 is P by the criterion: 3991, 3991 and 3921 bites for `e = 2, 1, 0`, with no failure.
* The `e = 0` replies with `ω ≤ z < ω²` use side elements up to index 14701 (`x = 35490`).
* The rectangles `3×z` with `z` finite are N by strategy stealing.
* The inverse of `a ↦ G(2×a)` used for the `e = 2` replies is explicit: `G(2×a)` for
  `a = ω·k + a₀` is `3^k·⌊(3a₀+1)/2⌋ + (3^k−1)/2`, which takes every natural value exactly once.

## Section 11 (the `2×2` base) has no such gap

§11 classifies the P-positions over a `2×2` base, including `2×2×ω³`. Its Front-Top Theorem
uses a restricted Grundy value on a "front class" `F`, just as the Side-Top Theorem uses `𝒮`.
Here, though, the class is given explicitly by the finite P-positions PA1 and PB1. Write the
heights as `u = (0,0)`, `v = (0,1)`, `y = (1,0)`, `z = (1,1)` with `v ≥ y`. Then:
* (PA1) for `z = y` the position is P iff `u = v + z + 1`;
* (PB1) for `z < y` the P-positions are `u = v = y = z+1`.

So every front `1×2×z` lies in `F` with `G_F = z`, and no infinitude has to be proved.
`scripts/hs_check_22.py` confirms PA1 and PB1 by brute force for all heights `≤ 16` (4844
positions). The `3×ω^ω` theorem is the only place in the paper where an infinite class is
assumed rather than constructed.

## Conclusion

Within these ranges the three-wide criterion behaves exactly as a correct characterisation must.
The tall box's named replies are all P under it. The one non-local ingredient is `𝒮` being
infinite, which the criterion needs as well as the tall-box proof. It is now proved (notes/13).
The paper's proof of (10-1) is a sketch. The checks above find no case where its prescribed
replies fail.

**Update.** [notes/16](16-three-wide-proof.md) proves the closed form below completely, using
only §8, §9 (two-column values), the Beanstalk Lemma and notes/13. This closes the gaps in §10
of Huddleston–Shurman's proof that `3×ω^ω` is a P-position.
