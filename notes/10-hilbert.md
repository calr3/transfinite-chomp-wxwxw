# Idea E: does the "size at infinity" fix the leading term of the Grundy value?

**The idea.** A Chomp position on `N^d` is the set of monomials outside a monomial ideal. Its
growth at infinity is measured by the Hilbert polynomial of the quotient:
* the degree is the number of independent infinite directions;
* the leading coefficient is the multiplicity.

The Huddleston–Shurman Stratification Conjecture says the large-scale part of a position
determines the large-scale part of its Grundy value. A concrete form to test:

> **Hypothesis E.** The coefficient of the highest power of `ω` in `G(X)` depends only on the
> Hilbert polynomial of `X`.

In 2D, for `k` rows of which `j` are infinite, the Hilbert polynomial is the constant `j`. So
the test is: **is the `ω`-coefficient of `G` the same for all positions with `j` infinite rows,
whatever finite rows sit on top?**

## Data (from Idea D, `tools/rows.cpp`)

| infinite rows `j` | positions checked | `ω`-coefficient of `G` | status |
| --- | --- | --- | --- |
| 0 | all finite positions | 0 | trivial |
| 1 | all | **1**, `G = ω + γ(R)` | **proved** (notes/09-rows.md) |
| 2 | 21 (up to two finite rows of length ≤ 5), plus `(ω,ω,x,x)` for `x ≤ 18` | 0 in every case | heuristic, stable in `T` |
| 3 | 16 (`(ω,ω,ω,x)` for `x ≤ 10` and five with two finite rows) | 1 in every case | heuristic, uses the frontier rule, stable in `T` |
| 4 | `4×ω` only | unknown (literature: at least 46?, conjectured `ω·2`) | out of reach |

**Every case computed fits Hypothesis E.** Within each `j` the finite part of `G` varies wildly
(e.g. `G(ω,ω,R)` takes the values 0 to 16 in no visible order), but the leading term does not.
The leading coefficients so far are `1, 0, 1` for `j = 1, 2, 3`. If the conjectured `ω·2` for
`j = 4` is right, the sequence is not periodic. We have no formula.

## An exact 3D statement of the same kind

The proof for one infinite row works word for word for rods in 3D:

> In a rod position (finite cross-section, heights in `N ∪ {ω}`) whose only infinite column is
> the poison column, `G = ω + γ`, where `γ` is the normal-play Grundy value of the other columns
> with no poison.

The cuts of the poison column at `x` form a row of the mex table, blocking its own past and the
injective rows for the finitely many fixed parts. So they take every natural value, and the other
options are rods of the same kind. This is Hypothesis E for Hilbert polynomial `1`: leading
coefficient 1, always.

For two infinite columns (Hilbert polynomial `2`), Idea B found many exact P-positions (`G = 0`):
`2×ω`, and the pairs `(0,0), (1,1), (2,4), (3,2), (4,5), (5,3)` of the family `T(a,b)`. If
Hypothesis E holds there, **every** position with two infinite columns has a finite Grundy value,
as in 2D. That is a sharp, testable prediction. Testing it needs Grundy values (not just P/N)
for two-wide stalks, which the certificate method of Idea B could provide by tracking values
instead of P/N.

## What it would mean for `ω×ω×ω`

* If the leading term is fixed by the Hilbert polynomial, positions can be grouped into large
  classes that share a leading term. P-positions can only occur where that term is 0.
* Data so far: in 2D, `j = 2` gives leading term 0 (so P-positions occur) and `j = 1, 3` give
  `ω`-coefficient 1 (no P-positions at all).
* In 3D, the options of `ω×ω×ω` have Hilbert polynomials of degree 2:
  * the slab `ω×ω×c` has `c·n + const`;
  * two crossing slabs have degree 2 as well.

  Knowing the leading term per Hilbert polynomial would show at once which options *cannot* be
  P. That is exactly the information the first-move problem needs.
* We cannot compute any 3D values with an infinite slab, so this is a direction, not a result.
