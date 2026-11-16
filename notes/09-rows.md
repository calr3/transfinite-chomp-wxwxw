# Idea D: ordinal Grundy values of 2D positions with infinite rows

**Why.** Positions that split into independent parts are disjunctive sums, so their outcome needs
Grundy values, not just P/N. Two examples:
* the rod plus a plane from Idea 4: `N³ ∖ ↑{(1,1,0),(1,0,1)}` is P iff the Grundy value of the
  2D board `ω×ω` is `ω`;
* the open problem "Grundy value of `ω×4`" from the unsolved-problems lists.

2D positions with a few infinite rows are the simplest testbed for computing ordinal values.

**Tool.** `tools/rows.cpp` takes `k` rows of lengths in `N ∪ {ω}`, with row 0 holding the
poison. Values are ordinals below `ω²`, written `ω·n + m`.

## An exact result: one infinite row

> **`G(ω, R) = ω + γ(R)`**, where `R` is the finite rows above the infinite one and `γ(R)` is
> the ordinary normal-play Grundy value of `R` with **no poison** (every cell may be taken, and
> the player who cannot move loses).

*Proof.*
* **Every natural number occurs.** The options that cut the infinite row at `x` are finite
  positions `(x, min(R,x))`. For `x ≥ max R` their values `g(x, R)` form a row of the mex table:
  `g(x,R)` is the mex of its own earlier values, finitely many constants, and the values
  `g(x, R')` for the finitely many options `R'` of `R`. Each of those is injective in `x`. If some
  `n` never appeared, then from some point on `n` would have to be blocked at every `x`. That
  can't happen: each injective sequence blocks it at most once, and every value below `n` is
  taken at most once. So `{g(x,R)}` is all of `N`, and `G ≥ ω`.
* **The ω-level.** Every other option is `(ω, R')` for an option `R'` of `R`, with value
  `ω + γ(R')` by induction. Hence `G = ω + mex{γ(R')} = ω + γ(R)`. ∎

Examples: `G(ω) = ω`, `G(ω,1) = ω+1`, `G(ω,1,1) = ω+2`, `G(ω,3,3) = ω+5`.

The first step is a case of Byrnes's Corollary 4 (one growing chain: `g(A_n) − n` is
eventually periodic). The formula as a whole sharpens the Huddleston–Shurman Beanstalk Lemma
(leading term `ω`) to an exact value.

The first version of the tool guessed tails from contiguous runs and got `G(ω,3,3) = 23`. That
is wrong: the row sequences are permutations of `N` that wander a lot. This theorem replaced
that guess.

## Heuristic results: two or more infinite rows

With two or more infinite rows, the excluded values come from a two-parameter family, so the
argument above fails. The tool computes each family up to `F + T`, where `F` is the largest
finite length, and takes the mex. It uses a **frontier rule**: a gap at least half the largest
value seen at that level is treated as an artefact of the range. Results that use the rule are
flagged. All results below were checked for stability in `T`.

**Two infinite rows: all finite.** These values are identical for `T = 16` and `T = 24`, and
none uses the frontier rule:

| `R` | — | 1 | 1,1 | 2 | 2,1 | 2,2 | 3 | 3,1 | 3,2 | 3,3 | 4 | 4,1 | 4,2 | 4,3 | 4,4 | 5 | 5,1 | 5,2 | 5,3 | 5,4 | 5,5 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `G(ω,ω,R)` | 0 | 1 | 5 | 3 | 2 | 4 | 6 | 4 | 7 | 2 | 7 | 1 | 2 | 6 | 11 | 12 | 7 | 10 | 1 | 8 | 16 |

`G(ω,ω) = 0` is `2×ω`, as expected.

**Three infinite rows: all `ω + k`.** These use the frontier rule at level 0, i.e. they assume
every natural number is the value of some option:

* `G(ω,ω,ω) = ω+1`, the same for `T = 16, 24, 32, 40`;
* `G(ω,ω,ω,x)` for `x = 0..10`: `ω+1, ω+2, ω+4, ω+7, ω+8, ω+13, ω+9, ω+17, ω+11, ω+15, ω+16`;
* `G(ω,ω,ω,R)` for `R = (1,1), (2,1), (2,2), (3,1), (3,3)`: `ω+6, ω+3, ω+5, ω+5, ω+3`, the same
  for `T = 16` and `24`.

This fits Huddleston–Shurman's result that `3×β` is P only for `β = ω^ω`: `3×ω` is not P, and
indeed `G ≠ 0`. Their paper does not give `G(3×ω)`.

Note on conventions: Huddleston–Shurman use unrestricted Grundy values (P-positions have value
1). Finite values here are one smaller; from `ω` on the two agree. With that shift our tool
reproduces their Table 1 of two-wide values exactly.

**Four infinite rows (`ω×4`, the open problem): out of reach.** Huddleston–Shurman show
`G(4×ω) = mex(L)`, where `L` is the set of values of exactly our two families `G(ω,ω,a,a)` and
`g(a,a,a,a)`. They report that `L` contains every unrestricted value below 46 (restricted below
45), with witnesses up to `a ≈ 480`. So the gap we saw is an artefact of our range
(`notes/11-literature.md`).
* The least missing value at level 0 moves with the range: 10 at `T = 16`, and 15 at
  `T = 24`, `32` and `40`. The value 10 was filled by an option with `x` between 17 and 24.
  At `x ≤ 40`, every value below 15 is attained and 15 is not.
* The families feeding level 0 are very irregular. Small values turn up late:
  `G(ω,ω,11,11) = 1`, and `g(x,x,x,x)` goes `3, 5, 9, 6, 13, 16, 19, 12, …`.
* So a finite range says little here. This fits the problem lists' remark that the value
  "could be as low as 46". Presumably every value below 46 has been seen in larger computations,
  and the conjectured value is `ω·2`.
* The frontier rule misfired on two infinite rows: it gave `G(ω,ω,15,15) = ω·2`. Without it the
  value is 40, the same for `T = 24` and `T = 40`, and `G(ω,ω,16,16) = 41`. The rule is now used
  only with three or more infinite rows, where all the data support it.

## What this gives for `ω×ω×ω`

* One infinite row is fully understood, two are finite (heuristically), and three are `ω + k`
  (heuristically). That is the pattern Idea E tests.
* The value that matters for the disjunctive sum above, `G(ω×ω)`, has infinitely many infinite
  rows *and* columns, and this tool cannot reach it.
