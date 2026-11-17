# What the literature says, and how it matches our results

Seven sources, read in full:

* **[HS]** S. Huddleston and J. Shurman, *Transfinite Chomp*, More Games of No Chance (MSRI
  Publications 42), 2002, 183–212.
* **[N17]** R. J. Nowakowski, *Unsolved problems in combinatorial games*, Games of No Chance 5
  (MSRI Publications 70), 2017, problem D1.
* **[B03]** S. Byrnes, *Poset game periodicity*, Integers 3 (2003), #G3.
* **[DFP]** A. Dress, A. Flammenkamp and N. Pink, *Additive periodicity of the Sprague–Grundy
  function of certain Nim games*, Adv. Appl. Math. 22 (1999), 249–270.

## Conventions

[HS] use **unrestricted** Grundy values: the poison alone has value 1, the empty position has
value 0, and P-positions are exactly those with value **1**. Our tools (`rows`, the notes) use
**restricted** values, where the poison move is forbidden and P means value 0.
* For finite values, restricted = unrestricted − 1.
* From `ω` on, the two agree.

Checked: our 2D tool reproduces [HS] Table 1 (finite two-wide values) exactly on 12 entries
after adding 1, and their formula (9-3), `G(ω+a, b) = ω + (a ⊕ b)`, matches our `G(ω, b) = ω+b`.

## The problem itself

* [N17], D1: "David Gale asks for the solution of the infinite 3D version where the board is the
  set of all triples (x, y, z) of nonnegative integers … The problem is to decide whether it is a
  win for the first or second player."
* **None of [HS], [N17] or Gale's book chapter [G98] mentions a prize.** The $100 comes only
  from Wikipedia's uncited remark. The original *Intelligencer* columns are unchecked.
* [HS] do not discuss `ω×ω×ω` at all.

## Results of [HS] that bear on our work

| [HS] | Statement | Relation to our work |
| --- | --- | --- |
| Thm 5.1 (Fundamental Theorem) | For a `d`-dimensional `A` and a nonempty `(d−1)`-dimensional base `B`, there is a unique `h` such that `E(A,B,h) = A + (B×Ω)` truncated at height `h` is P. | Our P-height `h(B)` is their `H(∅, B)`. **`ω×ω×ω` is P iff `H(∅, ω×ω) = ω`.** |
| Proof of 5.1 | `H(A,B) = mex(M_ω)` with `M_ω = ⋃ M_i`. `M_0` comes from bites into `A`. `M_{i+1}` holds the heights of the P-positions `A + E(A,B,k) − v` over a smaller base `B − u`, for `k ∈ M_i`. | For `A = ∅`, `B = ω×ω`: `M_1` is the set of P-heights of the proper sub-bases, i.e. the **strips** `k×ω` and the **L-bases** `L(a,b)`. Their extensions are our rods `k×h×ω` and our **L-prisms**, the same objects as our P-pairs. Known members: `H(1×ω) = 2`, `H(2×ω) = 1`, `H(L(1,1)) = 1`. So `H(∅, ω×ω) ≥ 3`, as we found. |
| Cor 5.2 (Size Lemma) | `H(A, B₀) ≤ 1 + size(A − B₀×Ω)` for the poison base `B₀`. | This bounds our `f` (completing height). |
| Prop 6.1 (Beanstalk Lemma) | A finite position plus a tower of height `h` over the poison has a Grundy value with the same leading term as `h`. | Our exact `G(ω, R) = ω + γ(R)` (notes/09) and its 3D one-column version (notes/10) sharpen this for `h = ω`. |
| Thm 7.1 | `G(X × P) = G(X)` whenever `P` is a **P-ordered** P-position: `2×ω`, `(1×(i+1)) + (2×i)`, or `(1×a) + (a×1)`. | **New exact Grundy values for first-move results:** after `(0,0,2)` the position `ω×ω×2 = ω × (2×ω)` has `G = ω`, and after `(0,1,1)` the position `ω × L(ω,ω)` has `G = ω`. Rods `n×2×ω` have unrestricted `G = n`, which is our domino rule with values. In 6D, `ω×ω×ω×2×2×2` is P. |
| Thm 8.1 (Side-Top), Thm 11.1 (Front-Top) | `2×ω` (or the brick `1×2×ω`) with finite material on one side and anything on top is P iff the restricted Grundy value of the side equals that of the top (when the side's P-height is infinite), and N otherwise. | These are the two-wide-stalk positions our certified solver decides (notes/07). [HS] mention a more general "Base-Top Theorem", with finite material on several sides, without stating it. Our family `T(a,b)` (material beside *and* in front of the stalk) is such a case, and our exact P-table is data for it. |
| §9 | Grundy values of **all** two-wide positions, e.g. `G(ω·u, ω·u) = (3^u − 1)/2`. | Agrees with our tool where both apply. |
| §10 | All three-wide P-positions; `3×ω^ω` is P. | Agrees with `G(3×ω) ≠ 0`. Our heuristic `G(3×ω) = ω+1` is not stated in [HS]. |
| §11 | P-positions of `2×2×Ω` (types A–F); `2×2×ω³` is the only type F. | Our `2×2×ω` being N is their type C (PC2). |
| §12 | Stratification Conjecture 12.1; two one-wide stalks or one two-wide stalk is "not difficult to show recursive"; `3×Ω` believed recursive; `G(4×ω)` open. | See below. `3×Ω` recursive: now proved, given their §8–§9 ([notes/16](16-three-wide-proof.md)). |

## Open questions in [HS] §12, against our results

* **Stratification Conjecture.** Define `strat(X, ω^i)` by deleting every rectangle of size less
  than `ω^i` from the construction of `size(X)`. The conjecture: if `strat(X, ω^i) =
  strat(Y, ω^i)` then `strat(G(X), ω^i) = strat(G(Y), ω^i)`. [N17] phrase it as "if the number of
  elements taken in a move is `< ω^i`, then the change in the nim-value is also `< ω^i`".
  * Our **Hypothesis E** (notes/10) is this conjecture at `i = 1` for 2D positions with
    infinite rows.
  * Their *size* plays the role of our Hilbert polynomial: both record the leading growth of the
    position.
  * [N17] also points to **Dozier & Perry** [DP16], who play Chomp on monomial monoideals
    ("Ideal Nim"). Their paper uses the ideal view only for termination (Dickson's lemma) and
    small values, not for Hilbert polynomials or Grundy growth. See below.
* **One two-wide stalk is recursive.** [HS] say this is "not difficult to show" but give no
  algorithm. Our certified solver (notes/07) is such an algorithm, with a certificate.
* **`G(4×ω)`.** [HS] show `G(4×ω) = mex(L)`, where `L` is the set of values of `(4×a) + (2×ω)`
  and `4×a` for finite `a`. In our notation these are `G(ω,ω,a,a)` and `g(a,a,a,a)`, exactly the
  two families we computed (notes/09).
  * **`L` contains every unrestricted value below 46**, and 46 would need some `a > 480`. If
    `mex(L)` is infinite they believe `G(4×ω) = ω·2`.
  * Our computation stopped at `a ≤ 40`, where restricted 15 (unrestricted 16) had not yet
    appeared. So that gap was an artefact of the range, as we suspected. A run to larger `a`
    checks this. For `41 ≤ a ≤ 80` the only new value below 46 is `G(ω,ω,42,42) = 24`
    (restricted), so restricted 15 has still not appeared by `a = 80`. That is consistent with
    [HS], whose witnesses go up to `a ≈ 480`, but our range cannot confirm it. Our values for
    large `a` are approximate (`T = 16`, no frontier rule).

## Gale's own account: [G98]

**[G98]** D. Gale, *Tracking the Automatic Ant and Other Mathematical Explorations*, Springer
1998, chapter 11 "Games: Real, Complex, Imaginary", section "Games people could play",
pp. 78–81. This is the book version of his *Intelligencer* columns, and it is where [HS] point
for the history.

* **The problem.** "The game on the positive octant in 3-space remains unsolved; is it a first-
  or second-player win?" Gale says the new results "reduce this question to a problem in the
  arithmetic of transfinite ordinals". **No prize is mentioned.** So the $100 remains
  unsourced. The only places left to check are the original columns (*Math. Intelligencer* 15:3,
  1993, 59–60; 18:3, 1996, 26).
* **The reduction.** "The problem would be solved if one knew for which ordinal α the `ω×ω×α`
  game is a P-position." That is our reformulation `h(ω×ω)` (README, fact 5).
* **Gale's simpler question.** "A possibly simpler question is to decide whether the `3×3×ω` game
  is a first-player win. Any takers?" This is exactly the open case of Idea 1 (notes/01). Our
  solvers say N only heuristically, with winning moves that change with the cap, and the hybrid
  solver returns "unknown" (notes/06).
* **History of the Fundamental Theorem.** Huddleston communicated it to Gale. The proof printed
  is a modification of one by **George Bergman**, which also shows the P-height of `n×·` is a
  countable ordinal. Gale also states the 3D version: for all `α, β` there is a unique `γ` with
  `α×β×γ` P.
* **Huddleston's claims in 1998.** Gale reports that "Huddleston is convinced that the
  rectangles `3×ω^ω` and `4×ω²` are P-positions", and that `2×2×ω³` is P.
  * [HS] later proved `3×ω^ω` and `2×2×ω³`.
  * **`4×ω²` is not mentioned in [HS]**, which instead lists `G(4×ω)` as open. So that claim
    should be treated as an unproved conjecture.
* **Finite Chomp.** Gale's uniqueness conjecture for winning first moves fails: `6×13` has two.
  `ω×ω` is won by "row 3, column 1", our `(0,2)`.

## Periodicity theorems: [B03] and [DFP]

**[B03], the Poset Game Periodicity Theorem.** Take a poset with two infinite chains `C`, `D`
(no element of `C` below an element of `D`) and a finite set `A`. Let `A_{m,n}` be the position
with the chains cut at lengths `m` and `n`, and fix a value `k`. Then either only finitely many
`A_{m,n}` have Grundy value `k`, or the function `f_{A,k}(m)`, the `n` with `g(A_{m,n}) = k`,
satisfies "`f_{A,k}(m) − m` is eventually periodic".

* **Lemma 5** bounds the offsets: `g(A_{m,n}) = k` implies `n − m ≤ |A| + k`.
* **Lemma 10** says `f_{A,k}` can be found in finite time, by guessing its periodic form and
  checking it symbolically.
* **Corollary 4** covers one chain: `g(A_n) − n` is eventually periodic.

How this fits our work:

* **The two-wide-stalk solver (notes/07) is the case `k = 0` of this theorem.** The chains are
  the poison column and its infinite neighbour `c`, and our `F_R(z)` is `f_{A,0}`. Our
  repeated-state simulation is an efficient, self-certifying version of the proof of Lemma 9
  (which tracks the same window of offsets `S(m)`).
  * Soundness was already immediate: the dynamics are deterministic, so a repeated state
    repeats forever.
  * **Lemma 5 now also gives termination.** The offsets are bounded, so the state space is
    finite and a repeat must occur.
* **Corollary 4 is the published core of our `G(ω, R) = ω + γ(R)`** (notes/09). The truncations
  of the infinite row satisfy "`g − n` eventually periodic", and being injective, they take
  every large value.
* [B03] also covers values `k > 0`. So the same certificate can be extended from P-positions
  to Grundy values of two-wide stalks, which is what the prediction of notes/10 needs (all
  positions with two infinite columns have finite Grundy value).
* With three or more chains no such theorem is known. That matches the boundary where our exact
  methods stop.

**[DFP], Theorem 3.** Suppose a sequence is defined as the mex of its own past together with
finitely many shifted additively periodic sequences, on what they call a T-extension of a
finite-type graph. Then it is additively periodic. This gives Wythoff's rows and columns, and
is the general form of the recursions above. Remark 6 and Theorems 1–2 contain the
bounded-offset argument that guarantees a finite state.

## A related but different game: [RH26]

**[RH26]** F. Rivero Herrera, *Hanf numbers for poset games*, arXiv:2504.07317v3 (2026),
formerly *A poset game on submonoids of additively indecomposable ordinals*.

* It plays Chomp on **lexicographic** products and powers of well partial orders. Its main
  examples are submonoids of `ω^σ` under the natural (Hessenberg) sum, ordered by "`β − α`
  lies in `S`" with ordinary left subtraction.
  * On the full monoid `ω³` this order is lexicographic, a well-order, so Chomp is trivial there.
  * The interesting cases come from numerical-semigroup generators, extending García-Marco &
    Knauer's *Chomp on numerical semigroups*.
  * **It is not our game.** `ω×ω×ω` uses the componentwise order, which corresponds to the
    natural sum with *componentwise* subtraction.
* **Lemma 3.5** shows why the lexicographic case is easy and ours is not. For lexicographic
  powers, a first-player win on `P^α` gives one on every larger power: play `(0, t)` for the
  winning move `t` and what remains is an isomorphic copy. For the componentwise order the same
  move leaves `P × (T ∖ ↑t)`. So "`ω×ω` is N" says nothing about `ω×ω×ω`.
* **Theorem 4.5** proves that a "Hanf number" threshold `ch(Γ)` exists and is below `ω₁` (for
  finite `Γ ⊂ ω`). It uses elementary embeddings and writes "B wins" as an infinite conjunction
  of first-order sentences. It shows existence, not values, and concerns families indexed by
  `σ` rather than one fixed board, so it does not help with `ω×ω×ω` directly.

## Chomp on ideals: [DP16]

**[DP16]** H. Dozier and J. Perry, *Androids armed with poisoned chocolate squares: ideal Nim and
its relatives*, Math. Mag. 89(4) (2016), 235–250. An expository article.

* **Ideal Nim** is Chomp with an arbitrary finite antichain of "poison" generators: play happens
  on the monoideal northeast of them, and the last player to take a healthy square wins. Gobbled
  squares always form a monoideal of `N^n` (equivalently a monomial ideal), hence the name.
* **Dickson's lemma** is shown equivalent to termination of every game, with a game-based proof.
* **Worked values:** small configurations, a closed binary rule for one row plus one column, and
  "Couch Potato". That example is an infinite two-row strip won by the second player with the
  pairing `(m,0) ↔ (m−n,1)`, a shifted form of the `2×ω` argument.
* **Gröbner Nim** is a game version of Buchberger's algorithm.
* **What it does not contain:** Hilbert polynomials, the growth of Grundy values, transfinite
  positions, or `ω×ω×ω`. So our Hypothesis E (leading Grundy term fixed by the Hilbert
  polynomial) is our own phrasing. Its content is the Huddleston–Shurman Stratification
  Conjecture, since their `size` records the same leading growth.

## What this changes

1. **The right recursion for `h(ω×ω)`** is the Fundamental Theorem's `M_ω`. `M_1` consists of
   the P-heights of strips and L-bases, and its finite part is `{1, 2}` plus any finite P-height
   of an L-prism or a strip of 3 or more rows. If Conjecture 1.1 holds, strips of 3 or more rows
   have no finite P-height, which leaves L-prisms.
   * `ω×ω×ω` is P iff `M_ω` contains every natural number but not `ω`.
   * So the L-prisms `L(a,b)×h` and the towers in `M_2, M_3, …` are exactly the positions to
     study. This agrees with what our P-pair analysis pointed to (notes/04).
2. **Product positions** (Thm 7.1) give exact Grundy values for free, and should be seeded into
   the solvers' tables of known values.
3. **Attribution.** The tools and data are ours. The underlying theory (Fundamental Theorem,
   stratification, recursiveness of two-wide stalks) is theirs.

## Still worth reading

* Gale's original *Intelligencer* columns (15:3, 1993, 59–60; 18:3, 1996, 26): the only remaining
  place the $100 prize could come from, since the book chapter [G98] does not mention it.
* Landman (MSRI 42, 2002): the short finite-state-machine proof for Wythoff rows. Optional now
  that [B03] and [DFP] are read.
