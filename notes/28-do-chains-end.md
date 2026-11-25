# Do irregular chains always end? What is proved, what is measured, what is missing

25 November 2026. Continues [notes/27](27-how-a-chain-ends.md). Positions are written by the
heights of the nine columns in the order `(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) |
(2,0),(2,1),(2,2)`, `w` for an infinite column.

notes/27 ended with a working hypothesis: a position with the `2×2` block infinite is N
unless its chains are regular, because an irregular chain sooner or later has a P member.
This note is an attempt to prove that. **It does not succeed.** It records what can be
proved, a test of the mechanism behind the `1/u` law, an explanation of the constant, two
corrections to notes/27, and a precise statement of what a proof would need.

## Results

1. **No proof (§5).** The statement "every chain whose diagonal cell is eligible infinitely
   often has a P member" needs information about finite P-positions that nobody has, of the
   same kind as the open questions about three-row Chomp. The exact constraints we can prove
   do not imply it: an eligibility pattern that satisfies all of them and never ends is easy
   to write down (§2).
2. **Exact lemmas (§1).** A column of the grid is dead from the height of the finite P cut of
   a tripod position. The cells with a finite P cut at a given height above their row form a
   partial matching. The cells blocked by an attachment bite form a union of at most `B`
   partial matchings, where `B` is the number of attachment bites of the position.
3. **The mechanism of the law is the pool (§3, measured).** A row with `k` unused live
   columns has no partner with probability close to `δ^k`, `δ ≈ 0.43` to `0.49`: 38 %, 18 %,
   7 %, 5 %, 1 %, 0 % for `k = 1, …, 6`. The pool grows by about one column each time the
   height is multiplied by `e`. Chains do not differ durably from one another. So the `1/u`
   law is not produced by a mixture of chains with different constant rates.
4. **The exponent (§4).** In the model "no partner with probability `δ^k`, and then the
   diagonal is eligible with probability `ε`", the chance to be alive at height `h` is
   `h^−γ` up to constant factors, with `γ = ln(1/(1−ε)) / ln(1/δ)`. This is proved for the
   model. The measured `δ` and `ε` give `γ = 0.96` and `1.03` in two worlds where the
   measured constant of the law is 1.00 and 0.98. `γ = 1` exactly when `δ = 1 − ε`, that is,
   when the diagonal cell is as likely to be eligible as a cell of the pool. In the model
   every chain ends with probability 1, and its expected length is infinite.
5. **A second world (§3).** A new census with attachments up to 5 (812 positions with the
   block infinite, 562 irregular chains): the constant of the law is **0.98** with 534 chain
   ends. No new regular chain, and A and its transpose are again the only positions the
   census labels P.
6. **The classification with attachments up to 5 (§6, exact).** Of the 812 positions with
   the `2×2` block infinite and attachments of height at most 5, 362 have a finite P cut, 444
   are N by a certified reply that leaves two infinite columns, A and its transpose are P,
   and **4 are open**: `(w,w,5 | w,w,5 | 5,2,2)`, `(w,w,5 | w,w,5 | 4,3,3)` and their
   transposes. Both chains of each are exactly N up to height 24, and the census puts their
   first P members at heights 68 and 42, out of reach of the solver. They are in the position
   of A′: survivors of the kind the law leads one to expect, with no reason to be P.
7. **Two corrections to notes/27 (§3).** The worlds measured there are symmetric under
   transposition, so every chain was counted twice: the 216 chains are 108 pairs, and the
   208 chain ends are 104. The constant is unchanged, its uncertainty is about ±0.1. And the
   eligible cells are not confined to a narrow band below the diagonal: they are spread over
   the live part of the row. The partners are close to the diagonal, for another reason.

Items 2, 6 and the statement about the model in item 4 are proved or exact. Items 3, 5 and
the numbers in item 4 are measurements on census data (notes/26 §2).

## 1. What is exact

Let X have the columns `(0,0),(0,1),(1,0),(1,1)` infinite, finite attachments elsewhere, and
no finite P cut. As in notes/27, `S(u,v)` is X after cutting `(1,0)` at `u` and `(1,1)` at
`v ≤ u`; the chain member at height `u` is `S(u,u)`; the cell `(u,v)` is *eligible* if
`S(u,v)` has no finite P cut and no P option by a bite in an attachment column. Then
(notes/27 §1, the preprint `paper/three-by-three.pdf` §4):

> **The rule.** As long as no chain member below is P, `S(u,v)` is P iff `(u,v)` is eligible,
> no `S(t,v)` with `t < u` is P, and no `S(u,t)` with `t < v` is P. Row `u` takes the smallest
> eligible `v < u` that no earlier row has taken. The chain ends at the first `u` whose
> diagonal cell is eligible and whose row finds no such `v`. The number of unused columns
> grows by one at every row without a partner.

Three more statements about where the ineligible cells are.

**Lemma 1 (dead columns).** Let `T_v` be X after cutting `(1,1)` at `v`: a position with the
tripod `(0,0),(0,1),(1,0)` infinite. If `T_v` has a finite P cut at height `k`, then `k > v`,
and `S(u,v)` has the same finite P cut for every `u ≥ k`. Conversely, a finite P cut of
`S(u,v)` at a height `h ≤ u` is a finite P cut of `T_v`.

*Proof.* Cutting the poison column at `h ≤ u` cuts `(0,1)` and `(1,0)` to `h` and `(1,1)` to
`min(v,h)`. The result is the same for `S(u,v)` and for `T_v`. If `k ≤ v` it is X cut at `k`,
and X has no finite P cut. ∎

So column `v` has eligible cells only in the rows `v ≤ u < k(v)`, where `k(v)` is the finite P
cut of `T_v`. Whether every tripod position has a finite P cut is the conjecture of notes/17;
it holds for the 1001 tripod positions with attachments up to 4 (notes/26 §3).

**Lemma 2 (cuts above the row).** For a height `h`, let `C_h` be the set of cells `(u,v)`
with `u < h` such that `S(u,v)` has its finite P cut at `h`. Then `C_h` has at most one cell
in each row and at most one in each column.

*Proof.* For `v' < v ≤ u < h`, the position `S(u,v')` cut at `h` is an option of `S(u,v)` cut
at `h` (cut `(1,1)` at `v'`). For `v ≤ u' < u < h`, `S(u',v)` cut at `h` is an option of
`S(u,v)` cut at `h` (cut `(1,0)` at `u'`). Two positions of which one is an option of the
other are not both P. ∎

**Lemma 3 (blocked cells).** Let `X_1, …, X_B` be the positions left by the bites of X in its
attachment columns. A cell `(u,v)` has a P option by an attachment bite iff the cell `(u,v)`
of the grid of some `X_i` is P. For each `i` those cells have at most one in each row and
each column. So at most `B` cells of a row are blocked.

*Proof.* Bites commute: an attachment bite of `S(u,v)` leaves the position `X_i` cut at
`(1,0)@u` and `(1,1)@v`. Inside the grid of `X_i` two P cells in a row, or in a column, would
be an option of one another. ∎

So an ineligible cell is of one of three kinds: in a dead column (Lemma 1), in some `C_h`
with `h` above its row (Lemma 2), or blocked (Lemma 3). The second kind is not bounded: a
row can meet `C_h` for many `h`. That is why none of this gives a density.

## 2. The lemmas do not decide the question

A chain can go three ways.

* (a) It ends: some `S(u,u)` is P, and X is N.
* (b) It never ends because its diagonal cell is eligible only finitely often (*regular*).
  A's two chains are of this kind, with the finite cut of `S(u,u)` at `u+1`.
* (c) It never ends although its diagonal cell is eligible infinitely often: each time, a
  partner is available.

The working hypothesis of notes/27 is that (c) does not occur. The rule and Lemmas 1 to 3
allow it. Take the pattern: column `v` is dead from row `v+2` on; the cell `(u,u−1)` is
eligible for every `u`; the diagonal cell `(u,u)` is eligible for even `u` and has its finite
cut at `u+1` for odd `u`. Then every row takes the column `u−1`, no row is ever without a
partner, the diagonal needs one at every second row, and each `C_h` is a single cell. So
whatever excludes (c) is a fact about which finite positions are P, not about the shape of
the rule.

## 3. The mechanism, measured

`scripts/chain_band.py` reads a census dump (notes/26 §2, notes/27 §1) and follows every
irregular chain up to its first P member. For each row it counts the *live* columns (not yet
dead in the sense of Lemma 1, as far as the dump shows) and among them the *unused* ones (no
earlier row has taken them). The unused live columns are the pool of the row.

**The two worlds.** The `2×2` block with attachments up to 4 at `H = 253`, `Z = 120` (the
tall run of notes/27), and a new census with attachments up to 5:
`base3_table 160 -c H,H,5,H,H,5,5,5,5 -T 70` (table 1.0 GB, 91 million census positions,
8 minutes). The new world has 812 positions with the block infinite. 362 have a finite P cut,
448 are N in the census and two are labelled P: A and its transpose. Its chains
(`chain_survival.py`):

| heights | rows | diagonal eligible | no partner | chain ends | ends × height |
| --- | --- | --- | --- | --- | --- |
| 5–9 | 2154 | 28 % | 48 % | 296 | 0.88 |
| 10–19 | 1792 | 47 % | 18 % | 158 | 1.16 |
| 20–39 | 1450 | 49 % | 6.6 % | 62 | 1.15 |
| 40–69 | 1126 | 46 % | 2.5 % | 18 | 0.83 |

Fitted constant **0.98** (534 ends). Chains alive at heights 10, 20, 40, 70: 236, 102, 46, 28;
the law with that constant gives 230, 117, 59, 34. The six regular chains are the same six as
before (notes/27 §5).

**Correction: every chain is counted twice.** Both worlds are symmetric under transposition,
and the chain "cut `(1,0)`" of X is the chain "cut `(0,1)`" of the transpose of X. So the 216
chains of notes/27 are 108 pairs, the 208 ends are 104, the 8 chains alive at height 120 are
4, and the 562 chains here are 281 pairs. Ratios and the fitted constant do not change. The
statistical weight is half of what the counts suggest: the constant is `1.0 ± 0.1` in the
first world and `0.98 ± 0.06` in the second. (The worlds of A′ and B in notes/27 are not
symmetric and are not affected.)

**The pool decides.** Rows at height 10 or more, by the size `k` of the pool:

| `k` | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| attachments ≤ 4: rows | 26 | 316 | 782 | 604 | 280 | 72 | |
| without a partner | 38 % | 18 % | 6.9 % | 4.6 % | 0.7 % | 0 % | |
| attachments ≤ 5: rows | 84 | 570 | 1758 | 1262 | 660 | 40 | 20 |
| without a partner | 43 % | 21 % | 11 % | 7.0 % | 2.7 % | 5 % | 0 % |

This is close to `δ^k`, with `δ = 0.425` and `0.485` (maximum likelihood). And the pool
grows slowly:

| heights | 5–9 | 10–19 | 20–39 | 40–69 | 70–99 | 100–120 |
| --- | --- | --- | --- | --- | --- | --- |
| live columns | 3.5 | 6.3 | 10.2 | 19.1 | 30.5 | 39.6 |
| unused live columns (the pool) | 2.1 | 2.8 | 3.2 | 3.7 | 4.5 | 5.0 |
| of those, eligible | 0.7 | 1.4 | 1.7 | 2.0 | 2.4 | 2.9 |

(attachments up to 4). The pool gains about one column when the height is multiplied by `e`,
which is what the sketch of notes/27 §4 needs.

**Chains do not differ durably.** If the law came from a mixture of chains, each with its
own constant rate, a chain with few partnerless rows early would have few later. Across the
chains alive at height 40, the share of rows without a partner in heights 10–19 and the share
in 20–39 have correlation 0.28 (20 chains) and 0.31 (46 chains, attachments up to 5); for
20–39 against 40–69 it is −0.40 (12 chains) and 0.09 (28 chains). So there is no sign of
durable differences, and the rate of a chain falls because its own pool grows.

**The diagonal does not hide behind the partners.** On the rows without a partner at height
10 or more, the diagonal cell is eligible in 86 of 154 cases (56 %) and 238 of 452 (53 %),
against 46 % and 47 % over all rows. So the six misses of A′ (notes/27 §2: six rows without a
partner, each time with a finite cut on the diagonal) are not typical, and there is no
general tendency of the diagonal to be ineligible when it matters.

**The cells of a row are not independent.** Among rows with `k = 3`, none of the three pool
cells is eligible in 54 rows where independent cells with the same mean would give 73, and all
three are eligible in 88 against 127. The number of eligible cells is more concentrated than
a binomial. Lemma 2 gives a reason: two cells of a row never have their finite cut at the
same height. With independent cells of the common frequency `q = 0.52` one would have
`δ = 1 − q = 0.48` instead of 0.425, and 114 chain ends instead of the 86 observed at height
10 or more.

**Correction: the eligible cells are not in a narrow band.** notes/27 §1 says that away from
the diagonal almost every cell has a finite cut. That was read off the grid of B and is wrong
in general. At height 20 or more the eligible cells are spread evenly over the distances 1 to
12 below the diagonal (750 to 870 cells at each distance) and thin out slowly beyond. The
*partners* sit at distance 1 to 8, mostly 3 or 4, because a row takes the oldest eligible
column that is still unused, and old columns have been used. The life of a column,
`k(v) − v` in the notation of Lemma 1, grows in proportion to its height:

| height `v` of the column | 5–9 | 10–19 | 20–39 | 40–69 |
| --- | --- | --- | --- | --- |
| mean life, when the death is seen | 5.8 | 9.2 | 16.1 | 31.4 |
| still alive at the end of the data | 44 % | 38 % | 36 % | 39 % |

So a column stays alive for a time comparable to its height, and the number of live columns
grows linearly. What stays small is the pool.

Outputs: `data/chains/band_*.txt`, and `data/chains/survival.txt` for the new world.

## 4. A model, and where the constant 1 comes from

**The model.** The state is the size `k` of the pool. At each row, independently of the
past:
* with probability `1 − δ^k` the row finds a partner, and nothing changes;
* with probability `δ^k` it finds none. Then the diagonal cell is eligible with probability
  `ε` and the chain ends; otherwise the pool grows to `k+1`.

Columns that die unused are ignored, which the long lives of §3 justify to first order.

**Proposition.** Let `T` be the height at which the chain ends in this model, and
`γ = ln(1/(1−ε)) / ln(1/δ)`. There are constants `0 < c < C`, depending on `δ`, `ε` and the
initial pool, such that `c·h^−γ ≤ P(T > h) ≤ C·h^−γ` for all `h ≥ 1`. In particular the chain
ends with probability 1, and the expectation of `T` is infinite if `γ ≤ 1`.

*Proof.* Let `L_k` be the number of rows spent with pool `k`: a geometric variable with
`P(L_k > t) = (1−δ^k)^t`. Starting from the pool `k_0`, the `m`-th row without a partner
comes at `τ_m = L_{k_0} + … + L_{k_0+m−1}`, and the chain survives each such row with
probability `1−ε`, independently. So `P(T > h) = E[(1−ε)^{N(h)}]`, where `N(h)` is the number
of `m` with `τ_m ≤ h`. Let `n` be the integer with `δ^{−(n−1)} < h ≤ δ^{−n}`.

Lower bound: `N(h) ≤ n − k_0 + 1` as soon as `L_{n+1} > h`, which has probability
`(1−δ^{n+1})^h ≥ (1−δ/h)^h`, bounded below. So `P(T > h) ≥ c'·(1−ε)^{n−k_0+1}`, and
`(1−ε)^n` is `h^−γ` up to a constant factor.

Upper bound: `N(h) < n − k_0 − j` means `τ_m > h` for `m = n − k_0 − j`. The terms of `τ_m`
have means `δ^{−k_0}, …, δ^{−(n−j−1)}`, the largest of which is at most `δ^j·h`. Splitting
`h` into shares proportional to `θ^r` for the term `r` places below the last, with
`δ < θ < 1`, each term exceeds its share with probability at most `exp(−c''·(θ/δ)^r·δ^{−j})`.
So `P(N(h) < n − k_0 − j) ≤ C''·exp(−c''·δ^{−j})`, which decays faster than `(1−ε)^{−j}`
grows. Summing over `j` gives `P(T > h) ≤ C·(1−ε)^n`. ∎

`scripts/chain_model.py` iterates the model exactly: for `δ = 0.425`, `ε = 0.558` the local
exponent between heights `h` and `2h` is 0.72 at `h = 10`, 0.89 at 40, 0.95 from 1000 on,
and `h^γ·P(T > h)` converges to a constant.

**The numbers.** `δ` from the table of §3 and `ε` from the rows without a partner:

| world | `δ` | `ε` | `γ` of the model | measured constant of the law |
| --- | --- | --- | --- | --- |
| attachments ≤ 4, `H = 253`, `Z = 120` | 0.425 | 0.558 (86 of 154) | 0.96 | 1.00 (104 pairs of ends) |
| attachments ≤ 5, `H = 160`, `Z = 70` | 0.485 | 0.527 (238 of 452) | 1.03 | 0.98 (267 pairs) |
| the world of A′ (notes/26 §8) | 0.475 | 0.35 (8 of 23) | 0.57 | 0.87 with B's world (28 ends) |

In the two large worlds the model reproduces the constant of the law from two frequencies
that are measured separately from it.

**Why the constant is 1.** `γ = 1` exactly when `δ = 1 − ε`: the diagonal cell is eligible as
often as a pool cell is. In that case the picture is symmetric. A row has `k + 1` candidate
cells in a fixed order, the `k` of the pool and then the diagonal; each is eligible with the
same probability; the row takes the first eligible one; the chain ends when that is the last
one; and the pool grows when there is none. Then `P(T > h)` is proportional to `1/h`
whatever the common probability is. In the data the diagonal is eligible 46 % of the time
and a pool cell 53 %, and the dependence between the cells of a row moves `δ` a little below
`1 − q`. So the constant is 1 because the diagonal cell behaves like any other cell near it,
and it is 1 only approximately.

This also says that the constant is not universal. A family in which the diagonal cell is
eligible less often than its neighbours, or in which a row has several kinds of partner, has
a smaller exponent. The roofs over the `3×2` block, with `G ≈ 0.14` on three chain ends
(notes/27 §6), are such a family; we cannot measure `δ` and `ε` there, because the census is
not reliable in that world (notes/26 §5).

## 5. What a proof would need

**Conjecture E (ends).** If the diagonal cell of a chain is eligible infinitely often, the
chain has a P member.

**Conjecture R (rigidity).** If the diagonal cell of a chain is eligible only finitely often,
then from some height on the finite P cut of `S(u,u)` is at `u + c` for a constant `c`.

Both hold in everything computed: the regular chains found are A's (`c = 1`) and one chain
of `(w,w,1 | w,w,1 | 0,0,0)` and of its transpose (`c = 2`), and the scan of notes/27 §5 for
chains that are regular from height 14 on found nothing else among 4917 attachments up to 8.
With E and R, deciding a position with the `2×2` block infinite would come down to
statements about finite positions in linear families, the kind that Z3 proved for A
(notes/25).

A proof of E has two parts, and both are out of reach for the same reason.

1. *The diagonal is eligible at infinitely many heights, in a controlled way.* Eligibility of
   `(u,u)` says that the finite positions `(h, h, · | u, u, · | ·)` are N for every `h`. In
   two dimensions the statement of this kind is that the side class is infinite, which we
   proved in notes/13, and the proof rests on Sheiner's lemmas for three-row Chomp. For
   finite positions over the `2×2` base with attachments there is no such theory: the only
   closed forms known are the pure `2×2×n` positions and the families of notes/25, and the
   sequences that decide a single cell have periods of millions of terms (notes/26 §5).
2. *At one of those heights, every unused live column is ineligible.* By §3 this happens with
   the frequency of independent coin tosses. Proving it means proving that a handful of
   irregular 0/1 sequences attached to neighbouring columns do not conspire, forever, to
   leave one cell open. No statement of this kind is known in Chomp. Even for three rows,
   where the side class has the measured density `√2 − 1`, what we could prove is a lower
   density of `1/5` (notes/13).

What the measurements add is that there is no hidden structure to exploit: the cells behave
like slightly negatively dependent coin tosses, the diagonal like its neighbours, and the
chains like one another. A proof of E would be a proof that this pseudo-randomness is
real. The lemmas of §1 are the deterministic part, and §2 shows they are not enough.

**What would count as progress.**
* Conjecture R, or a weaker form: a chain that is regular has its cut at `u + c`. This is a
  statement about finite positions only, and a counterexample would show up in a table.
* E for one explicit irregular chain *without* computing its P member: for instance that the
  diagonal of B's chain is eligible infinitely often. This would need the first structure
  theorem about finite positions over the `2×2` base with attachments.
* A proof of the tripod conjecture of notes/17 for the positions `T_v` of Lemma 1. It would
  make "live" a proved notion.

None of these is in sight, and none would settle `3×3×ω`.

**Where this leaves the working hypothesis.** It stays a hypothesis, now with a mechanism
whose two parameters are measured and reproduce the law. For a single position it still
says nothing certain: A′ has each of its chains alive at height 120, and by the law each ends
before height 240 with probability one half (notes/27 §5).

## 6. The classification with attachments up to 5

The census of §3 proposes a reply for each of the 448 positions that are N in the census
without a finite P cut. `scripts/verify_census_options.py` sends them to the solver, as in
notes/26 §3 (`rodf -a 3 -d 12 -L 60000000`, 900 seconds and 3 GB per position).

**442 of the 448 are certified N by this run**: 423 by a reply the census proposed, 9 by a
lower cut of the same column (the census had the wrong height), 10 by a reply the solver
found itself. No census verdict was refuted.

The six others ran into the memory limit on replies proposed at heights 27 to 68.
* `(w,w,4 | w,w,2 | 5,4,2)` and `(w,w,5 | w,w,4 | 4,3,2)` are the transposes of two positions
  the run did certify, by replies at heights 10 and 9 that the census had missed. The
  mirrored replies are confirmed directly: cut `(1,0)` at 10 and at 9 leaves a certified
  P-position (`chain_runs.py`). So both are N, exactly.
* `(w,w,5 | w,w,5 | 5,2,2)` and its transpose `(w,w,5 | w,w,2 | 5,5,2)`: **open**. The census
  has a P chain member at height 68, two below its limit `Z = 70`, and its other chain alive.
* `(w,w,5 | w,w,5 | 4,3,3)` and its transpose `(w,w,4 | w,w,3 | 5,5,3)`: **open**. The census
  has a P chain member at height 42.

For the two open pairs an exact run of both chains (`chain_runs.py`, 520 seconds and 4.5 GB
per chain) shows every member N up to height 24 and then stops for time. They are in the
position of A′ (notes/26 §8): no finite P cut up to height 160, chains alive as far as the
solver goes, and a census reply too deep to check.

| attachments | positions | finite P cut | N by a certified reply | P | open |
| --- | --- | --- | --- | --- | --- |
| up to 4 (notes/26 §3) | 371 | 156 | 213 | 2 | 0 |
| up to 5 | 812 | 362 | 444 | 2 | 4 |

How the replies are distributed: of the 442 certified ones, 251 are at height 0 to 4, 152 at
5 to 9, 22 at 10 to 14, 13 at 15 to 19, 3 at 20 to 24 and one at 31 (B). The census puts the
lowest reply of 9 of the 448 positions above height 24. Five of those were decided all the
same (B, and four whose true reply is at height 9 or 10, lower than the census had it), and
the four open positions are the rest. A position stays undecided when both of its chains
are deep, and by the law of notes/27 a few such positions among 450 are to be expected. This
is the situation of A′ and is not evidence that any of them is P.

`data/census/block220_att5_certified_replies.txt` has all replies.

## Tools and data

```
STALKS=1 ./base3_table 160 -c H,H,5,H,H,5,5,5,5 -T 70 -O mK5 > mK5.txt
python3 scripts/chain_survival.py mK5_stalks.txt mK5.txt 70
python3 scripts/chain_band.py mK5_stalks.txt mK5.txt 70 [--chains]     # §3
python3 scripts/chain_model.py 0.425 0.558 2 200000                    # §4
python3 scripts/verify_census_options.py rodf mK5.txt 900 3 3000       # §6
```

* `scripts/chain_band.py`: pool, life of columns, persistence, the fit of `δ` and `ε`.
* `scripts/chain_model.py`: the model of §4, iterated exactly.
* `data/chains/band_block_att4_H253_Z120.txt`, `band_block_att5_H160_Z70.txt`,
  `band_Aprime_world.txt`: outputs of `chain_band.py`.
* `data/census/block220_att5_H160_Z70.txt`: the census report of the new world;
  `block220_att5_certified_replies.txt`: §6.
