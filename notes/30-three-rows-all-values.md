# Three-row Chomp, all Grundy values: the value of `3×ω`

The side-class theorem (notes/13) says that infinitely many rows `x` have no P-position
`[p,p,x]`. This note looks at the same statement for every Grundy value: for each `g`, the
rows `x` with no position `[p,p,x]` of value `g`. It was meant as a third attempt at the
"cube case" of notes/19, with all values at once. The statement is not proved. What the note
contains:

1. **A reduction** (§1, proved). `G(3×ω)` is infinite iff every positive integer is the value
   of some `(ω,ω,x)` or of some rectangle `3×x`, and this holds if for every `g` at least `g`
   rows avoid the value `g`. If in addition the values `G(ω,ω,x)` are finite, then
   `G(3×ω) = ω + 1`.
2. **Proved values** (§2, computer-assisted). `G(ω,ω,x)` for `x ≤ 129`. Every `g ≤ 236` is the
   value of some `(ω,ω,x)` or `3×x`, so `G(3×ω) ≥ 237`.
3. **Computed values** (§2, not proved). Up to `x = 1000`, `G(ω,ω,x) = 1.857·x` and
   `G(3×x) = 2.16·x` to within about 11, and every value up to 1859 is attained. Unlike the
   four-row case of notes/23, no value arrives late.
4. **What the layers look like** (§3, computed). For every value `g ≤ 64` and rows
   `100 ≤ x ≤ 1200`: the rows that never die have density `√2 − 1`, with the same count to
   within a few units for every `g`; no row dies after its own birth value (hypothesis (H4) of
   notes/19); no level is both a death level and a birth value; a dying row has at most 12
   levels at which its value is below its death level; and a weaker form of Sheiner's
   row-start lemma holds without exception (§4).
5. **A conditional theorem** (§3). Theorem 12 of notes/19 applies to each value: if (H4) and
   (L_K) hold for the value `g` from some row on, then infinitely many rows avoid `g`. With 1,
   these two hypotheses for every `g` give `G(3×ω) ≥ ω`.
6. **Why the proof for value 1 does not extend** (§4). Sheiner's counting argument has no
   slack: it compares `p − q` rows with `p − q − 1` values. Rows of different values may take
   the same value at the same level, so the count is lost as soon as one lower value takes
   part. The statements above are also false for small rows, so a proof has to use the size.

Conventions are those of notes/23: values are unrestricted (the empty position has value 0, a
P-position has value 1), and `[a,b,x]` is a finite three-row position. The value `g = 1` here
is the P-positions of notes/13; `g = 2` is the cube family of notes/19.

## 1. The value of `3×ω`

Write `g_x = G(ω,ω,x)` and `r_x = G[x,x,x]`. The options of `3×ω` are the rectangles `3×x`,
the positions `(ω,x,x)` and the positions `(ω,ω,x)`. By notes/09, `G(ω,x,x) = ω + γ`, where
`γ` is the value of the two rows of length `x` as a game in which every cell may be taken. So
`γ = 0` for `x = 0`, and `γ ≠ 1` for `x ≥ 1`, because a `2×x` rectangle is not a P-position.

> **Lemma 1.** `G(3×ω) ≥ ω` iff every `g ≥ 1` is some `r_x` or some finite `g_x`. If moreover
> every `g_x` is finite, then `G(3×ω) = ω + 1`.

The options of `(ω,ω,x)` with finite values are `(ω,ω,j)`, `j < x`, and the finite positions
`[t,t,min(t,x)]`. For `t ≤ x` these are rectangles. Say that the row `x` **avoids** `g` if no
`[t,t,x]` with `t > x` has value `g`, and let `𝒮_g` be the set of these rows. `𝒮_1` is the
side class.

> **Lemma 2.** Suppose `g` is no `r_x` and no `g_x`. Then at most `g − 1` rows avoid `g`.

*Proof.* The `g_x` are distinct, because `(ω,ω,j)` is an option of `(ω,ω,x)` for `j < x`. So
`g_x < g` for at most `g − 1` rows. For any other row, `g` is smaller than `g_x`, the least
value that is not the value of an option, so `g` is the value of an option of `(ω,ω,x)`. It is
no `g_j` and no rectangle, so it is the value of some `[t,t,x]` with `t > x`. ∎

> **Corollary 3.** If `|𝒮_g| ≥ g` for every `g ≥ 1`, then `G(3×ω) ≥ ω`.

So the statement

> **(K)** for every `g ≥ 1`, infinitely many rows avoid `g`

gives `G(3×ω) ≥ ω`, and much less would do. [HS] §12 call the set of P-positions of
`(1×3×Ω) + (Ω×1×1)`, which encodes the values of three-wide positions, "very likely"
recursive and give no proof; the value `ω + 1` in notes/09 came from truncated runs.

The same statement appears in two other places. A stalk of `g − 1` cells beside the wall `3×ω`
is a sum with a Nim heap, so the `(0,1)` towers of `3×3×ω` whose top part is a stalk of one or
two cells are N if `𝒮_2` and `𝒮_3` are infinite (notes/14). And the box `2×3` at ordinal
heights, the successor of [HS]'s `2×2×ω³`, has the positions `(ω,ω,ω | a,b,c)` among its
options, which are towers of the same kind over a smaller base.

## 2. The values

`tools/three_row_values.cpp` is the program of notes/23 without the fourth row. A **row** is a
pair `(x,g)`; it is born at level `x`, and for `b ≥ x` its value `A(b; x,g)` is the `a ≥ b`
with `G[a,b,x] = g`. It **dies** at level `b` if `G[b,b,x] = g`. Its **older rows** are the
rows `(j,g)`, `j < x`, and `(x,h)`, `h < g`. The recurrence, the certificate that a row never
dies, and the proof rules for the values are those of notes/23, §2 to §4.

> **Theorem 4** (computer-assisted). The values `G(ω,ω,x)` for `x ≤ 129` are as in
> `data/three-row/values_x150_g340_T1000000.txt`. Every `g` with `1 ≤ g ≤ 236` is the value of
> a position `(ω,ω,x)` or of a rectangle `3×x` with `x ≤ 129`. Hence `G(3×ω) ≥ 237`.

Run: `three_row_values 150 340 1000000` with 110 periods of the form `2^i·3^j·5^k` up to
393216 (eight and a half minutes). 18149 of the 20354 rows alive at level 1000000 are
certified, and 130 of the 151 values are proved. The periods that certify rows go up to
`184320 = 2¹²·3²·5`, so the periods grow as in the four-row case (notes/23, §8), and this
method will not go much further.

The first values:

| `x` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `G(ω,ω,x)` | 1 | 2 | 4 | 7 | 8 | 13 | 9 | 17 | 11 | 15 | 16 | 18 | 21 | 19 | 23 | 24 | 26 | 30 | 28 | 31 | 34 |
| `G(3×x)` | 0 | 3 | 5 | 6 | 10 | 12 | 13 | 14 | 17 | 20 | 22 | 25 | 27 | 29 | 32 | 33 | 36 | 37 | 40 | 43 | 42 |

(13 and 17 occur in both rows: `(ω,ω,5)` and `3×6`, `(ω,ω,7)` and `3×8`. Neither is an option
of the other.)

**Computed, not proved** (`three_row_values 1000 2200 2400`, values in
`data/three-row/values_x1000_g2200_T2400.txt`). If no row alive at level 2400 dies later:

* every value up to 1859 is attained with `x ≤ 1000`: 1001 values by the positions
  `(ω,ω,x)` and 858 by rectangles;
* `G(ω,ω,x) = 1.857·x` to within 11 (it is 184, 557, 930, 1300, 1857 at `x` = 100, 300, 500,
  700, 1000), and `G(3×x) = 2.16·x` to within 11 (218, 648, 1077, 1511, 2160). The two
  densities add up to 1;
* the value `v` is attained at an `x` within 6 of `v/1.857`, or by a rectangle within 5 of
  `v/2.16`.

So in three rows every value arrives on time. In four rows the value 46 arrives at height
1012 after all values up to 45 are in place at height 107 (notes/23). The difference is that
a three-row side `(x)` has only the sides `(j)`, `j < x`, as options, and in each layer about
41% of the rows never die, so the least value still free for `x` is always near.

## 3. The layers

Call the rows `(x,g)` with a fixed `g` the **layer** `g`. If `g = r_j` is a rectangle value,
the layer stops at `x = j`. Otherwise every row of the layer is born, and it dies or it is in
`𝒮_g`. `tools/three_row_layers.cpp` follows all layers and records, for each row that dies,
the quantities of notes/19, §9.

For `100 ≤ x ≤ 1200` and the 35 values `g ≤ 64` that are not rectangle values
(`data/three-row/layers_x100-1200_g64.txt`):

| | all 35 layers | per layer |
| --- | --- | --- |
| rows that die | 22563 | 641 to 648 |
| rows alive at level 2600 | 15972 (41.45%) | 453 to 460 |
| rows that die after their own birth value, or after the birth value of a younger row born before their death ((H4) violated) | 0 | 0 |
| death levels that are the birth value of a younger row | 0 | 0 |
| low levels | 11178 | at most 12 per row |
| of these: the value is the death level of an older row | 2892 | at most 4 per row |
| of these: the death level of a younger row | 8245 | |
| of these: another value | 41 | |

A **low level** of a row that dies at `p` is a level at which its value is below `p`. For
`g = 1` there are none (Sheiner's row-start lemma). With the run
`three_row_values 2500 64 6000` the first two lines extend to `x ≤ 2500`: each layer has
between 1036 and 1052 rows alive at level 6000, where `(√2 − 1)·2501 = 1036`, and the only
rows that die after their own birth value are 47 rows with `x ≤ 31`.

So in this range:

* **(H4)** of notes/19 holds for every value: a row that is alive when the level reaches its
  own birth value never dies, and no row dies after the birth value of a row born during its
  life;
* **(L_K)** holds with `K = 4`: a row has at most four low levels whose value is the death
  level of an older row;
* every layer has the density of the side class.

> **Theorem 5** (notes/19, Theorem 12, with `M = g − 1` extra blocked values). Fix `g`. If (H4)
> and (L_K) hold for the rows of layer `g` from some row on, then `𝒮_g` is infinite, with
> lower density at least `1/8`.

With Corollary 3: if (H4) and (L_K) hold in every layer from some row on, then
`G(3×ω) ≥ ω`. This is the same reduction as for the cube, now with evidence for 35 values
instead of one, and with a use for it.

**Small rows.** None of this holds for small rows. For `x ≤ 300` and `g ≤ 64`
(`data/three-row/layers_x0-300_g64.txt`) there are 993 violations of (H4) and 135 death levels
that are birth values. The row `(7,4)` has birth value 11 and dies at level 30, having taken
values below 30 at the 18 levels from 7 to 24. In the run up to 2500 the rows that die after
their own birth value have `x ≤ 31`; in the run with values up to 2200 there are 40682 of
them, up to `x = 1000`, and those with `x ≥ 50` all have `x < 0.541·g`. The layers of the
large values also have more surviving rows (up to 664 of 1001, against 415). So each layer has
a transient that ends near `x = 0.54·g`, which is where the value `g` is attained as
`G(ω,ω,x)` (`x ≈ g/1.857`).

## 4. Why the proof for `g = 1` does not extend

**Sheiner's argument.** Let the row `r` of layer 1 die at `p`, and `r < q < p`. His Lemma 4.2
says that some older row takes the value `p` at level `q`. The proof is a count (it is
`row_start_isP` in `lean/Chomp/ThreeRow.lean`). Suppose no older row takes `p` at level `q`.
By induction there is, for each level `t` with `q < t < p`, an older row `s_t` that takes `p`
at level `t`. At level `q` the value `p` is free for `r` and for each `s_t`, and none of them
takes it. So each takes a value in `(q,p)`. These are `p − q` rows of one layer, their values
at one level are distinct, and `(q,p)` has `p − q − 1` elements.

**With several values.** In layer `g` the row `(r,g)` has the older rows `(j,g)` and `(r,h)`,
`h < g`. Three things go wrong.

* The row that takes `p` at level `t` may be `(r,h)`. Rows of different layers and different
  `x` are not options of one another, so their values at level `q` need not be distinct.
* The value `p` may be free for `(r,g)` at level `q` and not for `(s_t,g)`: the row
  `(s_t,h)` may take it.
* The count has no room: `p − q` rows against `p − q − 1` values. One row that drops out of
  the count is enough to lose the contradiction, and each lower layer can remove one.

So the lemma fails, and it does fail: in the data of §3 there are 11178 low levels.

**What holds in its place.** For a row `(r,g)` that dies at `p` and a level `q` with
`r < q < p`, look at who takes the value `p` at level `q`:

| `100 ≤ x ≤ 1200`, `g ≤ 64` | levels |
| --- | --- |
| an older row `(b,g)`, `b < r` | 5949145 |
| otherwise a row `(r,h)`, `h < g` | 10414 |
| otherwise a row `(b,h)` with `b < r` and `h < g` | 464 |
| otherwise a younger row of the layer | 0 |
| none of these | 0 |

> **Observation 6** (product row-start). In this range: if `G[p,p,r] = g` and `r < q < p`,
> then `G[p,q,b] = h` for some `b ≤ r` and `h ≤ g` with `(b,h) ≠ (r,g)`.

For `g = 1` this is Sheiner's lemma. In 464 cases the row is below `(r,g)` in both
coordinates, so the position `[p,q,b]` with a stalk of `h − 1` cells is not an option of
`[p,q,r]` with a stalk of `g − 1` cells. I could not prove the observation. The count above
does not give it either: under the hypothesis that no such `(b,h)` exists at level `q`, every
row below `(r,g)` that takes `p` later takes a value in `(q,p)` at level `q`, and there are at
least `p − q` such rows, but they need not have distinct values. The observation is also
false for small rows: for `x ≤ 300`, `g ≤ 64` it fails at 17 levels, all of them levels of
the row `(7,4)`.

**What this means for a proof.** The facts of §3 are exact for large rows and false for small
ones, with a threshold near `x = 0.54·g`. A proof therefore cannot be a local argument about one
row and its options, as Sheiner's is. It has to use that the layer is long compared with the
number of layers below it, and I have no argument of that kind. The general statements that
can be proved (Lemma 6 and Lemma 7 of notes/23, §8) hold for any recurrence of this type and
are too weak, as the random model of notes/19 already showed.

## 5. Status

* (K), and with it `G(3×ω) ≥ ω`: open. Reduced to (H4) and (L_K) for every value.
* `G(3×ω) ≥ 237`: proved (Theorem 4).
* The computed values and the layer statistics say that (K) holds with the density of the
  side class in every layer, and that `G(3×ω) = ω + 1`.
* New compared with notes/19: the reduction to `3×ω`; every value instead of one; the
  observation that no level is both a death level and a birth value for large rows; the
  product form of the row-start lemma, with no exception for large rows.

## Tools

* `tools/three_row_values.cpp`: `three_row_values X GM T [P1,P2,…] [OUT]`. Values
  `G(ω,ω,x)` and `G[x,x,x]`, with the certificate of notes/23 for the periods given. `OUT`
  receives death level and birth value of every row. `WORDS` sets the window.
* `tools/three_row_layers.cpp`: `three_row_layers X GM T [XMIN]`. The statistics of §3 and §4
  for the rows with `XMIN ≤ x ≤ X`.
* `data/three-row/`: the tables quoted above.
