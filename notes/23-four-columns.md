# Four columns: Huddleston–Shurman's open value `G(4×ω)`

Huddleston and Shurman ("Transfinite Chomp", §12) do not know the Grundy value of `4×ω`, or
whether it is computable. They show `G(4×ω) = mex(L)`, where

`L = { G(ω,ω,a,a), G(a,a,a,a) : a < ω }`,

and state: "We know L contains all g < 46, we don't know if 46 ∈ L, but if 46 ∈ L then
46 = G((4×a) + (2×ω)) for some a > 480. If mex(L) is infinite then we believe
G(4×ω) = ω·2." Nowakowski's list of unsolved problems still carries the question (2025): "it
could be as low as 46, or even uncomputable".

This note sets up an exact method for the values in `L` and reports what it gives.

**Results.**

1. **Proved** (computer-assisted, §4): the values `G(ω,ω,x,y)` up to 46 for all sides
   `y ≤ x ≤ 107`. In particular every `g` with `1 ≤ g ≤ 45` is in `L`, with the witnesses of
   the table in §5. This is their first claim, with a proof. Also proved: no `a ≤ 158` gives
   46.
2. **Computed, not proved**: no `a ≤ 1000` gives 46. This rests on the assumption that no row
   (defined below) which is alive at level 2400 dies later. Their bound was 480.
3. **Why 46 is slow to appear, and why it should appear** (§6). From `a = 108` on, 46 is the
   only value up to 46 that a side can have. Each row of the table of sides places its 46 in
   one of 8 to 11 free columns just below the diagonal. The diagonal side `(a,a)` gets it only
   if none of them can take it and the diagonal row itself never dies. Up to 1000 the first
   condition held three times (`a = 507, 601, 778`) and the second failed each time. A random
   model of this process puts 46 on the diagonal eventually with probability 1. So the data
   give no support to `G(4×ω) = 46`.

Conventions: positions have columns of heights `h₁ ≥ h₂ ≥ h₃ ≥ h₄`, finite or `ω`. Values are
**unrestricted**, as in [HS]: the poison may be taken, the empty position has value 0, and a
P-position of ordinary Chomp has value 1. `[a,b,x,y]` is a finite position.

## 1. Which options of `4×ω` have finite values

The options of `4×ω` are `(t,t,t,t)`, `(ω,t,t,t)`, `(ω,ω,t,t)` and `(ω,ω,ω,t)`. The second and
fourth kinds have infinite values ([HS]; for one infinite column, `G(ω,R) = ω + γ(R)` by
notes/09). So `G(4×ω)` is the least `g ≥ 1` that is not the value of a rectangle `4×a` or of
a **diagonal side** `(ω,ω,a,a)`, if there is one. Positions `(ω,ω,a,a)` with different `a` are
options of one another, so each value occurs for at most one `a`.

A **side** is a pair `(x,y)`, `y ≤ x < ω`, standing for `(ω,ω,x,y)`. Its options with finite
values are the sides `(x,j)`, `j < y`, and `(j, min(y,j))`, `j < x`, and the finite positions
`[t,t,min(t,x),min(t,y)]`, `t ≥ 1`. Let

`F(x,y) = { G[t,t,min(t,x),min(t,y)] : t ≥ 1 }`.

> **Lemma 1.** `G(ω,ω,x,y)` is the least `g ≥ 1` not in
> `F(x,y) ∪ {G(ω,ω,x,j) : j < y} ∪ {G(ω,ω,j,min(y,j)) : j < x}`, if there is one.

So everything comes down to the sets `F(x,y)`: which values occur among the finite four-row
positions `[t,t,x,y]`. For three rows and the value 1 this is the side class of notes/13.

## 2. Rows, and the recurrence

A position `X` has value `g` iff `X` plus a one-wide stalk of height `g` over the poison cell,
in a new direction, is a P-position: the stalk is a Nim heap of size `g − 1` next to the game
on the other cells. Write `X + g` for it.

For fixed `(b,x,y)` the positions `[a,b,x,y]`, `a ≥ b`, are options of one another, so at most
one of them has value `g`. Call it `A(b; x,y,g)`.

A **row** is a triple `ρ = (x,y,g)` with `y ≤ x` and `g ≥ 1`. It is **born** at level `x`.
Its **older rows** are `(j, min(y,j), g)` for `j < x`, `(x,j,g)` for `j < y` and `(x,y,g′)`
for `1 ≤ g′ < g`. For `j < x` write `ρ_j = (j, min(y,j), g)`, and `ρ_j = ρ` for `j ≥ x`.

> **Lemma 2.** Let `b ≥ x`, and suppose no `[j,j,min(x,j),min(y,j)]` with `1 ≤ j < b` has
> value `g`. Then `A(b; ρ)` exists, and it is the least `a ≥ max(b,1)` that is not
> * `A(j; ρ_j)` for some `j < b`, or
> * `A(b; ρ′)` for an older row `ρ′`.

*Proof.* Let `Q_a = [a,b,x,y] + g`. Its options:
* the first row cut to `j`, `1 ≤ j < a`. For `j ≥ b` this is `Q_j`. For `j < b` it is
  `[j,j,min(x,j),min(y,j)] + g`, which is not P by assumption;
* the second row cut to `j < b`: `[a,j,min(x,j),min(y,j)] + g`, which is P iff `a = A(j; ρ_j)`;
* the third row cut to `j < x`, the fourth to `j < y`, the stalk to `g′ < g`: P iff
  `a = A(b; ρ′)` for the corresponding older row `ρ′`.

So `Q_a` is P iff `a` is not one of the listed values and no `Q_j`, `b ≤ j < a`, is P. ∎

The row **dies** at level `b` if `A(b; ρ) = b`, that is `G[b,b,x,y] = g`. From then on it has
no values. It is **stillborn** if some `ρ_j`, `j < x`, dies at its own birth level `j`. So

`F(x,y) = { g : the row (x,y,g) dies or is stillborn }`.

A death is a finite fact. That a row never dies is not.

For three rows and `g = 1` this is the recurrence of Brouwer et al. for `f(q,r)`, and "dies at
level `b`" is `τ(r) = b`. For three rows and `g = 2` it is the cube family of notes/19.

## 3. A certificate that a row never dies

Fix a bound `X` on `x` and a bound on `g`. Above level `X` no row is born, and by Lemma 2 the
value `A(b; ρ) − b` depends only on the differences `v − b` of the earlier values `v ≥ b` of
`ρ` and on the values of its older rows at level `b`. So the **state** at level `b` (for each
row, whether it is dead, and the set of `v − b`) determines everything later.

> **Lemma 3.** Let `X < b₁ < b₂`, and let `C` be a set of rows that contains the older rows of
> each of its members, such that every row of `C` has the same state at `b₁` and at `b₂`. Then
> no row of `C` that is alive at `b₂` ever dies.

*Proof.* `C` evolves by itself and deterministically, so its states are periodic with period
`b₂ − b₁` from `b₁` on. ∎

The program compares the states at `T − P` and `T` and takes the largest such `C`. The rows of
`C` alive at `T` are **certified**. By Byrnes's periodicity theorem (notes/11) every row is
eventually periodic, so a suitable `P` and `T` exist for any finite set of rows. Finding them
is the cost.

**Proof rules for the values.** For a side, call `g` *attained* if it is the value of an
option. With Lemma 1:
* `g` is attained if the row `(x,y,g)` is dead or stillborn, or if a smaller side among the
  options has proved value `g`;
* `g` is not attained if the row `(x,y,g)` is certified and every smaller side among the
  options is proved to have a value other than `g`.

If `lb` is the least `g` not proved attained and `ub` the least `g` proved not attained, the
value lies in `[lb, ub]`. It is proved when `lb = ub`, or when `lb` exceeds the bound on `g`
("above the bound").

## 4. What is proved

`tools/four_row_values.cpp` runs Lemma 2 level by level, with the rows' earlier values kept as
bit sets, and then applies Lemma 3 and the proof rules. Checks of the program:
* its death levels agree row by row with a direct Python implementation
  (`scripts/four_row_check.py`), which agrees with brute-force Grundy values of all positions
  `[a,b,x,y]` with `a ≤ 8`;
* the certified two-wide-stalk solver `rodf` of notes/07 is an independent program, and it
  handles stalks up to height 13. For each of the 26 sides with `x ≤ 6` and value at most 13,
  it confirms that `(ω,ω,x,y)` plus a stalk of that height is a P-position, and that with a
  stalk one cell shorter it is an N-position. The same for `(ω,ω,a,a)` with `a = 7, 8, 11`
  (values 9, 8, 2);
* results do not depend on the number of threads or on the window size.

> **Theorem 4** (computer-assisted). For all sides `y ≤ x ≤ 107` the value `G(ω,ω,x,y)` is as
> computed, where values above 46 are only known to be above 46. Hence `{1, …, 45} ⊆ L`, and
> 46 is not the value of `(ω,ω,a,a)` or of `4×a` for any `a ≤ 107`.

Run: `four_row_values 107 46 100000 23040`. All 68691 rows alive at level 100000 have the same
state at levels 76960 and 100000, so all are certified, and all 5886 sides get proved values.

* **Periods.** The period 23040 = `2⁹·3²·5` works for every row with `x ≤ 107`, `g ≤ 46`. For
  `x ≤ 40`, `g ≤ 64` the minimal periods of the value sequences are of the form `2^i 3^j 5^k`,
  from 1 to 11520.
* **Transients are long.** With `T = 31000` only 25527 of the 68691 rows are certified, with
  `T = 60000` it is 60738. So some rows take more than 37000 levels to become periodic, though
  every death happens before level 1500.

> **Proposition 5** (computer-assisted). 46 is not the value of `(ω,ω,a,a)` or of `4×a` for
> any `a ≤ 158`.

Run: `four_row_values 200 46 300000 23040,46080,69120,92160,115200,138240,161280,184320`. Of
the 227602 rows alive at level 300000, 198991 are certified by one of the eight periods, and
19737 of the 20301 sides get proved values, among them all diagonal sides with `a ≤ 158`.
Between 159 and 200 there are 19 diagonal sides for which "the value is not 46" is not
proved by this run.

* **The periods grow.** The period 23040 certifies 150393 of these rows, and
  `138240 = 2¹⁰·3³·5` certifies the most, 185625. Other rows need `2¹¹` (period 92160), so a
  common period for `x ≤ 200` is at least `2¹¹·3³·5 = 276480`. With the long transients, a
  certificate for every row up to 200 would need close to a million levels, and the growth
  from 107 to 200 suggests far more for 480.

## 5. The values

`G(ω,ω,a,a)` and `G(4×a)` for `a ≤ 107`; "–" means above 46. All proved.

| `a` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `G(ω,ω,a,a)` | 1 | 6 | 5 | 3 | 12 | 17 | 15 | 9 | 8 | 18 | 22 | 2 | 30 | 32 | 33 | 41 | 42 | 37 | 43 | 38 | 39 | 45 | 28 | 11 |
| `G(4×a)` | 0 | 4 | 6 | 10 | 7 | 14 | 17 | 20 | 13 | 27 | 29 | 31 | 34 | 36 | 40 | 35 | 44 | – | – | – | – | 38 | – | – |

For `24 ≤ a ≤ 107` both are above 46, except
`G(ω,ω,a,a) = 21, 25, 16, 26, 23, 19, 24` at `a = 38, 47, 49, 51, 63, 65, 107`.

So each `g ≤ 45` is in `L`, by the following witness (a number `a` means `(ω,ω,a,a)`):

| `g` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| witness | 0 | 11 | 3 | `4×1` | 2 | 1 | `4×4` | 8 | 7 | `4×3` | 23 | 4 | `4×8` | `4×5` | 6 |

| `g` | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| witness | 49 | 5 | 9 | 65 | `4×7` | 38 | 10 | 63 | 107 | 47 | 51 | `4×9` | 22 | `4×10` | 12 |

| `g` | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43 | 44 | 45 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| witness | `4×11` | 13 | 14 | `4×12` | `4×15` | `4×13` | 17 | 19 | 20 | `4×14` | 15 | 16 | 18 | `4×16` | 21 |

The last value to arrive is 24, at `a = 107`.

The earlier values of notes/09 and notes/11 for `41 ≤ a ≤ 80` came from a capped search and
were wrong: for example the value 25 first occurs at `a = 47`, not at 42.

**Beyond 158, not proved.** `four_row_values 1000 46 2400` finds no `a ≤ 1000` with value 46.
What is exact in that run: the 5.9 million deaths and 11.6 million stillborn rows. What is
assumed: that the 5.6 million rows alive at level 2400 never die. The evidence for that:
* for `x ≥ 400` every death is at a level below `1.753·x` (mean `1.37·x`), and 2400 is well
  above that for the rows near the diagonal with `x ≤ 1000`;
* late deaths exist only for small `x`. No row with `32 ≤ x ≤ 1000`, `g ≤ 46`, dies above
  level `2x`. The rows that die far above it are `(20,11,16)` at level 1447, `(15,9,16)` at
  866, `(22,4,14)` at 723, `(27,10,16)` at 299 and `(31,5,11)` at 126. The run to level 100000
  for `x ≤ 107` shows no death above 1447.

For 587 of the 1001 diagonal sides, "the value is not 46" is nevertheless proved, because the
row `(a,a,46)` is dead.

Of the rows with `x ≥ 400`, 50% are stillborn, 26% die and 24% are alive at the end.

## 6. Where 46 can appear

After 24 has arrived at `a = 107`, every `g ≤ 45` is the value of a rectangle or of a diagonal
side `(j,j)`, `j ≤ 107`. A rectangle value `g` makes the rows `(x,y,g)` beyond it stillborn,
and a diagonal side `(j,j)` is an option of every side `(x,y)` with `y > j`. So:

> for `y > 107`, the side `(x,y)` has value 46 or more, and it has value 46 iff the row
> `(x,y,46)` never dies and none of its options `(x,j)`, `j < y`, and `(j, min(y,j))`,
> `j < x`, has value 46.

Write `E(x,y) = 1` if the row `(x,y,46)` never dies. As long as no diagonal side has the value
46, it is placed greedily: go through the sides of row `a` in the order `y = 0, 1, …`, and put
46 on the first `(a,y)` with `E(a,y) = 1` whose column `y` does not yet hold a 46. Each row and each column gets at most
one. **46 ∈ L iff it is ever put on a diagonal side `(a,a)`**: that needs `E(a,a) = 1` and no
earlier side of row `a` taking it.

What the run to 1000 shows (`scripts/four_row_46.py`):
* every row `a` from 100 to 1000 except three contains a 46, at distance 1 to 22 below the
  diagonal, mostly 5 to 13;
* the columns within 60 of the diagonal that do not yet hold a 46 number 8 for
  `204 ≤ a ≤ 507`, then 9, then 10 from `a = 602` and 11 from `a = 779`;
* of these free columns, the number with `E(a,y) = 1` is 3.6 on average. It is 1 in 44 rows
  and 0 in three rows: `a = 507, 601, 778`. In those rows 46 is put nowhere, because the
  diagonal rows die too (`(507,507,46)` at level 871, the others at 1029 and 1341). Each such
  row leaves one more free column;
* `E = 1` for 37% of the sides within 20 of the diagonal, and for 40% of the diagonal sides.

**A model.** If the `E(a,y)` on the free columns were independent with probability `p ≈ 0.4`,
a row with `n` free columns would find none usable with probability `(1−p)^n`: 1.7% for
`n = 8`, 0.4% for `n = 11`. When that happens, 46 goes on the diagonal with probability `p`,
and otherwise `n` grows by one. Such events get rarer, but they keep occurring, and each is a
fresh chance. So in the model 46 reaches the diagonal with probability 1, typically at a
height of a few thousand. The same would hold for every later value.

This is a heuristic, not a proof. It says that the absence of 46 up to 480, or up to 1000, is
what one should expect, and that it is not evidence for `mex(L) = 46`. It is in line with
[HS]'s belief that `mex(L)` is infinite.

## 7. Status

* `{1,…,45} ⊆ L`: proved here, with data ([HS] state it without data or proof).
* "46 is not attained for `a ≤ 480`" ([HS]): reproduced, and extended to `a ≤ 1000`, under the
  assumption on late deaths. Proved here only for `a ≤ 158`.
* Whether `46 ∈ L`: open. The model of §6 suggests yes.

**What would extend this.**
* *A proof up to 480 or 1000.* It needs the certificate of §3 for all rows up to that height.
  The common period grows with the height (23040 up to 107, at least 276480 up to 200), and
  the run has to be longer than the period plus the transient. Up to 480 this looks out of
  reach for a level-by-level simulation; it needs a certificate that treats rows with
  different periods separately, or a bound on death levels.
* *A search beyond 1000.* Memory is the limit: a living row needs a window of about `1.3·x`
  bits, and about 40% of the rows are alive at the peak. Height 1800 fits in 12 GB.
* *Theory.* A bound on death levels (in the data `1.75·x` for large `x`) would make
  "never dies" a finite check and remove the certificate. For three rows and `g = 1` this is
  the bound `τ(r) ≤ (5r+3)/3` of notes/19. For `g = 2` it is the open cube case, so no such
  bound is in sight.

## Tools

* `tools/four_row_values.cpp`: `four_row_values X GM T [P1,P2,…] [OUT]`. Compile with
  `-fopenmp`. `WORDS` sets the window (64 bits each), `PROGRESS=n` reports every `n` levels,
  `DIAG=M` prints the minimal periods of the last `M` values of each row, `TARGET=g` reports
  for which `a` "the value is not `g`" is proved. `OUT` receives the death levels.
* `scripts/four_row_check.py X GM T`: the same recurrence in Python, compared with brute force
  and, if the binary is given, row by row with the C++ program.
* `scripts/four_row_46.py X GM OUT [g] [A0]`: from the death levels, where each row of the
  table of sides puts the value `g`, the free columns and how many are usable.
