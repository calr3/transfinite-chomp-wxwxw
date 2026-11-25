# How a chain of cuts ends: the matching behind B, A and A′

25 November 2026. Continues [notes/26](26-census.md). Positions are written by the heights of
the nine columns in the order `(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`,
`w` for an infinite column.

A position whose infinite part is the `2×2` block is N as soon as one member of a *chain* is
P: the positions left by cutting `(1,0)` at height `u = 0, 1, 2, …` (or `(0,1)`). B has a P
member at 31, A has none, A′ has none up to 120. This note describes what happens inside a
chain, exactly, and then measures it on all the chains we have.

## Results

1. **The rule (exact, §1).** Inside a chain the P-positions with two infinite columns form a
   greedy matching between rows `u` and columns `v < u`. A chain member is P at the first row
   where the diagonal cell needs a partner and none is available. The number of unused
   columns grows by exactly one at every row that finds no partner.
2. **B, A, A′ (§2).** B runs with one or two partners available per row and has none at row
   31. In A the diagonal never needs a partner. A′ has two or three available per row; six
   times in 224 rows it had none, and each time the diagonal did not need one.
3. **A law (§3, measured).** Over the 216 chains of the `2×2` block with attachments up to 4
   whose diagonal sometimes needs a partner, a chain that is alive at height `u` ends there
   with probability close to **`1/u`** (fitted constant 1.00, 208 chain ends, the same in
   five height bands). So a chain alive at height `s` is still alive at `h` with probability
   about `s/h`. Fitted on heights up to 70, the law predicted 8.4 chains alive at height 100
   and 7.0 at 120; a taller run found 8 and 8.
4. **What it means (§5).** A′ is the survivor one expects to find among a few hundred
   chains, not a position with a reason to be P; by the law each of its chains ends before
   height 240 with probability one half. "Alive up to height `s`" is evidence of exactly this
   strength for every irregular candidate. The only chains with a reason to live forever are
   the regular ones, where the diagonal never needs a partner, and among the classified
   positions those belong to A.
5. **The `3×2` block is different (§6, exact runs).** Of the 23 roofs up to height 4 without
   a finite P cut, 11 are N by a P chain member at height 18 or lower and 12 are alive at
   heights 16 to 42. Between heights 5 and the end of the runs only 3 chains ended, where the
   `1/u` law would give 21. So in the family that contains the towers `T((0,2),g)` of
   `3×3×ω` and the positions `X_g`, replies are about seven times rarer, and those that
   exist are likely to be far beyond what can be computed.
6. **Deeper exact runs (§6).** `X_3`'s chain is exactly N up to height 42 (before: 35) and
   A′'s chain of cuts of `(0,1)` up to 59 (before: 45). `X_2` has a P chain member at height
   18, which shows that it is N without using the proof of A.

Items 1, 5 and 6 are exact (the comparison with the law in item 5 is not). Item 3 is a
measurement on census data (notes/26), and item 4 is an interpretation.

## 1. The rule

Let X be a position with the columns `(0,0),(0,1),(1,0),(1,1)` infinite and finite
attachments elsewhere. Fix the chain "cut `(1,0)`"; the other chain is the transpose. Write

`S(u,v)` = X after cutting `(1,0)` at `u` and `(1,1)` at `v ≤ u`.

`S(u,u)` is the chain member at height `u`. Every `S(u,v)` has two infinite columns, `(0,0)`
and `(0,1)`. Its options are:
* cuts of the poison column: finite positions;
* cuts of `(0,1)`: one infinite column is left, so these are N and never matter;
* bites of `(1,0)` at `t < u`: `S(t,v)` if `t ≥ v`, and the chain member `S(t,t)` if `t < v`;
* bites of `(1,1)` at `t < v`: `S(u,t)`;
* bites in an attachment column: the same `S(u,v)` built on a position X′ with a smaller
  attachment.

Call the cell `(u,v)` *eligible* if `S(u,v)` has no P cut of the poison column and no P option
by a bite in an attachment column. Then, as long as no chain member below is P:

> `S(u,v)` is P iff `(u,v)` is eligible, no `S(t,v)` with `t < u` is P (the column is free)
> and no `S(u,t)` with `t < v` is P (the row is free).

So the P-positions are found row by row: **row `u` takes the smallest `v < u` that is
eligible and whose column is free**. Call it the partner of `u`. For the diagonal cell the
column is always free, so:

> **The first P chain member is `S(u,u)` for the first `u` such that `(u,u)` is eligible and
> row `u` has no partner.**

Two consequences that need no computation.
* *The pool.* A column is used by at most one row and a row uses at most one column. So the
  number of unused columns below `u` goes up by one at every row without a partner and stays
  the same otherwise.
* *Regular chains.* If the diagonal cell is never eligible, the chain has no P member. This
  is A: `S(u,u)` has the finite P cut at height `u+1` for every `u ≥ 2` (the family `F1` of
  notes/25).

Eligibility is where the irregularity sits. Away from the diagonal almost every cell has a
finite P cut. Close to it, within about ten cells, some do and some do not, with no pattern
(§2).

`scripts/chain_matching.py` reads all this off a census dump (`STALKS=1 base3_table … -T`,
which lists every position with two infinite columns with its finite P cut, its label and the
columns that hold a P option).

## 2. Three chains

**B** `= (w,w,2 | w,w,2 | 2,2,0)`. The cells just below the diagonal, row by row
(`data/chains/B_chain10_grid.txt`; `P` partner, `E` eligible with a free column, `e` eligible
but the column is used, `c` finite P cut; after the gap the diagonal: `p` has a partner, `c`
finite cut, `P` chain member):

```
 24  cccccccceeccPE p        28  cccccccecceePE c
 25  cccccccceceecP p        29  cccccceeceeccP c
 26  cccccccceeeceP p        30  cccccceeeccPec p
 27  cccccccecePeeE c        31  ccccceeeececcc P
```

Every row takes a column one to four places back, and one or two columns are available. Row
10 finds none, with a diagonal that has a finite cut, so one more column stays unused from
then on. Row 31 finds none either: the three newest cells have finite cuts and the older
eligible ones are used.
Its diagonal cell is eligible, so `S(31,31)` is P.

**A** `= (w,w,1 | w,w,1 | 2,0,0)`. Every row `u ≥ 2` has the partner `u−1`, and the diagonal
has its finite cut at `u+1`. Nothing ever needs a partner (`data/chains/A_chain10.txt`).

**A′** `= (w,w,1 | w,w,1 | 9,2,1)`, from the census at `H = 253`, `Z = 120`
(`data/chains/Aprime_*.txt`):

| chain | rows 9–120 where the diagonal needs a partner | partners available: 0, 1, 2, 3, 4, 5+ | rows with none |
| --- | --- | --- | --- |
| cut `(1,0)` | 43 of 112 | 4, 35, 44, 26, 3, 0 | 9, 10, 25, 109 |
| cut `(0,1)` | 48 of 112 | 2, 14, 29, 36, 18, 13 | 31, 50 |

Its partners sit four to seven places back, so the pool of unused recent columns is five or
six, against two for B. At the six rows without a partner the diagonal has a finite cut. If
the two things were independent, the chance of six misses out of six would be about 5 %
(`0.6⁶`).

## 3. A law for the end of a chain

`scripts/chain_survival.py` follows every chain of every position without a finite P cut in a
census world, from the height of its largest attachment (at least 5) to its first P member.
Chains whose diagonal never needs a partner are set aside.

The `2×2` block with attachments up to 4 (`H = 160`, `Z = 70`; this is the world classified
exactly in notes/26, where the census had the right verdict for all 213 positions and the
wrong height for 6):

| heights | rows | diagonal needs a partner | no partner available | chain ends | ends × height |
| --- | --- | --- | --- | --- | --- |
| 5–9 | 794 | 33 % | 42 % | 122 = 15.4 % | 0.98 |
| 10–19 | 652 | 51 % | 14 % | 52 = 8.0 % | 1.06 |
| 20–39 | 570 | 47 % | 7.0 % | 22 = 3.9 % | 1.04 |
| 40–69 | 426 | 42 % | 2.3 % | 8 = 1.9 % | 0.97 |

The last column is the number of ends divided by the sum of `1/u` over the rows. It is
constant: **a chain alive at height `u` ends there with probability `G/u`, `G = 1.01`**.
The law predicts how many of the 216 chains are alive at each height:

| height | 10 | 20 | 40 | 70 |
| --- | --- | --- | --- | --- |
| alive, observed | 84 | 40 | 20 | 12 |
| alive, predicted | 85.9 | 42.8 | 21.3 | 12.1 |

**A test above the fitted range.** The same world at `H = 253`, `Z = 120` (64 minutes):

| heights | rows | chain ends | ends × height |
| --- | --- | --- | --- |
| 70–99 | 262 | 4 = 1.5 % | 1.26 |
| 100–120 | 168 | 0 | 0 |

From the 12 chains alive at height 70 the law gives `12·70/100 = 8.4` alive at 100 and 7.0 at
120. Observed: 8 and 8. Over all heights of this run, `G = 1.00` with 208 ends. (Between the
two runs a few ends move by a row or two, because some finite cuts lie between heights 160
and 253.)

The two smaller worlds of notes/26 (B's and A′'s, `H = 253`, `Z = 120`, 31 chains, 28 ends)
give `G = 0.87`, and 3 chains alive at height 120 against 1.9 predicted.

With `G = 1` the law says: **a chain alive at height `s` is alive at height `h` with
probability `s/h`**. The height of the first P member has no mean, half of the chains alive
at `s` end before `2s`, and one in ten is still alive at `10s`.

Output: `data/chains/survival.txt`.

## 4. Why something like `1/u`

A sketch, not a proof. A row has no partner when all the unused recent columns have a dead
cell in it. Suppose each such cell is dead with probability `δ`, independently, and the pool
has `k` columns: the row has no partner with probability `δ^k`. By the pool rule of §1, `k`
grows by one each time this happens. So the events come at times that grow geometrically,
the number of events up to height `u` is about `log u / log(1/δ)`, and the rate at height `u`
is `1/(u·log(1/δ))`, whatever the starting pool. With the diagonal needing a partner a
fraction `ε` of the time, the chain ends at rate `ε/(log(1/δ)·u)`. For `ε ≈ 0.45` and
`δ ≈ 0.6` that is `0.9/u`.

The measured rate of rows without a partner falls a little faster than `1/u` (its product
with the height goes from 2.7 to 1.4 in the table), and the share of rows that need a partner
rises, so the two parts of the sketch are rough. The product is what comes out constant.

## 5. What this changes

* **A′.** By the law, a position with two chains alive at height 9 has both alive at 120
  with probability about `(9/120)² ≈ 0.6 %` if the chains were independent. Among the 250 or
  so positions without a finite cut that the census has covered, one such survivor is not a
  surprise. Each of its chains is expected to end before height 240 with probability one
  half and before 1200 with probability nine tenths. So A′ is more likely N than P, by a
  reply that may be out of reach.
* **Depth of evidence.** For an irregular candidate, "every chain member up to height `s` is
  N" leaves the probability `s/h` that the first P member is above `h`. B had been checked up
  to 24: by the law its first P member was below 48 with probability one half, and it came
  at 31. A check to a fixed height was never evidence that a chain lives forever.
* **Regular or dead.** A chain escapes the law only if its diagonal stops needing partners.
  That is a statement about finite positions, and it is the kind that Z3 proved for A. Among
  the 371 positions of the classified world, 6 chains are of this kind: the four of A and its
  transpose, and two belonging to positions that are N by their other chain
  (`(w,w,1 | w,w,1 | 0,0,0)` and its transpose, whose diagonal has the finite cut at `u+2`).
  A scan for positions that are regular only from height 14 on (`ZLOW=14 base3_table 100 -c
  H,H,8,H,H,8,8,8,8 -F`: every cut of an infinite column at a height from 14 to 50 has a
  finite reply) finds nothing new among the 4917 attachments up to 8: A, its transpose and
  the two N positions of notes/24 §6.
* **`X_3`, `T((0,2),2)` and the roof `(2,1,0)`.** Their chains are of the same kind but live
  in a larger family (the `3×2` block, with three sorts of partner instead of one). The
  census is not reliable in that world (notes/26 §5), so the law cannot be measured there in
  the same way. The exact runs of §6 give a first number: chains end about seven times more
  rarely. If the form `G/u` holds there with `G ≈ 0.14`, a chain alive at 42 such as `X_3`'s
  has its first P member below 100 with probability 11 %, and below 10 000 with probability
  about one half. These positions cannot be settled by running the chain further.
* **`3×3×ω`.** Its own options keep three or more infinite columns, so no chain of this kind
  starts at `3×3×ω` or at its towers of type `(1,2)` and `(2,2)`. Its towers of type `(0,2)`
  do have one, and they belong to the family of §6 where chains seldom end: `T((0,2),1)`,
  `T((0,2),3)` and `T((0,2),4)` are N, and `T((0,2),2)` is open with a chain that is N up to
  height 24. Running that chain further will not decide it. If chains there end at a rate
  `0.14/u`, the chance that it ends before height one million is about three in four, and
  the chance that it ends within reach of the solver is a few per cent.
* **A working hypothesis, and where it stands.** *A position whose infinite part is at most
  two columns wide is N unless its chains are regular.* For three and four infinite columns
  with attachments up to 4 this is what the classification of notes/26 §9 found, and the law
  of §3 explains it. For the `3×2` block it is open: twelve of 35 small roofs are undecided,
  and §6 shows why. If the hypothesis held everywhere, a position whose infinite part is
  three wide in both directions would be P exactly when it has no finite P cut and none of
  the positions below it by a bite in the corner block `(1,1),(1,2),(2,1),(2,2)` is P, and
  the question about `3×3×ω` would become a question about which of those positions have a
  finite P cut. The cross positions, the bottom of that family, all have one as far as
  computed (notes/26 §7).

## 6. Exact runs: deeper chains, and the roofs over the `3×2` block

**Deeper chains.** `rodf -D file` keeps the solver's cached sequences in a file on disk, and
`-L 60000000` raises the step limit of a period certificate. With both, the chains are
limited by disk space (12 GB here) and time.

| position | chain | every member N up to | before | stopped by |
| --- | --- | --- | --- | --- |
| `X_3` | cut `(1,0)` | 42 | 35 | disk: the store reached 7 GB |
| A′ | cut `(0,1)` | 59 | 45 | time: the member at 60 was not decided in 25 minutes |
| A′ | cut `(1,0)` | 26 | 26 | no member in 25 minutes |
| `T((0,2),2)` | cut `(1,0)` | 24 | 24 | the store is 3.5 GB at height 23 |

`X_2 = (w,w,2 | w,w,0 | w,w,0)` has a P chain member at height 18:
`(w,w,2 | 18,18,0 | 18,18,0)` is P (exact). `X_2` was known to be N because the transpose of A
is one of its options; this reply does not use A.

**The roofs up to height 4.** `scripts/chain_runs.py` runs the chain "cut `(1,0)` at `z`",
`z ≤ 20`, for all 35 roofs `(w,w,f0 | w,w,f1 | w,w,f2)` with `f0 ≤ 4`, with 500 seconds and
2.6 GB each (`data/roofs/roofs_up_to_4_chain_cut10.txt`). A table to height 60 gives their
finite P cuts.

| | roofs |
| --- | --- |
| finite P cut (N) | 12: `(2,2,0)` `(2,1,1)` `(2,2,1)` `(3,2,1)` `(3,2,2)` `(3,3,1)` `(3,3,2)` `(4,2,1)` `(4,3,1)` `(4,4,1)` `(4,4,3)` `(4,4,4)` |
| P chain member (N), with its height | 11: `(0,0,0)` 0, `(1,0,0)` 2, `(1,1,0)` 1, `(1,1,1)` 4, `(2,0,0)` 18, `(3,1,0)` 7, `(3,1,1)` 1, `(3,3,0)` 3, `(3,3,3)` 1, `(4,1,1)` 2, `(4,4,0)` 9 |
| open, with the height up to which the chain is N | 12: `(2,1,0)` 24, `(2,2,2)` 24, `(3,0,0)` 42, `(3,2,0)` 20, `(4,0,0)` 20, `(4,1,0)` 20, `(4,2,0)` 20, `(4,3,0)` 19, `(4,2,2)` 17, `(4,3,2)` 16, `(4,3,3)` 16, `(4,4,2)` 16 |

The towers of `3×3×ω` among them: `T((0,2),1) = (1,1,1)` and `T((0,2),3) = (3,3,3)` are N by a
chain member, `T((0,2),4) = (4,4,4)` by a finite cut, and `T((0,2),2) = (2,2,2)` is open.
These agree with notes/12. The positions `X_g = (g,0,0)`: `X_1`, `X_2` are N, and `X_3`, `X_4`
are open.

**How often these chains end.** Fifteen of the 23 chains are alive at height 5. Three end
later (at 7, 9 and 18), twelve are alive when their run stops. With the rows weighted by
`1/u` as in §3 this is 3 ends against an exposure of 21.1, so `G ≈ 0.14`; with `G = 1` one
would expect 21 ends. Three events do not fix the constant (anything from 0.03 to 0.4 is
compatible), and they say nothing about the form of the law. They do show that this family
is not like the `2×2` block: its chains have more ways to find a partner and end much more
rarely.

## Tools and data

* `tools/base3_table.cpp`: with `STALKS=1` the census writes `prefix_stalks.txt`, every
  position with two infinite columns with its finite P cut, label and option columns.
* `scripts/chain_matching.py`: one chain row by row; `--grid W` draws the cells below the
  diagonal, `--pool` follows the pool of unused columns.
* `scripts/chain_survival.py`: the tables of §3.
* `scripts/chain_runs.py`: exact chains for a list of positions, with the solver.
* `data/chains/`: the outputs used here. The dumps themselves (25 to 60 MB each) are not in
  the repository; the commands below rebuild them.

```
STALKS=1 ./base3_table 160 -c H,H,4,H,H,4,4,4,4 -T 70 -O k4 > k4.txt      # 7 minutes
python3 scripts/chain_survival.py k4_stalks.txt k4.txt 70
STALKS=1 ./base3_table 253 -c H,H,2,H,H,2,2,2,2 -T 120 -O b > b.txt
python3 scripts/chain_matching.py b_stalks.txt "w w 2 | w w 2 | 2 2 0" 1,0 60 --grid 14
```
