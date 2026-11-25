# A census of the positions with infinite columns below `3×3×ω`

24 November 2026. Continues [notes/24](24-three-by-three.md) and
[notes/25](25-a-P-position-with-four-infinite-columns.md). Positions are written by the heights
of the nine columns in the order `(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`,
`w` for an infinite column.

`3×3×ω` is still undecided. This round changes how the candidates below it are judged.
Until now a position counted as a "P candidate" when the certified solver had found a winning
reply to each of its options up to cut height 12 to 25. That is too shallow. A new pass of the
table tool labels every position with infinite columns inside a capped region, with cuts of the
infinite columns tried up to height 50 to 110. It shows that candidate B is N by a reply at
height 31, which the solver then certifies, and it gives a first picture of how common
P-positions are among positions with several infinite columns. It also has a weak point,
which this note documents (§5).

## Results

1. **Candidate B is N** (exact, §4). The cut of `(1,0)` at height 31 leaves
   `(w,w,2 | 31,31,2 | 2,2,0)`, which the solver certifies as a P-position. The earlier checks
   had found a reply to every cut up to height 24.
2. **A census of positions with infinite columns** (§2): `base3_table -T`. Checked against
   the definition. It is a search, not a proof, and it has a weak point (item 4).
3. **The `2×2` block with attachments up to 4 is classified** (exact, §3): of the 371
   positions, A and its transpose are P, 156 are N by a finite P cut, and the other 213 are N
   by a cut of `(0,1)` or `(1,0)` that leaves a certified P-position with two infinite
   columns. The census proposed the replies and the solver certified them.
4. **Finite P cuts can be very high** (§5): 381 for attachments of height 8, 978 for height
   11. The census does not see them and then puts a P label in the wrong place.
5. **The roofs over the `3×2` block** (§6): `T((0,2),1)` is N by a certified reply at height 4.
   `T((0,2),2)`, `(w,w,2 | w,w,1 | w,w,0)` and `X_3` are open. Their chains of cuts of `(1,0)`
   are exactly N up to heights 24, 24 and 35.
6. **All 105 cross positions and all 1001 tripod positions with attachments up to 4 have a
   finite P cut** (exact, §7 and §3). So do all 825 cross positions with attachments up to
   8, the highest at 70.
7. **A second candidate with four infinite columns** (§8): `A′ = (w,w,1 | w,w,1 | 9,2,1)`.
   No finite P cut up to height 240, every option up to cut height 26 exactly N (one chain up
   to 45), no P option in the census up to cut height 110. It is not regular.
8. **A correction to notes/24 §6** (§7): the finite-reply scan missed the cuts of the poison
   column below the largest attachment.
9. **The shapes with three or four infinite columns are classified for attachments up to 4**
   (exact, §9): A and its transpose are the only P-positions among 2177.
10. `3×3×ω` is still open (§10).

## 1. Regular P-positions: no second one found

A position is *regular* here if every cut of an infinite column has a finite winning reply.
A is of this kind, and that is why it could be proved P. The scan of notes/24 §6
(`base3_table -F`) was repeated with larger attachments, with the corrected tool (§7):

| infinite shape | attachments up to | `H` | attachments | no finite P cut | all cuts answered |
| --- | --- | --- | --- | --- | --- |
| `220` (the `2×2` block) | 8 | 100 | 4917 | 2513 | 4 |
| `310` | 6 | 90 | 1344 | 94 | 0 |
| `320` | 6 | 64 | 462 | 24 | 0 |
| `311` cross | 6 | 64 | 336 | 0 | 0 |
| `330` (the `3×2` block) | 6 | 44 | 84 | 50 | 0 |
| `321` | 6 | 44 | 140 | 39 | 0 |
| `331` | 6 | 40 | 28 | 13 | 0 |
| `332` | 8 | 34 | 9 | 3 | 0 |

The four positions of shape `220` are the same as before: A, its transpose, and the two
positions `(w,w,1 | w,w,0 | 1,0,0)` and `(w,w,1 | w,w,1 | 1,1,0)`, which are N. So with
attachments up to 6 or 8 there is no second position like A. Output:
`data/base3/finite_reply_scan_corrected.txt`. (A first run with the uncorrected tool is in
`data/base3/finite_reply_scan_K6_K8.txt`; its column "no finite P cut" is too large and its
last column is the same.)

## 2. The census

**Definition.** Fix a height `H`, a cut bound `Z < H` and caps on the columns. The cells with
cap `H` are *free*; the others carry attachments within their caps. The census runs over all
positions whose free columns have a height in `0..Z` or are infinite, with the poison column
infinite. A position with no other infinite column is N (by the fundamental theorem: some cut
of the poison column is P). Every other position is labelled, from the smallest up:

* **P** if no cut of the poison column at a height up to `H` is P, and no option is labelled
  P. The options are the bites in the finite columns and the cuts of an infinite column at a
  height up to `Z`.
* **N** otherwise.

**What the labels mean.** The label is the true status with two truncations: cuts of the
poison column above `H` and cuts of other infinite columns above `Z` are ignored.
* "N by a P cut of the poison column" is exact (the table of finite positions is exact).
* A label P is never exact. It says: no winning reply within the bounds.
* "N by an option labelled P" is as good as that P label. If the option has two infinite
  columns, the certified solver of notes/07 can decide it exactly.

So the census is a search and a filter, not a proof. Its value is depth: the solver decides
single options one at a time, up to cut heights between 12 and 45 depending on the position;
the census covers every position in the region up to cut height 50 to 110.

**Method.** `base3_table H -c caps -T Z`, after the table of finite positions is built.
* Let `s⁻` be `s` after the highest bite allowed in column `c` (one layer off a finite column,
  the cut at `Z` for an infinite one). Every lower bite in column `c` is a bite on `s⁻` and
  gives the same position. So "`s` has an option labelled P by a bite in column `c`" holds iff
  `s⁻` is labelled P or has such an option itself. One bit per column and position, eight
  look-ups per position.
* A position has at most one P cut of the poison column. The cuts below the largest finite
  height `m` are the cuts of the position with one top layer removed, so they are read off
  there. Only the positions with no option labelled P are scanned from `m` to `H`.
* The positions are ranked like the rests of the main table and done in the same parallel
  order. The census itself is small (10⁷ to 10⁹ positions, three bytes each); the table of
  finite positions decides the cost.

**Checks.**
* `scripts/census_check.py` recomputes the labels from the definition with no shortcuts.
  Eight settings (heights 5 to 10, `Z` from 2 to 4, between 325 and 4410 positions each): the
  sets of positions labelled P are identical.
* In the world of the `2×2` block with attachments up to 2, the labels for `(H, Z) = (100, 50)`
  and `(160, 70)` agree on every position with attachments up to 50 (482 labelled P in both).
* Known results are reproduced: `2×2×ω` is N by the bite to the domino rod, A and its
  transpose are the only positions labelled P among the 46 with the `2×2` block infinite and
  attachments up to 2 (§3).
* Against the certified solver: in the four shapes classified completely in §9 the census
  had the right verdict for every position. It had the wrong reply height for 7 of the 464
  positions that needed a reply, because of finite cuts above `H` (§5), and its P labels for
  positions with larger attachments are less reliable (§6, §8).

## 3. The world of the `2×2` block

`base3_table 160 -c H,H,4,H,H,4,4,4,4 -T 70`: the columns `(0,1)`, `(1,0)`, `(1,1)` are free,
the five others carry attachments up to height 4. 1.8 million positions, of which 371 have the
whole `2×2` block infinite.

| infinite part | positions | labelled P | finite P cut and no option labelled P |
| --- | --- | --- | --- |
| two columns `(0,0),(0,1)` | 888 013 | 1 697 | 195 517 |
| two columns `(0,0),(1,0)` | 888 013 | 1 697 | 195 517 |
| tripod `(0,0),(0,1),(1,0)` | 25 487 | 0 | 2 945 |
| the `2×2` block | 371 | 2 | 40 |

* **Only A and its transpose are labelled P** among the 371 positions with four infinite
  columns. Every other one is N in the census.
* **This is exact.** 156 of the 371 have a finite P cut. For each of the other 213 the solver
  certifies a reply that leaves two infinite columns (`scripts/verify_census_options.py`,
  `data/census/block220_att4_certified_replies.txt`): for 207 a reply proposed by the census,
  for 4 a lower cut of the same column, for 2 a reply that the solver found itself. In those
  6 cases the census had the right verdict with the wrong height, for the reason of §5.
  So **A and its transpose are the only P-positions with the `2×2` block infinite and
  attachments of height at most 4**, regular or not.
* **No tripod position is labelled P** (25 487 positions, the column `(1,1)` up to height 70).
* **All 1001 tripod positions with attachments up to 4 have a finite P cut** (exact):
  `base3_table 200 -c H,H,4,H,4,4,4,4,4 -T 90`. The cut is at height 6 or lower for half of
  them and at most 23. This is the conjecture of notes/17 for these attachments. The "48
  tripods without a finite P cut" of notes/24 §6 were an artefact of the scan (§7): their
  cuts lie below their largest attachment.
* **All 490 rows of three with attachments up to 4 are N** (exact): 243 by a finite P cut and
  247 by a cut of `(2,0)` that leaves a certified P-position with two infinite columns
  (`data/census/row_att4_certified_replies.txt`). This agrees with notes/14, where all such
  positions with entries up to 8 were decided.
* Of the 371 block positions, 156 have a P cut of the poison column and 215 do not. Among the
  213 of those that are N, the census finds a P option in *both* chains "cut `(0,1)` at `z`"
  and "cut `(1,0)` at `z`" for 199, and in one of them for 14. The height of the lowest P
  option (as the census has it): 0 to 4 for 145 positions, 5 to 9 for 52, 10 to 14 for 12, 15
  to 19 for 3, and 31 for one. The other chain is often much deeper: its P option is above height 20 in 29
  positions, up to 56.

So in this world a position survives because *every* member of both chains has a winning
reply, and that happens only for A, where all those replies are finite and regular. Everything
else is caught by a chain member that is P, usually early and sometimes late.

The height truncation is light here, though not absent (§5): of the 195 517 positions with
two infinite columns that are N by a finite cut only, 68 have that cut above height 80 and 5
above 120.

## 4. Candidate B is N, by a reply at height 31

`B = (w,w,2 | w,w,2 | 2,2,0)` was the second candidate of notes/24: no finite P cut up to 110,
and the solver had found a certified reply to every cut of `(1,0)` up to height 24. The census
labels it N, and the solver confirms the reply, so **B is N (exact)**. The P option is the cut
of `(1,0)` (or `(0,1)`) at height **31**, which leaves

`S(31,31) = (w,w,2 | 31,31,2 | 2,2,0)`,

a position with two infinite columns. Write `S(u,v) = (w,w,2 | u,v,2 | 2,2,0)`. For each `u` at
most one `S(u,v)` is P, and for each `v` at most one, so the P-positions among them form a
matching. In the census it reads

| `u` | 5 | 6 | 7 | 8 | 9 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | **31** | 32 | 34 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `v` | 4 | 5 | 6 | 7 | 8 | 10 | 11 | 9 | 12 | 13 | 14 | 16 | 15 | 17 | 18 | 19 | 20 | 21 | 22 | 24 | 25 | 23 | 26 | 28 | 27 | **31** | 29 | 30 |

For `u < 31` the diagonal position `S(u,u)`, which is the option "cut `(1,0)` at `u`" of B, is N:
it has a finite P cut or the partner `S(u,v)` below it. At `u = 31` neither exists.

This is the same mechanism as the side class of the two-dimensional game (notes/13,
notes/20): a matching with a first fixed point. It also shows what a check "up to cut height
24" is worth: B had passed it.

**Certificate.** `rodf -L 60000000 -p w,w,2,31,31,2,2,2 332` answers "P exact"
(`data/atlas3/B_reply_cut31.txt`). The decision rests on 1559 positions with two infinite
columns, each with a certified period; the longest certified sequence has 5.5 million terms.
With the default step limit the same run ends as "P heuristic", because 57 of the
certificates do not close within 3 million steps. The solver also agrees with the census on
the smaller members tested: `S(5,4)`, `S(9,8)`, `S(13,9)`, `S(18,15)` are P, and `S(10,10)` is
N by a finite cut at 17.

## 5. How high a finite cut can be

The census with `H = 100` over the `3×2` block with roofs up to 2 labelled the position

`D_8 = (w,w,2 | 8,8,2 | 8,8,2)`,

the option "cut `(1,0)` at 8" of the tower `T((0,2),2)`, as P. The solver decides `D_8`
exactly: it is **N, by the cut of the poison column at height 381**. So a position with two
infinite columns and attachments of height 8 can have its only finite P cut at height 381.

A second example, from the world of §8, at `H = 240`: the census labels
`(w,11,1 | w,10,1 | 8,2,1)` as P. The solver finds that it is **N by the cut of the poison
column at height 978**. The wrong label moves the P member of one chain from height 11 to
height 17: the solver certifies `(w,11,1 | w,11,1 | 8,2,1)` as P, the census has it as N
and puts the P label on `(w,17,1 | w,17,1 | 8,2,1)`, which is N. (notes/12 already met a
finite cut at height 4107.)

Consequences.
* A label P of the census is only as good as `H`. In the world of the `2×2` block the high
  cuts are rare (§3). In the world of the `3×2` block they are not: of the first five cuts of
  `(1,0)` of `T((0,2),2)` without a finite reply up to height 100 (`z = 4, 5, 6, 8, 11`), one
  has a finite reply above it.
* The lists "cut heights without a finite reply" of notes/24 §6 and of
  `data/x3/finite_replies_H110.txt` are upper bounds for the same reason.
* For positions with two infinite columns the solver is exact at every height, because it
  certifies the period of the sequence of partner heights. The certified sequences met here
  have up to 5.5 million terms. For three or more infinite columns there is no such
  certificate.

So the census is used in two ways only: as statistics in worlds where the truncation is
light, and as a source of candidates that the solver then decides.

## 6. The roofs over the `3×2` block

Let `Q(f0,f1,f2)` be the `3×2` block of columns infinite with a roof on the row `y = 2` of
heights `f0 ≥ f1 ≥ f2`: the position `(w,w,f0 | w,w,f1 | w,w,f2)`. So `Q(g,g,g)` is the tower
`T((0,2),g)` of `3×3×ω` and `Q(g,0,0)` is `X_g`, the tower of type `(0,2)` of the rod `331×ω`.
With roofs up to height 2:

| roof | position | status | reason |
| --- | --- | --- | --- |
| `(0,0,0)` | `3×2×ω` | N | bite `(1,0,0)` leaves the domino rod |
| `(1,0,0)` | `X_1` | N, exact | cut `(1,0)` at 2 leaves `(w,w,1 \| 2,2,0 \| 2,2,0)`, certified P |
| `(1,1,0)` | | N, exact | cut `(1,0)` at 1 leaves `(w,w,1 \| 1,1,1 \| 1,1,0)`, certified P |
| `(1,1,1)` | `T((0,2),1)` | N, exact | cut `(1,0)` at 4 leaves `(w,w,1 \| 4,4,1 \| 4,4,1)`, certified P |
| `(2,0,0)` | `X_2` | N, proved | cut `(2,0)` at 1 leaves the transpose of A |
| `(2,1,0)` | | **open** | |
| `(2,1,1)` | | N, exact | finite P cut at height 8 |
| `(2,2,0)` | | N, exact | finite P cut at height 3 |
| `(2,2,1)` | | N, exact | finite P cut at height 2 |
| `(2,2,2)` | `T((0,2),2)` | **open** | |

In four of the first five rows the winning reply is in the same chain: cut `(1,0)` at a small
height, which leaves two infinite columns. The three certified positions were suggested by the
census and then decided by the solver.

What is known exactly about the open ones, and about `X_3 = Q(3,0,0)`:

| position | finite P cut | options, all cut heights up to | chain "cut `(1,0)` at `z`" |
| --- | --- | --- | --- |
| `T((0,2),2)` | none up to 100 | 12: all N, except one not decided | N for every `z ≤ 24` (notes/12; 22 in this round's run) |
| `Q(2,1,0)` | none up to 100 | | N for every `z ≤ 24` |
| `X_3` | none up to 110 | 13: all N | N for every `z ≤ 35` |

* `T((0,2),2)`: the cuts of `(0,1)`, `(1,1)`, `(2,0)`, `(2,1)` at heights 0 to 12 are N by an
  exact reply (`data/t02/options_cut0-12.txt`), with two remarks. The cut of `(1,1)` at 2 is N
  by a finite cut at height 70 and the cut of `(2,1)` at 3 by a finite cut at height 29, which
  the solver finds only when told to search that high. The cut of `(1,1)` at 9 ran out of
  memory and is not decided.
* The chain members have two infinite columns, so the solver decides them exactly
  (`data/t02/chain_cut10.txt`, `data/roofs/roof210_chain_cut10.txt`, `data/x3/`). Beyond the
  heights in the table it runs out of memory (4 GB per run). For `X_3` the larger step limit
  `-L 60000000` moved that point from 27 to 35.
* The census of this world (`H = 100`, `Z = 50`) labels both open roofs N, but by options that
  are wrong or cannot be checked: for `T((0,2),2)` the option `D_8` of §5, which is N, and a
  cut of `(0,1)` at 29; for `Q(2,1,0)` a cut of `(1,1)` at 21 and a cut of `(2,0)` at 16, which
  leave four infinite columns. So the census decides nothing here.

By the statistics of §3 a position of this kind that is not regular is N by some member of
its chain, possibly a deep one (B: 31). The three positions above are not regular: about half
of their chain members have no finite reply. So the expectation is that they are N, by a
chain member beyond the reach of the solver. This is an expectation, not a result.

## 7. Cross positions have a finite reply, as far as computed

A *cross position* has the five columns of the cross `(0,0),(0,1),(0,2),(1,0),(2,0)` infinite
and attachments `(a, b, c, d)` on the corner block `(1,1),(1,2),(2,1),(2,2)`. The towers
`T((1,1),g)` of `3×3×ω` are the cross positions `(g,g,g,g)`.

`base3_table 100 -c H,H,H,H,4,4,H,4,4 -T 48`: **all 105 cross positions with attachments up to
4 have a finite P cut**, at height 27 or lower. This is exact. 13 of them have the cut below
their largest attachment (for example `(w,w,w | w,3,2 | w,2,1)` at height 2).

| height of the P cut | 1–4 | 5–8 | 9–12 | 13–18 | 20–27 |
| --- | --- | --- | --- | --- | --- |
| cross positions | 34 | 34 | 18 | 13 | 6 |

**Attachments up to 8.** `base3_table 64 -c H,H,H,H,8,8,H,8,8 -T 30`: of the 825 cross
positions, 823 have a finite P cut at height 57 or lower (half of them at 10 or lower, nine
in ten at 26 or lower). The two others are `(w,w,w | w,7,7 | w,5,2)` and its transpose. A
table for that position alone (`base3_table 96 -c H,H,H,H,7,7,H,5,2`, 7 GB) finds its P cut
at height **70**. So **all 825 cross positions with attachments up to 8 have a finite P cut**
(exact).

Together with the cuts of the towers `T((1,1),g)` for `g ≤ 14` (notes/24) and of the towers of
type `(1,1)` of the rod `331` for `g ≤ 24`, no cross position without a finite P cut is known.
The cuts get higher with the attachments (27, then 57 and 70), so a table that stops at a
fixed height will show apparent exceptions.

**A correction to notes/24 §6.** The finite-reply scan (`base3_table -F`) tested the cuts of
the poison column only at or above the largest attachment, for the position itself and for
the reply to a cut. So its column "no finite P cut" was too large: for the crosses with
attachments up to 4 it said 13, and the true number is 0. The same holds for the reply to a
cut at a height below the largest attachment. The scan is fixed (it now tests every height).
The table of notes/24 §6 with the corrected tool (`data/base3/finite_reply_scan_corrected.txt`):

| shape | attachments up to | `H` | attachments | no finite P cut (was) | all cuts answered |
| --- | --- | --- | --- | --- | --- |
| `300` row of three | 3 | 120 | 175 | 92 (116) | 0 |
| `210` tripod | 3 | 120 | 330 | 0 (48) | 0 |
| `310` | 3 | 90 | 125 | 4 (18) | 0 |
| `220` | 4 | 100 | 371 | 215 (274) | 4 |
| `320` | 4 | 64 | 140 | 12 (30) | 0 |
| `311` cross | 4 | 64 | 105 | 0 (13) | 0 |
| `330` | 4 | 44 | 35 | 23 (28) | 0 |
| `321` | 4 | 44 | 55 | 12 (20) | 0 |
| `331` | 3 | 40 | 10 | 5 (6) | 0 |
| `332` | 4 | 34 | 5 | 1 (1) | 0 |

The last column is unchanged, and so is the conclusion of notes/24 §6: A is the only position
in that table whose infinite cuts all have finite replies.

## 8. A second candidate with four infinite columns

The census of the `3×2` world labels five more positions with the `2×2` block infinite as P.
Their third column is taller than in §3: `(w,w,1 | w,w,1 | 9,2,1)` and
`(w,w,2 | w,w,1 | d,e,0)` with `(d,e) = (11,9), (15,12), (16,16), (21,14)`. A census with more
height decides which of them survive.

**`A′ = (w,w,1 | w,w,1 | 9,2,1)`**: the wings of A, and a third column of heights 9, 2, 1.
`base3_table 240 -c H,H,1,H,H,1,10,2,1 -T 110` covers the 109 positions with the block
infinite, wings up to 1 and a third column up to `(10,2,1)`:

* 83 have a finite P cut. Of the 26 others, 24 are N in the census by an option labelled P.
  For all 24 the solver certifies a reply that leaves two infinite columns, at height 11 or
  lower (`data/aprime/neighbours_certified_replies.txt`). So in this world every position
  other than A and A′ is exactly N.
* **A and A′ are labelled P.** A′ has no P cut of the poison column up to height 240 and no
  option labelled P among the cuts of its infinite columns up to height 110.
* Every cut of `(1,1)` of A′ up to height 110 has a finite reply. The cuts of `(0,1)` and of
  `(1,0)` have a finite reply for about half of the heights, and for the other half a reply
  with two infinite columns. So A′ is not regular and the method of notes/25 does not apply.

Exact results on A′ (`data/aprime/`):
* no P cut of the poison column up to height 240 (table);
* the cuts of `(1,1)` at heights 0 to 110 are N, each by a finite reply (table);
* the cuts of `(0,1)` at heights 0 to 45 and the cuts of `(1,0)` at heights 0 to 26 are N
  (solver: they leave two infinite columns);
* the 14 options by a bite in a finite column are N (solver).

So every option of A′ up to cut height 26 is exactly N, and in one of the two chains up to
45. Above that the statement rests on the census. (The solver needs the larger step limit
`-L 60000000` here too: with it the cuts of `(0,1)` from 27 to 45 take three minutes, with
the default limit the first of them did not finish in twenty.)

So A′ has survived to cut height 110, where B fell at 31 and every other position of its
world at 11 or lower. It is a candidate, not a result: a chain member far up can still be P.

**Later assessment ([notes/27](27-how-a-chain-ends.md)).** Chains of this kind end at height
`u` with probability about `1/u`, measured over 216 of them. By that law a survivor like A′
is expected among the few hundred positions scanned, and each of its chains ends before
height 240 with probability one half. So A′ is more likely N than P.

**The other four.** `base3_table 200 -c H,H,2,H,H,1,16,16,0 -T 90` covers the positions
`(w,w,a | w,w,b | d,e,0)` with `a ≤ 2`, `b ≤ 1`, `d, e ≤ 16`. At this height the three
positions with `(d,e) = (11,9), (15,12), (16,16)` are N in the census (their replies there
have not been certified), `(21,14)` is outside the region, and a different position is
labelled P: `(w,w,2 | w,w,1 | 10,10,0)`. The solver settles it: the cut of `(1,0)` at
height 19 leaves `(w,w,2 | 19,19,1 | 10,10,0)`, which is **P (exact)**, so
`(w,w,2 | w,w,1 | 10,10,0)` is **N (exact)** (`data/aprime/second_block_options.txt`). The
census had put the P label of that chain elsewhere. So labels of single positions move with
`H`, and only A′ has stood up to the solver so far.

## 9. The two-wide shapes with attachments up to 4

The method "the census proposes, the solver decides" classifies a region exactly when every
position in it has a finite P cut or a reply with two infinite columns. For the positions
whose infinite part has at most two columns in one direction, and attachments up to 4:

| infinite part | positions | P | N by a finite P cut | N by a certified reply | open |
| --- | --- | --- | --- | --- | --- |
| row of three `(0,0),(1,0),(2,0)` | 490 | 0 | 243 | 247 | 0 |
| tripod `(0,0),(0,1),(1,0)` | 1001 | 0 | 1001 | 0 | 0 |
| row of three and `(0,1)` (shape `310`) | 315 | 0 | 311 | 4 | 0 |
| the `2×2` block (shape `220`) | 371 | 2 | 156 | 213 | 0 |
| five columns `(0,0),(0,1),(1,0),(1,1),(2,0)` (shape `320`) | 140 | 0 | 132 | 7 | 1 |
| the `3×2` block, roofs up to 2 (§6) | 10 | 0 | 3 | 5 | 2 |
| the `3×2` block, roofs up to 4 ([notes/27](27-how-a-chain-ends.md) §6) | 35 | 0 | 12 | 11 | 12 |

The two P-positions are A and its transpose. In the last row the five replies are the domino
rod, three certified positions and the transpose of A. Each count is for one orientation of
the shape; the transposed positions have the transposed status.

The open position of shape `320` is `(w,w,4 | w,w,4 | w,4,2)`. The census proposed the cut of
`(1,0)` at height 20, and the solver finds that member N. Its chain of cuts of `(1,0)` is
exactly N up to height 22; the run was stopped there after twenty minutes at 4.5 GB.

So below `3×3×ω`, among the positions with three or four infinite columns and attachments of
height at most 4, **A and its transpose are the only P-positions** (2177 positions). The
certified replies are in `data/census/*_certified_replies.txt`. Over the four shapes with a
complete classification the census had the right verdict for every position and the wrong
reply height for 7 of the 464 that needed a reply; in shape `320` it had the height wrong
for 2 of 8.

## 10. What this says about `3×3×ω`

Nothing is decided. The round changes the reading of the evidence.

* **Shallow checks do not carry.** "Every option up to cut height 13 is N" was the evidence
  for `X_3` and `T((0,2),2)` as P candidates. B passed that test up to height 24 and is N by
  a reply at height 31. The finite cut at height 381 (§5) shows the same for the height of the
  poison column. The honest status of `X_3`, `T((0,2),2)` and `Q(2,1,0)` is "open, with a
  reply expected deep in the chain of cuts of `(1,0)`".
* **Where a position is two columns away from the poison column, the solver is exact.** A
  position whose infinite part misses the row `y = 2` has the chain "cut `(1,0)` at `z`", whose
  members have two infinite columns. If one member is P the position is N, exactly. That is
  how the roofs of §6 and B were settled.
  `3×3×ω`, the rod `331×ω` and the positions between them have no such chain: cutting any one
  column leaves three or more infinite columns. For them neither a P claim nor an N claim
  can be certified by the present tools.
* **Cross positions are not candidates** (§7): all 825 computed have a finite P cut. The towers of type `(1,1)` of `3×3×ω` are cross positions. So the P option of
  `3×3×ω`, if there is one, is more likely a tower of type `(0,2)`, `(1,2)` or `(2,2)`, or the
  rod `331×ω`.
* **P-positions with four infinite columns are rare.** With attachments up to 4 there are
  exactly two, A and its transpose (§3). With a taller third column the census proposed six
  more. The solver refuted one, three turned N in a taller census, one was not looked at
  again, and A′ is left (§8). A chain of
  infinitely many positions, such as the towers `T(b,g)` of one type, meets such an exception
  with some small chance at each step. Whether it ever does is exactly what cannot be
  computed.
* **The working method** that came out of this round: the census proposes, the solver
  decides. It classifies a whole region exactly whenever every position in it has a finite
  P cut or a reply with two infinite columns. That covers the positions whose infinite part
  is at most two columns wide. It does not reach `3×3×ω` or its towers of type `(1,2)` and
  `(2,2)`, whose options all keep three or more infinite columns.

## Tools and data

* `tools/base3_table.cpp`: `-T Z` census, `-O prefix` its output files, `-U file` reports on
  listed positions, `PROFILE=1` one letter per cut height for the positions with every free
  cell infinite (`P` labelled P, `f` finite reply, `i` reply with infinite columns only).
  The scan `-F` now tests every cut height.
* `scripts/census_check.py`: the census against its definition.
* `scripts/option_runs.py`: the solver on single options "cut cell `c` at `z`", with a memory
  watch.
* `scripts/verify_census_options.py`: asks the solver to certify the replies that the census
  proposes.
* `scripts/solver_replies.py`: turns the solver's replies into queries for the census.
* `data/census/`: census outputs. `data/aprime/`, `data/t02/`, `data/roofs/`, `data/x3/`:
  solver runs. `data/atlas3/B_reply_cut31.txt`: the certificate run for B.

```
g++ -O3 -march=native -std=c++17 -Wall -fopenmp -o base3_table tools/base3_table.cpp
./base3_table 160 -c H,H,4,H,H,4,4,4,4 -T 70 -O block4      # §3: 0.5 GB, 9 minutes
PROFILE=1 ./base3_table 240 -c H,H,1,H,H,1,10,2,1 -T 110    # §8: A′
./base3_table 100 -c H,H,H,H,4,4,H,4,4 -T 48                # §7: the crosses
./rodf -L 60000000 -p w,w,2,31,31,2,2,2 332                 # §4: B's reply, "P exact"
./rodf -p w,w,2,8,8,2,8,8,2 333                             # §5: N by the cut at 381
python3 scripts/census_check.py ./base3_table 9 H,H,2,H,H,2,H,H,2 4
```
