# `3×3×ω`: finite tables, an atlas of small positions, and a P candidate with four infinite columns

23 November 2026. Gale's `3×3×ω` is still undecided. This note records a round of work on it:
a new exact tool for finite positions, the rod `331×ω` (the smallest undecided rod, and an
option of `3×3×ω`), a scan of all small positions with three or more infinite columns, and
the first position with more than two infinite columns that looks like a P-position for a
structural reason.

Positions are written by the heights of the nine columns in the order
`(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`, with `w` for an infinite column.
Bases are written by column heights as in notes/01: `331` is the `3×3` base without the cells
`(2,1)` and `(2,2)`, and `322` is its mirror image.

## Results

1. **The tower `T((1,1),12)` of `3×3×ω` is N** (exact): it has a finite P cut at height 39.
   It was one of the 23 open towers with `g ≤ 12`; 38 of the 60 are now N, none is P.
2. **`h(331) > 72`** (exact): no finite cut of the rod `331×ω` is P up to height 72. Before
   it was 20. The finite P cuts of all its towers up to height 72 are in
   `data/base3/base322_H72.txt`.
3. **The towers of `3×3×ω` with `g = 0`** are rods over smaller bases. Four of the five types
   are N. The fifth is `331×ω`. If it is P, `3×3×ω` is N.
4. **Atlas** (exact). Of the 240 positions below `3×3×ω` with three or more infinite columns
   and attachments of height at most 2 (up to transposition), 229 are N by an exact winning
   reply. The 11 others are listed in §4.
5. **Candidate A** `= (w,w,1 | w,w,1 | 2,0,0)`: the `2×2` block of columns infinite, the
   columns `(0,2)` and `(1,2)` of height 1 and the column `(2,0)` of height 2.
   * A is a P-position if three one-parameter families of finite positions are P (§5).
   * That is verified for all heights up to 252 (exact, by the table). Every infinite cut of
     A at height `z` is answered by cutting the poison column at `z+1` or `z+2`.
   * This is not a proof. Most of the replies one level down have the same simple form, but
     at least one family of options has only irregular replies (§5).
   * No P-position with more than two infinite columns was known before, with or without
     proof. A is the only position of this kind among the shapes and attachments scanned
     (§6).
6. **Nothing here decides `3×3×ω`.** A is not an option of it. If A is P, the tower
   `T_331((2,0),2)` of the rod `331×ω` is N, and so are the other positions listed in §7.

## 1. The towers with `g = 0`, and the rod `331×ω`

The tower tables of notes/12 start at `g = 1`. With `g = 0` the tower `T(b,0)` is the rod over
the base `3×3 ∖ ↑b`:

| type `b` | `(0,1)` | `(0,2)` | `(1,1)` | `(1,2)` | `(2,2)` |
| --- | --- | --- | --- | --- | --- |
| base | `3` | `33` (`3×2`) | `311` | `322` (mirror of `331`) | `332` |
| rod | N (domino rule) | N (domino rule) | N, `h = 1` | **open** | N, `h(332) = 5` |

`331×ω` is the smallest undecided rod. Neither the domino rule nor a finite P-height applies,
and every rod over a smaller base inside it is N (`33`, `321`, `32`, `311`, `3`). `331×ω` is
an option of `332×ω` and of `3×3×ω`, and `332×ω` is an option of `3×3×ω`, so at most one of
the three is P; `332×ω` is N.

Conjecture 1.1 (notes/01) says that no rod but the domino is P. Its evidence is rods that are
N by a finite P-height or by the domino rule. The rods where neither applies (`331`, `511`,
`611`) are all undecided, so the conjecture is untested where it matters, and so is the guess
that `3×3×ω` is N.

`331×ω` is P iff it has no finite P cut and all its towers are N. In the orientation `322`
(columns `(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1)`) the six tower types are:

| `b` | cells cut to `g` | infinite part | kind |
| --- | --- | --- | --- |
| `(0,1)` | `(0,1),(0,2),(1,1),(2,1)` | row `y = 0` | `W(R)` of notes/14 |
| `(1,0)` | `(1,0),(1,1),(2,0),(2,1)` | column `x = 0` | `W(R)`, transposed |
| `(0,2)` | `(0,2)` | `3×2` | six columns |
| `(1,1)` | `(1,1),(2,1)` | cross `311` | five columns, no two-wide option |
| `(2,0)` | `(2,0),(2,1)` | `32` | five columns |
| `(2,1)` | `(2,1)` | `321` | six columns, no two-wide option |

## 2. The dense table of finite positions

`tools/base3_table.cpp` computes, for every finite position over the `3×3` base within given
caps on the column heights, whether it is P.

**Method.** Fix the heights `r` of the eight columns other than the poison column. Lowering
the poison column is a move, so at most one height `a` makes `[a; r]` P. Call it `π(r)`.
* `r` is *killed* if `π(min(r, a')) = a'` for some `1 ≤ a' < max(r)`. Then no `[a; r]` is P.
* Otherwise `π(r)` is the least `a ≥ max(r)` (and `≥ 1`) that is not `π(r')` for a rest `r'`
  one bite below `r`.

This is the "completing height" of `tools/rodf.cpp`. The new tool stores `π` for all rests in
one array (one byte each), indexed by a ranking of plane partitions. The rests that agree
outside column `x = 2` form a block. A bite outside that column maps a block into one other
block, so the table is read in streams and not at random. Blocks with the same total height
of the other five columns do not depend on each other and are computed in parallel.

**Sizes.** The full `3×3` base at height 40 has `1.1·10¹⁰` rests. The base `331` at height 72
has `4.7·10⁹` and took 14 minutes on four cores. With caps on the attachment cells the table
is small and reaches height 254 (the limit of one byte).

**Checks.**
* `scripts/base3_check.py` compares the list of all P-positions with a brute-force search:
  33 cap settings at heights 4 and 6, all identical.
* At height 20 the table reproduces the finite P-heights of notes/01 (`21`, `31`, `32`, `311`,
  `321`: 1, 5, 1, 1, 5) and every finite tower cut of notes/12 for the five types.
* `h(332) = 5` agrees with `rodf -H`.

**Other uses.**
* `-q`: one-parameter families of positions, for example `h+1 h+1 1 h h 1 2 0 0`.
* `-F`: for every attachment within the caps, whether each infinite cut has a finite winning
  reply (§6).
* A line `m …` in the query file lists the winning bites of a finite position.

## 3. Finite results

**The rod `331`.** No finite P cut up to height 72. Finite P cuts `g → h` of its towers, in
the orientation `322`, for `h ≤ 72`:

| `b` | finite P cuts | least `g` without one |
| --- | --- | --- |
| `(0,1)` | 1→2, 3→5, 5→8, 7→12, 16→30, 17→25, 18→24, 20→28, … | 2 |
| `(1,0)` | 1→2, 2→3, 3→11, 8→12, 9→13, 11→16, 14→40, 15→21, … | 4 |
| `(0,2)` | none at all for `g ≤ 71` | 1 |
| `(1,1)` | every `g ≤ 24`: 1→4, 2→5, 3→8, 4→9, 5→15, 6→17, 7→20, 8→28, 9→16, 10→22, 11→26, 12→18, 13→45, 14→30, … | 25 |
| `(2,0)` | every `g ≤ 15`: 1→5, 2→6, 3→13, 4→8, 5→41, 6→15, 7→19, 8→10, 9→34, 10→39, … | 16 |
| `(2,1)` | every `g ≤ 8`: 1→19, 2→7, 3→29, 4→10, 5→20, 6→58, 7→32, 8→71 | 9 |

The cuts can be deep: `5→41`, `6→58`, `8→71`, `13→45`. At height 40 the same table showed
`g = 5`, `6`, `8` and `13` as unmatched. So "no finite cut up to `H`" says little about a
single tower.

So the towers of `331` are N for:
* types `(1,1)`, `(2,0)`, `(2,1)` and all `g ≤ 8` (finite cuts);
* types `(0,1)` and `(1,0)` and all `g ≤ 8`: these are positions `W(R)` with entries at most 8,
  all N by notes/14;
* type `(0,2)`, `g = 1`: exact, by the reply "cut `(1,0)` at 2", a certified two-wide stalk.

The open part is the type `(0,2)`: the positions `X_g = 3×2×ω ∪ (0,2)×g`, the `3×2` rod with
one more column of height `g`. None of them has a finite P cut up to height 72. At most one
`X_g` is P.

**The full base.** `base3_table 36 -s -t` (4.7 GB, 8 minutes on three cores) gives every
finite P cut of every tower of `3×3×ω` up to height 36 (`data/base3/base333_H36.txt`):

| `b` | `g → h` for `h ≤ 36` |
| --- | --- |
| `(0,1)` | 1→7, 2→11, 6→15, 8→18, 14→26, 15→30, 16→29, 18→36, 20→31 |
| `(0,2)` | 4→9, 6→10, 16→20, 18→23, 19→25, 21→24 |
| `(1,1)` | 1→3, 2→8, 3→5, 4→6, 5→10, 6→19, 7→17, 8→20, 9→25, 10→24, 11→22, 13→32, 14→29 |
| `(1,2)` | 1→11, 2→15, 5→13, 11→12, 25→28, 27→35, 29→33 |
| `(2,2)` | 1→2, 2→6, 3→4, 5→19, 6→12, 9→14, 11→16, 14→21, 18→28, 20→27, 22→34, 23→33 |

For `g ≤ 12` these are the cuts of notes/12 and no others. So none of the open towers has a
finite P cut up to height 36. Before, the bound was at most 29 for the types `(0,2)`, `(1,2)`
and `(2,2)`.

**`T((1,1),12)` is N.** With the four columns above `(1,1)` capped at 12 the table reaches
height 56 (`base3_table 56 -c H,H,H,H,12,12,H,12,12`, 5.2 GB, 11 minutes). It finds the
finite P cut **`12 → 39`**: the position with the block at height 12 and the five other
columns at height 39 is P. The earlier search had stopped at height 31 for lack of memory.
So 38 of the 60 towers with `g ≤ 12` are now N, and every `(1,1)` tower with `g ≤ 12` is N
by a finite cut.

**Deeper tables with capped attachments.** Capping the cut columns makes the table smaller,
so it reaches further:

| towers | caps | height | finite P cuts |
| --- | --- | --- | --- |
| `(1,1)`, `g ≤ 12` | block `≤ 12` | 56 | every `g ≤ 12`; new: 12→39 |
| `(0,2)`, `g ≤ 2` | row `y = 2` `≤ 2` | 100 | none for `g = 1, 2` |
| `(0,2)`, `g ≤ 12` | row `y = 2` `≤ 12` | 44 | only 4→9 and 6→10 |
CAP02ROWS
| `(1,2)`, `g ≤ 4` | `(1,2),(2,2) ≤ 4` | 48 | 1→11, 2→15; none for `g = 3, 4` |

So `T((0,2),2)` has no finite P cut up to height 100 (before: 29). The table with the row
capped at 2 also decides the positions one bite below it in the roof: the roofs `(2,2,1)`,
`(2,2,0)` and `(2,1,1)` have finite P cuts at heights 2, 3 and 8, the roof `(1,1,1)` is the
tower `T((0,2),1)`, which is N, and the roof `(2,0,0)` is `X_2`. So the status of
`T((0,2),2)` now depends only on its infinite cuts, and on A through `X_2`.

## 4. The atlas of small positions

`scripts/atlas3.py K` runs the rod solver on every position below `3×3×ω` whose finite columns
have height at most `K` and which has at least three infinite columns, up to transposition.
The verdict "N exact" means an exact P option was found: a finite position, or a two-wide
stalk with a periodicity certificate. Outputs are in `data/atlas3/`.

| `K` | positions | N exact | rest |
| --- | --- | --- | --- |
| 1 | 62 | 59 | 3 |
| 2 | 240 | 229 | 11 |

The counts include positions that the first pass (60 s each) left open and that are N for a
known reason or after a longer run: `3×2×ω` (domino rule), `X_1`, the tower `T((0,2),1)`
(notes/12), `(w,w,1 | w,w,1 | w,w,0)`, `(w,w,1 | w,w,1 | w,2,1)` (finite cut at height 73)
and `(w,w,2 | w,w,2 | w,1,0)`.

By infinite shape (row lengths of the infinite part, notes/17), for `K = 2`:

| shape | `300` | `210` | `310` | `220` | `311` | `320` | `321` | `330` | `331` | `332` | `333` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| positions | 50 | 52 | 40 | 28 | 15 | 25 | 10 | 10 | 6 | 3 | 1 |
| not N exact | 0 | 0 | 0 | 2 | 0 | 0 | 3 | 3 | 2 | 0 | 1 |

The positions that are not N exact:

| position | shape | what it is | status |
| --- | --- | --- | --- |
| `(w,w,1 \| w,w,1 \| 2,0,0)` | `220` | candidate A | P up to height 252 (§5) |
| `(w,w,2 \| w,w,2 \| 2,2,0)` | `220` | candidate B | open (§6) |
| `(w,w,2 \| w,w,0 \| w,w,0)` | `330` | `X_2` | N if A is P (§7) |
| `(w,w,2 \| w,w,1 \| w,w,0)` | `330` | | open |
| `(w,w,2 \| w,w,2 \| w,w,2)` | `330` | the tower `T((0,2),2)` | open (notes/17) |
| `(w,w,w \| w,w,1 \| w,1,1)` | `321` | the staircase rod on a full `3×3` layer | open |
| `(w,w,w \| w,w,1 \| w,2,1)` | `321` | | open |
| `(w,w,w \| w,w,2 \| w,2,2)` | `321` | | open |
| `(w,w,w \| w,w,0 \| w,w,0)` | `331` | the rod `331×ω` (as `322`) | open |
| `(w,w,w \| w,w,2 \| w,w,0)` | `331` | | open |
| `(w,w,w \| w,w,w \| w,w,w)` | `333` | `3×3×ω` | open |

For `K = 1` the three open positions are the staircase rod on a full layer, the rod `331×ω`
and `3×3×ω`.

Every position of the shapes `300` (row of three), `210` (tripod), `310`, `311` (cross) and
`320` with attachments up to height 2 is N by an exact reply. The two exceptions of shape
`220` are the candidates A and B below.

## 5. Candidate A

`A = (w,w,1 | w,w,1 | 2,0,0)`. In layers: the bottom layer is the shape `331`, the next one
is `221`, and above that the `2×2` block goes on forever.

Finite positions of this kind are written `(a; b, c, d)` for the heights of `(0,0)`, `(0,1)`,
`(1,0)`, `(1,1)`, with the three short columns as in A. Let

* `F1(z) = (z+1; z+1, z, z)`,
* `F2(z) = (z+1; z, z+1, z)`,
* `F3(z) = (z+2; z+2, z+2, z)`.

**Proposition.** If `F1(z)` is P for every `z ≥ 2`, and `F2(z)` and `F3(z)` are P for every
`z ≥ 1`, then A is a P-position.

*Proof.* Every option of A has a P option:

| option of A | reply |
| --- | --- |
| cut the poison column at `h ≥ 3` | cut `(1,0)` at `h−1`: `F1(h−1)` |
| cut the poison column at 2, at 1 | cut `(1,0)` at 0; take `(1,1,0)` (finite, checked) |
| cut `(1,0)` at `z ≥ 2` | cut the poison column at `z+1`: `F1(z)` |
| cut `(1,0)` at 1, at 0 | take `(1,2,0)`; cut the poison column at 2 (exact, `rodf`) |
| cut `(0,1)` at `z ≥ 1` | cut the poison column at `z+1`: `F2(z)` |
| cut `(0,1)` at 0 | take `(2,0,0)`: the row `y = 0` is the domino rod |
| cut `(1,1)` at `z ≥ 1` | cut the poison column at `z+2`: `F3(z)` |
| cut `(1,1)` at 0 | cut the poison column at 1: the hook `311`, a symmetric L |
| take `(0,2,0)` | take `(1,0,0)`: the column `x = 0` is the domino rod |
| take `(1,2,0)` | cut `(0,1)` at 2: a two-wide stalk, certified P (`rodf`) |
| take `(2,0,1)` | exact (`rodf`): `(w,w,1 | w,w,1 | 1,0,0)` is N |
| take `(2,0,0)` | take `(0,1,0)`: the row `y = 0` is the domino rod |

The three families enter in the rows with `F1`, `F2`, `F3`; every other reply is checked. ∎

**Verified.** `base3_table 254 -c H,H,1,H,H,1,2,0,0` with the queries of the proposition:
`F1(z)` is P for all `2 ≤ z ≤ 253`, `F2(z)` for all `1 ≤ z ≤ 253`, `F3(z)` for all
`1 ≤ z ≤ 252`, and no finite cut of A is P up to height 254. The rod solver finds the same
replies for all cuts up to height 40.

So A is "P up to height 252", and the reason is uniform. It is the same shape of argument as
for `2×ω`, where the cut `(ω, t)` is answered by `[t+1, t]`.

**What a proof needs.** `F1`, `F2`, `F3` must be shown P for all `z`.
* Most options of `F1(z)`, `F2(z)`, `F3(z)` are answered in the same way. After a cut of
  some column at height `t`, cut the poison column at `t+1` or `t+2`, which gives `F1(t)`,
  `F2(t)` or `F3(t)` again, or the fourth family `(t+2; t+1, t+1, t)`. For `z = 30` this
  covers all but a handful of the roughly 130 options of `F1(z)`.
* The largest set of P-positions that is closed under "every option has a reply in the set"
  and consists only of translation families without gaps does not contain `F1`, `F2`, `F3`
  beyond small heights. The families are not self-contained.
* A specific obstruction: taking the foot `(2,0,0)` from `F2(z)` leaves
  `(z+1; z, z+1, z)` with the two columns of height 1 only. That is the three-row position
  `[z+1, z, 1]` thickened to two layers. It is N for every `z ≤ 253`, but its winning replies
  are cuts at heights `z−2, z−2, z−3, z−4, z−6, z−19, z−13, …` for
  `z = 10, 15, 20, 25, 30, 60, 80`, with no pattern. So a proof needs at least one statement
  of the side-class kind.
* The P-positions over the `2×2` base with these short columns are not all regular either.
  Of 340 diagonal families with at least 8 members up to height 120, 9 have no gaps
  (`F1`, `F2`, `F3`, `(z+2; z+1, z+1, z)` and five others).

## 6. Is A alone? The finite-reply scan

A position is P if it has no finite P cut and every option is N. For A every infinite cut is
answered by a *finite* reply. That property can be tested with the table alone.
`base3_table H -c caps -F` does it for all attachments within the caps: it lists those with no
P cut of the poison column and with a finite reply to every cut of every infinite column at
heights from 4 to `H/2`.

| shape | attachments up to | `H` | attachments | no finite P cut | all cuts answered |
| --- | --- | --- | --- | --- | --- |
| `300` row of three | 3 | 120 | 175 | 116 | 0 |
| `210` tripod | 3 | 120 | 330 | 48 | 0 |
| `310` | 3 | 90 | 125 | 18 | 0 |
| `220` | 4 | 100 | 371 | 274 | 4 |
| `320` | 4 | 64 | 140 | 30 | 0 |
| `311` cross | 4 | 64 | 105 | 13 | 0 |
| `330` | 4 | 44 | 35 | 28 | 0 |
| `321` | 4 | 44 | 55 | 20 | 0 |
| `331` | 3 | 40 | 10 | 6 | 0 |
| `332` | 4 | 34 | 5 | 1 | 0 |

The four positions of shape `220` are A, its transpose, and the two symmetric positions
`(w,w,1 | w,w,0 | 1,0,0)` and `(w,w,1 | w,w,1 | 1,1,0)`. The last two are N: for each the cut
of `(0,1)` at height 1 leaves a certified P stalk. So A is the only position in this table
whose infinite cuts all have finite replies. With attachments up to height 2 every cross
position (`311`) has a finite P cut.

The 48 tripod positions without a finite P cut up to height 120 are worth a note: notes/17
conjectured that every tripod position has one. They are N or undecided here, not candidates.

**Candidate B** `= (w,w,2 | w,w,2 | 2,2,0)`: two layers of the shape `332` under the `2×2`
block. The solver finds no winning reply within its caps. It is of a different kind:
* no finite P cut up to height 110;
* the cuts of `(1,1)` are all answered by finite replies, at irregular heights
  (1→2, 2→3, 3→4, 4→6, 5→8, 6→10, 7→11, 8→13, …);
* the cuts of `(1,0)` have finite replies for only about half of the heights. The others
  (0, 1, 6, 8, 9, 11, 12, 14, 16, 21, …) need a reply with infinite columns. The certified
  search has found one for every height up to 24.

So B is a candidate of the irregular kind, like the tower `T((0,2),2)` of notes/17, and is
not assumed anywhere.

## 7. Consequences if A is P

`rodf -A file` takes a list of positions assumed to be P. A verdict that rests on one is
printed as "N via assumed P" and is never reported as exact.

The positions with A as an option are N. Up to transposition they are:
* `(w,w,1 | w,w,1 | k,0,0)` with `k ≥ 3` or `k = w`;
* `(w,w,j | w,w,i | 2,0,0)` with `j ≥ 2`, `1 ≤ i ≤ j`, including `j = w` and `i = w`;
* `(w,w,1 | w,w,1 | 2,1,k)` and `(w,w,1 | w,w,1 | 2,2,k)` with `k ≤ 1`.

The second line with `i = j = w` is the tower `T_331((2,0),2)` of the rod `331×ω`, which is
`X_2` in the other orientation. So `X_1` is N exactly and `X_2` is N if A is P.

Re-running the open positions of §4 with A assumed changes this one verdict and no other
(`data/atlas3/k2_open_rerun_A_assumed.txt`). The solver's heuristic verdicts for the large
shapes are not reliable and are not used here: its search for finite cuts stops at a small
height, so for example it takes `T_331((1,2),1)` for a P-position, which has a finite P cut
at height 19.

## 8. Where this leaves `3×3×ω`

* The question is open. One more tower is N (`T((1,1),12)`); 22 with `g ≤ 12` are open.
* `331×ω` is the sharper target. Its towers are N for `g ≤ 8` in five of the six types. What
  is left is the chain `X_g = 3×2×ω ∪ (0,2)×g`, `g ≥ 3`, and the larger `g` of the other
  types.
* P-positions with more than two infinite columns very probably exist, and the first one is
  small. The picture of notes/17, in which such positions can only live in the irregular
  "multi-cell growing regime", is too narrow: A is regular.
* The irregular positions (B, `T((0,2),2)`, the open positions of §4) remain out of reach.
  For those the replies to infinite cuts are themselves infinite positions, at heights with
  no pattern.

**Next steps.**
1. A proof that A is P. The proposition reduces it to three families of finite positions.
   The missing ingredient is a statement like "`[z+1, z, 1]` thickened to two layers is N for
   every `z`".
2. The chain `X_g`: run the certified families of `X_3, X_4, …` with A assumed.
3. The same search one size up: positions whose infinite cuts have finite replies, for
   attachments of height 3 and 4 over the five- and six-column shapes. The table sizes
   allow it.

## Tools

* `tools/base3_table.cpp`: the dense table; `-s` P-heights, `-t` tower cuts, `-q` queries,
  `-F` finite-reply scan, `-P` dump.
* `scripts/base3_check.py`: brute-force check of the table.
* `scripts/atlas3.py`: the atlas; `ATLAS_SHAPE` restricts it to one shape.
* `scripts/base_towers.py`: the towers of a rod over any base.
* `tools/rodf.cpp -A file`: assumed P-positions.

```
g++ -O3 -march=native -std=c++17 -Wall -fopenmp -o base3_table tools/base3_table.cpp
./base3_table 72 -c H,H,H,H,H,0,H,H,0 -s -t        # the rod 331 (as 322), 4.4 GB, 14 min
printf 'h h 1 h h 1 2 0 0\nh+1 h+1 1 h h 1 2 0 0\nh+1 h 1 h+1 h 1 2 0 0\nh+2 h+2 1 h+2 h 1 2 0 0\n' > qA.txt
./base3_table 254 -c H,H,1,H,H,1,2,0,0 -q qA.txt   # candidate A
./base3_table 100 -c H,H,4,H,H,4,4,4,4 -F          # finite-reply scan, shape 220
python3 scripts/atlas3.py ./rodf 2 60 2 3 -a 2 -d 10 -Q 80
```
