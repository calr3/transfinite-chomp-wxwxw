# Ordinal heights over the `3×3` base: the brick with attachments

Huddleston and Shurman ([HS] §11) classify the P-positions of `2×2×Ω`. Their tool is the
Front-Top Theorem for the brick `1×2×ω` with finite material in front of it, and they remark
that "a more complicated Base-Top Theorem holds, where finite base material may be added in all
directions around the brick", without stating it. This note states and proves that theorem for
positions over the `3×3` base, computes it for every small attachment with the certified
solver, and says why the same cannot yet be done for the `2×2` block of notes/25.

**Results.**

1. **Base-Top Theorem** (§1, proved). Let two adjacent columns have height at least `ω`, with a
   finite attachment `F` on the other columns and a two-wide position `T` on top. The position
   is P iff `brick + F` has no finite P cut and `G_F(F) = G(T)`, where `G_F` is the restricted
   value of §1.
2. **P-ordinals** (§2). If `brick + F` has no finite P cut, the height at which the brick with
   attachment `F` is a P-position is `ω·(j+1) + a`, where
   `G_F(F) = 3^j·⌊(3a+1)/2⌋ + (3^j − 1)/2`. So it is `ω` for value 0, `ω·2` for value 1, `ω+1`
   for value 2, `ω+2` for value 3, `ω·3` for value 4.
3. **Table** (§3, computer-assisted, exact). For all 4704 attachments with heights at most 5:
   3282 have a finite P cut (the highest at 1472) and 1422 have none. Of those, 361 have
   value 0 (P at height `ω`) and 1061 have a value from 1 to 8. So 1061 attachments give
   P-positions with two columns of a height above `ω`, between `ω+1` and `ω·3`.
4. **The `2×2` block** (§4). The same analysis for four tall columns needs two things we do not
   have: a proof that `block + R` has no finite P cut, which exists only for the empty
   attachment and for A, and the positions with three tall columns.

Conventions as in notes/23 and [HS]: Grundy values are unrestricted (the empty position has
value 0, a P-position of ordinary Chomp has value 1). Heights over the `3×3` base are listed
in the order `(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`.

## 1. The Base-Top Theorem

The **brick** is the pair of columns `(0,0)`, `(0,1)`. A position `U(F,T)` consists of

* the brick up to height `ω`;
* a **top** `T`: the cells of the brick at heights `ω` and above. Read from height `ω` it is a
  two-row position `[t₁,t₂]` with ordinal lengths `t₁ ≥ t₂`, so the brick columns have heights
  `ω + t₁` and `ω + t₂`;
* an **attachment** `F`: finite heights on the other seven columns, non-increasing in both
  coordinates.

No attachment column lies below a brick column, so a bite into `F` does not touch the brick,
and a bite into `T` does not touch `F`.

`H(F)` is the height `h` at which the finite cut `(h,h,…)` of `U(F,∅)` is a P-position, or `∞`
if there is none. There is at most one, since these cuts are options of one another. The
**restricted value** of an attachment with `H(F) = ∞` is

`G_F(F) = mex { G_F(F′) : F′ an option of F with H(F′) = ∞ }`.

`G(T)` is the unrestricted value of the two-row position `T`; the empty top has value 0. These
are Huddleston–Shurman's two-wide values (9-1)–(9-6), proved in notes/18 and notes/21.

> **Lemma 1.** A position with exactly one column of height at least `ω` and finitely many
> other cells is an N-position.

*Proof.* The column is `(0,0)`. For a finite rest, some finite cut of this column is a
P-position: this is the Fundamental Theorem with the Size Lemma of [HS] (Corollary 5.2), and
for the `3×3` base it is `P_bounded` in `lean/Chomp/Block.lean`. That cut is an option. ∎

> **Theorem 2 (Base-Top).** If `H(F)` is finite, `U(F,T)` is an N-position for every `T`. If
> `H(F) = ∞`, then `U(F,T)` is a P-position iff `G_F(F) = G(T)`.

*Proof.* The options of `U(F,T)` are of four kinds.

* (a) A bite into the top: `U(F,T′)` with `T′` an option of the two-row position `T`. Taking
  the cell `(0,0,ω)` gives the empty top.
* (b) A bite into the attachment: `U(F′,T)`.
* (c) A bite at `(0,0,h)` with `h` finite. It leaves the finite cut of `U(F,∅)` at height `h`,
  which is P iff `h = H(F)`.
* (d) A bite at `(0,1,h)` with `h` finite. It leaves one tall column and finitely many other
  cells, an N-position by Lemma 1.

If `H(F)` is finite, (c) gives a P option. Let `H(F) = ∞`, and argue by induction on `F` and
`T`. The options (c) and (d) are N. An option `U(F′,T)` with `H(F′)` finite is N by the first
part. So `U(F,T)` is P iff `G_F(F) ≠ G(T′)` for every option `T′` and `G_F(F′) ≠ G(T)` for
every option `F′` with `H(F′) = ∞`. If `G_F(F) = G(T)` both hold. If `G_F(F) < G(T)`, some
`T′` has `G(T′) = G_F(F)`. If `G_F(F) > G(T)`, some `F′` with `H(F′) = ∞` has
`G_F(F′) = G(T)`. ∎

The proof uses nothing about the base except that no attachment column lies below a brick
column, so it holds over any finite base. For an attachment on one side it is the Side-Top
Theorem ([HS] Theorem 8.1; `F` a single column `(0,2)` of height `x`, `G_F` the index of `x` in
the side class), and for an attachment in front it is their Front-Top Theorem 11.1.

**What is decidable here.** `H(F)` is decided exactly by the certified stalk solver
(`rodf -I 1`, notes/07): either a finite P cut is found, or a periodicity certificate shows
that there is none. So `G_F` is computable, and with the two-wide values the theorem decides
every position over the `3×3` base in which only the two brick columns reach height `ω`.

## 2. The height at which the brick with an attachment is P

By the Fundamental Theorem there is exactly one height `α` for which the two brick columns of
height `α`, with attachment `F`, form a P-position. If `H(F)` is finite, it is `H(F)`.
Otherwise it is `ω + α′` with `G(2×α′) = G_F(F)`. For `α′ = ω·j + a` with `a` finite,

`G(2×α′) = 3^j·⌊(3a+1)/2⌋ + (3^j − 1)/2`

(notes/15), and this takes every natural value exactly once. `G_F(F)` is finite, since `F` has
finitely many options. So:

> **Corollary 3.** If `brick + F` has no finite P cut, it is a P-position exactly at the height
> `ω·(j+1) + a`, where `j`, `a` are determined by `G_F(F) = 3^j·⌊(3a+1)/2⌋ + (3^j − 1)/2`.

| `G_F(F)` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 13 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| height | `ω` | `ω·2` | `ω+1` | `ω+2` | `ω·3` | `ω+3` | `ω+4` | `ω·2+1` | `ω+5` | `ω+6` | `ω·2+2` | `ω·4` |

All these heights are below `ω²`. More generally `U(F,T)` is P for every two-wide `T` with
`G(T) = G_F(F)`: for value `g`, the top can be a single column of `g` cells on `(0,0)`.

## 3. The table

`scripts/brick_values.py M` runs through all attachments with heights at most `M`, decides
`H(F)` with `rodf -I 1` and computes `G_F` by the recursion. The tables are in `data/brick/`.

| heights at most | attachments | finite P cut (highest) | no finite P cut | values 0, 1, 2, … |
| --- | --- | --- | --- | --- |
| 3 | 490 | 316 (74) | 174 | 59, 43, 42, 25, 5 |
| 4 | 1666 | 1105 (145) | 561 | 162, 112, 124, 84, 46, 21, 10, 2 |
| 5 | 4704 | 3282 (1472) | 1422 | 361, 253, 234, 229, 168, 102, 55, 16, 4 |

Every attachment is decided; the run for heights at most 5 takes half a minute. By Corollary 3
the heights at which the 1422 positions without a finite P cut are P are: `ω` (361), `ω·2`
(253), `ω+1` (234), `ω+2` (229), `ω·3` (168), `ω+3` (102), `ω+4` (55), `ω·2+1` (16) and `ω+5`
(4).

Checks.
* For every attachment with `H(F) = ∞` and heights at most 3, `rodf -p` decides the position
  at height `ω` directly: it is P exactly when `G_F(F) = 0` (174 positions, no mismatch).
* Fronts `1×2×z` (the columns `(1,0)`, `(1,1)` of height `z`): `G_F = z` for `z ≤ 5`, as [HS]
  state for their Front-Top Theorem.
* Sides (the column `(0,2)` of height `x`): `H = ∞` for `x = 0, 2, 5`, with values 0, 1, 2, the
  indices in the side class `{0, 2, 5, …}`; `x = 1, 3, 4` have the finite P cuts `[2,2,1]`,
  `[5,5,3]` and `[7,7,4]`.
* The P-positions with two infinite columns used in the proof that A is P (notes/25, checked in
  Lean in notes/29), for example `Σ1 = (ω,ω,1 | 1,1,0 | 1,0,0)`, have value 0.

Examples of P-positions with brick height above `ω`, from the table for heights at most 3
(attachment in the order
`(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`):

| attachment | `G_F` | P at brick height |
| --- | --- | --- |
| `1 \| 1,1,0 \| 1,1,0` | 1 | `ω·2` |
| `2 \| 1,1,0 \| 1,0,0` | 2 | `ω+1` |
| `1 \| 1,1,1 \| 1,1,1` (one layer of the `3×3` base) | 2 | `ω+1` |
| `3 \| 3,0,0 \| 0,0,0` | 2 | `ω+1` |
| `0 \| 3,3,0 \| 0,0,0` | 3 | `ω+2` |

## 4. Why not the `2×2` block

The positions of notes/25 and notes/26 have the four columns of the `2×2` block infinite, with
an attachment `R` on the other five columns. With a top `T ⊆ 2×2×Ω` on the block one gets the
positions `V(R,T)`; for `R = ∅` these are the positions of [HS] §11. The options of `V(R,T)`:

* bites into `T` and into `R`;
* the finite cuts of `(0,0)`: finite positions, the finite cuts of `block + R`;
* the finite cuts of `(0,1)` or `(1,0)`: a brick with an attachment and a top, decided by
  Theorem 2;
* the finite cuts of `(1,1)`: three tall columns with an attachment and a top.

So `V(R,T)` can only be P if `block + R` has no finite P cut. That is a statement about
infinitely many finite positions, and there is no certificate for it as there is for the
brick: the cuts form a family with three growing columns. It is known in two cases. For
`R = ∅` the cuts are boxes, N by strategy stealing, and [HS] §11 is the result. For A it is
part of the proof that A is P, and then `V(R_A, T)` is N for every nonempty `T`, since taking
the cell `(0,0,ω)` leaves A. Of the 812 attachments with heights at most 5 (notes/28), 362
have a finite P cut, so `V(R,T)` is N for every `T`. The other 444, apart from A and its
transpose, are N at height `ω` by a certified reply, and for them the height at which
`block + R` is P is above `ω` if and only if no finite cut is P. That is the statement we
cannot prove for an irregular family (notes/28, notes/30).

The positions with three tall columns are the second obstacle: with a top they are not covered
by any theorem here or in [HS].

What would extend this note without new theory: the Base-Top table for larger attachments and
other bases (the solver is fast for these). The machine check of [HS]'s types C to F for
`R = ∅` is in [notes/32](32-hs-section-11-audit.md).

## Tools

* `scripts/brick_values.py M RODF OUT [JOBS]`: the table for attachments with heights at most
  `M`; needs the `rodf` binary (`g++ -O2 -pthread -o rodf tools/rodf.cpp`).
* `data/brick/`: the tables.
