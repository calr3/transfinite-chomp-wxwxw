# What to try next

Status: 20 November 2026, after notes [20](20-corner-and-matching.md) and
[21](21-two-column-above-omega-omega.md). The open problems are stated in
[notes/00](00-overview.md); this note lists the directions that look worth trying, in order of
preference, each with what exists, a first step and the risk. The last section lists what has
been tried and should not be retried without a new idea.

Directions 2 and 3 have been taken up since; their sections say what came of them.

## 1. `G(4×ω)`, Huddleston–Shurman's open value

**The question** ([HS] §12). They do not know `G(4×ω)`, or whether it is computable. They show
`G(4×ω) = mex(L)`, where

`L = { G(ω,ω,a,a), G(a,a,a,a) : a < ω }`

(their `(4×a) + (2×ω)` and `4×a`; values unrestricted, so a P-position has value 1). The other
options of `4×ω`, `(ω,t,t,t)` and `(ω,ω,ω,t)`, have infinite values. They report that `L`
contains every `g < 46`, that 46 could only occur for `a > 480`, and that they believe
`G(4×ω) = ω·2` if `mex(L)` is infinite. They state without an algorithm that the set
`{(a,b,g) : G(ω,ω,b,a) = g}` is recursive. So the question is whether every natural number is
the value of some `(ω,ω,a,a)` or `4×a`.

Gale (1998) reports that Huddleston was convinced `4×ω²` is P. That is not in [HS] and has no
proof (notes/11).

**What it involves.** For finite `x ≥ y`, the value of `(ω,ω,x,y)` is the mex of

* the values of `(ω,ω,x,t)`, `t < y`, and `(ω,ω,t,min(t,y))`, `t < x`;
* the values of the finite four-row positions `(t,t,min(t,x),min(t,y))`, `t < ω`.

The options `(ω,t,…)` have infinite values and do not matter. For `t ≥ x` the positions
`(t,t,x,y)` form a chain, so their values are distinct, and whether a given `g` ever occurs
among them is a question of the same kind as the side class: `x ∈ 𝒮` says that the three-row
positions `[t,t,x]` never have restricted value 0. Here it is needed for four rows and for
every value.

**This is harder than what we have proved.** The cube case (direction 2) is three rows with
restricted value 1, and it is open. `G(4×ω)` needs four rows and all values. A proof is
unlikely by our present methods. The realistic gains are computational: exact values beyond
[HS]'s range, and a test of which lemmas survive.

**What exists.**
* `tools/rows.cpp` and notes/09: values of `(ω,ω,a,a)` and `4×a` for `a ≤ 40`, and approximate
  values for `41 ≤ a ≤ 80` (`T = 16`, no frontier rule). Restricted 15 had not appeared by
  `a = 80`.
* An exact route. A 2D position `X` has unrestricted value `g` iff `X` plus a one-wide stalk of
  height `g` over the poison cell, in a third direction, is a P-position. For `X = (ω,ω,x,y)`
  that is a finite part plus a two-wide infinite stalk, the class decided exactly by the
  certified solver of notes/07 (`tools/rodf.cpp`). The cost has not been measured.

**First steps.**
1. Compute `G(ω,ω,a,a)` exactly for `a ≤ 40` with the two-wide solver, compare with `rows`, and
   time it. This says how far the exact route reaches.
2. Work out how [HS] reached `a = 480`. A plain table of four-row positions `(p,q,x,y)` with
   `x, y ≤ 480` has of the order of `T²·480²` entries for first rows up to `T`, which is too
   many. They must have used more structure, probably their two-wide-stalk theory.
3. Tabulate, for small `(x,y)` and `g`, the `t` with `G(t,t,x,y) = g`, and test the analogues
   of Sheiner's lemmas (S1)–(S5) and of the remaining-lifetime lemma (notes/19) for four rows.

**Risk.** 46 may not appear in any range we can reach. The lemmas may fail as they do for the
cube.

## 2. The cube case, with two new facts (tried, no progress)

**The question.** `[p,q,r | cube]` is P iff the three-row position `[p,q,r]` has restricted
Grundy value 1. Its side set `𝒮₁` is infinite if two statements hold from some row on
(notes/19, §9): **(H4)** no partner `τ(r)` exceeds the diagonal value of a row `a ≥ r`;
**(L_K)** each row picks the partners of at most `K` older rows that die before it. Both are
theorems for value 0 and hold in all the data. The cube is the base case of the induction
over attachments for the `(0,1)` towers (notes/14).

**What is new since the last attempt.**
* No `[k,k,k | cube]` is P. This was an assumption and is now a theorem (notes/20,
  Corollary 3).
* The matching lemma (notes/20, Lemma 6): at the death time `p` of a row `x`, every older row
  still alive has exactly one level `j` with `[p,j,b]` P, and different rows have different
  levels. Its proof uses only the rules of the game, not Sheiner's row-start lemma, which is
  what fails for the cube.

**Tried on 20 November 2026: no progress** (notes/20, §5).
* The matching lemma holds in the cube family, with at most one exceptional row per death
  time, the row `b` with `τ₀(b) = p`. The proof is two lines, and
  `scripts/cube_matching_check.py` confirms it.
* It is the death criterion of notes/19 read at one cell. That criterion was already known to
  carry over, and the model with random blocked values satisfies it, so it cannot be the
  missing ingredient.
* It concerns the rows older than the dying one. (L_K) is about younger rows, and reduces again
  to a bound on dead levels. (H4) is a bound on lifetimes. The matching bounds neither.

What is left is what notes/19, §8 already said: a proof needs control of the eventual patterns
of the rows of both families, which is not available even in 2D.

## 3. Consolidate and get outside review

* **Literature search** for the two statements that may be new: the corner theorem
  (`[k,k,k−1]` is N for `k ≥ 3`, so `G(3×n) ≥ 2`; notes/20) and the self-similarity theorem
  for two columns at scales (notes/21). Places to look: Zeilberger's and Brouwer's work on
  three-row Chomp, Sheiner (2026), Padhi (2026), and anything citing [HS].
* **Check one sentence of [HS] against the PDF.** notes/21 records that "catching up at
  `G((ω^ω)², (ω^ω)²) = (ω^ω)²`" disagrees with (9-6), which gives `(ω^ω)²·2`. That reading is
  from extracted text.
* **The preprint** (`paper/side-class.tex`, 11 pages) has placeholders for author and
  repository. It could be split into a three-row paper (side class, corner theorem; checked in
  Lean) and an ordinal paper ((9-1)–(9-6), (10-1), `3×ω^ω`, recursiveness).
* **Readers**: Sheiner, Shurman, Padhi. Sending anything is the repository owner's decision.

This is cheap and can run alongside direction 1 or 2.

## 4. Formalise the ordinal results in Lean

`lean/` uses core Lean only and has no ordinals. The ordinal results would need a second Lake
project that depends on Mathlib. A sensible order: Theorem 1 of notes/21 (short and
self-contained, given the nim-sum on ordinals), then the two-column values of notes/18, then
the three-wide criterion of notes/16 and `3×ω^ω`. It is a large effort and is worth it only if
a machine-checked proof that `3×ω^ω` is P is a goal in itself.

## 5. The open towers of `3×3×ω`

These need compute, not ideas (notes/17, notes/00 §5).
* `T((1,1),12)`: no finite P cut up to height 31. The run (`rodf -K 0`) then exceeded 6.5 GB;
  the table of finite positions is the bottleneck. The `(1,1)` towers with `g ≤ 11` all have
  finite P cuts at heights up to 25, so a deeper search is likely to settle it. It needs the
  table moved to disk, or a larger machine.
* `T((0,2),2)`: every cut of `(1,0)` up to `z = 24` is exactly N. The heuristic search
  (`rodf -W 1 -Q 200`) reached no verdict in 30 minutes.
* `T((0,1),12)`: two-wide replies ruled out up to `z = 14`; limited by disk.

One more N tower adds no understanding. A P tower would show `3×3×ω` is N.

## 6. Longer shots

From notes/00, §8, unchanged:
* an exact method for positions with three infinite columns, for example a nested certificate
  for two-parameter families of sequences. Highest value, and nothing tried so far suggests a
  way in;
* a provable P tower. There is no candidate position.

## Tried; do not retry without a new idea

| What | Where it stopped | Note |
| --- | --- | --- |
| `τ` is increasing | An inversion `x < y`, `τ(y) < τ(x)` needs `τ(y) ≥ x + 4`; no contradiction found. | 20, §3 |
| `I(T) ≤ s(T−1)` (would give upper density `≥ (3−√5)/2`) | Only `I(T) ≤ 2·s(T−1)` is proved. | 20, §4 |
| Lower bounds on lifetimes by the corner induction | Stops at `τ(x) ≥ x + 3`; offset 3 never becomes constant. | 20, §1 |
| An exact rule for `𝒮` | Not a Beatty (Sturmian) sequence, and no local rule. | 12 |
| The matching lemma for the cube case | It carries over, but it is the death criterion in another form, and the random model satisfies it. | 20, §5 |
| A direct bound on the defects for the cube | A model with random blocked values satisfies every lemma we have and violates the bound. | 19, §8 |
| Exhaustive search with relative caps on positions containing a slab or plane | Cannot decide them. | 02, 06 |
