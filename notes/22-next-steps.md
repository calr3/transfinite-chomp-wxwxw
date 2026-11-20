# What to try next

Status: 20 November 2026, after notes [20](20-corner-and-matching.md) and
[21](21-two-column-above-omega-omega.md). The open problems are stated in
[notes/00](00-overview.md); this note lists the directions that look worth trying, in order of
preference, each with what exists, a first step and the risk. The last section lists what has
been tried and should not be retried without a new idea.

Directions 1, 2 and 3 have been taken up since; their sections say what came of them.

## 1. `G(4×ω)`, Huddleston–Shurman's open value (started; see notes/23)

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

**Done on 20 November 2026** ([notes/23](23-four-columns.md)).
* A dedicated exact solver, `tools/four_row_values.cpp`: a recurrence for the values of
  four-row positions (a "row" `(x,y,g)` takes one value per level and may die), and a
  periodicity certificate for rows that never die.
* Proved: the values of `(ω,ω,x,y)` for `x ≤ 107`, hence `{1,…,45} ⊆ L` with witnesses; and
  no 46 for `a ≤ 158`.
* Computed: `G(ω,ω,1012,1012) = 46`, so `46 ∈ L`, and no smaller height gives 46. This
  assumes that no row alive at level 12000 dies later; the last death is at level 1752. [HS]
  had the bound 480 and did not know whether 46 occurs.
* The mechanism by which 46 reaches the diagonal: three near-misses at 507, 601 and 778, then
  1012.
* The approximate values of notes/09 for `41 ≤ a ≤ 80` were wrong (for example value 25 first
  occurs at `a = 47`, not 42).

**Still to do.**
1. A proof of the statement at 1012: the certificate for all rows up to that height. The
   common period grows (23040 up to 107, at least 276480 up to 200) and transients exceed
   37000 levels, so a plain simulation will not get there. It needs certificates per group of
   rows with their own periods, or a bound on death levels.
2. A bound on death levels (in the data, below `2x` for `x ≥ 32`), which would replace the
   certificate. For three rows and value 2 this is the open cube case.
3. The next missing values, 57 and 67 (none up to height 1100), and whether the same
   mechanism brings them in.

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

## 3. Consolidate and get outside review (literature search done)

* **Literature search: done on 20 November 2026** (notes/11, "Literature check").
  * The corner theorem is the case `m = 3` of a conjecture that Brouwer et al. (2005)
    attribute to Gale. No earlier proof was found.
  * No proof of the side class being infinite, and none of (9-6), was found.
  * Several sources could not be reached (Brouwer's web page, OEIS, MathOverflow, zbMATH,
    Google Scholar). A search there is still worth doing before anything is submitted.
* **The sentence of [HS] about `G((ω^ω)², (ω^ω)²)`** is as printed (p. 199).
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
