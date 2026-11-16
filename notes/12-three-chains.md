# Three chains: toward Gale's `3×3×ω`

Every case decided exactly so far has at most **two** infinite columns. That is Byrnes's
two-chain theorem and our certified solver (notes/07). Every open question is the first case
with **three**:
* Gale's `3×3×ω`;
* the slab `ω×ω×3`, i.e. the first move `(0,0,3)`;
* L-prisms of height 3;
* Huddleston–Shurman's "`3×Ω` is recursive (not fully proved)".

This note records the work on that boundary.

## Step 1a: an exact oracle for 2D positions with three columns

`tools/hs_oracle.py` implements Huddleston–Shurman §9–§10 for column heights below `ω^ω`, using
their unrestricted Grundy values (P iff value 1):

* **Two columns:** the closed formulas (9-1)–(9-5). For example `G(ω·u, ω·u) = (3^u − 1)/2`,
  `G(ω·u+a, ω·v+b) = ω·(u−v) + (a ⊕ b)` for `u > v`, and `G(ω^i·u+a, ω^i·u+b) = ω^{i−1}·u +
  G(a,b)` for `i ≥ 2`.
* **Three columns `u ≥ v ≥ x`:**
  * `x` and `v` finite: brute force if `u` is finite, otherwise N (Beanstalk Lemma).
  * `x` finite and `v ≥ ω`: the **Side-Top Theorem**. The position is P iff `x` is in the side
    class `𝒮` and `G_𝒮(x) = G(top)`, where the top is the two-column position
    `(ω\u, ω\v)`.
  * `ω ≤ x < ω^ω`: the **decomposition (i)–(iv)** into bottom and top pieces, with criterion
    (10-1): `G(U_b) = G(X_b)` and `G(U_t) ⊕ G(V_t) ⊕ G(X_t) = 0`.
* **The side class** `𝒮` is the set of finite `x` with no finite `h` making `(h,h,x)` P. That is
  exactly "no cut of the poison column is P" for the two-wide stalk `(ω,ω,x)`, which our
  certified solver decides. `rodf -I 1 -p w,w,x 3` answers it.

### Validation (`scripts/hs_check.py`)

* Finite positions agree with the rod solver (0 mismatches for heights ≤ 8).
* **Local consistency.** A claimed P-position must have no option claimed P, and a claimed
  N-position should have one. Options are sampled over all ordinals below each height with small
  coefficients, plus truncations of the heights.
  * 400 random positions with heights below `ω³`: no inconsistency (314 N verified, 83 N with no
    P option in the sample, 3 P).
  * 41 generated P-positions: no inconsistency.
* **Every P-position the paper describes** in its proof that `3×ω^ω` is P is reproduced:
  * `(ω·2, ω, ω)`, `(ω·4+5, ω·2+3, ω·2+3)`, `(ω²·2+10, ω²+ω+2, ω²+ω+2)` (case `e = 1`);
  * `(ω², ω², ω)`, `(ω³+4, ω³+4, ω²+6)` (case `e = 0`, `z ≥ ω²`);
  * for `ω ≤ z < ω²`, a **unique** finite `x` with `(z,z,x)` P, as the paper states. For
    example `x = 5` for `z = ω+1`, and `x = 74` for `z = ω·3+2`.

### A by-product: the side class

`𝒮 = {0, 2, 5, 7, 9, 11, 14, 17, 19, 22, 24, 26, 28, 31, 34, 36, 38, 40, 42, 45, 48, 51, 53,
56, 58, 60, 62, 65, 67, 69, 72, 74, 77, 79, …}`. The gaps are 2 or 3 in an irregular pattern of
density about 0.43, and `G_𝒮(x)` is the index of `x` in `𝒮`. Every other `x` has a finite `h`
with `(h,h,x)` P. For `x = 1, 3, 4, 6, 8, 10, 12` that `h` is `2, 5, 7, 9, 12, 14, 17`.

## Step 1b: the towers of `3×3×ω`

**Reformulation.** `3×3×ω` is N iff some option is P. The options are the towers `T(b,g)`: the
columns in `↑b` cut to height `g` and the rest infinite. For each `b`, at most one `g` gives a
P tower (antichain lemma). Up to transposition, `b ∈ {(0,1), (0,2), (1,1), (1,2), (2,2)}`.

**The thinnest towers, `T((0,1), g)`** (a stalk of three infinite columns, the row `y = 0`, on a
`3×3×g` block) are **N exactly** for `g = 1, …, 4`:

| `g` | exact winning reply |
| --- | --- |
| 1 | cut everything at height 7 (a finite P-position) |
| 2 | cut everything at height 11 |
| 3 | cut cell `(2,0)` at 11, leaving a two-wide stalk proved P |
| 4 | cut cell `(2,0)` at 1, leaving a two-wide stalk proved P |

### Scan of all five tower types

`scripts/towers.py` runs the solver on every tower, at caps `-a 2 -d 10` and 150 s per tower.
"N" means an **exact** winning reply was found. "·" means no reply was found in the time limit,
which says nothing either way. The table combines the first scan (`g ≤ 12`) with a rescan after
the solver improvements below (`g ≤ 16`, two-wide options tried first), and the exact family
searches further down.

| `b` \ `g` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `(0,1)` | N | N | N | N | N | N | · | N | · | · | · | · |
| `(0,2)` | N | · | N | N | · | N | · | · | · | · | · | · |
| `(1,1)` | N | N | N | N | N | N | N | N | N | N | · | · |
| `(1,2)` | N | N | · | · | N | · | · | · | · | · | N | · |
| `(2,2)` | N | N | N | · | N | N | · | · | N | · | N | · |

**32 of the 60 towers with `g ≤ 12` are exactly N.** None with `13 ≤ g ≤ 16` was settled in
the scan's time limit.

Most replies are "cut everything at height `h`", leaving a finite P-position. For fixed `b`
these also form a partial permutation `g ↔ h`, because lowering the block is a move and so is
lowering everything:

| `b` | `g → h` |
| --- | --- |
| `(0,1)` | 1→7, 2→11, 6→15, 8→18 |
| `(0,2)` | 4→9, 6→10 |
| `(1,1)` | 1→3, 2→8, 3→5, 4→6, 5→10, 6→19, 7→17, 8→20, 9→25, 10→24 |
| `(1,2)` | 1→11, 2→15, 5→13, 11→12 |
| `(2,2)` | 1→2, 2→6, 3→4, 5→19, 6→12, 9→14, 11→16 |

The replies `9→25`, `10→24` for `(1,1)`, `2→15` for `(1,2)` and `5→19` for `(2,2)` came from
deciding every finite cut `h ≤ 32` exactly (`towerfam.py`, `TOWERFAM_CELLS=poison`). No finite
reply exists at small heights for these open towers:

| tower | no finite P-reply at heights |
| --- | --- |
| `T((0,1),g)`, `g = 7, 9, 10, 11` | `h ≤ 40` |
| `T((0,1),12)` | `h ≤ 37` |
| `T((0,2),2)` | `h ≤ 29` |
| `T((2,2),4)` | `h ≤ 25` |
| `T((1,2),3)` | `h ≤ 27` |

The last two runs stopped when the table of finite positions outgrew memory (about 7 GB).

The other replies leave a two-wide stalk: `T((0,1),g)` for `g = 3, 4, 5` and `T((0,2),g)` for
`g = 1, 3` (sections below).

### `T((0,1),5)` is N, by a deep two-wide stalk

`T((0,1),5)` timed out at every cap (`a1d10` to `a3d40`). Deciding its options family by family
(`rodf -K cell -Z zmax`, new) found the reply:

> **Cut cell `(2,0)` to height 10.** This leaves the poison column and `(1,0)` infinite, `(2,0)`
> at height 10 and every cell with `y ≥ 1` at height 5. That is a two-wide stalk, and the
> certified solver proves it **P exactly**.

So `T((0,1),5)` is N. The other options checked are all N: the cuts of `(2,0)` at heights 0–9 and
11–17 (all exact, height 13 after raising the simulation limit), the cuts of the poison cell at
heights up to 80 (finite, exact), and the moves inside the block at cells `(0,1)`, `(0,2)` and
`(1,1)` (mostly exact). The first scan's search ran out of time in harder options before it
reached this one. The rescan, which tries two-wide options first, finds it within 150 s.

### Speed-up: caching certified sequences

The certificate of notes/07 simulates `F_R(z)` for every `R` in a closed family. `F_R` depends on
`R` alone, not on the family it was computed in, so `tools/rod.h` now keeps every certified
sequence: its values up to the start of the periodic part, and the period of the offsets. Later
certificates read cached members instead of simulating them again.

* Each member's own minimal period and preperiod are stored, not the family's joint period. A
  first version stored the joint period, and combining them made the joint period too long to
  certify. Certificates then failed, and the solver fell back to heuristics and answered one
  position wrongly. If a certificate using cached members fails, the solver now reruns it
  without the cache, so the cache can never turn an exact answer into a heuristic one.
* A cached position that is itself the root of a later certificate is answered from its
  sequence, using `f` directly for heights below the cached range.
* With the cache alone, the P-position above takes 10 s instead of 10.5 min. Every version
  agrees with the old solver on random two-wide stalks in `3×3` with heights up to 6 (60 cases
  each), and on the `(2,0)`-cut families of `T((0,1),g)` for `g = 3, 4` and, up to height 15,
  `g = 5`.
* **Member by member (the main gain).** A sequence `F_R` depends only on the sequences of the
  options `R'` of `R`. So the certificate now works bottom-up: certify every option first
  (recursively, through the cache), then simulate `R` **alone**. Its state is its NONE flag,
  its pending offsets, and the phase `z mod L`, where `L` is the lcm of its options' periods.
  The joint simulation has to run until the whole family repeats, i.e. for the longest
  preperiod plus the lcm of all periods, with the whole family in every step. Member by member,
  each sequence runs only for its own preperiod and period. The joint certificate remains as a
  fallback (and as `rodf -M 0`).
  * On 40 random two-wide stalks with heights up to 9, the two methods give the same verdicts
    in 82 s instead of 1536 s.
  * The P-reply to `T((0,1),5)` now takes **1.3 s**, against 10.5 min originally. The
    period-4320 stalk below takes 1.1 s.
* **Memory.** The joint certificate now keeps a 128-bit hash of each state instead of the state
  itself. When a hash repeats, the simulation is replayed from the start and the two full
  states are compared, so a hash collision can only make a certificate fail, never make it
  wrong. The recorded history uses 16-bit offsets and is capped. Peak memory on the P-position
  above fell from 373 MB to 96 MB. Before this, families run four at a time were killed for
  lack of memory (16 GB).
* The simulation limit is now a flag (`-S`, default 30000 steps; it was a fixed 4000). Some
  stalks need more than 4000. For
  example `(ω,5,3 | ω,5,3 | 13,5,3)` (columns `x = 0, 1, 2`, cells `y = 0, 1, 2`) certifies
  only after 5777 states, with period 4320. It is exactly P, which makes the cut of `(2,0)` at
  13 in `T((0,1),5)` exactly N as well.
* `rodf -K` now stops at the first exact P in a family. Every taller cut of the same cell has
  that P-position as an option, so it is N.
* **Move order.** The search now tries the options that leave a two-wide stalk before the
  options that leave three or more infinite columns. The first are decided exactly and
  quickly. The second need the capped heuristic search, which can use up the time limit
  before the easy options are reached. This alone settles `T((0,2),1)` and `T((0,2),3)`
  (below) in under a second; the first scan had timed out on both.

**A warning about heuristic answers.** With the old 4000-step limit, the scan reported
`T((0,2),2)` as "N heuristic" through the reply "cut `(1,0)` at 8". The position after that
reply, `(ω,ω,2 | 8,8,2 | 8,8,2)`, only looked P. With 30000 steps its certificate closes and
shows it is **N exactly**: cutting the poison column at height **381** leaves a P-position. That
height is far beyond any heuristic cap. `T((0,2),2)` is still open.

### The two-wide family of the `(0,1)` towers

Write `P_g(z)` for `T((0,1),g)` with cell `(2,0)` cut to height `z`. The poison column and
`(1,0)` stay infinite, `(2,0)` is at `z`, and the cells with `y ≥ 1` are at `g` (or `min(g,z)` in
column `x = 2`). Every `P_g(z)` is a two-wide stalk, so its outcome is exact.

* For fixed `g`, at most one `z` makes `P_g(z)` P, since each cut is an option of every taller
  one. For fixed `z`, at most one `g` does, since lowering the block is a move. So the
  P-positions form a **partial permutation** `g ↔ z`, like the Wythoff-like table of
  notes/07.
* `T((0,1),g)` is N whenever row `g` has an entry.

| `g` | 3 | 4 | 5 |
| --- | --- | --- | --- |
| `z` with `P_g(z)` P | 11 | 1 | 10 |


### The two-wide family of the `(0,2)` towers

For `b = (0,2)` the cells `(0,0)` and `(0,1)` are infinite, and cutting cell `(1,0)` to height
`z` leaves a two-wide stalk: column `x = 0` is `(ω, ω, g)` and columns `x = 1, 2` are
`(z, z, min(g,z))`. The same partial-permutation argument applies.

| `g` | 1 | 3 |
| --- | --- | --- |
| `z` with the cut P | 4 | 1 |

* `T((0,2),1)` is **N**: the reply leaves `(ω,ω,1 | 4,4,1 | 4,4,1)`, exactly P. This was
  confirmed by the old cache-free solver too.
* `T((0,2),3)` is **N**: the reply leaves `(ω,ω,3 | 1,1,1 | 1,1,1)`, exactly P.

