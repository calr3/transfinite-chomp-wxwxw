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
| `(0,1)` | N | N | N | N | N | N | N† | N | N† | · | · | · |
| `(0,2)` | N | · | N | N | · | N | · | · | · | · | · | · |
| `(1,1)` | N | N | N | N | N | N | N | N | N | N | N | · |
| `(1,2)` | N | N | · | · | N | · | · | · | · | · | N | · |
| `(2,2)` | N | N | N | · | N | N | · | · | N | · | N | · |

**35 of the 60 towers with `g ≤ 12` are exactly N.** None with `13 ≤ g ≤ 16` was settled in
the scan's time limit.

† certified by the member-by-member certificate only; see "Verification status" below.

Most replies are "cut everything at height `h`", leaving a finite P-position. For fixed `b`
these also form a partial permutation `g ↔ h`, because lowering the block is a move and so is
lowering everything:

| `b` | `g → h` |
| --- | --- |
| `(0,1)` | 1→7, 2→11, 6→15, 8→18 |
| `(0,2)` | 4→9, 6→10 |
| `(1,1)` | 1→3, 2→8, 3→5, 4→6, 5→10, 6→19, 7→17, 8→20, 9→25, 10→24, 11→22 |
| `(1,2)` | 1→11, 2→15, 5→13, 11→12 |
| `(2,2)` | 1→2, 2→6, 3→4, 5→19, 6→12, 9→14, 11→16 |

The replies `9→25`, `10→24`, `11→22` for `(1,1)`, `2→15` for `(1,2)` and `5→19` for `(2,2)`
came from deciding every finite cut up to a height bound exactly (`towerfam.py`, `TOWERFAM_CELLS=poison`). No finite
reply exists at small heights for these open towers:

| tower | no finite P-reply at heights |
| --- | --- |
| `T((0,1),g)`, `g = 7, 9, 10, 11` | `h ≤ 40` |
| `T((0,1),12)` | `h ≤ 37` |
| `T((0,2),2)` | `h ≤ 29` |
| `T((1,1),12)` | `h ≤ 30` |
| `T((1,2),3)` | `h ≤ 27` |
| `T((1,2),4)` | `h ≤ 28` |
| `T((1,2),g)`, `g = 6, 7, 8, 9, 10, 12` | `h ≤ 22` |
| `T((2,2),4)`, `T((2,2),7)` | `h ≤ 25` |
| `T((2,2),g)`, `g = 8, 10, 12` | `h ≤ 22` |

Runs at larger heights stop when the table of finite positions outgrows memory or time. A
compact open-addressing table (about 14 bytes per entry instead of about 50) cut the peak memory
of one such run from 3.5 GB to 2.0 GB.

The other replies leave a two-wide stalk: `T((0,1),g)` for `g = 3, 4, 5, 7, 9` and `T((0,2),g)` for
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
* **Bit-mask simulation (`rodf -F`, default on).** In a single member's certificate, the
  offsets and the pending set are now 128-bit masks instead of sorted vectors. The options'
  sequences are read through running indices instead of a modulo. Visited states are keyed
  exactly by `(z mod L, pending set)` instead of a decimal string. If an offset reaches 128,
  the member is redone by the general simulation.
  * The `(2,0)`-cut family of `T((0,1),9)` up to its P-reply at 8 takes **20 s instead of
    163 s**.
  * The P-reply to `T((0,1),5)` takes 0.4 s instead of 1.6 s. The original solver took 10.5 min.
  * `rodf -F 2` runs both simulations on every member and aborts on any difference. It agrees
    on every member of the `(2,0)`-cut families of `T((0,1),5)` and `T((0,1),7)`, the latter up
    to its P-reply at 20 (9.5 min).
  * Profiling the stalls with `rodf -P` (progress reports) showed what made the hard heights
    slow: about 10⁵ members per height, each simulated for a few thousand steps, with option
    periods up to 30240.
  * Three further changes:
    * **Grouping.** Options already inside their periodic part are merged by period into one
      cyclic table of masks, so a step costs one lookup per distinct period instead of one
      per option.
    * **Brent's cycle detection.** It replaces the table of visited states: one saved state,
      moved forward at powers of two, finds the exact cycle length without storing states. The
      step limit for this search is `3 × MSIM`.
    * **Scan cache.** Each sequence caches its own first P height, so the search over a
      stalk's options no longer rescans long sequences.

    Together these take the `T((0,1),9)` P-reply `(ω,9,9 | ω,9,9 | 8,8,8)` from 30 s to 12 s.
    Check mode (`-F 2`) agrees on every member of the `(2,0)`-cut families of `T((0,1),5)` and
    `T((0,1),9)`, and of the `(1,0)`-cut families of `T((0,2),1)` and `T((0,2),3)`. Verdicts
    agree with the earlier solver on 46 random two-wide stalks.
  * **What actually stalled the open towers.** At heights like `T((0,1),10)` cut at 15, some
    member's option periods (up to 302400) have an lcm above the default single-member limit
    of 300000 steps. That member's certificate failed, and the solver fell back to the joint
    certificate of the whole family, which is hopeless at that size. The 2-hour runs above
    were stuck there. With `-L 6000000` the member certificates close.
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

| `g` | 3 | 4 | 5 | 7 | 9 |
| --- | --- | --- | --- | --- | --- |
| `z` with `P_g(z)` P | 11 | 1 | 10 | 20 | 8 |

Together with the finite replies (`g = 1, 2, 6, 8`), **every `T((0,1),g)` with `g ≤ 9` is N**.

The N-cuts can be deep too. `P_9(3) = (ω,9,9 | ω,9,9 | 3,3,3)` is N, but its first winning cut
of the poison column is at height **4107**. Every solver version since the first family run
agrees on this.
With the fixed solver (below: the stalls were a step limit, not the size of the problem):
* for `g = 10` every cut `P_10(z)` with `z ≤ 25` is N;
* for `g = 11` every one with `z ≤ 18` is N;
* for `g = 12` every one with `z ≤ 14` is N.

Runs are in progress. They are now limited by **memory**: the cached sequences of a family
reach about 10 GB by `z ≈ 15–17`, even with offsets packed in 4–6 bits.

**Verification status.** `P_5(10)` was confirmed by the original solver (no cache, joint
certificate), which took 10.5 min. `P_7(20)` and `P_9(8)` were found and certified member by
member, in about 8 min for both families. The joint certificate did not finish on `P_9(8)` in
50 min, and the original solver did not finish in about 1.5 h (that run was then lost to a
container restart). The member-by-member certificate has agreed with the joint one on every
comparison: about 100 random two-wide stalks and the `(2,0)`-cut families of `g = 3, 4, 5`.


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
* For the open `(0,2)` towers, every cut of `(1,0)` checked so far is N: up to height 16 for
  `g = 2`, 11 for `g = 5`, 13 for `g = 7` and 8 for `g = 8`. With the default step limit a
  single height could take over an hour; with `-L 6000000` the heights 11–13 of `g = 7` took
  a few minutes each.


### The closed class of the `(0,1)` towers

Write `W(R)` for the position where the row `y = 0` (cells `(0,0)`, `(1,0)`, `(2,0)`) is
infinite and the cells `(x,1)`, `(x,2)` carry a finite `3×2` plane partition `R`. The tower
`T((0,1),g)` is `W(□_g)`, where `□_g` has every entry `g`. Every option of `W(R)` is one of:

* a **finite** position: cut the poison column at `h`;
* **N outright**: cutting `(1,0)` leaves only the poison column infinite;
* a **two-wide stalk** `S(z,R)`: cut `(2,0)` at `z`. The poison column and `(1,0)` stay
  infinite, `(2,0)` is at `z`, and column `x = 2` of `R` is cut to `z`;
* `W(R')` with `R' < R`: a move inside `R`.

So the class `{W(R)}` is closed apart from options that are decided exactly. Let
`D(R)` say that some finite or two-wide option of `W(R)` is P, and let
`U = {R : not D(R)}`. Reading off the list of options:

> **`W(R)` is P iff `R ∈ U` and `W(R')` is N for every `R'` reached from `R` by one move.** So
> `T((0,1),g)` can be P only if `□_g ∈ U`. If `U` is empty, every `W(R)` is N, and so is
> every tower `T((0,1),g)`.

(A first version of this note claimed that the P-positions are the minimal elements of `U`.
That is wrong. A smaller plane partition `R' < R` is not always one move away from `R`, so a P
`W(R')` below `R` does not by itself make `W(R)` N.)

**Side sets.** Let `𝒮_R` be the set of `z` such that no cut of the poison column of `S(z,R)`
**above `z`** is P. A cut at `h ≤ z` is a finite option of `W(R)` itself, so it is not counted.
For `R = 0` the class is 2D: `W(0)` is three columns of height `ω`, and `𝒮_0` is exactly the side
class `𝒮` of Huddleston–Shurman (Step 1a; `rodf -I 2` reproduces `0, 2, 5, 7, 9, 11, 14, …`).

> **Lemma.** If `|𝒮_R| > #{Q : Q < R}`, in particular if `𝒮_R` is infinite, then `D(R)` holds.
> So `W(R)` is N, by an exact finite or two-wide reply.

*Proof.* Take `z ∈ 𝒮_R`. The options of `S(z,R)` are:
* poison cuts at `h ≤ z`: the finite options of `W(R)`;
* poison cuts at `h > z`: none is P, since `z ∈ 𝒮_R`;
* cuts of `(1,0)`: N;
* cuts of `(2,0)` at `z' < z`: `S(z',R)`, two-wide options of `W(R)`;
* moves inside `R`: `S(z,Q)` with `Q < R`.

If none of these is P, then `S(z,R)` is itself P and `D(R)` holds. If a poison cut at `h ≤ z`
or a cut of `(2,0)` is P, `D(R)` holds too. Otherwise `S(z,Q)` is P for some `Q < R`. For a fixed `Q`, at most
one `z` does this, because the positions `S(z,Q)` form a chain under cuts of `(2,0)`. So at most
`#{Q < R}` values of `z` escape. ∎

> **Corollary.** If every side set `𝒮_{□_g}` is infinite, then **every tower
> `T((0,1),g)` is N**. Then `3×3×ω` is decided by the other four tower types alone.

**How plausible is that?**
* If `W(R)` has a finite P cut at `h₀`, then `𝒮_R ⊇ [h₀, ∞)`. Indeed `(h; h, z; R)` with
  `h > z ≥ h₀` has that P-position as an option.
* So only `R` without a finite P cut matter. For these, the computed side sets have about the
  density of the 2D one:

  | `R` | finite P cut | `𝒮_R` (computed range) |
  | --- | --- | --- |
  | `0` (2D) | none | `0 2 5 7 9 11 14 17 19 22 24 26 28 31 …` (density ≈ 0.43) |
  | `□_1` | `h = 7` | `1 3 4 5 6 7 8 …` (every `z ≥ 3` up to 40) |
  | `□_2` | `h = 11` | `3 4 6 7 8 10 11 12 …` (every `z ≥ 10` up to 40) |
  | `□_3` | none `≤ 40` | 77 elements in `3 ≤ z ≤ 179` (density 0.435): `6 7 8 9 11 12 14 20 21 23 26 27 28 30 32 …` |
  | `□_4` | none found | 45 elements in `4 ≤ z ≤ 113` (density 0.41): `8 12 13 15 16 17 19 21 24 25 …` |
  | `□_5` | none found | 34 elements in `5 ≤ z ≤ 73` (density 0.49): `10 13 14 16 18 20 21 23 24 25 …` |

  (`rodf -I 2 -K 6 -Y g -Z zmax -p ω,g,g,ω,g,g,ω,g,g 333`, with `-L 6000000`: periods of the
  sequences involved reach 302400 by `z ≈ 150`.)

So the 3D side sets look like the 2D one: irregular, with density around 0.4–0.5 and no sign
of thinning out. A P tower of type `(0,1)` would need the opposite: by the lemma, `𝒮_{□_g}` would
have at most `#{Q < □_g}` elements.

**What is open in 2D.** Huddleston–Shurman's proof that `3×ω^ω` is P uses the case `R = 0`
without proving it. Their answer to the bite `(0, ω+c)` is a side `x` with
`G_𝒮(x) = G(c,c)`, and `G(c,c)` is unbounded, so `𝒮` must be infinite. Their criterion (10–1)
cannot supply this either:
* if `|𝒮| = m` were finite, `(ω+m, ω, ω)` would be P, since its only possibly-P options are
  side-top positions `(ω+m, ω, x)` and the smaller `(ω+t, ω, ω)`;
* (10–1) says `(ω+m, ω, ω)` is N;
* but proving that direction of (10–1) for this position needs a P side-top option, i.e. the
  infinitude of `𝒮`.

The provided literature (Huddleston–Shurman, Byrnes, Rivero Herrera, Nowakowski's problem list)
has no proof of it.

In finite terms, `x ∈ 𝒮` iff no 3-row Chomp position `[h,h,x]` (row lengths) is P. Brouwer's
Chomp page (<https://www.win.tue.nl/~aeb/games/chomp.html>) states the dichotomy for each third
row `r`: either some `(p,p,r)` is P and there are finitely many P-positions `(·,·,r)`, or there are
infinitely many, eventually in a linear pattern. So `𝒮` is the set of third rows with infinitely
many P-positions, and the question is whether there are infinitely many such rows. A direct
computation (`[a,b,c]` for `b ≤ 1600`, valid for `x ≤ 800`) gives:

| `X` | 100 | 200 | 400 | 600 | 800 |
| --- | --- | --- | --- | --- | --- |
| `#(𝒮 ∩ [0,X]) / (X+1)` | 0.416 | 0.418 | 0.416 | 0.414 | 0.414 |

For `x ∉ 𝒮` the partner `τ(x)` (with `[τ(x),τ(x),x]` P) satisfies `τ(x)/x ≈ 1.415` near
`x = 800`. So `𝒮` has density close to `√2 − 1 ≈ 0.4142`, and `τ(x) ≈ √2·x`. The numbers are
consistent: the complement has density `2 − √2`, and `τ` maps it injectively onto a set of
density `(2 − √2)/√2 = √2 − 1`. A search found one preprint with the same numerical
observation, stated as a conjecture. That is arXiv 2608.11290, which says the P-positions
`(w,w,t)` satisfy `w_n = (1+√2)n + O(1)`; it is not verified here.

"`𝒮_R` is infinite" is the natural 3D extension. It is a statement about **finite** Chomp:
infinitely many `z` such that no `(h; h, z; R)` with `h > z` is P.

**Computation (`scripts/w3row.py`).** For every `R` with entries `≤ 8` (9075 plane partitions),
an exact finite or two-wide P option was found (two-wide cuts searched up to `z = 30`, finite cuts
up to `h = 40`):

| `R` with entries `≤` | count | two-wide reply | finite reply | largest `z` | largest `h` |
| --- | --- | --- | --- | --- | --- |
| 1 | 10 | 6 | 4 | 3 | 2 |
| 2 | 50 | 36 | 14 | 12 | 3 |
| 3 | 175 | 126 | 49 | 15 | 8 |
| 4 | 490 | 347 | 143 | 15 | 11 |
| 5 | 1176 | 777 | 399 | 17 | 12 |
| 6 | 2520 | 1599 | 921 | 25 | 15 |
| 7 | 4950 | 3016 | 1934 | 25 | 17 |
| 8 | 9075 | 5278 | 3797 | 27 | 21 |

So `U` contains no `R ≤ □_8`, and **all 9075 positions `W(R)`, `R ≤ □_8`, are exactly N**, each
by a direct exact reply. This is the "`U` is empty" picture so far: no `R` has been found whose
`W(R)` lacks a finite or two-wide P option.
