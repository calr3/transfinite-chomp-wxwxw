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
| `(0,1)` | N | N | N | N | N | N | N† | N | N† | N‡ | N‡ | · |
| `(0,2)` | N | · | N | N | · | N | · | · | · | · | · | · |
| `(1,1)` | N | N | N | N | N | N | N | N | N | N | N | · |
| `(1,2)` | N | N | · | · | N | · | · | · | · | · | N | · |
| `(2,2)` | N | N | N | · | N | N | · | · | N | · | N | · |

**37 of the 60 towers with `g ≤ 12` are exactly N.** None with `13 ≤ g ≤ 16` was settled in
the scan's time limit.

† certified by the member-by-member certificate only; see "Verification status" below.

‡ found with the rank-coded, disk-backed solver (`rodf -D`, below).
* `P_10(29)` was reproduced by a second run with different settings:
  * every rank-coded sequence is round-trip checked through both decoders (the bulk decoder
    and the cursor used by the member's own scan) when it is stored;
  * the decoded-sequence pool is 64 MB instead of 1 GB.

  Same result, same arena (10.75 GB), and no check failed. A re-run with the old packed
  storage did not fit in this session's disk: it reached 12 GB of an estimated 17 GB.
* `P_11(26)` has not been re-run. It needs about 24 GB of disk, more than this session had
  left.

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

| `g` | 3 | 4 | 5 | 7 | 9 | 10 | 11 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `z` with `P_g(z)` P | 11 | 1 | 10 | 20 | 8 | 29 | 26 |

Together with the finite replies (`g = 1, 2, 6, 8`), **every `T((0,1),g)` with `g ≤ 9` is N**.

The N-cuts can be deep too. `P_9(3) = (ω,9,9 | ω,9,9 | 3,3,3)` is N, but its first winning cut
of the poison column is at height **4107**. Every solver version since the first family run
agrees on this.
With the fixed solver (below: the stalls were a step limit, not the size of the problem):
* for `g = 10` every cut `P_10(z)` with `z ≤ 25` is N (extended below: `P_10(z)` is N for
  `z ≤ 28` and **P for `z = 29`**, so `T((0,1),10)` is N);
* for `g = 11` every one with `z ≤ 18` is N;
* for `g = 12` every one with `z ≤ 14` is N.

Runs are in progress. They are now limited by **memory**: the cached sequences of a family
reach about 10 GB by `z ≈ 15–17`, even with offsets packed in 4–6 bits.

**Memory work (`rodf -D`, rank-coded sequences).** A breakdown of the solver's memory on
`T((0,1),10)` (`-P` now prints it) shows that the certified offset sequences of the members are
about 92% of it. There are about 5500 offsets per member on average and up to 180000, with
periods (lcms) up to 302400. The `f`-memo and the ω-position memo are negligible. Two changes:

* **Rank coding.** Each member's sequence is a mex-sequence. Its offset at `z` is never in the
  member's own pending set `X(z)` (the offsets still blocked by its earlier values), and `X(z)`
  is determined by the earlier offsets. So each offset is stored as its rank among the values
  not in `X(z)`, in a Golomb–Rice code.
  * The order-0 entropy of the offsets is 4.1 bits; that of the ranks is 2.5 bits (36% are 0,
    20% are 1).
  * Storage: about 2.7 bits per offset instead of 4–5. NONE is stored as a suffix index.
  * Access: checkpoints every 2048 entries and at the start of the periodic part. An LRU pool
    (1 GB) of decoded sequences means each one is decoded once rather than once per reading
    certificate.
  * On the `g = 7` family: 37% less memory, 1.18× the running time.
* **A disk-backed arena.** With `-D path` the sequences live in a sparse memory-mapped file,
  deleted on exit. A certificate only touches its own options' sequences, so the kernel can keep
  the hot ones in RAM and write the rest to disk. The limit becomes disk space, not RAM.

Both are checked against the previous solver:
* 110 random two-wide stalks with the internal fast/general cross-check (`-F 2`), in heap and
  file modes: no mismatch;
* the five known tower results `P_3(11)`, `P_4(1)`, `P_5(10)`, `P_7(20)`, `P_9(8)`: all
  reproduced.

On `T((0,1),10)` the old packed storage grows by about 0.9 GB per height from `z = 15` on (4.5
GB at `z = 18`).

**Results.** With rank coding and `-D`, the family of `T((0,1),10)` was run from `z = 0`:
* `P_10(z)` is N for every `z ≤ 28`. The replies at the new heights are cell `(1,1)` at 8
  (`z = 26`) and poison-column cuts at 39 and 44 (`z = 27, 28`).
* **`P_10(29) = (ω,10,10 | ω,10,10 | 29,10,10)` is P, exactly.**
* So **`T((0,1),10)` is N**, by the two-wide reply cutting `(2,0)` to height 29. This is exactly
  the height the heuristic stalk programme of notes/14 predicted.
* The run took about 75 minutes with a 10.8 GB arena on disk; peak RAM stayed well below
  that.
* `T((0,1),11)` in the same way: `P_11(z)` is N for every `z ≤ 25`, and **`P_11(26)` is P**
  (arena 23.9 GB, about 2.5 hours). So **`T((0,1),11)` is N**. Here the heuristic programme's
  guess (23) was wrong.

**Verification status.** `P_5(10)` was confirmed by the original solver (no cache, joint
certificate), which took 10.5 min. `P_7(20)` and `P_9(8)` were found and certified member by
member, in about 8 min for both families. The joint certificate did not finish on `P_9(8)` in
50 min, and the original solver did not finish in about 1.5 h (that run was then lost to a
container restart). The member-by-member certificate has agreed with the joint one on every
comparison: about 100 random two-wide stalks and the `(2,0)`-cut families of `g = 3, 4, 5`.

**Why the exact tables cannot shortcut these runs.** One might hope to seed the rod solver with
the exact P-positions of `tools/attach3row.cpp`. A partner `[h,h,z | □_g]` found in its table
proves `P_g(z)` N at no cost, so only the side elements `z` would need the rod solver. This does
not reduce the disk needed for `T((0,1),12)` or for an independent re-run of `P_11(26)`. The
arena is filled by the certificate of the P reply itself, not by the N cuts below it:
* to show that `P_g(z*)` has no P cut of the poison column at any height, the solver certifies
  the periodicity of the sequence of the rest `(z*, □_g)`;
* that certificate simulates the rest's sequence from its options' sequences, so every rest
  below `(z*, □_g)` must be certified in full, through its preperiod and its period;
* those are the members the family run stores anyway. The N cuts below `z*` only add the
  short simulations up to their partners.

The tables stop at a few hundred rows, while the periods reach `3·10^5`, so they cannot replace
the certificates either. The P reply needs about as much disk with or without seeding.


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
* For the open `(0,2)` towers, every cut of `(1,0)` checked so far is N:

  | `g` | 2 | 5 | 7 | 8 |
  | --- | --- | --- | --- | --- |
  | checked up to `z =` | 24 | 11 | 15 | 8 |

  With the old default step limit a single height could take over an hour. With `-L 6000000`
  the heights 11–15 of `g = 7` and 17–24 of `g = 2` took a few minutes each, until memory ran
  out.


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
many P-positions, and the question is whether there are infinitely many such rows.

#### The side class up to `x = 50000` (`tools/side3row.cpp`)

`side3row` computes, for all `b ≤ N`, the unique `a = A(b,c)` with `[a,b,c]` P (or none). It
processes one third row `c` at a time and finds each `A(b,c)` as the first zero of three
word-aligned bitsets ORed together:
* the values already used in row `b`;
* the values used in column `c` so far;
* the diagonal values `A(j,j)`.

A stage stops at `b = τ(c)`, since every larger `b` gives no P-position. The cost is about
`N³/900` word reads.
* It reproduces the earlier `O(N³)` program exactly for `N = 1600` and `8000`, 65× faster at
  `8000`.
* `N = 100000` takes 35 minutes and 1 GB.
* The side class is reported for `x ≤ N/2`. That is safe because `τ(x)/x ≤ 1.4423` for every
  `x ≥ 50`.

The data (`data/side-class/side2d_x_le_50000.txt.gz`), up to `x = 50000`:

| `X` | 1000 | 10000 | 20000 | 30000 | 40000 | 50000 |
| --- | --- | --- | --- | --- | --- | --- |
| `#(𝒮 ∩ [0,X])` | 415 | 4143 | 8285 | 12427 | 16569 | 20712 |
| minus `(√2 − 1)(X+1)` | 0.37 | 0.45 | 0.32 | 0.18 | 0.04 | 0.91 |

Every bound measured holds over the whole range `x ≤ 50000`:

* **Bounded discrepancy.** `#(𝒮 ∩ [0,x]) − (√2 − 1)(x+1)` stays in `[−0.50, 1.46]` (it was
  `[−0.46, 1.32]` up to 10000). Gaps between consecutive side elements are 1 to 5.
* **The partner law.** For `x ∉ 𝒮`, the partner `τ(x)` (with `[τ(x),τ(x),x]` P) satisfies

  > `τ(x) = x + #(𝒮 ∩ [0,x]) + ε(x)` with `ε(x) ∈ {−2, −1, 0, 1, 2}`

  (counts 41, 7897, 14553, 6690, 108). Equivalently, `τ(x) − √2·x ∈ [−1.12, 2.50]`.
* **Images match side elements.** The number of values `τ(x) ≤ v` trails `#(𝒮 ∩ [0,v])` by
  0, 1 or 2 for every `v`. Pairing the `k`-th image with the `k`-th side element, the image is
  larger by 1 to 5.

**What would prove infinitude.** Think of the P-positions `[h,h,x]` as a 0/1 matrix with at
most one 1 in each row `h` and in each column `x`. Then `𝒮` is the set of empty columns, and the
images of `τ` are the nonempty rows.

> **(B′)** For every `v`, the number of P-positions `[h,h,x]` with `x < h ≤ v` is at most
> `#(𝒮 ∩ [0,v])`. Equivalently, the `k`-th image of `τ` is never smaller than the `k`-th side
> element.

**(B′) alone implies that `𝒮` is infinite.** If `|𝒮| = m`, (B′) allows at most `m` P-positions
`[h,h,x]` in all. But every `x ∉ 𝒮` has its own one (`τ` is injective, since `[h,h,x']` is an
option of `[h,h,x]` for `x' < x`), and there would be infinitely many such `x`. The data satisfy
(B′) at every `v ≤ 50000`, with a lead of 0 to 2. A proof of (B′), even with a fixed constant
added on the right, would close the gap in Huddleston–Shurman. Any injection from the images
of `τ` into `𝒮` would do as well.

**Why `√2`.** Counting the matrix entries in the triangle `x < h ≤ v` gives
`#images ≤ v = (v+1) − #(𝒮 ≤ v) − #{x ≤ v : τ(x) > v}`. Suppose `𝒮` has density `σ`, the
partner law holds (`τ(x) ≈ (1+σ)x`), and images and side elements have equal counts up to
`O(1)` (the two-sided form of (B′)). Then `σ = (1−σ)/(1+σ)`, i.e. `σ² + 2σ − 1 = 0` and
`σ = √2 − 1`. The partner law alone does not force this: with finite `𝒮` it would just make
`τ(x) − x` bounded.

Two negative findings:
* `𝒮` is not a Beatty (Sturmian) sequence. The deviation `s_n − (1+√2)n` of the `n`-th side
  element is not a function of the phase `n√2 mod 1`: points in the same phase bin still spread
  by about 1.9, against a total spread of 2.9.
* `ε(x)` has no local rule either. The membership pattern of `x − 6, …, x + 6` in `𝒮` predicts
  it only 64% of the time.

So `𝒮` looks like a bounded, irregular perturbation of the Beatty sequence `⌊n(1+√2)⌋`. That
matches the "quasi-periodic with bounded discrepancy" conjecture of arXiv 2608.11290, which
states `w_n = (1+√2)n + O(1)` for the P-positions `(w,w,t)`; that preprint is not verified
here.

#### Towards a proof of (B′): the diagonal as a greedy matching

Write `A(b,c)` for the first row of the P-position `[A(b,c), b, c]` (or none), `τ` for the
partner map and `D = {A(k,k) : k ≥ 0}` for the diagonal values.

**Greedy matching (exact).** Fix a first row `h`. The positions `[h,h,c]`, `c < h`, have these
options:
* `[h,h,c']` with `c' < c`;
* `[a',a',min(c,a')]` with `a' < h`, which is P iff `a' = τ(c)`;
* `[h,b',min(c,b')]` with `b' < h`, which is P iff `A(b', min(c,b')) = h`.

So `[h,h,c]` is P exactly for the least `c < h` that is

* **available**: `τ(c)` is not below `h`;
* **unblocked**: not hit by a P-position `[h,b',c'']` with `b' < h`. Such a position blocks the
  single column `c''` if `c'' < b'`, and the whole half-line `c ≥ b'` if `c'' = b'`.

Processing `h = 1, 2, 3, …`, row `h` matches that column, which gives `τ(c) = h`, or nothing.
The side class is the set of columns that are never matched. A program that recomputes this
greedy from the full table of `A` agrees with the actual partners for every `h ≤ 1500`.

**Lemma L1.** Every `h ≥ 1` is **exactly one** of: a partner `τ(x)` (some `[h,h,x]` P), or a
diagonal value `A(k,k)` (some `[h,k,k]` P).
* **At least one (proved).** The rectangle `[h,h,h]` is N by strategy stealing. Its options are
  `[h,h,c']`, `[h,b',b']` and smaller rectangles, which are N. So some `[h,h,c']` or some
  `[h,b',b']` is P.
* **Not both: proved by Sheiner (2026).** L1 at row `h` says exactly that **the rectangle
  `[h,h,h]` has a unique winning opening move**. Its winning openings are the P-positions among
  `[h,h,c']` and `[h,b',b']`. This is Gale's first-move uniqueness question for three rows. It
  was verified by computation up to 100000 (Brouwer) and is proved in E. Sheiner, *Unique
  Winning Opening Move in Three-Row Chomp*, arXiv:2605.23837v2 (2026), Proposition 4.4. The
  author reports a Lean formalisation. I have read the proof (four pages, based on the recurrence
  of Brouwer, Horváth, Molnár-Sáska and Szabó) and found no gap.
  * Sheiner's `f(q,r)` is our `A(q,r)` where that exists, and `τ(r)` otherwise.
  * Sheiner's `D` is our `D`. Sheiner's `S` (rows that become constant) is our image set
    `τ(non-side)`, **not** our side class `𝒮`.
  * Before finding the paper, I had proved only the "at least one" half. Locally I could show
    only that a "both" case forces `A(k,x)` strictly between `k` and `h`. Numerically, every
    non-side column `x < k` is matched before row `A(k,k)`, with a margin growing like
    `0.12·k`.

**Monotonicity (verified up to `x = 50000`, not proved).** `τ` is strictly increasing on the
columns outside `𝒮`. So the matching is order-preserving and the greedy is a pointer process:
* a diagonal row `A(k,k)` matches nothing;
* every other row matches the first unblocked column at or after the pointer;
* the columns it skips become side elements for good.

Between consecutive matched columns there are 0, 1 or 2 side columns (9285, 19297 and 707
times up to 50000). `A(k,k)` itself is not monotone: it drops by exactly 1 at 20 values of
`k ≤ 1500`, e.g. `A(51,51) = 89`, `A(52,52) = 88`.

**What (B′) becomes.** With L1, the images of `τ` are the complement of `D`. Then (B′) reads:
for every `v`,

> `#{1 ≤ x ≤ v : x ∉ 𝒮, x ∉ D} ≤ 1 + #{1 ≤ x ≤ v : x ∈ 𝒮 ∩ D}`,

i.e. the side class and the diagonal values together cover `[0,v]` at least once on average.
Up to 1500 there are 202 numbers in each of the two sets, and the inequality holds at every
`v`, sometimes with equality.

**Status of (B′).** Still open, together with the monotonicity of `τ`. Both need control of the
point blocks `[h,b',c'']`, i.e. of the rest of the table of `A`. But (B′) is no longer needed
for the main question.

#### Theorem: the 2D side class is infinite

**Theorem.** Huddleston–Shurman's side class `𝒮` (the `x` with no P-position `[h,h,x]`,
`h > x`) is infinite. In fact `#(𝒮 ∩ [0,v]) > v/5` for infinitely many `v`. This was the first
proof. [notes/13](13-side-class-theorem.md) now has a shorter one with better constants
(`> v/5` for every `v`, upper density `≥ 1/4`), based on the remaining-lifetime lemma of
[notes/19](19-remaining-lifetimes.md).

The proof uses three results from Sheiner's paper. Write `f` for his function and `S_τ` for the
image set of `τ`.

* **(Prop. 4.3)** No number is both a partner `τ(x)` and a diagonal value `A(k,k)`.
* **(Lemma 4.2, row-start propagation)** If `[p,p,r]` is P, then for every `q` with `r < q < p`
  there is `b_q < r` with `f(q,b_q) = p`, i.e. `[p,q,b_q]` is P.
* **(Lemma 2.3(b))** In that situation the `b_q` are distinct.

Two more facts:

* **(Diagonal bound)** `A(a,a) ≤ 2a+1`.
  * `A(a,a)` is the mex of a set `B(a,a)` with at most `2a` elements that contains `1, …, a`
    (Sheiner, Lemma 2.2).
  * An elementary argument gives `A(a,a) ≤ 3a` for `a ≥ 1`, which also suffices for the
    infinitude: `A(a,a)` is the least `p ≥ a` outside `{f(a,b) : b < a} ∪ {f(t,t) : t < a}`.
  * `a ↦ A(a,a)` is injective, since `[n,a,a]` is an option of `[n,b,b]` for `a < b`.
* **(Alive rows)** If `[p,q,b]` is P with `p > q`, then `b ∈ 𝒮` or `τ(b) > q`. Otherwise, cutting
  row 1 to length `τ(b) ≤ q` leads to the P-position `[τ(b), τ(b), b]`.

*Proof.* Write `s(v) = #(𝒮 ∩ [0,v])`.

1. **Slope 2.** For non-side `r` with `p = τ(r)`, the `p − r − 1` distinct values `b_q` lie in
   `[0, r)`. So `τ(r) ≤ 2r + 1`.
2. **Improving the slope.** Suppose `τ(x) ≤ c·x + K` for every non-side `x`, with constants
   `c ≥ 1` and `K`. Fix a non-side `r` with `p = τ(r)`. Each `b_q` (`r < q < p`) is either in
   `𝒮 ∩ [0,r)` or non-side with `c·b_q + K ≥ τ(b_q) > q ≥ r + 1`. The second case means
   `b_q ∈ ((r+1−K)/c, r)`. Counting the distinct `b_q`:

   `p − r − 1 ≤ s(r−1) + r − (r+1−K)/c`, so `τ(r) ≤ (2 − 1/c)·r + s(r−1) + O(1)`.
3. **Infinitude.** Suppose `|𝒮| = m` is finite. Iterating step 2 from `c = 2` gives slopes
   `3/2, 4/3, 5/4, …`. With slope `c < 2`:
   * all `x ≤ (v − K)/c` outside `𝒮` have distinct partners `≤ v`, so
     `#(S_τ ∩ [1,v]) ≥ v/c − O(1)`;
   * by Prop. 4.3 and the diagonal bound, `#(S_τ ∩ [1,v]) ≤ v − #(D ∩ [1,v]) ≤ v/2`.

   This is a contradiction for large `v`. With only the elementary `3a` bound, use slope `4/3`
   against `2v/3`.
4. **Density.** Suppose instead `s(r) ≤ δr` for all large `r`. Step 2 gives the slope recursion
   `c ↦ 2 − 1/c + δ`. It decreases from 2 to the root
   `c*(δ) = 1 + δ/2 + √(δ + δ²/4)` of `c² − (2+δ)c + 1 = 0`. Step 3 needs
   `#(S_τ ∩ [1,v]) ≥ (1−δ)v/c − O(1)` to beat `v/2`, i.e. `c < 2(1−δ)`. For `δ = 1/5`,
   `c* ≈ 1.558 < 1.6`, so the iteration reaches a slope below `1.6` and gives a contradiction.
   Hence `s(v) > v/5` infinitely often. ∎

**Checks** (`tools/side_ingredients.cpp`, second rows up to 1500):
* Lemma 4.2 holds in all 136170 instances, with distinct `b_q`, each alive in the sense above.
* `A(a,a) ≤ 2a+1` holds, with equality at `a = 0`, and `{1, …, a} ⊆ B(a,a)` always.
* `τ(r) ≤ 2r` holds.

**What it settles.** For each finite `x ∈ 𝒮`, `G_𝒮(x)` is the index of `x` in `𝒮`. So
`G_𝒮` now takes every natural number value. That is exactly what Huddleston–Shurman's proof
that `3×ω^ω` is P needs for its answers `(2,x)` to the bites `(0, ω·(n+1)+c)`. This fills the
gap identified above. The rest of their argument is audited in [notes/15](15-hs-audit.md).

The constant `1/5` is far from the observed density `√2 − 1`. A lower density bound, the partner
law and (B′) all remain open.

#### The 3D side sets: the same argument, with defects

The `(0,1)`-tower corollary needs `𝒮_R` infinite for `R = □_g`. Write `[p,q,r]` for the
position with heights `(0,0) = p`, `(1,0) = q`, `(2,0) = r` and the box `□_g` on the cells
`(x,1)`, `(x,2)`, each column of the box cut to the height of the cell below it. Row cuts keep
this family; cuts inside the box leave it, to a smaller attachment `R'`.

**Assume `W(□_g)` has no finite P cut.** Otherwise the tower is N anyway. Then every
`[k,k,k]` is N: for `k ≤ g` it is a box, N by strategy stealing, and for `k > g` this is the
assumption.

**What carries over (proved).**
* **Encoding.** Sheiner's Lemma 2.1 holds for this family.
  * The function `f(q,r)` (the unique `p > r` with `[p,p,r]` P for `p < q`, or `[p,q,r]` P for
    `p ≥ q`) exists and is unique.
  * Cuts inside the box add at most `M` blocked values at each `(q,r)`, where `M` is the number
    of one-cut attachments. Each smaller attachment blocks at most one `p`.
* **Basic facts.** Distinctness (Lemma 2.3(a),(b)) and the alive-rows fact hold, as does the
  row-2 exclusion of Lemma 2.3(c).
* **Diagonal bound.** `f(a,a) ≤ 3a + M` for `a ≥ g`, and `a ↦ f(a,a)` is injective for `a ≥ g`.

**What breaks.** Sheiner's interval-blocking step (Lemma 3.1) assumes that the winning reply
from `[p,q,s_t]` cuts a row. In 3D it can also cut inside the box. For a fixed level `q`, each
smaller attachment supplies at most one such reply, so the lemma holds up to `M` exceptions per
level. But then the rightmost-hole step only gives `f(q,r) ≥ (first uncovered value)`, and an
uncovered value can create a further defect lower down.

A **defect** of a partner `p = τ(z)` is a `q ∈ (z,p)` with no row `b_q < z` such that
`[p,q,b_q]` is P. A **coincidence** is a partner that is also a diagonal value.

**Conditional theorem.** Suppose that, for `R = □_g` (no finite P cut):
* (D) the number of defects of `τ(z)` is at most `θ·(τ(z) − z) + K` for some `θ < 1/3`;
* (C) there are finitely many coincidences.

Then `𝒮_{□_g}` is infinite, so `T((0,1),g)` is N.

*Proof.* As in 2D:
* The defect-free `q` give distinct rows `b_q < z`. Each is a side element, a small row
  (`< g`, at most `g` of them), or a non-side row with `τ(b_q) > q`.
* If `𝒮_R` were finite, the slope recursion becomes `c ↦ 1 + (1 − 1/c)/(1 − θ)`. It converges
  to `1/(1 − θ) < 3/2`.
* That gives at least `(1 − θ)v − O(1)` partners up to `v`.
* (C) and the diagonal bound leave room for at most `2v/3 + O(1)`.

The contradiction needs `1 − θ > 2/3`. A diagonal bound `2a + O(1)`, which the data show, would
relax this to `θ < 1/2`. ∎

**Evidence** (`tools/side3d_ingredients.cpp`, `z ≤ 110`, exact finite evaluation):

| box | non-side `z` | defects (most at one `z`) | at most per `z` for `z ≥ 4g` | from box cuts | coincidences | `max f(a,a) − (2a+1)` |
| --- | --- | --- | --- | --- | --- | --- |
| `□_3` | 61 | 42 (8, at `z = 4`) | 2 | 37 | 2 (values 8, 14) | 8 |
| `□_4` | 62 | 37 (6, at `z = 11`) | 4 | 35 | 2 (values 12, 15) | 9 |
| `□_5` | 59 | 109 (38, at `z = 7`) | 4 | 77 | 1 (value 21) | 14 |

In every case the rows found are distinct and alive. Defects cluster near the box height and
then stay at a few per `z`, while `τ(z) − z ≈ 0.4z`, so the observed defect rate tends to 0.
Coincidences occur only at small values.

**Anatomy of the defects** (`tools/side3d_defects.cpp`). Fix a partner `p = τ(z)` and a
level `q ∈ (z,p)`. The position `[p,q,z]` is N (it is an option of `[p,p,z]`), and its winning
reply is one of:
* a **row-3 cut** to `[p,q,b]`, `b < z`: a good level;
* a **cut inside the box** to `[p,q,z | R'']`: a *box-cut-blocked* defect;
* a **row-1 cut** to `[k,q,z]` with `q < k < p`: a *dead* defect, `k = f(q,z)`.

Row-2 cuts are impossible, since they are also options of `[p,p,z]`.

* **Box-cut-blocked defects are at most `M` per partner (proved).** For a fixed smaller
  attachment `R''`, two P-positions `[p,q₁,z | R'']` and `[p,q₂,z | R'']` with `q₁ < q₂`
  would be options of each other.
* **Dead defects need a free slot.** At level `q`, the values `u_t = f(q,s_t)`, for good
  `t ∈ (q,p)` whose position `[p,q,s_t]` has a row-1 reply, fill all of `(q,p)` except
  `#(defects in (q,p)) + α_q` values. Here `α_q` counts good `t` whose `[p,q,s_t]` has only a
  box-cut reply. A dead level's value `k = f(q,z)` must lie outside the `u_t`. In 2D both
  counts are 0, which is Sheiner's argument.

Data up to `z = 110`:

| box | good levels | box-cut blocked | dead |
| --- | --- | --- | --- |
| `□_3` | 1261 | 37 | 5 |
| `□_4` | 1276 | 35 | 2 |
| `□_5` | 1109 | 77 | 32, all but one at `z ≤ 15` |

For large `z`:
* the box-cut-blocked levels sit at the top of the range, mostly `q = p−1, …, p−4`. In the
  smaller family, the P-position `[p,p,z]` has moved slightly to `[p,q,z | R'']`;
* dead levels sit just below a defect, typically with `k = q + 1`. For example, for `□_3` and
  `z = 88`, level 129 is box-cut blocked and level 128 is dead with `k = 129`;
* each dead level is fed either by a defect directly above it or by a box-cut-only reply
  (`α_q = 1` or `2` in the few cases with no defect above).

**Sharpened conjecture.** For each box, the number of dead levels of a partner is at most the
number of box-cut events (box-cut-blocked levels plus box-cut-only replies) of that partner,
and those are bounded. Together with the proved bound `M` on box-cut-blocked levels, this would
give (D) with a bounded number of defects per partner, far stronger than the `θ < 1/3` needed.

**No finite P cut for the single cube** (the rectangle fact used above). The stealing argument
shows `G(k,k,k) ≥ 2` whenever `[k,k,k−1]` is not P. The first player removes the top corner;
any winning reply inside the rectangle was also available directly, and removing the cube wins
only if `[k,k,k−1]` is P, i.e. `τ(k−1) = k`. In 2D, `τ(x) = x+1` only for `x = 1`, and
`τ(x) ≥ x+2` for every `x ≥ 2`: removing just the corner never wins `3×n` Chomp for `n ≥ 3`.
This is now proved ([notes/20](20-corner-and-matching.md), Theorem 1, also in Lean). With
`G(2,2,2) = 4`, the cube family therefore has no finite P cut at all, and every `3×n`
rectangle has Grundy value at least 2.

**Smallest attachments** (`side3d_defects g ZMAX a01,a02,a11,a12,a21,a22`, `z ≤ 110`, or
`z ≤ 60` for the single cube):

| attachment | finite P cut | box-cut blocked | dead |
| --- | --- | --- | --- |
| a cube on `(0,1)` | none | 0 | 0 |
| a column of 2 on `(0,1)` | none | 3 | 2 |
| `(0,1),(0,2)` at 1, or `(0,1),(1,1)` at 1, or `(0,1),(0,2)` at 2 | at height 1 | – | – |

In the last row the height-1 layer is a symmetric L, which is P. So `W(R)` is N, every `z` is a
side element, and nothing needs proving.

**The single cube is a disjunctive sum.** The cell `(0,1,0)` is comparable only with the
poison. So taking it affects nothing else, and nothing else removes it. Chomp is normal play on
the board minus the poison, so `[p,q,r | cube]` is P exactly when the 2D 3-row position
`[p,q,r]` has normal-play Grundy value **1** (value 2 in Huddleston–Shurman's unrestricted
convention). The first step of the induction is therefore Sheiner's theory with Grundy value 1
in place of 0. There the cube's removal is the only extra move, and the data show it never
creates a defect.

Sheiner's interval-blocking step does not transfer verbatim. An option of a value-1 position
can have value 0, and then it has no move to value 1. So even this first step needs a new
argument.

#### Large-scale data for the boxes (`tools/attach3row.cpp`)

`attach3row g N [Z]` computes the P-positions `[a,b,c | R]` exactly for **every** attachment
`R ≤ □_g` at once, with no cap on heights. It runs stage by stage in the third row, with
aligned bitsets as in `side3row`. A row cut caps the attachment, and a cut inside it moves to a
smaller attachment at the same `(b,c)`; both are handled in the recurrence.

**Validation.**
* Plain 2D, 801 rows, and the single cube, 600 rows: identical to `side3row` and
  `side3row_cube`.
* The 2-box, every cell with `b ≤ 7` (1455 cells), and a random sample of 600 cells of the
  3-box (`b ≤ 9`): identical to the rod solver's exact `f`.
* The 3-box partners up to `z = 150` and its defect counts up to `z = 110`: identical to the rod
  solver.

**Results.** Partners `[p,p,z | □_g]` found in the table are exact P-positions, and the defect
classification uses only exact table entries. A z with no partner found below `N` is only
"probably side": a partner could lie above `N`.

| box | rows | `z ≤` | partners | defects per partner: max (for `z ≥ 4g`) | box-cut / dead | coincidences | side density |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `□_3` | 6000 | 2500 | 1460 | 8 (4) | 479 / 69 | 2 (8, 14) | 0.4149 to `z = 3000` |
| `□_4` | 4000 | 1500 | 876 | 375 (4) | 373 / 400 | 3 | |
| `□_5` | 3000 | 1000 | 579 | 38 (4) | 381 / 51 | 1 | |

For the 3-box up to `z = 3000`:
* `τ(z)/z ∈ [1.347, 1.442]` for `z > 100`, and `τ(z) − √2·z ∈ [−9.4, 8.9]`;
* the partner law `τ(z) = z + #(𝒮 ∩ [3,z]) + ε` holds with `ε ∈ [−12, 10]`.

So the 3-box family has the same `√2` structure as 2D, with wider error windows.

For the 5-box, the large counts are at `z = 7, 8, 5` (38, 16, 12 defects). The 375 is the
deep partner `(396, 396, 14 | □_4)`. Its 381 levels cannot all have rows
`b < 14`, so at least 367 defects are unavoidable. A finite set of such small `z` only changes
the constants in the bootstrap. For `z ≥ 4g` no partner has more than 4 defects, so the
hypothesis (D) of the conditional theorem holds with a bounded number of defects throughout
these ranges.

**Universality** (`UNIVERSAL=1 attach3row g 3000`). The `√2` structure is not special to the
boxes. Here are all attachments `R ≤ □_g`, using partners and side elements for
`z ∈ [375, 1500]`:

| attachments | count | with a finite P cut | others: side density | mean `τ(z)/z` | `τ(z) − √2·z` |
| --- | --- | --- | --- | --- | --- |
| `≤ □_1` | 10 | 5 | 0.4139–0.4147 | 1.4130–1.4150 | `[−4.3, 6.2]` |
| `≤ □_2` | 50 | 25 | 0.4130–0.4156 | 1.4099–1.4150 | `[−7.7, 6.2]` |
| `≤ □_3` | 175 | 83 | 0.4121–0.4174 | 1.4062–1.4150 | `[−11.1, 7.5]` |
| `≤ □_4` (rows 2400, `z ∈ [300,1200]`) | 490 | 243 | 0.4107–0.4195 | 1.4034–1.4152 | `[−12.9, 8.0]` |

The single cube, computed to `x = 10000` with `side3row_cube`, has side density 0.41426,
discrepancy `[−0.85, 2.42]` against `(√2−1)(x+1)`, and `τ₁(x) − √2·x ∈ [−3.7, 4.8]`.

> **Universality conjecture.** For every finite attachment `R` such that no `[k,k,k | R∧k]` is
> P, the side set `𝒮_R` has density `√2 − 1`, and `τ_R(z) = √2·z + O(1)`.

In particular every such `𝒮_R` would be infinite, which is what the `(0,1)` towers need. The
attachment only perturbs the 2D quasi-periodic structure (Padhi's Conjecture 4.6, notes/13)
by a bounded amount.

**A heuristic shortcut that does not work.** The table also suggests deciding the two-wide
stalks `S(z,R)` of every `W(R)` by a dynamic programme over `(z, R)`. This would make towers
like `T((0,1),10)` cheap to test, but its P-claims rely on "no partner up to `N`". Partners can
be enormously deep for small `z`: for `T((0,1),9)` cut at 3, the P cut of the poison column is
at height 4107. So the programme's P-claims are wrong in places: it gives 18 and 28 for the 7-
and 9-boxes, where the certified answers are 20 and 8. Only the rod solver's periodicity
certificates decide stalks exactly. The programme is kept as a heuristic (`STALKDEBUG`,
`ZSTALK`), and nothing is claimed from it.

#### The single cube in detail (`tools/side3row_cube.cpp`)

The cube family's table `A₁(b,c)` (first row of the P-position `[a,b,c | cube]`) obeys
Sheiner's recurrence with one extra forbidden value per cell: the 2D value `A₀(b,c)`, from the
cube-removal option. `side3row_cube` computes both tables together, stage by stage. For
`x < 15` it agrees with brute-force Grundy values (`[p,q,r | cube]` P iff `G([p,q,r]) = 1`).

**Facts verified up to `N = 20000`** (second rows; partners and diagonal values up to 10000,
defects for `z ≤ 9000`):
* **No finite P cut.** `[k,k,k | cube]` is never P, i.e. `G(k,k,k) ≥ 2` for 3-row rectangles.
  Small values are `G(k,k,k) = 2, 4, 5, 9, 11, 12, …`.
* **Exactly one.** Every `h ≤ 10000` is exactly one of a cube partner `τ₁(x)` or a cube
  diagonal value `A₁(a,a)`. This is the analogue of Sheiner's Proposition 4.4.
* **Diagonal bound.** `A₁(a,a) ≤ 2a + 2`.
* **Defects.** There are 5272 partners and 9818607 good levels, with no box-cut-blocked level
  and **24 dead levels, at most one per partner**. All have the same shape:
  * `q = p − 5`, `k = A₁(q,z) = p − 1`, and `p ≡ 0 (mod 8)`;
  * the exception is the 2D P-position `[p, p−5, 7]`, i.e. third row 7, together with the cube
    P-position `[p, p−4, 7 | cube]`.

**Lemma (proved, given that `[k,k,k | cube]` is N for all `k`).** Let `p = τ₁(r)`, and let `q` be
the largest level in `(r,p)` without a row-3 witness, i.e. with no P-position
`[p,q,b | cube]`, `b < r`. Then either:
* `A₀(q,r) = p` (the cube-removal reply; at most one such `q` per partner), or
* some `s < r` has the 2D P-position `[p,q,s]` while `[p,t,s | cube]` is P for some
  `t ∈ (q,p)`.

*Proof.*
1. By maximality, every level `t ∈ (q,p)` has a row `s_t < r` with `[p,t,s_t | cube]` P.
2. As in Sheiner's Lemma 3.1, the position `[p,q,s_t | cube]` is N. Its P reply is a row-1 cut
   to `[u_t,q,s_t | cube]` with `q < u_t < p`, unless it is the cube removal `[p,q,s_t]`. The
   cube removal is the second alternative.
3. If every reply is a row-1 cut, then `t ↦ u_t` maps `(q,p)` injectively into itself, so the
   row-3 values at `(q,r)` cover `(q,p)`.
4. `A₁(q,r) > q`, since otherwise `τ₁(r) ≤ q`. And `p` is not blocked at `(q,r)`: not by row
   3 (choice of `q`), not by row 2 (Lemma 2.3(c)), not by the cube (first alternative excluded).
   So the least unblocked value `≥ q` is `p`.
5. Then `[p,q,r | cube]` is a P option of the P-position `[p,p,r | cube]`, which is
   impossible. ∎

**Why defects are rare: row resonances.** In 2D, a side row `s` eventually has its P-positions
at a fixed offset, `[b+d₀(s), b, s]`. In the cube family the eventual offsets of a side row are
periodic (periods 1, 2, 4, 8 for `s ≤ 30`) and can dip below `d₀(s)`. For example, row 7 has
2D offset 5 and cube offsets 4, 6. A defect needs such a dip to line up with a partner, and it
then occurs at most once per row. Up to 9000 only row 7 ever lines up. Rows 5, 11, 24, 26 also
dip but never coincide with a partner in range.

**Side observation (2D).** Of the 1036 side rows `s ≤ 2500`, 985 have a constant offset on
`b ∈ [10000, 20000]`. All 985 have offset exactly `d₀(s) = 1 + #(non-side x < s)`. The other 51
(the first is `s = 120`) alternate between that value and one off it, apparently periodically.

**Every defect has its own source; nothing cascades** (`RES=1 side3row_cube N Z`). Call a
level `t > q` a *cube-removal-only reply at level `q`* if:
* `t` is good with witness `s < z`;
* `[p,q,s]` is a 2D P-position;
* `[p,q,s | cube]` has no row-1 reply inside `(q,p)`.

The lemma above says the topmost defect needs one (or `A₀(q,z) = p`). Slot counting would also
allow a lower defect to live on the slot left by a defect above it, a cascade. The data say this
never happens:

| `z ≤` | partners | defect levels | with their own cube-removal-only reply | such replies at good levels |
| --- | --- | --- | --- | --- |
| 1000 | 584 | 5 (all dead) | 5 | 12155 |
| 4000 | 2342 | 14 (all dead) | 14 | about 208500 |

So every defect is fed at its own level, and no defect feeds another. The sources themselves
are not rare: about 90 per partner at good levels for `z ≤ 4000`. There they are harmless,
because a good level has a row-3 witness anyway. A crude count of sources therefore cannot bound
the defects. Nor can a count of "resonant rows", meaning rows `s` whose cube level lies above
their 2D level: there are about 45 such rows per partner at `z ≈ 1000`. A proof of (D) for the
cube has to show two things:
1. no cascades: a defect level without its own source is impossible, extending the topmost-defect
   lemma to every level;
2. a source sits at a non-good level only rarely.

Neither is proved.

**Status of the cube case.** Not proved. A later attempt is in
[notes/19](19-remaining-lifetimes.md), §8: it explains the single shape of the defects, and
shows that a bound on them cannot follow from the lemmas used here alone. What remains is to bound the defects of a partner,
i.e. to show that resonances below the topmost defect cannot pile up. The data say there is at
most one. A proof seems to need global control of the eventual row patterns of both families,
plus a proof that `G(k,k,k) ≥ 2` for all 3-row rectangles.

**What a proof still needs.** Slot counting alone allows a dead level to feed another dead
level below it indefinitely. What stops the cascade in the data must come from the smaller
families' own P-positions near `[p,p,z]`. So the induction over attachments needs a hypothesis
like: "in each smaller family, the P-positions with first row `p` and second row close to `p`
are few and lie next to the family's own partners." Formulating and proving that is the open
step.

**The same law in 3D** (`rodf -I 2 -K 6 -v 1`, partners printed as `[z:h]`;
`data/side-sets/box*_with_partners.txt`). For the 3-, 4- and 5-boxes, with `z` up to 150, 120
and 90:
* the side sets have density 0.43, 0.41 and 0.45;
* `τ_R(z)/z` is 1.39, 1.39 and 1.34 at the top of the range;
* the error `τ_R(z) − z − #(𝒮_R ∩ [g,z])` fluctuates within about `±10` with no visible drift.

There are also isolated deep partners: `(h; h, 14; □_4)` is P only at `h = 396`. The 3D law may
hold with a larger error, but these ranges are too short to say.

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
| 9 (partial) | 12137 of 15730 | | | | |

The run for entries `≤ 9` checks `R` in lexicographic order. It was stopped after 12137 of the
15730 plane partitions, all with an exact P option: one fresh solver process per `R` repeats
too much work near `□_9`.

So `U` contains no `R ≤ □_8`, and **all 9075 positions `W(R)`, `R ≤ □_8`, are exactly N**, each
by a direct exact reply. This is the "`U` is empty" picture so far: no `R` has been found whose
`W(R)` lacks a finite or two-wide P option.
