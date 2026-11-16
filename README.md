# Chomp on ω×ω×ω

**Problem.** Chomp is played on the board `N³` (cells `(x, y, z)` with natural coordinates,
ordered componentwise). A move takes a remaining cell `m` and every remaining cell `≥ m`.
The cell `(0,0,0)` is poison: whoever takes it loses. Who wins, and what is a winning first
move? The question is due to David Gale (*Tracking the Automatic Ant*, 1998, ch. 11;
Nowakowski, GONC5 problem D1). Gale also proposed `3×3×ω` as "a possibly simpler question".
Wikipedia reports a $100 reward for a winning first move, with a "citation needed" tag. None of
Gale's book chapter, Huddleston–Shurman or Nowakowski's list mentions a prize, so its source and
terms are unconfirmed.

## Layout and building

| Path | Contents |
| --- | --- |
| `notes/` | One write-up per idea tried (`01`–`10`); start with the table under "Progress notes" below. |
| `tools/` | C++ solvers: `box_chomp` (finite boxes), `chomp3`/`chomp3f` (capped DFS), `chomp3p` (df-pn with the rod oracle), `rodf` + `rod.h` (rods `S×ω`, exact for two-wide stalks), `rows` (2D ordinal Grundy values), `tower_scan`; and `hs_oracle.py`, an exact oracle for 2D positions with up to three columns of height below `ω^ω`. |
| `scripts/` | Sweeps and probes that drive the solvers (Python 3, shell). |
| `lean/` | The Lean library `Chomp` (core only, no `sorry`). |

```
lake build                                                # Lean proofs (Lean 4.36.0-rc2)
g++ -O3 -march=native -std=c++17 -pthread -o rodf tools/rodf.cpp     # likewise for the other tools
./rodf 2                                                  # 2 x omega : P exact
./chomp3p why "0,1,1"                                     # the first move (0,1,1) loses
```

The work began on branch `chomp-omega-cubed` of `calr3/cgt`, which has the full commit history.

Conventions: a position is a downset `X ⊆ N³`. `P` means the player to move loses, and `N`
means the player to move wins. `X ∖ ↑m` is the position after taking `m`.
`ω×ω×c = N×N×[0,c)` and so on. For a finite base `B`, `B×β` is the box over `B` of
height `β`.

## Where things stand

* **Proved (Lean, `lean/`):** the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their
  permutations lose; `2×ω` and the infinite L-shape are P; the 2D board `ω×ω` has winning moves
  `(1,1)`, `(0,2)`, `(2,0)`; winning moves form an antichain; outcomes are symmetric.
* **Reformulation:** a first move `m` loses iff some `m'` makes `N³ ∖ (↑m ∪ ↑m')` P, a
  "P-pair". So everything comes down to positions with two generators (Idea 4).
* **Exact data:** finite P-heights `h(S)` of small cross-sections (Idea 1). The finite
  truncations of the three-plane position `U` are P only for the cubes up to size 3 (Idea 3).
* **Conjecture 1.1:** `S×ω` is P only for the domino `S`. If true, boxes `j×n×ω` cannot rule out
  `(0,0,n)` for `n ≥ 3`.
* **Exact solver results (second round, ideas A–E):**
  * `2×ω` is proved P by a repeated-state certificate in the rod solver.
  * Every position whose infinite part is two columns wide is decided exactly.
  * A rod with a single infinite column, and a 2D position with a single infinite row, has
    Grundy value `ω + γ` (proved).
* **Open:** every other first move, in particular `(0,0,3)` (Idea 2) and `(1,1,1)` (Idea 3).
  The `2×ω` proof template (answering every option with a rod) fails for `ω×ω×3`.
* **Main obstacle:** positions containing a full infinite slab or plane. Exhaustive search with
  relative caps cannot decide them. The way forward looks like Grundy-value theory for rods and
  slabs (Huddleston–Shurman), or periodicity detection, rather than more search.

## Progress notes

Each idea from section 4 gets its own write-up in `notes/`:

| Idea | Notes | Outcome in one line |
| --- | --- | --- |
| 1. Rods `S×ω` | [`notes/01-rods.md`](notes/01-rods.md) | Only the domino gives a P rod among small cross-sections. `3×3×ω` is out of reach, and an exact table of finite P-heights came out of it. |
| 2. Slab `ω×ω×3` | [`notes/02-slab.md`](notes/02-slab.md) | Undecided. The options that keep a full slab defeat exhaustive search. Proved `L(a,b)×2` and `L(1,1)×c` are N, and found the P-pair reformulation. |
| 3. Candidate `(1,1,1)` | [`notes/03-three-planes.md`](notes/03-three-planes.md) | Undecided. Three options of `U` are proved N, and the finite truncations weakly suggest `(1,1,1)` loses. |
| 4. Ledger | [`notes/04-ledger.md`](notes/04-ledger.md) | 9 first moves proved losing, the rest open. P-pair framework, and a disjunctive-sum view of split positions. |
| A. Proof-number search | [`notes/06-search.md`](notes/06-search.md) | df-pn plus a table of known P-positions solves easy positions instantly. The rod oracle exposed two wrong small-cap answers, and the hard positions remain unknown. |
| B. Exact arm solver | [`notes/07-arms.md`](notes/07-arms.md) | Two-wide stalks are decided exactly by a repeated-state certificate. `2×ω` is now proved by the solver, rods up to 8 cells are almost all exact, and a new Wythoff-like exact P-table came out. |
| C. A P-family for `ω×ω×3`? | [`notes/08-family.md`](notes/08-family.md) | No rod reply answers any of 35 options (163 of 210 rod replies are exact N), so the `2×ω` proof template fails. Flattening reduces the question to the winning moves of `ω×ω×2`. |
| D. 2D ordinal values | [`notes/09-rows.md`](notes/09-rows.md) | Proved `G(ω,R) = ω + γ(R)`. Heuristically, two infinite rows give finite values and three give `ω + k`, e.g. `G(3×ω) = ω+1`. `4×ω` (the open `ω×4` problem) is out of reach. |
| E. Hilbert polynomial | [`notes/10-hilbert.md`](notes/10-hilbert.md) | Every computed case fits "the leading term of `G` depends only on the number of infinite rows". The one-column case is proved in 3D too. |
| Literature | [`notes/11-literature.md`](notes/11-literature.md) | Huddleston–Shurman and Nowakowski read in full. Our tables agree with theirs. Hypothesis E is their Stratification Conjecture, and the two-wide-stalk solver implements a case they call recursive. `ω×ω×ω` is P iff `h(ω×ω) = mex(M_ω) = ω`. |
| Three chains | [`notes/12-three-chains.md`](notes/12-three-chains.md) | An exact oracle for 2D positions with three columns (Huddleston–Shurman §9–10), validated. Gale's `3×3×ω` reduced to a search over towers `T(b,g)`: 25 of the 60 with `g ≤ 12` are exact N so far, `T((0,1),5)` only through a deep two-wide-stalk reply. Caching certified sequences makes the solver up to 60× faster. |
| 5. Lean | [`notes/05-lean.md`](notes/05-lean.md) | Lean proofs that `2×ω` is P and that the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their permutations lose. |

## 1. Previous work

| Work | What it gives |
| --- | --- |
| Schuh (1952), "Spel van delers" | The divisor game, which is Chomp on products of chains (3D Chomp = divisors of `pᵃqᵇrᶜ`). |
| Gale (1974), *Amer. Math. Monthly* 81 | Chomp itself. Strategy stealing: any board with a top cell is `N`. |
| Gale (1998), *Tracking the Automatic Ant*, ch. 11 | States the octant problem, reduces it to the ordinal `α` with `ω×ω×α` P, and asks the "simpler" question about `3×3×ω`. Reports Huddleston's Fundamental Theorem with Bergman's proof, and Huddleston's (then unproved) claims that `3×ω^ω`, `4×ω²` and `2×2×ω³` are P. |
| Zeilberger (2001), "Three-rowed CHOMP"; Sun (2002); Brouwer's tables | Finite data and recurrences for 3-row Chomp. |
| Byrnes (2003), "Poset game periodicity", *Integers* 3 | With two growing chains and a finite rest, the positions of any fixed Grundy value are eventually periodic (`f(m) − m` periodic), with bounded offsets and finite-time computability. This is exactly the two-wide-stalk case our certified solver handles. |
| Dress, Flammenkamp & Pink (1999), *Adv. Appl. Math.* 22 | Additive periodicity of mex-recursions (Wythoff rows and columns, T-extensions of finite-type graphs). |
| Dozier & Perry (2016), "Androids armed with poisoned chocolate squares", *Math. Mag.* 89 | "Ideal Nim": Chomp on monomial monoideals with arbitrary poison sets. Termination is equivalent to Dickson's lemma; small values; a game version of Buchberger's algorithm. |
| Rivero Herrera (2026), "Hanf numbers for poset games", arXiv:2504.07317 | Chomp on lexicographic powers and on ordinal submonoids with the natural sum. A different (lexicographic) order, where first-player wins carry over to larger powers. That is exactly what fails for the componentwise order of `ω×ω×ω`. |
| Friedman & Landsberg (2007), "Renormalizing Chomp", *Chaos* 17 | Scaling and renormalisation picture of 3-row P-positions. |
| Grier (2013) | Finite poset games are PSPACE-complete. |
| **Huddleston & Shurman (2002), "Transfinite Chomp"**, *More Games of No Chance* (MSRI 42), 183–212 | Chomp on ordinal boards, with ordinal Grundy values. See below. |
| xorshammer blog (2008), "Ordinal Chomp" | Exposition. It says the H–S theory decides `ω×ω×ω` *in principle*: the Fundamental Theorem's construction gives `h(ω×ω) = mex(M_ω)`, though nobody has carried it out. |
| Nowakowski (2017), "Unsolved problems in combinatorial games", GONC5 problem D1 | States Gale's `ω×ω×ω` question, the `ω×4` problem and the Stratification Conjecture. Points to Byrnes's periodicity theorem and to Dozier & Perry (2016) on Chomp over ideals and Gröbner bases. |
| arXiv 2605.23837 (2026), not checked | Claims every `3×n` rectangle has a unique winning opening. Finite, but relevant to Gale's uniqueness question. |

Huddleston–Shurman, now read in full (summary and comparison with our results in
[`notes/11-literature.md`](notes/11-literature.md)):

* *Fundamental Theorem* (Thm 5.1): for every position `A` and nonempty base `B` there is
  **exactly one** height `h` such that `A` plus the tower over `B` cut at `h` is a P-position.
  The proof builds it as `h = mex(M_ω)` from the P-heights of smaller bases. We write `h(B)` for
  `A = ∅`, the "P-height" of `B`. **`ω×ω×ω` is P iff `h(ω×ω) = ω`.**
* P-boxes: `2×ω`, `3×ω^ω`, `2×2×ω³`, `2×2×ω×ω`, `ω×ω×ω×2×2×2`. So `h(2) = ω`,
  `h(3) = ω^ω` and `h(2×2) = ω³`.
* Products: `G(X × P) = G(X)` for the "P-ordered" P-positions `P` (`2×ω`, two-row `(i+1, i)`,
  L-shapes). Complete Grundy values of two-wide positions, all three-wide P-positions, the
  P-positions of `2×2×Ω`, and the Side-Top and Front-Top theorems.
* *Stratification Conjecture* (Conj. 12.1): positions that agree in their large-scale part
  (rectangles of size at least `ω^i`) have Grundy values that agree in their terms from `ω^i` up.
* `G(4×ω)` is open: it is `mex(L)` for an explicit set `L` that contains every (unrestricted)
  value below 46, and 46 would need `a > 480`. They believe `ω·2`.
* The paper does **not** discuss `ω×ω×ω`. Nowakowski's unsolved-problems list (GONC5, 2017,
  problem D1) attributes the question to **David Gale** and mentions no prize.

## 2. Elementary facts (proved here)

1. **Play is finite.** Downsets of `N³` satisfy the descending chain condition by Dickson's lemma,
   so P/N is well defined by well-founded recursion. Every position reachable from `N³`
   is a subset of `N³`, so the game needs no ordinals beyond ω. Ordinals appear only
   in Grundy values and in `h(·)` for other bases.
2. **Winning moves form a finite antichain.** If `m < m'` are both legal in `X`, then
   `X ∖ ↑m` is an option of `X ∖ ↑m'`, so at most one of them is P. Hence the set `W(X)`
   of winning moves is an antichain, which is finite by Dickson's lemma. For `X = N³` it is
   also closed under the 6 coordinate permutations.
3. **One-parameter uniqueness.** This is a special case of (2). For example, at most one `c` makes
   `ω×ω×c` P, and at most one `j` makes `j×k×ω` P for a fixed `k`.
4. **2D warm-up.** `W(ω×ω) = {(1,1), (0,2), (2,0)}`:
   * `(1,1)` leaves two equal arms, and the second player mirrors.
   * `(0,2)` leaves `2×ω`, which is P. With `g+1` cells left in the bottom row and `g` in the
     top, every option of `2×ω` has a move back to such a 2-row P-position.
   * By (2), no other move can also win.
5. **Reformulation.** `ω×ω×ω` is P iff `h(ω×ω) = ω`. If `h(ω×ω) = n` is finite, then
   `(0,0,n)` is a winning first move.
6. **First moves up to symmetry**, with `X(m) = N³ ∖ ↑m`:
   * A: `(0,0,c)` gives the slab `ω×ω×c`.
   * B: `(0,b,c)` with `1 ≤ b ≤ c` gives two crossing slabs, `ω × (N²∖↑(b,c))`.
   * C: `(a,b,c)` with `1 ≤ a ≤ b ≤ c` gives three mutually perpendicular slabs.
7. **Moves already ruled out** (all proved in Lean, `lean/Chomp/FirstMoves.lean`):
   * `(0,0,1)`: it leaves `ω×ω`, which is N.
   * `(0,0,2)`: `ω×ω×2` is N. Taking `(0,1,0)` from it leaves `ω×1×2 ≅ 2×ω`, which is P.
     So `h(ω×ω) ≥ 3`.
   * `(0,1,1)`: `ω×L(1,1)` is N, because taking `(1,0,0)` leaves the 2D L-shape `N²∖↑(1,1)`,
     which is P.
   * More generally, `ω×ω×n` is N whenever `j×n×ω` is P for some `j` (take `(0,j,0)`).
8. **Finite-base boxes.** For finite `B`, the options of `B×ω` are the finite boxes `B×g`
   (all N, by strategy stealing) and the towers
   `T(b,g) = B×[0,g) ∪ (B∖↑b)×[g,ω)`. So `B×ω` is P iff every tower is N. Let
   `R = {(j,k) : j×k×ω is P}`. Then `R` has at most one cell in each row and column, and its
   first two rows are `{(1,2)}` and `{(2,1)}`. A cell `(j,n) ∈ R` rules out first move `(0,0,n)`.

## 3. First computations (`tools/`)

Later tools (`rodf`, `chomp3`, `chomp3f`) and sweeps (`scripts/`) are described in the notes.


* `box_chomp.cpp a b c`: exact winning first moves of a finite box. Results:
  * `2×5` (as `1×2×5`): `(0,1,4)`. `5×5`: `(1,1)`. These are sanity checks.
  * `2×2×2` and `3×3×3`: `(1,1,1)` only.
  * `4×4×4`: `(2,3,3)` and its permutations. This is a far-corner move from strategy stealing,
    so finite cubes are a poor proxy for `N³`.
* `tower_scan.cpp j k G T`: for base `j×k`, it finds which towers `T(b,g)` (`g ≤ G`) have a
  P truncation `B×[0,g) ∪ (B∖↑b)×[g,t)` with `t ≤ T`. Such a truncation shows the tower is N.
  This is a one-sided filter: a tower can be N only through options that keep an infinite rod.
  * `1×2`: every tower has a P truncation at `t = g+1`, consistent with `2×ω` being P.
  * `1×3`, `2×2`, `2×3`: the tower with `g = 0` is `2×ω`, which is P. So all three bases give
    N, matching H–S.
  * `3×3` (`g ≤ 4`, `t ≤ 13`): 23 of the 40 towers have no P truncation. That includes towers
    known to be N, such as `3×ω`. The filter is inconclusive, and a real decision procedure is
    needed (Idea 1).

## 4. Ideas to explore

1. **Solver for one infinite direction.** Store columns with heights in `N ∪ {ω}`. A position
   with `k` columns of height ω has finitely many options that keep all `k` such columns, plus
   finitely many families indexed by `z ∈ N` that have fewer. Decide each family with
   Byrnes-style eventual periodicity in `z`: detect it empirically, then prove it or certify it.
   * Validate against `2×ω` (P) and `3×ω`, `2×2×ω` (N).
   * Then compute `R` row by row. Each `(j,n) ∈ R` rules out `(0,0,n)`.
2. **The slab question `h(ω×ω)`.** Is `ω×ω×3` P? This needs positions with two infinite
   directions: a finite core, rods along x and y, and full slabs. Develop a "dominant term"
   description in the spirit of the Stratification Conjecture, and start with `ω×ω×3`
   restricted to options that are known to matter.
3. **Candidate `(1,1,1)`.** It wins `2×2×2` and `3×3×3`, and it is the 3D analogue of the 2D
   winning move `(1,1)`. It leaves `U = {x=0} ∪ {y=0} ∪ {z=0}`, which has full S₃ symmetry.
   * Map which options of `U` are known N (for example, `(1,0,0)` gives `ω×ω`, and `(0,1,1)`
     gives `ω×L(1,1)`).
   * Probe the rest with truncations `U(M₁,M₂,M₃)` of unequal lengths. In 2D, `2×ω` behaves
     like the unequal truncations `(g+1, g)`, not like equal ones.
4. **Keep a ledger of first moves.** Record each move proved losing and why, as in (7). Note that
   a losing move says nothing about the moves below it. If any move is proved winning, the
   antichain property (2) settles every comparable move at once, and S₃ symmetry gives its
   permutations.
5. **Formalise in Lean** (core only, no Mathlib). Define the game on `N³` with
   downsets given by finite antichains, prove facts (1)–(7), and reuse the certificate machinery
   (`Cgt/Certificate.lean` in the `calr3/cgt` repository) for finite sub-claims.
