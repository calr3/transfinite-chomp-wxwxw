# What to try next

Status: 20 November 2026, after notes [20](20-corner-and-matching.md) and
[21](21-two-column-above-omega-omega.md). The open problems are stated in
[notes/00](00-overview.md); this note lists the directions that look worth trying, in order of
preference, each with what exists, a first step and the risk. The last section lists what has
been tried and should not be retried without a new idea.

Directions 1, 2 and 3 have been taken up since; their sections say what came of them. Section 7
asks whether the problem could be undecidable and how one would prove it.

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

## 7. Could the problem be undecidable?

Added 21 November 2026. Nothing here is proved beyond the four facts below; it is a direction.

**What the claim can mean.** Whether `ω×ω×ω` is P is one bit, so it is computable in the
trivial sense. Three statements make sense.

* **(U1) No decision procedure.** Every position reachable from `N³` is `N³ ∖ ↑A` for a finite
  antichain `A` (Dickson's lemma), so positions are finite objects. Claim: the set of `A` whose
  position is P is not decidable.
* **(U2) No computable winning strategy** from `N³`. This is about the single game. Rabin
  (1957) gave a game with recursive rules and no recursive winning strategy; Blass (1972)
  showed that a recursive game always has a hyperarithmetical one.
* **(U3) No proof** in a fixed theory such as ZFC. This is not a computability statement. See
  "Independence" below.

(U1) is to `ω×ω×ω` what Conway's undecidable generalised Collatz problems are to `3x+1`: it
would explain the difficulty without settling the single case.

**Four facts.**

1. *In 2D the P/N problem is decidable.* A position inside `ω×ω` that properly contains two
   infinite rows (or two infinite columns) is N, by the move to `2×ω`. One infinite row and a
   finite rest is N: beyond the partners of the finitely many smaller rests, the first cut of
   the infinite row that is not N is P. One infinite row and one infinite column: all cuts of
   either are N, so the status is a finite recursion over the finite part.
2. *3D P/N contains the 2D Grundy values.* For a 2D position `X` and `g ≤ ω`, `X` with a
   stalk of `g` cells above the poison in the third direction is a disjoint sum, so it is P iff
   `G(X) = g`. So "`46 ∈ L`" and "`G(4×ω) ≥ ω`" (notes/23) are P/N questions about
   positions inside `N³`.
3. *Upper bound.* With `r` infinite columns and no slab, the P-set is at level `r` of the
   arithmetical hierarchy at most: a cut of a column leaves fewer infinite columns, and only
   finitely many moves keep them all. A slab costs `ω` more levels, because a bite into it
   leaves any number of columns. So the P-set of `N³` is computable from the `ω²`-th jump.
   Nothing better follows from the definition, and no lower bound is known.
4. *Where it could first fail.* Positions with at most two infinite columns are decidable
   (Byrnes; notes/07). With three, "N" is witnessed by a P reply that a search finds, and "P"
   is the statement that the search never ends. So this class is decidable iff the depth of
   the shallowest winning reply is bounded by a computable function of the size of the
   position. One level down this is what happened: `𝒮` is decidable because
   `τ(x) ≤ (5x+3)/3` (notes/13, notes/16).

**How a proof of (U1) would go.** The only known method is a reduction from the halting
problem: a computable map from machines `M` to positions `X_M` with `X_M` P iff `M` never
halts.

* An infinite column gives a player a move that names a number `t`. That supplies the
  quantifier "there is a step `t`" for free.
* What is missing is the verifier: the finite cut of `X_M` at height `t` must be P exactly
  when `M` has halted by step `t`. So the recurrence for finite Chomp must be able to
  compute, with `X_M` as the program. Chomp's rules are fixed, so this is like proving rule 110
  universal: it needs persistent structures (clocks, signals, counters) whose interactions can
  be controlled.
* Byrnes's theorem says two growing columns are finite-state, hence periodic. So the memory
  must come from a third growing column, where offsets are unbounded.
* A model: Larsson and Wästlund (2013) prove that it is undecidable whether two heap games
  with finite move lists have the same P-positions. There the move list is the program, and
  moves are local. In Chomp only the position can be the program, and a cut reaches any lower
  height.
* (U2) needs (U1) inside the positions a winning strategy can reach, plus an argument that
  the opponent can steer the game to the hard instances.

**What our data say.** Against, at the levels we can test:
* every bound we have proved or measured is linear (`τ(x) ≤ (5x+3)/3`; (H4) without exception;
  death levels below `2x` in notes/23);
* every attachment shows the same large-scale structure (density `√2−1`, notes/12). The
  system forgets its seed, which is the opposite of being programmable.

For: the first winning reply can be deep for a small position (height 4107 for a small
two-column position in notes/12; 46 at height 1012 in notes/23), periods and transients grow fast, and no P-position with three
infinite columns is known at all. Undecidability at that level needs infinitely many of them.

**First steps, cheapest first.**
1. *A census of depths.* For all attachments up to a given size, the depth of the shallowest
   P reply (`tools/attach3row.cpp`, `rodf`). By fact 4 this is the quantity that decides the
   matter. A geometric tail supports the random model; isolated huge values would be the
   places to look for structure.
2. *Damage spreading.* Change one cell of the seed and follow the difference between the two
   arrays of partners. A difference that stays localised or travels coherently is a signal. A
   difference that spreads and mixes leaves nothing to build with.
3. *A barrier result.* notes/19, §8 has a model with random blocked values that satisfies all
   our lemmas. Build one that satisfies them and simulates a counter machine. That would show
   that no proof from these lemmas alone can bound the depths.
4. *A generalised family.* Prove undecidability for poset games on `P×ω` with `P` a finite
   poset, or in dimension 4, where the board contains sums of two 2D positions and
   `G(X) = G(Y)` becomes a P/N question. Neither has been done as far as we know.

**Independence (U3).** If `N³` is N, some reply position `Q` is P, and "`Q` is P" says that
all of its countably many options are N. Could that be true and unprovable in ZFC?

* *It cannot be ruled out.* Statements of the form "for every `n`, a finite check passes"
  (`Π₁`) can be true and unprovable, and P claims are of this kind or more complex. "This
  tower is P" is `Π₁` in the simplest cases with three infinite columns. "`ω×ω×n` is P" is
  far more complex (level about `ω·n`, by fact 3). If the winner has a strategy given by an
  explicit rule with a known running time, "this rule wins" is `Π₁`: no finite play that
  follows the rule ends with its player taking the poison.
* *It is not the kind of independence that the continuum hypothesis has.* The statement is
  about a recursion over a computable well-founded relation on the natural numbers, so it
  has the same truth value in every transitive model of ZFC. Forcing cannot change it. It
  could only be true and unprovable, as a consistency statement is.
* *For a `Π₁` statement, a proof of independence is a proof of the statement.* If it were
  false, a finite counterexample would refute it in ZFC. So "this tower is P is independent"
  is not easier to establish than "this tower is P".
* *Known ways to prove unprovability, and why they do not reach this statement.*
  1. Coding: show that the statement implies the consistency of the theory. The position
     would have to simulate a search for proofs. That needs (U1), and then gives a position
     built for the purpose, not `ω×ω×ω`.
  2. Fast growth (Paris–Harrington, Goodstein, Kruskal): for a statement "every `g` has a
     witness", show that the least witness outgrows every function the theory proves total.
     The ordinals in sight are `ω³`, and `ω^ω` over all dimensions. That is enough only
     against very weak base theories, in which `ω^ω` is not provably well-ordered (Simpson
     1988, for the Hilbert basis theorem). In our data witnesses grow slowly, with outliers
     (notes/23: values up to 45 by height 107, 46 at 1012).
* *What (U1) would give.* Suppose the P-positions of a family in which "P" is `Π₁` are
  undecidable. Then for every consistent, recursively axiomatised theory some position of
  the family is P and the theory does not prove it. Otherwise one could decide the family by
  searching for a proof and for a winning reply at the same time. So an undecidability
  theorem is the route by which independence could be proved, for a constructed position.
* *What is more likely.* The count of options is not the obstacle: `2×ω` has countably many
  and the proof is one rule. A proof needs finitely many arguments that cover all options. A
  formula for the replies is one way. A counting argument is another, and it works without
  any pattern: the side-class theorem proves that infinitely many replies exist without
  saying which. The realistic danger is a statement that is true for statistical reasons and
  has no proof that anyone finds. That cannot be told apart from independence in practice.

**Related.** Brumleve, Hamkins and Schlicht (2012): mate-in-`n` in infinite chess is decidable
because it is expressible in Presburger arithmetic; whether a position is won at all is open.
The same holds here: "the player to move wins within `n` moves" is Presburger-definable for
positions with a bounded number of corners, but an infinite position is not won in a bounded
number of moves. García-Marco and Knauer (2018): the winner of Chomp on a numerical semigroup
is decidable. Grier (2013): finite poset games are PSPACE-complete, with the poset as the
program.

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
