# Chomp on ω×ω×ω: where things stand

A summary of what this repository has established about Gale's question, as of November 2026.
Details and evidence are in the numbered notes; each section below links to them.

**The question.** Chomp on the board `N³`: a move takes a remaining cell and every cell above
it in all three coordinates, and whoever takes the poison cell `(0,0,0)` loses. Who wins, and
what is a winning first move? (Gale, *Tracking the Automatic Ant*, 1998, ch. 11; Nowakowski,
GONC5 problem D1.)

**Notation.** P means the player to move loses; N means the player to move wins. `X ∖ ↑m` is
the position after taking `m`. `B×β` is the box over a base `B` of height `β`.

**Short answer.** The question is still open. We have:
* exact control over every position with at most two infinite columns;
* a proof that 9 first moves lose;
* a reduction of Gale's `3×3×ω` to a search over towers, 38 of the 60 with `g ≤ 12` settled
  (all N);
* a proved P-position with four infinite columns (notes/25), the first with more than two.

Along the way we proved that Huddleston–Shurman's 2D side class is infinite (notes/13) and gave
a complete proof of their three-wide criterion (notes/16). Together these close the gaps in
their proof that `3×ω^ω` is P. Everything still open involves three or more infinite columns,
which is where our exact methods stop, with one exception so far (notes/25).

## 1. Exact reformulations

* **Winning first moves** form a finite antichain (no winning move lies above another), closed
  under permuting the coordinates. ([README](../README.md), facts 2 and 3)
* **P-pairs.** A first move `m` loses iff some reply `m'` makes `N³ ∖ (↑m ∪ ↑m')` a
  P-position. So the whole problem is about positions with two removed corners.
  ([04](04-ledger.md))
* **P-heights.** Huddleston–Shurman's Fundamental Theorem gives each base `B` a unique height
  `h(B)` with `B×h(B)` P. **`ω×ω×ω` is P iff `h(ω×ω) = ω`.** If `h(ω×ω) = n` is finite,
  `(0,0,n)` is a winning first move. Equivalently, `ω×ω×ω` is P iff the set `M_ω` from their
  proof contains every natural number but not `ω`. ([11](11-literature.md))

## 2. Proved

* **In Lean** ([05](05-lean.md)):
  * the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their permutations lose (9 moves), so
    `h(ω×ω) ≥ 3`;
  * `2×ω` and the infinite L-shape are P;
  * the 2D board `ω×ω` is won by `(1,1)`, `(0,2)` and `(2,0)`. Every other move lies above or
    below one of these, so by the antichain property none of them wins;
  * the side-class theorem for three-row Chomp (§6): `s(v) > v/5` for every `v`, the side class
    is infinite, `I(T) ≤ 2 s(T−1)`, `τ(x) ≤ (5x+3)/3`. This is checked from the rules of the
    game; the lemmas of Sheiner's preprint that the proof uses are proved in Lean too;
  * `[k,k,k−1]` is an N-position for every `k ≥ 3`: the corner bite never wins the `3×n`
    rectangle for `n ≥ 3` ([20](20-corner-and-matching.md)).
* **By the certified solver** ([07](07-arms.md)): every position whose infinite part is at most
  two columns wide (a "two-wide stalk") is decided exactly, by a repeated-state certificate for
  the eventually periodic sequences of Byrnes's theorem. This covers `2×ω`, Huddleston–Shurman's
  side-top positions and all two-wide options in the tower work below. The solver is now about
  2500 times faster than the first version on a benchmark P-position (10.5 min → 0.25 s).
* **Grundy values** ([09](09-rows.md), [10](10-hilbert.md)): a position with one infinite
  column has value `ω + γ`, in 2D and in 3D (proved).

## 3. The open first moves

| First move | It wins iff | Status |
| --- | --- | --- |
| `(0,0,3)` | the slab `ω×ω×3` is P | undecided ([02](02-slab.md), [08](08-family.md)) |
| `(0,b,c)`, `1 ≤ b ≤ c`, other than `(0,1,1)` | the L-prism `L(b,c)×ω` is P | undecided ([04](04-ledger.md)) |
| `(a,b,c)`, all `≥ 1` | three crossing slabs form a P-position | undecided ([03](03-three-planes.md)) |

* **The slab.** No rod reply answers any of 35 options of `ω×ω×3`, so the proof template for
  `2×ω` fails. Flattening (replying `(0,0,c')`) answers a few options and reduces the rest to
  the unknown winning moves of `ω×ω×2`. ([08](08-family.md))
* **`(1,1,1)`.** It wins the cubes `2×2×2` and `3×3×3`, and the finite truncations of its
  position weakly suggest it loses. Finite cubes are a poor guide anyway: `4×4×4` is won by
  `(2,3,3)`. ([03](03-three-planes.md), [README](../README.md) §3)
* **Columns of infinite height** (rods `S×ω`). Among small bases `S`, only the domino gives a
  P rod. *Conjecture 1.1*: that holds for every finite `S`. If it does, rods can never rule out
  `(0,0,n)` for `n ≥ 3`. ([01](01-rods.md))

## 4. The boundary: three infinite columns

Every case decided so far has at most two infinite columns. Every open case is the first one
with three or more:

* Gale's `3×3×ω`;
* the slab `ω×ω×3`, i.e. the first move `(0,0,3)`;
* the L-prisms `L(b,c)×ω`;
* Huddleston–Shurman's "`3×Ω` is recursive", which they believe but do not prove.

Exhaustive search with caps cannot decide such positions: some winning replies are very deep,
for example a cut at height 4107. What is missing is an exact method for a two-parameter
family of sequences, a "nested certificate". ([12](12-three-chains.md))

**A first P-position** ([24](24-three-by-three.md), [25](25-a-P-position-with-four-infinite-columns.md)).
`A = (ω,ω,1 | ω,ω,1 | 2,0,0)` has the `2×2` block of columns infinite, two columns of height
1 and one of height 2. **A is a P-position** (computer-assisted proof, notes/25). Every
infinite cut of A at height `z` is answered by cutting the poison column at `z+1` or `z+2`,
which leaves a finite P-position from one of three explicit families. Z3 proves that those
families, with eleven others and 106 small positions, are closed under replies. The one
family of options with irregular replies is N by strategy stealing. No other position with
attachments up to height 4 over the four-column shapes has replies of this regular kind. A
is not an option of `3×3×ω`, so this does not decide Gale's question.

**How deep a reply can be** ([26](26-census.md)). A census of all positions with infinite
columns in a capped region, with cuts tried up to height 50 to 110, shows that the second
candidate of notes/24, `B = (ω,ω,2 | ω,ω,2 | 2,2,0)`, is N: the cut of `(1,0)` at height 31
leaves a P-position with two infinite columns, which the solver certifies. B had passed
every check up to cut height 24. Finite P cuts can be just as far away: positions with two
infinite columns and attachments of height 8 or 11 have their only one at heights 381 and
978. So "every option up to height 13 is N" is weak evidence, and the positions `X_3` and
`T((0,2),2)` that it supported are simply open. Among the 371 positions with the `2×2` block
infinite and attachments up to 4 only A and its transpose are P (exact: every other one has
a finite P cut or a certified reply); with a taller third
column there is a second candidate, `A′ = (ω,ω,1 | ω,ω,1 | 9,2,1)`, which survives to cut
height 110 and is not regular. The same method classifies all 2177 positions with three or
four infinite columns and attachments up to 4: no P-position besides A and its transpose.
All tripod positions with attachments up to 4 and all 825 cross positions with attachments
up to 8 have a finite P cut.

**A law for these replies** ([27](27-how-a-chain-ends.md)). Inside the chain "cut `(1,0)` at
height `u`" the P-positions form a greedy matching, and the chain has a P member at the first
row where the diagonal needs a partner and none is free. Over 216 chains of the `2×2` block
this happens at height `u` with probability about `1/u`. So a chain that is alive at height
`s` is alive at `h` with probability about `s/h`: B's end at 31 is typical, A′ is the
survivor one expects among a few hundred chains, and no finite check separates a P-position
from a position whose reply is far away. The chains with a reason to live forever are the
regular ones, where the diagonal never needs a partner, and those are A's. For the `3×2`
block (the family of `X_g` and of the towers `T((0,2),g)`) exact runs show chains ending
about seven times more rarely, so replies there are likely far out of reach: `X_3`'s chain
is N up to height 42.

## 5. Gale's `3×3×ω`

**Reduction.** The options of `3×3×ω` are finite boxes (all N) and the **towers** `T(b,g)`:
cut the cells above-right of `b` to height `g` and leave the rest infinite. So `3×3×ω` is P iff
every tower is N. Up to symmetry `b` is one of `(0,1)`, `(0,2)`, `(1,1)`, `(1,2)`, `(2,2)`, and
for each `b` at most one `g` gives a P tower.

**Link to the main question.** `3×3×ω` is the position `N³ ∖ (↑(3,0,0) ∪ ↑(0,3,0))`. If it
were P, the first moves `(3,0,0)`, `(0,3,0)` and `(0,0,3)` would all lose. Conjecture 1.1
predicts the opposite: `3×3×ω` is N, so some tower is P.

**Exact results** ([12](12-three-chains.md), [24](24-three-by-three.md)). Of the 60 towers
with `g ≤ 12`, **38 are N and none is P**:

| `b` | exactly N for `g =` | open for `g ≤ 12` |
| --- | --- | --- |
| `(0,1)` | 1–11 | 12 |
| `(0,2)` | 1, 3, 4, 6 | 2, 5, 7, 8, 9, 10, 11, 12 |
| `(1,1)` | 1–12 | none |
| `(1,2)` | 1, 2, 5, 11 | 3, 4, 6, 7, 8, 9, 10, 12 |
| `(2,2)` | 1, 2, 3, 5, 6, 9, 11 | 4, 7, 8, 10, 12 |

For the open towers whose two-wide replies are decided exactly, none is P up to these heights:

| tower | two-wide replies ruled out up to |
| --- | --- |
| `T((0,1),12)` | `z = 14` |
| `T((0,2),2)`, `T((0,2),5)`, `T((0,2),7)`, `T((0,2),8)` | `z = 24`, `11`, `15`, `8` |

`T((1,1),12)` is N by a finite P cut at height 39, found with the dense table of finite
positions (notes/24). That table also gives every finite tower cut up to height 36; no other
open tower has one.

**The towers with `g = 0`** (notes/24) are rods over smaller bases. Four of the five are N.
The fifth is `331×ω`, the smallest undecided rod: no finite P cut up to height 72, and its
towers are N for `g ≤ 8` in five of its six types. If it is P, `3×3×ω` is N.

`T((0,1),10)` and `T((0,1),11)` are N: their cuts of `(2,0)` at heights 29 and 26 are exact
P-positions, found after the
solver's sequences were rank-coded and moved to a disk-backed arena (notes/12). The searches
are now limited by disk space rather than RAM.

**The `(0,1)` towers.** These have the row `y = 0` infinite (three infinite columns in a row)
with a finite `3×2` plane partition `R` on top; call the position `W(R)`. Every move from `W(R)`
leaves a finite position, a position with one infinite column (N), a two-wide stalk (decided
exactly), or `W(R')` with a smaller top part `R'`. So:

* `W(R)` is P iff it has no exact P option and every `W(R')` one move below it is N.
* **Side-set lemma.** Let the side set `𝒮_R` be the heights `z` at which cutting `(2,0)` to `z`
  leaves a stalk with no P cut of the poison column above `z`. If `𝒮_R` is infinite, `W(R)` is
  N by an exact reply. So **if every side set is infinite, every `(0,1)` tower is N**. This is
  a statement about finite Chomp.
* **Computation.** All 9075 positions `W(R)` with entries `≤ 8` have an exact P option, so all of
  them are N. For entries `≤ 9` the check was stopped after 12137 of 15730, also all N.
* **Side sets measured so far.** The 3-, 4- and 5-boxes have density 0.435 (up to `z = 179`),
  0.41 (up to 113) and 0.49 (up to 73), with no sign of thinning out.

If Conjecture 1.1 holds and the side sets are infinite, the P tower must be of type `(0,2)`,
`(1,1)`, `(1,2)` or `(2,2)`.

## 6. The 2D side class: a gap in Huddleston–Shurman, now closed

With an empty top part, the side set above is Huddleston–Shurman's **side class** `𝒮`: the
`x` for which no 3-row Chomp position `[h,h,x]` (row lengths) is P. Their proof that `3×ω^ω`
is P needs `𝒮` to be infinite, but they do not prove it, and their criterion (10–1) cannot
supply it without circularity. ([12](12-three-chains.md))

**Theorem (this repository, using Sheiner 2026; [notes/13](13-side-class-theorem.md)).** `𝒮` is
infinite. In fact `#(𝒮 ∩ [0,v]) > v/5` for every `v`, the upper density is at least `1/4`,
and the P-positions `[h,h,x]` with `h ≤ T` number at most twice the side elements below `T`.
This fills the gap in Huddleston–Shurman's proof
that `3×ω^ω` is P, given the cited lemmas. Their three-wide criterion (10-1) needs it as well:
for the positions `(ω+a, ω, ω)` it is equivalent to `𝒮` being infinite. The rest of their
argument passes a computational audit ([notes/15](15-hs-audit.md)): the two- and three-column
formulas are locally consistent on thousands of positions, the written proof's prescribed
replies always exist, and every named reply to a bite into `3×ω^ω` is P. **[notes/16](16-three-wide-proof.md)
proves (10-1)** in a closed form with two families. So the gaps in their §10 are closed: `3×ω^ω`
is P, given their Beanstalk Lemma and Side-Top Theorem and notes/13. Their two-column values
(9-1)–(9-5) are proved here for heights below `ω^ω` ([notes/18](18-two-column-values.md); (9-1)
by Z3 as a Presburger sentence), and (9-6), for all larger heights, in
[notes/21](21-two-column-above-omega-omega.md). A preprint draft is in [`paper/`](../paper/side-class.pdf).
As a corollary, the P-positions of `3×Ω` form a recursive set, which they believed but did not
fully prove.

* **Proof idea.** E. Sheiner (arXiv:2605.23837, 2026) proves that every `3×n` rectangle has a
  unique winning opening move. Equivalently, partners `τ(x)` and diagonal values `A(k,k)`
  never coincide. His row-start lemma says that a P-position `[p,p,r]` forces P-positions
  `[p,q,b_q]` with distinct `b_q < r` for every `r < q < p`. These `b_q` must be side elements
  or rows that are still unpaired at `q`.
  * Read the level `q` as time: row `x` is "alive" until it gets its P-position `[h,h,x]` at
    `q = h`. The lemma then says that a row which is going to die has at most as many levels
    left as there are older rows still alive (**remaining-lifetime lemma**,
    [notes/19](19-remaining-lifetimes.md)).
  * So if `n` rows are alive at level `T`, those that are still alive `n` levels later never
    die: they are side elements.
  * In the other direction, every older row still alive when `x` dies has picked `τ(x)` at a
    level of its own ([notes/20](20-corner-and-matching.md)). Since rows 0 and 2 always use the
    two levels just below `τ(x)`, this gives `τ(x) ≥ x+2` for `x ≥ 2` and `τ(x) ≥ x+3` for
    `x ≥ 4`. The first says the corner bite never wins `3×n`, `n ≥ 3`, and implies that the
    single-cube family has no finite P cut (previously checked only to 50001).
  * The diagonal values `A(a,a) ≤ 2a+1` force at least half of all rows below `t` to be alive
    at level `t`. Counting at level `T + n` gives the factor-2 inequality, and the rest follows.
  * The first proof (notes/12, "Theorem: the 2D side class is infinite") bootstrapped the
    slope of `τ` instead and gave weaker constants.
* **Exact computation** (`tools/side3row.cpp`) up to `x = 50000`:
  * `𝒮` has density `√2 − 1` with bounded discrepancy (within `[−0.50, 1.46]`);
  * the partner law holds: `τ(x) = x + #(𝒮 ∩ [0,x]) + ε` with `|ε| ≤ 2`.

  `𝒮` is not an exact Beatty sequence.
* **Still open:** the density `√2 − 1`, the partner law, the monotonicity of `τ`, and the sharp
  inequality (B′). Numerically the side elements below `T` and the P-positions `[h,h,x]` with
  `h ≤ T` agree in number to within 2 for every `T ≤ 50000`; the theorem gives a factor 2.
  Monotonicity of `τ` is equivalent to a greedy rule for `τ` (notes/19).
* An arXiv preprint dated 2026 (2608.11290) reports the same `√2` behaviour as a conjecture.
  It has not been checked here.
* **In 3D**, a new exact solver (`tools/attach3row.cpp`) computes 3-row Chomp with any finite
  attachment, with no cap on heights.
  * Every attachment up to the 3-box without a finite P cut shows the same structure: side
    density `≈ √2 − 1` and partners `τ(z) = √2·z + O(1)`. This is the "universality
    conjecture" in notes/12.
  * The 3-box family up to `z = 3000` has side density 0.4149, and at most 4 defects per
    partner for `z ≥ 12`.
  * Deep partners occur for small `z`, e.g. height 396 for `z = 14` in the 4-box family.

## 7. Grundy values

Everything computed fits Huddleston–Shurman's **Stratification Conjecture**: the leading term
of a Grundy value depends only on the large-scale shape, e.g. the number of infinite rows.
Heuristically, two infinite rows give finite values and three give `ω + k`, for example
`G(3×ω) = ω+1`. ([09](09-rows.md), [10](10-hilbert.md))

Their `ω×4` problem, the value of `4×ω`, is open. [notes/23](23-four-columns.md) proves that
every value below 46 occurs among the options (their claim, with a table) and that 46 does
not occur up to height 158. A computation finds 46 at height 1012, where they had the bound
480 and did not know whether it occurs at all. That is not proved: it holds unless a row
dies after level 12000, and the last death seen is at level 1752.

## 8. What would move things forward

A fuller list, in order of preference, with first steps and with what not to retry, is in
[notes/22](22-next-steps.md). It adds Huddleston–Shurman's open value `G(4×ω)`, outside
review of the preprint, and a Lean formalisation of the ordinal results.

1. **An exact method for three infinite columns.** It is needed to prove any tower, slab or
   L-prism P. The natural next step is a nested certificate for two-parameter families of
   sequences.
2. **Infinitude of the 3D side sets.** The 2D case is now proved (§6). The 3D case would settle
   every `(0,1)` tower.
   * Sheiner's lemmas carry over to 3-row Chomp with the box attached, except that cuts inside
     the box create "defects".
   * The argument still works if each partner has fewer than a third of its range defective and
     coincidences are finite. The data for the 3-, 4- and 5-boxes show at most a few defects per
     partner beyond the box height (notes/12).
   * Proving that defect bound is the open step, already for a single cube. An attempt at the
     cube ([notes/19](19-remaining-lifetimes.md), §8) found the 2D lemma above, and pinned down
     the obstacle. The lemma holds for the cube with an error term, the levels at which no
     older row helps. In the data there are 6 such levels among 270672. But a model with
     *random* extra blocked values satisfies every lemma we have, and there a row can live like
     a side row for a long time and then die, with almost all its levels of that kind. So the
     bound needs the specific structure of the blocked values, which are the 2D P-positions.
   * But the defect bound is not needed (notes/19, §9). The 3D side set of an attachment is
     infinite, with lower density at least `1/8`, if two statements hold from some row on:
     **(H4)** no partner `τ(r)` exceeds the diagonal value of a row `a ≥ r`, and **(L_K)** each
     row picks the partners of at most `K` older rows that die before it. Both are theorems in
     2D. In the data (H4) has no exception (cube to `z = 3000`; 3-, 4- and 5-boxes), and (L_K)
     holds with `K = 0` for the cube and `K ≤ 6` for the boxes. (H4) is the hard one: it says
     in particular that a row never outlives the first value it picked.
3. **One P tower of any type.** It would show `3×3×ω` is N and support Conjecture 1.1. The
   `(0,2)`, `(1,1)`, `(1,2)` and `(2,2)` towers deserve more compute than the `(0,1)` ones.
   * notes/17 explains why. Among positions with three or more infinite columns, only those
     whose two-wide families have a multi-cell growing block (such as the `(0,2)` towers), or
     which have no two-wide options at all (the cross shapes of the `(1,1)`, `(1,2)`, `(2,2)`
     towers), can plausibly be P.
   * Heuristic searches mislead here, because finite P cuts can be deep (height 70 for a small
     shape-`(3,1)` position). They should be searched far beyond the usual caps (`rodf -Q`).
4. **Memory.** The stored sequences use 4–6 bits per offset against an entropy of about 3.4
   bits. Closing that gap, or sharing one cache across many searches, would push the tower
   searches deeper.

## Notes

| Note | Topic |
| --- | --- |
| [01](01-rods.md) | Rods `S×ω` and finite P-heights; Conjecture 1.1 |
| [02](02-slab.md) | The slab `ω×ω×3` |
| [03](03-three-planes.md) | The candidate first move `(1,1,1)` |
| [04](04-ledger.md) | Ledger of first moves; P-pairs |
| [05](05-lean.md) | Lean formalisation |
| [06](06-search.md) | Proof-number search |
| [07](07-arms.md) | Exact solver for two-wide stalks |
| [08](08-family.md) | Looking for a P-family that answers `ω×ω×3` |
| [09](09-rows.md) | 2D ordinal Grundy values |
| [10](10-hilbert.md) | Leading Grundy terms and the Hilbert polynomial |
| [11](11-literature.md) | Literature: Huddleston–Shurman, Byrnes, Nowakowski, Gale |
| [12](12-three-chains.md) | Three infinite columns: 2D oracle, towers of `3×3×ω`, side sets |
| [13](13-side-class-theorem.md) | Theorem: the side class of three-wide Chomp is infinite |
| [14](14-01-towers.md) | The `(0,1)` towers of `3×3×ω`: proved, conditional, evidence |
| [15](15-hs-audit.md) | Audit of Huddleston–Shurman's three-wide theory and the proof that `3×ω^ω` is P |
| [16](16-three-wide-proof.md) | A complete proof of the three-wide criterion (10-1) and of `3×ω^ω` being P |
| [17](17-classes.md) | Classes by infinite shape; where P-positions with three or more infinite columns can live |
| [18](18-two-column-values.md) | Proof of Huddleston–Shurman's two-column values (9-1)–(9-5) below `ω^ω` |
| [21](21-two-column-above-omega-omega.md) | Proof of (9-6): two-column values for heights `≥ ω^ω`, by self-similarity at scales |
| [19](19-remaining-lifetimes.md) | The remaining-lifetime lemma, its consequences in 2D, and the obstacle for the cube |
| [23](23-four-columns.md) | Four columns: `G(4×ω) = mex(L)`; proved values up to height 107, `{1,…,45} ⊆ L`; computed: 46 first occurs at height 1012; the mechanism |
| [24](24-three-by-three.md) | `3×3×ω`: dense table of finite positions; `T((1,1),12)` is N; the rod `331×ω`; atlas of small positions; candidate P-position A with four infinite columns |
| [25](25-a-P-position-with-four-infinite-columns.md) | Theorem: `A = (ω,ω,1 \| ω,ω,1 \| 2,0,0)` is a P-position; the closed family (Z3) and the strategy-stealing lemma |
| [22](22-next-steps.md) | What to try next: directions in order of preference, first steps, and what not to retry |
| [20](20-corner-and-matching.md) | The corner bite never wins `3×n` (`n ≥ 3`), `G(3×n) ≥ 2`; the matching at a death time; failed attempts at the sharp 2D statements |
