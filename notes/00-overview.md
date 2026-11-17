# Chomp on ω×ω×ω: where things stand

A summary of what this repository has established about Gale's question, as of November 2026.
Details and evidence are in the numbered notes; each section below links to them.

**The question.** Chomp on the board `N³`: a move takes a remaining cell and every cell above
it in all three coordinates, and whoever takes the poison cell `(0,0,0)` loses. Who wins, and
what is a winning first move? (Gale, *Tracking the Automatic Ant*, 1998, ch. 11; Nowakowski,
GONC5 problem D1.)

**Notation.** P means the player to move loses; N means the player to move wins. `X ∖ ↑m` is
the position after taking `m`. `B×β` is the box over a base `B` of height `β`.

**Short answer.** The question is still open. We have exact control over every position with at
most two infinite columns, a proof that 9 first moves lose, and a reduction of Gale's
`3×3×ω` to a search over towers, with partial results. Along the way we proved that
Huddleston–Shurman's 2D side class is infinite, a step their proof that `3×ω^ω` is P needs. Everything still open involves three or
more infinite columns, and that is exactly where our exact methods stop.

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
    below one of these, so by the antichain property none of them wins.
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

## 5. Gale's `3×3×ω`

**Reduction.** The options of `3×3×ω` are finite boxes (all N) and the **towers** `T(b,g)`:
cut the cells above-right of `b` to height `g` and leave the rest infinite. So `3×3×ω` is P iff
every tower is N. Up to symmetry `b` is one of `(0,1)`, `(0,2)`, `(1,1)`, `(1,2)`, `(2,2)`, and
for each `b` at most one `g` gives a P tower.

**Link to the main question.** `3×3×ω` is the position `N³ ∖ (↑(3,0,0) ∪ ↑(0,3,0))`. If it
were P, the first moves `(3,0,0)`, `(0,3,0)` and `(0,0,3)` would all lose. Conjecture 1.1
predicts the opposite: `3×3×ω` is N, so some tower is P.

**Exact results** ([12](12-three-chains.md)). Of the 60 towers with `g ≤ 12`, **35 are N and
none is P**:

| `b` | exactly N for `g =` | open for `g ≤ 12` |
| --- | --- | --- |
| `(0,1)` | 1–9 | 10, 11, 12 |
| `(0,2)` | 1, 3, 4, 6 | 2, 5, 7, 8, 9, 10, 11, 12 |
| `(1,1)` | 1–11 | 12 |
| `(1,2)` | 1, 2, 5, 11 | 3, 4, 6, 7, 8, 9, 10, 12 |
| `(2,2)` | 1, 2, 3, 5, 6, 9, 11 | 4, 7, 8, 10, 12 |

For the open towers whose two-wide replies are decided exactly, none is P up to these heights:

| tower | two-wide replies ruled out up to |
| --- | --- |
| `T((0,1),10)`, `T((0,1),11)`, `T((0,1),12)` | `z = 25`, `18`, `14` |
| `T((0,2),2)`, `T((0,2),5)`, `T((0,2),7)`, `T((0,2),8)` | `z = 24`, `11`, `15`, `8` |

These searches are now limited by memory (about 13–15 GB per tower), not by time.

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
infinite; in fact it has lower density at least `1/60` and upper density at least `(3−√3)/6 ≈ 0.211`. This fills the gap in Huddleston–Shurman's proof
that `3×ω^ω` is P, given the cited lemmas. Their three-wide criterion (10-1) needs it as well:
for the positions `(ω+a, ω, ω)` it is equivalent to `𝒮` being infinite. The rest of their
argument passes a computational audit ([notes/15](15-hs-audit.md)): the two- and three-column
formulas are locally consistent on thousands of positions, the written proof's prescribed
replies always exist, and every named reply to a bite into `3×ω^ω` is P. **[notes/16](16-three-wide-proof.md)
proves (10-1)** in a closed form with two families. So the gaps in their §10 are closed: `3×ω^ω`
is P, given their §8–§9 (two-column values, Beanstalk Lemma, Side-Top Theorem) and notes/13.

* **Proof idea.** E. Sheiner (arXiv:2605.23837, 2026) proves that every `3×n` rectangle has a
  unique winning opening move. Equivalently, partners `τ(x)` and diagonal values `A(k,k)`
  never coincide. His row-start lemma says that a P-position `[p,p,r]` forces P-positions
  `[p,q,b_q]` with distinct `b_q < r` for every `r < q < p`. These `b_q` must be side elements
  or rows that are still unpaired at `q`.
  * If `𝒮` were finite, this would bootstrap the bound `τ(x) ≤ 2x+1` down to slopes `3/2, 4/3,
    …`, giving more than `2/3` of all numbers as partners.
  * But the diagonal values `A(a,a) ≤ 2a+1` occupy at least half of them.
  * Details and numerical checks of every ingredient are in notes/12, "Theorem: the 2D side
    class is infinite".
* **Exact computation** (`tools/side3row.cpp`) up to `x = 50000`:
  * `𝒮` has density `√2 − 1` with bounded discrepancy (within `[−0.50, 1.46]`);
  * the partner law holds: `τ(x) = x + #(𝒮 ∩ [0,x]) + ε` with `|ε| ≤ 2`.

  `𝒮` is not an exact Beatty sequence.
* **Still open:** the density `√2 − 1` (even a positive lower density), the partner law, the
  monotonicity of `τ`, and the sharp inequality (B′).
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
`G(3×ω) = ω+1`. Their `ω×4` problem stays out of reach. ([09](09-rows.md), [10](10-hilbert.md))

## 8. What would move things forward

1. **An exact method for three infinite columns.** It is needed to prove any tower, slab or
   L-prism P. The natural next step is a nested certificate for two-parameter families of
   sequences.
2. **Infinitude of the 3D side sets.** The 2D case is now proved (§6). The 3D case would settle
   every `(0,1)` tower.
   * Sheiner's lemmas carry over to 3-row Chomp with the box attached, except that cuts inside
     the box create "defects".
   * The bootstrap still works if each partner has fewer than a third of its range defective and
     coincidences are finite. The data for the 3-, 4- and 5-boxes show at most a few defects per
     partner beyond the box height (notes/12).
   * Proving that defect bound is the open step.
3. **One P tower of any type.** It would show `3×3×ω` is N and support Conjecture 1.1. The
   `(0,2)`, `(1,1)`, `(1,2)` and `(2,2)` towers deserve more compute than the `(0,1)` ones.
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
