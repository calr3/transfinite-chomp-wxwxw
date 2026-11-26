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
| `tools/` | C++ solvers: `box_chomp` (finite boxes), `chomp3`/`chomp3f` (capped DFS), `chomp3p` (df-pn with the rod oracle), `rodf` + `rod.h` (rods `S×ω`, exact for two-wide stalks), `rows` (2D ordinal Grundy values), `tower_scan`, `four_row_values`, `three_row_values` and `three_row_layers` (the same recurrence for three rows and every value, notes/30) (four-row Grundy values for `G(4×ω)`), `base3_table` (exact table of all finite positions over the `3×3` base, and a census of the positions with infinite columns); and `hs_oracle.py`, an exact oracle for 2D positions with up to three columns of height below `ω^ω`. |
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

For a self-contained summary of the whole problem as of November 2026, see
[`notes/00-overview.md`](notes/00-overview.md). For what to try next, see
[`notes/22-next-steps.md`](notes/22-next-steps.md).

* **Proved (Lean, `lean/`):** the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their
  permutations lose; `2×ω` and the infinite L-shape are P; the 2D board `ω×ω` has winning moves
  `(1,1)`, `(0,2)`, `(2,0)`; winning moves form an antichain; outcomes are symmetric. The
  side-class theorem for three-row Chomp (below: more than `v/5` of the numbers `0..v` are in
  the side class, for every `v`) is checked in Lean from the rules of the game, including the
  lemmas of Sheiner's preprint that it uses. So is a small new fact: taking only the corner
  cell never wins the `3×n` rectangle for `n ≥ 3`. And so is the main 3D result:
  **`A = (ω,ω,1 | ω,ω,1 | 2,0,0)` is a P-position** (`Chomp.posA_isP`, notes/29), a
  position below `3×3×ω` with four infinite columns. That proof gives every reply
  explicitly and uses no solver.
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
* **Three infinite columns (notes/12, 13):**
  * Gale's `3×3×ω` reduces to towers `T(b,g)`. 37 of the 60 with `g ≤ 12` are exactly N, and
    none is P. The newest are `T((0,1),10)` and `T((0,1),11)`, with two-wide replies at heights
    29 and 26. Finding them needed a solver whose cached sequences are rank-coded and kept on
    disk.
  * The `(0,1)` towers form a closed class. Every one of them is N if the side sets of 3-row
    Chomp with a finite attachment are infinite.
  * **Theorem:** the 2D case holds. Huddleston–Shurman's side class is infinite: it has more
    than `v/5` elements up to `v`, for every `v` (notes/13, using Sheiner 2026; machine-checked
    in Lean from the rules of the game, notes/05). The proof is now short. It rests on a new **remaining-lifetime lemma** (notes/19): a row that is
    going to get a P-position `[h,h,x]` has at most as many levels left as there are older
    rows still without one. This fills the step their proof
    that `3×ω^ω` is P leaves out. Their three-wide criterion (10-1) needs it too. For the
    positions `(ω+a, ω, ω)` it is equivalent to the side class being infinite.
  * **Theorem (notes/20):** `[k,k,k−1]` is an N-position for every `k ≥ 3`, so the corner bite
    never wins `3×n` for `n ≥ 3`, and every `3×n` rectangle has Grundy value at least 2. The
    proof is a ten-line induction, checked in Lean. The two sharper statements in the data
    (`τ` increasing; never more P-positions `[h,h,x]` with `h ≤ T` than side elements below
    `T`) were attempted and are not proved.
  * **Theorem (notes/16):** a complete proof of (10-1), in a closed form with two families.
    Together with notes/13 this closes the gaps in §10 of Huddleston–Shurman's proof that
    `3×ω^ω` is a P-position. It still uses their Beanstalk Lemma and Side-Top Theorem (both
    with complete proofs in the paper); their two-column values (9-1)–(9-5) are now proved for
    heights below `ω^ω` (notes/18: (9-1) by Z3 in Presburger arithmetic, the rest by
    transfinite induction). The audit is in notes/15.
  * **Theorem (notes/21):** their last two-column formula (9-6), for heights `≥ ω^ω`, which the
    paper only sketches. It is a case of a self-similarity statement: at every "scale" `Ω`
    (an ordinal where the diagonal values have caught up, `ω^ω` being the first),
    `G(Ω·u + a, Ω·v + b) = Ω·G(u,v) + G(a,b)` or `+ (a ⊕ b)`, for all ordinals `u ≥ v`. So all
    two-column Grundy values of ordinal Chomp now have proofs, and the recursiveness corollary
    no longer depends on an unproved formula.
  * **Four columns (notes/23):** Huddleston–Shurman's open value `G(4×ω)` is `mex(L)` for a
    set `L` of values of four-column positions. A new exact solver proves the values of
    `(ω,ω,x,y)` for all `y ≤ x ≤ 107` (a periodicity certificate shows which "rows" never
    die). So their statement that `L` contains every `g < 46` now has a proof and a table of
    witnesses; the last value, 24, arrives at height 107. No height up to 158 gives 46
    (proved). **Computed, not proved: `46 ∈ L`**, first at height 1012 (their bound was 480,
    and they did not know whether 46 is in `L`). This holds unless one of the 5.7 million rows
    alive at level 12000 dies later; the last of 6 million deaths is at level 1752. The data
    also show the mechanism: 46 lands on the diagonal only when none of about ten free columns
    can take it, which happened at heights 507, 601, 778 and 1012, with success the fourth
    time. Under the same assumption every value up to 56 is in `L`; the least one not seen up
    to height 1100 is 57. The mechanism applies to later values too, so nothing points to a
    finite `G(4×ω)`.
  * **`3×3×ω` (notes/24):** still open. A new exact table of all finite positions over the
    `3×3` base settles one more tower, `T((1,1),12)` (N, by a finite P cut at height 39),
    and shows that the rod `331×ω`, the smallest undecided rod and an option of `3×3×ω`, has
    no finite P cut up to height 72. A scan of all small positions with three or more infinite
    columns finds the first one that looks like a P-position for a structural reason:
    `A = (ω,ω,1 | ω,ω,1 | 2,0,0)`, four infinite columns. Every infinite cut of A at height
    `z` is answered by cutting the poison column at `z+1` or `z+2`.
  * **Theorem (notes/25): A is a P-position.** It is the first position with more than two
    infinite columns proved P here. The proof is computer-assisted: Z3 proves that an
    explicit set of finite positions (a two-parameter family, eleven one-parameter families,
    and 106 small positions) is closed under replies; the one family of options whose
    replies are irregular is handled by strategy stealing on a top cell; three small
    positions with two infinite columns come from the certified solver.
  * **A census of positions with infinite columns (notes/26).** A new pass of the table tool
    labels every position in a capped region whose columns are finite or infinite, with cuts
    of the infinite columns tried up to height 50 to 110. It is a search, not a proof: its
    labels depend on two truncations, and it mislabels positions whose only finite P cut is
    very high (examples at heights 381 and 978). Its candidates are then decided by the
    certified solver where that is possible. Results: **candidate B is N** (exact), by the
    cut of `(1,0)` at height 31, which leaves a certified P-position; earlier checks had
    found replies to all cuts up to height 24. **All positions with three or four infinite
    columns and attachments up to 4 are classified exactly** (2177 positions: rows of three,
    tripods, shape `310`, the `2×2` block): A and its transpose are the only P-positions, and
    every other one is N by a finite P cut or by a certified reply. A second
    candidate appears with a taller third column, `A′ = (ω,ω,1 | ω,ω,1 | 9,2,1)`: no finite P
    cut up to height 240, every option up to cut height 26 exactly N, no P option in the
    census up to height 110; it is not regular, so the proof of A does not carry over. All
    1001 tripod positions with attachments up to 4, and all 825 cross positions with
    attachments up to 8, have a finite P cut (exact). `3×3×ω`, the
    rod `331×ω`, `X_3` and `T((0,2),2)` stay open, and the evidence that the last two are P
    was weaker than it looked.
  * **How a chain of cuts ends (notes/27).** For a position with the `2×2` block infinite,
    the positions left by cutting `(1,0)` at height `u` form a chain, and one P member makes
    the position N. Inside a chain the P-positions form a greedy matching, and a member is P
    at the first row where the diagonal needs a partner and none is free (exact). Measured
    over 216 such chains (108 up to transposition), **a chain alive at height `u` ends there
    with probability about `1/u`** (constant 1.00, 208 ends): alive at `s` means alive at `h`
    with probability `s/h`. Fitted up to height 70, the law predicted 8.4 and 7.0 chains alive at heights 100
    and 120; a taller run found 8 and 8. It explains B (it ran out at 31) and makes A′ an
    expected outlier rather than a candidate. Only chains whose diagonal never needs a
    partner escape, and those are A's. In the family of the `3×2` block, which contains the
    towers `T((0,2),g)` of `3×3×ω`, exact runs on 35 roofs show chains ending about seven
    times more rarely: 12 of the roofs are N by a finite cut, 11 by a P chain member, 12 are
    open, and `X_3`'s chain is now exactly N up to height 42.
  * **Do irregular chains always end? (notes/28).** An attempt to prove it, which does not
    succeed. What is proved: three lemmas on where the ineligible cells of a chain are, and
    an example showing that they do not decide the question. What is measured: the `1/u`
    law comes from the pool of unused columns (a row with `k` of them has no partner with
    probability `δ^k`, `δ ≈ 0.43`), not from a mixture of chains; a model with that rule has
    survival `h^−γ`, `γ = ln(1/(1−ε))/ln(1/δ)` (proved for the model), and the measured `δ`
    and `ε` give `γ = 0.96` and `1.03` where the law's constant is 1.00 and 0.98. The
    constant is 1 because the diagonal cell is eligible about as often as its neighbours. A
    second census (attachments up to 5, 281 pairs of chains) confirms the law. A proof would
    need a structure theory of finite positions over the `2×2` base that does not exist.
    With attachments up to 5, 808 of the 812 positions with the `2×2` block infinite are
    decided exactly (362 by a finite cut, 444 by a certified reply, A and its transpose P);
    two positions and their transposes are open, with replies proposed at heights 68 and 42.
  * **Checks before circulating (notes/29).** The statement "A is P" is now proved in Lean
    from the rules of the game (`lean/Chomp/Block*.lean`, about 600 lines by hand and 3800
    generated by `scripts/lean_A_gen.py`; axioms `propext`, `Classical.choice`, `Quot.sound`).
    The three positions with two infinite columns that the earlier proof took from the
    solver are proved there too, with eleven more families that have period 2 in the
    height. A second SMT solver (cvc5) confirms the closure claims of notes/25. A literature
    check found nothing that anticipates the results; it led to two corrections in the
    drafts (credit to Brouwer et al., whose "constant rows" are the complement of the side
    class, and a more careful statement of what Byrnes's periodicity theorem gives).
  * **Three attempts on the broader problem (26 November 2026; notes/23 §8, notes/30,
    notes/31).**
    * *`46 ∈ L` for `G(4×ω)` cannot be certified* (notes/23, §8). The period of the row
      system grows from 23040 at height 107 to at least 276480 at height 200, so a
      periodicity certificate at height 1012 is out of reach by a factor of at least a
      thousand. The statement follows from a bound on death levels, which holds for all 6
      million dying rows in the data and is not proved.
    * *All Grundy values of three-row Chomp* (notes/30). `G(3×ω)` is infinite iff every
      positive integer is the value of some `(ω,ω,x)` or `3×x`, and this holds if for each
      `g` at least `g` rows have no position `[p,p,x]` of value `g`. Proved by certificate:
      every value up to 236 occurs, so `G(3×ω) ≥ 237`. Computed up to `x = 1000`: every value
      up to 1859 occurs, with `G(ω,ω,x) ≈ 1.857·x`. Every value layer looks like the side
      class (density `√2 − 1`, the hypotheses of notes/19 hold without exception for
      `x ≥ 100`), but Sheiner's counting argument has no slack and does not extend. No proof.
    * *Ordinal heights over the `3×3` base* (notes/31). The Base-Top Theorem that
      Huddleston–Shurman mention without stating it, proved, and computed with the certified
      solver for all 4704 attachments of the brick with heights up to 5: 1422 have no finite
      P cut, and the brick with such an attachment is a P-position at the height
      `ω·(j+1) + a` given by its restricted value (`ω`, `ω·2`, `ω+1`, `ω+2`, `ω·3`, …). The
      `2×2` block with attachments cannot be treated the same way: it needs the statement
      that no finite cut is P, which we can prove only for the empty attachment and for A.
    * All three stop at the same kind of statement: that a row of a recurrence of
      Sheiner's type never dies once it has lived past a certain level.
  * **Preprint drafts:** [`paper/side-class.pdf`](paper/side-class.pdf) writes up the 2D
    theorems (side class infinite, lower density `≥ 1/5`; the three-wide criterion; the
    two-column values; `3×ω^ω` P; `3×Ω` recursive).
    [`paper/three-by-three.pdf`](paper/three-by-three.pdf) writes up the results on
    `3×3×ω`: A is P (with the full proof, and the Lean proof), the matching inside a chain, B is N, the
    classification of the positions with three or four infinite columns, the finite cuts of
    cross and tripod positions, and the `1/u` law as an observation.
  * In 3D the same argument goes through up to bounded "defects", which the data confirm.
    Proving that bound, even for a single cube, is open. notes/19 shows why: the lemma
    survives with an error term (levels where no older row helps), and a model with random
    extra blocked values satisfies every lemma we have and still violates the bound.
  * The bound is not needed, though (notes/19, §9). The 3D side sets are infinite if two
    statements about partners and diagonal values hold. Both are theorems in 2D and hold in
    all the data (cube and 3-, 4-, 5-boxes). The harder one says that a row which survives to
    the first value it ever picked never gets a partner.
    Far out there are at most 4 per partner for the 3-, 4- and 5-boxes, and at most 7 (defect
    rate `≤ 0.14` for `z ≥ 100`) for the open boxes 10, 11, 12 (notes/14). Every attachment
    tested has side density `≈ √2 − 1`.
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
| Three chains | [`notes/12-three-chains.md`](notes/12-three-chains.md) | An exact oracle for 2D positions with three columns (Huddleston–Shurman §9–10), validated. Gale's `3×3×ω` reduced to a search over towers `T(b,g)`: 37 of the 60 with `g ≤ 12` are exact N (all of type `(0,1)` up to `g = 11`), none P. Some replies are deep: a two-wide stalk at height `2g`, or a poison cut at height 4107. The `(0,1)` towers lie in a class `W(R)` closed up to exactly decided options, and every `(0,1)` tower is N if certain 3D side sets are infinite. Their 2D case is the side class that Huddleston–Shurman use without proof. **We prove it is infinite** (notes/13), with positive lower density (at least `1/5`), using Sheiner's 2026 three-row lemmas, which closes that gap. Computed exactly to 50000 (`tools/side3row.cpp`), its density is `√2 − 1` with bounded discrepancy. All 9075 positions `W(R)` with entries `≤ 8` are exactly N. A new exact solver for 3-row Chomp with any attachment (`tools/attach3row.cpp`, no height cap) shows the `√2` structure is universal. Every attachment up to the 3-box without a finite P cut has side density `≈ √2−1` and partners `√2·z + O(1)`, and the box families have at most 4 defects per partner far out (3-box to `z = 2500`). The two-wide-stalk solver is now about 2500× faster on a benchmark P-position (10.5 min → 0.25 s): member-by-member certificates, bit masks, period groups and Brent cycle detection. Its memory, with offsets packed in 4–6 bits, now bounds the searches: rank-coding the cached sequences and keeping them on disk then settled `T((0,1),10)` and `T((0,1),11)` (exact P replies at `z = 29` and `26`); the open `g = 12` has no P two-wide reply up to `z = 14`. |
| Side-class theorem | [`notes/13-side-class-theorem.md`](notes/13-side-class-theorem.md) | Self-contained proof that Huddleston–Shurman's side class of three-wide Chomp is infinite: `#(𝒮 ∩ [0,v]) > v/5` for every `v`, upper density at least `1/4`, and the P-positions `[h,h,x]` with `h ≤ T` number at most twice the side elements below `T`. It uses Sheiner's 2026 three-row lemmas plus the remaining-lifetime lemma, and fills the step their proof that `3×ω^ω` is P leaves out. The bound `v/5`, the infinitude and the factor-2 inequality are machine-checked in Lean from the rules of the game. |
| `(0,1)` towers | [`notes/14-01-towers.md`](notes/14-01-towers.md) | Consolidated account of the `(0,1)` towers of `3×3×ω`: what is proved (closed class, side-set lemma, the 2D case, all `W(R)` with entries `≤ 8`), the conditional theorem (a defect bound), and the evidence. The open towers `g = 10, 11, 12` have no finite P cut up to height 300, 280, 260. |
| HS audit | [`notes/15-hs-audit.md`](notes/15-hs-audit.md) | Audit of Huddleston–Shurman's §8–§10. The two-column formulas and the three-wide criterion (10-1) pass deep local-consistency checks: every N-position tested has a P reply, sometimes deep (`ω+445`); no P-position has a P option; and a reply of the kind their proof prescribes always exists. Every named reply to a bite into `3×ω^ω` is P. (10-1) itself needs the side class to be infinite: for `(ω+a, ω, ω)` the two are equivalent. (10-1) is then proved in notes/16. |
| Three-wide proof | [`notes/16-three-wide-proof.md`](notes/16-three-wide-proof.md) | Huddleston–Shurman's criterion (10-1) in closed form: `(u,v,x)` with `ω ≤ x < ω^ω` is P iff it lies in one of two explicit families. Complete proof, using only their two-column values, Beanstalk Lemma and Side-Top Theorem, plus the side-class theorem, which enters exactly once. Corollaries: `3×ω^ω` is a P-position, given their §8–§9; and the P-positions of `3×Ω` form a recursive set, which they believed but had not fully proved (`𝒮` is decidable since `τ(x) ≤ 2x+1`). The constructive half is checked against the oracle on 20000 positions. |
| Classes | [`notes/17-classes.md`](notes/17-classes.md) | Positions below `3×3×ω` with three or more infinite columns, sorted by the shape of their infinite part (11 shapes). Only the row of three has a fixed-attachment two-wide family, where universality rules out P. The tripod's family grows by one cell; all seven tripod positions tested have a finite P cut. Shapes with a multi-cell growing block (e.g. the `(0,2)` towers) have side elements that are all blocked by cuts inside the block, so P-positions can live there. Cross shapes (`(1,1)`, `(1,2)`, `(2,2)` towers) have no two-wide options at all. Heuristic verdicts can be wrong: `(ω,ω,2 \| ω,2,2 \| ω,2,2)` looked P but has a finite P cut at height 70. |
| Corner bite, matching | [`notes/20-corner-and-matching.md`](notes/20-corner-and-matching.md) | `[k,k,k−1]` is N for `k ≥ 3` (the corner bite never wins `3×n`, `n ≥ 3`), hence `G(3×n) ≥ 2` and the single-cube family has no finite P cut; `[k,k,k−2]` is N for `k ≥ 6`. Both come from a matching between the rows still alive when a row gets its P-position and the levels below it. The note also records the failed attempts at monotonicity of `τ` and at the sharp inequality `I(T) ≤ s(T−1)`. |
| Remaining lifetimes | [`notes/19-remaining-lifetimes.md`](notes/19-remaining-lifetimes.md) | The lemma behind the short proof of notes/13, with its other consequences: a deadline `τ(r) ≤ r + n(r+1) ≤ (5r+3)/3`, no diagonal value below a partner, a criterion for when a row gets its P-position, side rows as bijections, and the equivalence of "`τ` is increasing" with a greedy rule. Numerically the side elements below `T` and the P-positions `[h,h,x]` with `h ≤ T` agree in number to within 2 up to 50000. Then the single-cube family: what carries over, the mechanism of its rare defects, and a random-block model showing that the defect bound needed there does not follow from lemmas of this kind. |
| Two-column values | [`notes/18-two-column-values.md`](notes/18-two-column-values.md) | Proof of Huddleston–Shurman's two-column Grundy values (9-1)–(9-5) for heights below `ω^ω`. (9-1) and two consequences are proved by Z3 as Presburger sentences (`scripts/hs91_z3.py`); (9-2)–(9-5) follow by a short transfinite induction. The three-wide proof now uses the paper only through the Beanstalk Lemma and Side-Top Theorem. |
| Two columns above `ω^ω` | [`notes/21-two-column-above-omega-omega.md`](notes/21-two-column-above-omega-omega.md) | Proof of (9-6), the two-column values for heights `≥ ω^ω`: a self-similarity theorem at every scale `Ω` (defined by two covering properties of the values below `Ω`), the fact that `ω^ω` is a scale and that scales are closed under products and suprema. Valid for all ordinals `u ≥ v`, not only `u < ω^ω`. One example value printed in the paper disagrees with its own formula. Checked as a mex recursion on random positions below `(ω^ω)^3` (`scripts/hs96_check.py`). |
| Four columns | [`notes/23-four-columns.md`](notes/23-four-columns.md) | Huddleston–Shurman's open `G(4×ω) = mex(L)`: a recurrence for the unrestricted Grundy values of four-row positions, a periodicity certificate for "this value never occurs", proved values of `(ω,ω,x,y)` for `x ≤ 107`, hence `{1,…,45} ⊆ L` with witnesses; no 46 up to height 158 (proved). Computed: 46 first occurs at height 1012, unless a row dies after level 12000. How it gets there. |
| `3×3×ω`, finite tables | [`notes/24-three-by-three.md`](notes/24-three-by-three.md) | `tools/base3_table.cpp`, an exact table of all finite positions over the `3×3` base. `T((1,1),12)` is N (finite P cut at 39); all finite tower cuts up to height 36. The towers with `g = 0`: the rod `331×ω` is the smallest undecided rod, `h(331) > 72`. An atlas of all positions with attachments up to height 2 and three or more infinite columns: 229 of 240 are N exactly. Candidate P-position `A = (ω,ω,1 \| ω,ω,1 \| 2,0,0)` with four infinite columns: every infinite cut has a finite reply one or two levels up (proved P in notes/25). |
| A P-position with four infinite columns | [`notes/25-a-P-position-with-four-infinite-columns.md`](notes/25-a-P-position-with-four-infinite-columns.md) | Theorem: `A = (ω,ω,1 \| ω,ω,1 \| 2,0,0)` is a P-position. Finite families `F1`–`F4`, `K1`–`K4` and the two-parameter family `G(c,d) = (c+2; d+2, c, d)` are P for all heights. Proof: a closed set of finite positions (Z3, `scripts/candidate_A_closure_z3.py`), a strategy-stealing lemma for the two-layer positions `[m+1, m, 1]×2`, and three certified stalks. |
| Census | [`notes/26-census.md`](notes/26-census.md) | `base3_table -T`: labels for all positions with infinite columns in a capped region, up to two truncations; checked against the definition. Candidate B is N (exact, reply at height 31). The 2177 positions with three or four infinite columns and attachments up to 4 are classified exactly: only A and its transpose are P; a second candidate `A′ = (ω,ω,1 \| ω,ω,1 \| 9,2,1)` survives to cut height 110. Finite P cuts can be very high (381, 978), which limits what the census can say. All tripod positions with attachments up to 4 and all 825 cross positions with attachments up to 8 have a finite P cut. The roofs over the `3×2` block: `T((0,2),1)` is N by a certified reply at height 4; `T((0,2),2)`, `(ω,ω,2 \| ω,ω,1 \| ω,ω,0)` and `X_3` are open, with their chain of cuts of `(1,0)` exactly N up to heights 24, 24 and 35. |
| How a chain ends | [`notes/27-how-a-chain-ends.md`](notes/27-how-a-chain-ends.md) | The matching inside a chain of cuts (exact rule: rows take the smallest free eligible partner; the pool of unused columns grows by one at every row without a partner). B, A and A′ row by row. A measured law: a chain alive at height `u` ends there with probability about `1/u` (216 chains, 208 ends, constant 1.00; it predicted the survivors at heights 100 and 120). Consequences: A′ is an expected outlier, checks "up to height `s`" leave probability `s/h` for a reply above `h`, and only regular chains (A's) are safe. Exact chains for the 35 roofs up to height 4 over the `3×2` block: 12 N by a finite cut, 11 by a P chain member, 12 open; there chains end about seven times more rarely. `X_3`'s chain is N up to 42, A′'s up to 59. |
| Do chains end? | [`notes/28-do-chains-end.md`](notes/28-do-chains-end.md) | An attempt to prove that irregular chains always have a P member; no proof. Exact lemmas (dead columns, cuts above the row form matchings, blocked cells) and a pattern showing they are not enough. The mechanism of the `1/u` law, measured: no partner with probability `δ^k` for a pool of `k` unused columns; no durable differences between chains. A model with a proved survival exponent `ln(1/(1−ε))/ln(1/δ)`, which the measured frequencies put at 0.96 and 1.03. A second census (attachments up to 5) with constant 0.98, and the exact classification of 808 of its 812 block positions (4 open). Corrections to notes/27: chains were counted with their mirror images, and eligible cells are not confined to a narrow band. Two conjectures (E: ends; R: rigidity) and what a proof would need. |
| Checks, Lean proof of A | [`notes/29-checks-and-lean-proof-of-A.md`](notes/29-checks-and-lean-proof-of-A.md) | `Chomp.posA_isP`: A is a P-position, machine-checked in Lean 4 from the rules of the game, with explicit replies (182 family-by-column lemmas as decision trees checked by `omega`, 114 small positions by `decide`), Lemma W, the Fundamental Theorem for one infinite column, and the 46 positions with two infinite columns under the proof. The three positions formerly certified by the solver are proved with eleven more families of period 2. cvc5 confirms the Z3 claims. Literature check: nothing anticipates the results; two attributions corrected. |
| Three rows, all values | [`notes/30-three-rows-all-values.md`](notes/30-three-rows-all-values.md) | The value of `3×ω`: a reduction to "for every `g`, at least `g` rows avoid the value `g`"; `G(3×ω) ≥ 237` proved by certificate; computed values to `x = 1000` (`G(ω,ω,x) ≈ 1.857·x`, every value up to 1859 occurs). Statistics of the value layers for `g ≤ 64`: density `√2 − 1` in each, (H4) and (L_K) of notes/19 without exception for `x ≥ 100`, no level both a death level and a birth value, a product form of Sheiner's row-start lemma. Why his count does not extend, and why any proof must use the size of the row. |
| The brick with attachments | [`notes/31-brick-with-attachments.md`](notes/31-brick-with-attachments.md) | Ordinal heights over the `3×3` base. The Base-Top Theorem for two tall columns with a finite attachment in all directions and a top (proved); the height at which the brick with an attachment is P, from its restricted value; the exact table for all 4704 attachments with heights up to 5. Why the `2×2` block with attachments cannot be treated the same way. |
| Next steps | [`notes/22-next-steps.md`](notes/22-next-steps.md) | Directions not yet started, in order of preference: `G(4×ω)`; the cube case with the corner theorem and the matching lemma; literature check and outside review; Lean for the ordinal results; the open towers. Each with what exists, a first step and the risk, plus a table of what was tried and where it stopped. |
| 5. Lean | [`notes/05-lean.md`](notes/05-lean.md) | Lean proofs that `2×ω` is P and that the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their permutations lose. Also the side-class theorem (`s(v) > v/5`, infinitude, the factor-2 inequality), machine-checked from the rules of three-row Chomp with no hypothesis (`SideClass.lean`, `ThreeRow.lean`, `ThreeRowBoard.lean`), and the corner-bite theorem of notes/20 (`Corner.lean`). |

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
| Padhi (2026), "Solutions to Five Challenge Problems…", arXiv:2608.11290, §4.7 | Conjecture 4.6: the diagonal families `(w,w,t)` and `(w,t,t)` of three-row Chomp are quasi-periodic with bounded discrepancy and slopes `1+√2`, `1+1/√2` (checked to `w = 600`). Our data extends this to 50000 and 20000 (notes/13). |
| Sheiner (2026), "Unique Winning Opening Move in Three-Row Chomp", arXiv:2605.23837 | Proves every `3×n` rectangle has a unique winning opening (Gale's uniqueness question for three rows), via the recurrence of Brouwer et al. Read and checked here: it is our lemma L1, and its row-start lemma drives our proof that Huddleston–Shurman's side class is infinite (notes/12). |

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
  value below 46, and 46 would need `a > 480`. They believe `ω·2`. See
  [`notes/23-four-columns.md`](notes/23-four-columns.md) for a proof of the first statement,
  and for a computation in which 46 does occur, at `a = 1012`.
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
