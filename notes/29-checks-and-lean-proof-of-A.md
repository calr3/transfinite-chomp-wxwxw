# Checks before circulating: a second solver, the literature, and a Lean proof that A is P

26 November 2026. Continues [notes/25](25-a-P-position-with-four-infinite-columns.md) and
[notes/28](28-do-chains-end.md). Positions are written by the heights of the nine columns in
the order `(0,0),(0,1),(0,2) | (1,0),(1,1),(1,2) | (2,0),(2,1),(2,2)`, `w` for an infinite
column; finite positions below A also as `(a; b, c, d | e, f | k)` for the heights of `(0,0)`;
`(0,1)`, `(1,0)`, `(1,1)`; `(0,2)`, `(1,2)`; `(2,0)`.

Three things were done to make the result "`A = (w,w,1 | w,w,1 | 2,0,0)` is a P-position"
safe to show to other people.

## Results

1. **A is P, machine-checked.** Lean 4 (core library, no Mathlib) proves `Chomp.posA_isP`:
   the set of cells `{x,y ≤ 1} ∪ {(x,2,0) : x ≤ 1} ∪ {(2,0,z) : z ≤ 1}` of `ℕ³` is a
   P-position of Chomp. The proof depends on the axioms `propext`, `Classical.choice` and
   `Quot.sound` only. It uses no SMT solver, no table and no solver certificate (§3).
2. **The three "certified" positions are now proved.** notes/25 took three positions with two
   infinite columns from the solver `rodf`. They are P-positions by an explicit closed set of
   finite positions: the set `S` of notes/25 with eleven more families, which have a parity
   condition, and four more small positions (§2). So the proof of A no longer rests on
   `rodf`.
3. **A second solver agrees.** cvc5 1.4.2 proves the same three statements as Z3 in
   `scripts/candidate_A_closure_z3.py`, and finds the expected counterexample when the
   exception for `W(m)` is removed (§1).
4. **Literature (§4).** A search found nothing that anticipates the P-position A, the
   infinitude of the side class, or the proof of Huddleston–Shurman's criterion, and Gale's
   questions are still listed as open. Two attributions in the drafts were wrong or
   incomplete and are corrected: the side class is the set of non-constant rows of Brouwer
   et al., who should be credited as the closest earlier work; and Byrnes's periodicity
   theorem is about finite positions, so it does not by itself decide positions with two
   infinite columns.

## 1. A second solver

`scripts/candidate_A_closure_z3.py 10 --cvc5` gives the script's formulas to cvc5 through its
z3-compatible interface: part 1 (the set `S0` is closed), part 2 (the four replies in the
proof of Lemma W) and part 3 (`S` is closed up to `W(m)`) are all proved, in about one minute.
With the exception removed, cvc5 returns the counterexample `F2` with the column `(2,0)`
removed, at height 9. The two solvers share no code, so this checks the solver. It does not
check the encoding; §3 does.

## 2. The three positions with two infinite columns

The proof of A in notes/25 answers three options of A by moving to

* `Σ1 = (w,w,1 | 1,1,0 | 1,0,0)`,
* `Σ2 = (w,2,1 | w,2,0 | 2,0,0)`,
* `Σ3 = (w,3,1 | w,3,1 | 1,0,0)`,

which the solver certified as P. A position with two infinite columns is P when

* every cut of the poison column leaves an N-position: a finite position, which needs a
  reply for every height;
* every cut of the other infinite column leaves an N-position: this is the Fundamental
  Theorem, one infinite column;
* every bite in a finite column leaves an N-position: a smaller position with two infinite
  columns, which needs one winning move.

**The tree.** Under `Σ1`, `Σ2`, `Σ3` and the two rods there are 46 positions with two
infinite columns. Seven are P: the rods `2×ω` in both directions, `Σ1`, its transpose,
`Σ2`, `Σ3`, and `Σ4 = (w,2,1 | w,1,1 | 1,0,0)`. The 39 others are N by one move: 32 by a cut
of the poison column at height 6 or lower, 7 by a bite to one of the seven.

**The replies to the finite cuts.** For `Σ1` and its transpose they are in `S` already
(`TW2`, `TW1`). For the others they follow a pattern of period 2 in the height:

| position | cut at `h` | reply |
| --- | --- | --- |
| `Σ2` | `(h; 2, h, 2 \| 1, 0 \| 2)` | cut `(1,0)` at `h−1` (`h` odd), at `h−3` (`h` even), from `h = 5` |
| `Σ3` | `(h; 3, h, 3 \| 1, 1 \| 1)` | cut `(1,0)` at `h−2` (`h` even), at `h−4` (`h` odd), from `h = 10` |
| `Σ4` | `(h; 2, h, 1 \| 1, 1 \| 1)` | cut `(1,0)` at `h−2` (`h` even), at `h−4` (`h` odd), from `h = 4` |

**The closed set.** The positions these replies leave, and what their own options need, are
six families with small `b` in which `a − c` depends on the parity of `c`:

| `(b, d \| e, f \| k)` | `c` even | `c` odd |
| --- | --- | --- |
| `(1, 1 \| 1, 0 \| 2)` | `a = c+3`, `c ≥ 2` | `a = c+1`, `c ≥ 3` |
| `(1, 1 \| 1, 1 \| 1)` | `a = c+3`, `c ≥ 2` | `a = c+3`, `c ≥ 1` |
| `(2, 1 \| 1, 0 \| 1)` | `a = c+1`, `c ≥ 2` | `a = c+3`, `c ≥ 1` |
| `(2, 1 \| 1, 1 \| 1)` | `a = c+2`, `c ≥ 2` | `a = c+4`, `c ≥ 1` |
| `(2, 2 \| 1, 0 \| 2)` | `a = c+1`, `c ≥ 2` | `a = c+3`, `c ≥ 3` |
| `(3, 3 \| 1, 1 \| 1)` | `a = c+2`, `c ≥ 6` | `a = c+4`, `c ≥ 7` |

The second line is the transpose of `TW3`. With the four small positions
`(9; 3,4,3 | 1,1 | 1)`, `(8; 2,4,2 | 1,1 | 1)`, `(5; 3,4,1 | 1,1 | 1)`, `(9; 3,3,3 | 1,1 | 0)` the
enlarged set (26 families as counted in the Lean file, 114 small positions) is closed under
replies up to `W(m)`. It was found by a greedy closure in the exact table of finite
positions: start from the replies above, and for each option without a reply in the set add
one P option, preferring a cut of `(1,0)` near the top. 219 positions up to height 44 were
added: the six types, and the four small positions.

So the P-positions `(a; b, c, d | …)` with `b ≤ 3` that the proof meets are periodic in `c`
with period 2, where those of `S` have period 1. This is the periodicity that the solver's
certificates express, written out.

## 3. The Lean proof

Files (in `lean/Chomp/`; `lake build` builds everything, under three minutes):

| file | lines | content |
| --- | --- | --- |
| `Block.lean` | 482, by hand | positions over the seven columns as height vectors; the seven bites; every option is a cut; every finite position is N or P; the closure principle; the Fundamental Theorem |
| `BlockFamilies.lean` | 3181, generated | the 26 families, the 114 small positions, `S_closed` |
| `BlockFinite.lean` | 115, by hand | Lemma W by strategy stealing; `S_P`: every position of `S` is P |
| `BlockA.lean` | 581, generated | the 46 positions with two infinite columns, the options of A, `posA_isP` |

**What is formalised.**

* *The game.* `Chomp.Basic` (notes/05): a position is a set of cells of `ℕ³`, a move takes a
  cell other than `(0,0,0)` with everything above it, and N/P are defined inductively.
  `posA` is defined directly as a set of cells, and `posA_eq` identifies it with the
  height-vector form used in the proof.
* *The closure principle* (`closed_isP`). If every option of a position of `S` is in `W` or
  has an option in `S`, and every position of `W` is N as soon as the smaller positions of
  `S` are P, then `S` consists of P-positions. One induction on the number of cells proves
  both statements, so the two-stage argument of notes/25 (first `S0`, then `S`) is not
  needed.
* *`S_closed`*: 182 lemmas, one for each family and column. Each gives the reply
  explicitly, as a decision tree. For example, for the family `(c+4; 3, c, 3 | 1,1 | 1)`,
  `c` odd, and a cut of `(1,0)` at `t`: cut the poison column at `t+2` if `t` is even and
  at least 6, at `t+4` if `t` is odd and at least 7, and there are six special cases for
  `t ≤ 5`. Lean checks each leaf with `omega`: the reply is legal, and the position it leaves
  satisfies the equations of the named family. The trees have between 1 and 11 leaves. The
  114 small positions come with a table of replies that Lean checks by evaluation
  (`decide`, in the kernel).
* *Lemma W* (`W_isN`): the stealing argument of notes/25 §3, with the four replies.
* *The Fundamental Theorem* (`fundamental`) for these positions. For a fixed finite part,
  at most one height of the poison column gives a P-position (two such positions would be
  an option of one another), so the heights that can be answered by a bite elsewhere are
  bounded; above the bound, the finite position is N only by a cut of its poison column,
  which is a finite P cut of the infinite position.
* *The infinite positions*: each of the seven P-positions with two infinite columns by going
  through its bites as in §2 (lemmas `fc_…` give the replies to the finite cuts), each of
  the 39 others by one move, then the options of A as in the table of notes/25 §5.

**How the generated part is made.** `scripts/lean_A_gen.py` holds the families as lists of
linear conditions. For each family and column it looks for replies on the members up to
height 26 (candidate heights: a constant, a variable plus a constant, a sum or difference of
two variables plus a constant), covers the cases greedily, and asks Z3 for a case that no
candidate covers until there is none. It then builds a decision tree over simple conditions
(`t = n`, `t < n`, `t` even, `t + n = v`, …), asking Z3 at each leaf whether the conditions
imply that the candidate works. Z3 is a search tool here: if it were wrong, Lean would
reject the file. The same script emits the positions with infinite columns. Running it takes
about one minute and reproduces the two generated files exactly.

**What had to be worked around.** A single `omega` call for "one of these eight replies
works" does not terminate in reasonable time: the nested minima and the alternatives
multiply. The decision trees keep each call small. `omega` also gives up on goals that
contain `True` as a conjunct, which `simp` produces; the generated proofs remove them.

**What the proof now rests on.**

| | notes/25 | now |
| --- | --- | --- |
| closure of `S` | Z3, two Presburger sentences | Lean, explicit replies; Z3 and cvc5 agree on the sentences |
| Lemma W | by hand | Lean |
| three positions with two infinite columns | solver certificates | Lean, with the families of §2 |
| `2×ω` | Lean | Lean (inside the same proof) |
| Fundamental Theorem | cited | Lean, for the positions used |
| the statement itself | prose | `Chomp.posA_isP`, 20 lines of definitions to read |

Someone who wants to trust the theorem has to read the definitions in `Chomp/Basic.lean`
(`Pt`, `take`, `Opt`, `Out`) and the definition of `posA`, and run `lake build`.

## 4. Literature

A search of the web, arXiv and the citation lists that could be reached (the full report is
summarised here; sources read in full are marked).

* **Gale's questions.** No solution or partial result was found for `3×3×ω`, for `ℕ³`, or
  for positions with several infinite columns. `ℕ³` is problem D1 in Nowakowski's "Unsolved
  problems in combinatorial games" (Games of No Chance 6, 2025; read), where Gale's prize is
  mentioned. Huddleston–Shurman's section on three dimensions covers a `2×2` base.
* **The side class.** Brouwer, Horváth, Molnár-Sáska and Szabó (Integers 5, 2005, §8.5–8.8;
  read) call a row `r` of three-row Chomp *constant* when `[q,q,r]` is P for some `q`. So the
  side class is the set of non-constant rows. They prove that there are infinitely many
  constant rows and that the `n`-th value `q` is at most `3n−1`, and they report numerically
  that the constant rows grow like `(1+1/√2)·n`, which is the density `√2−1` of the side
  class. No proof was found that infinitely many rows are not constant. The first draft
  now says this in its introduction.
* **Huddleston–Shurman.** None of the papers that cite them (about ten were found) address
  the side class, the gap in the proof for `3×ω^ω`, criterion (10-1) or recursiveness. They
  say themselves (p. 211) that recursiveness for `3×Ω` "has not been fully proved", and, on
  the same page, that positions with a finite part and a two-wide infinite stalk have a
  recursive set of P-positions, "not difficult to show", without proof.
* **Byrnes** (Integers 3, 2003, #G03; read): for a finite poset with two chains attached, the
  positions of a given Grundy value are eventually periodic along the chains. It is a
  statement about finite positions. The second draft attributed decidability for two
  infinite columns to it; it now cites Huddleston–Shurman's remark and names Byrnes's
  theorem as the mechanism.
* **Sheiner** (arXiv:2605.23837) and **Padhi** (arXiv:2608.11290) exist with the titles
  cited. Sheiner's result is the unique winning move in `3×n`; Padhi's §4.7 states the
  `√2` structure as a conjecture. Neither overlaps with the side-class theorem.

Not reached: MathOverflow, OEIS, zbMATH, Google Scholar, and Gale's book beyond a snippet
(the page with the `3×3×ω` question was confirmed, the chapter text was not read). So
"nothing found" is not "confirmed absent", and the drafts keep the words "to our knowledge".

## Tools

```
python3 scripts/candidate_A_closure_z3.py 10 --cvc5      # §1 (pip install cvc5)
python3 scripts/lean_A_gen.py                            # §3: writes the two generated Lean files
lake build                                               # checks everything
```
