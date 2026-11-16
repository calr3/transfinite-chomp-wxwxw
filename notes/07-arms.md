# Idea B: an exact arm solver (certified periodicity)

**Goal.** Replace the heuristic caps with proofs, at least for the simplest infinite parts.

## The method (`tools/rod.h`, `typeI`)

Work in rod form: a finite cross-section `S` (a Young diagram) with column heights in
`N ∪ {ω}`. Suppose the infinite part is a **two-wide stalk**: the poison column plus one other
column `c` are infinite and every other column is finite. Then `c` is `(0,1)` or `(1,0)`, because
any cell below an infinite column must itself be infinite.

* **The infinite family.** The only infinite family of options is the cuts of the poison column
  at heights `z`, which leave `(z, c at z, R)`. Here `R` is the finite fixed part. Moves inside
  `c` remove the infinite part and are N.
* **The sequence to decide.** Let `F_R(z)` be the completing height of `(c at z, R)`, i.e. the
  poison height that makes the position P. Unfolding its definition, `F_R(z)` is the least
  `a ≥ z` not in:
  * `{F_R(z') : z' < z}`, the cuts of `c`;
  * `{F_R'(z)}` for `R'` a move on `R`. These never touch `c`;
  * a finite set of constants, the cuts of `c` at heights up to the largest finite height.

  `F_R(z)` is NONE once an earlier cut is P. The cut at `z` is P iff `F_R0(z) = z`.
* **The certificate.** Only the offsets `a − z ≥ 0` matter. So once `z` passes every constant,
  the system over all `R` in the closed family is a deterministic machine. Its state is, for each
  `R`, a NONE flag and the set of pending offsets. The simulation stops when a state repeats.
  From then on everything is additively periodic, so the family is **decided exactly**. This is
  the argument of Landman's FSM proof of additive periodicity for the rows of Wythoff's game.
  Huddleston–Shurman say this case (one two-wide stalk) is "recursive", and this makes it
  concrete.

When the certificate succeeds, `pw` returns **exact P** if every other option is exactly N.
Before, a P result for an infinite position was never exact.

## Validation

* `2×ω` is now proved P by the solver itself, by a repeated state with period 1. It no longer
  depends on the Lean proof.
* Every result that rests on `2×ω` became exact: the domino rule, `3×ω`, `2×2×ω`, `2×3×ω`,
  `k×ω`, and so on.
* The refactor into `rod.h` gives byte-identical output to the old `rodf` on all test cases.
* The heuristic mode (`-x 0`) agrees with the certified answers on every case checked, at
  increasing caps (`a2d6`, `a3d10`, `a4d20`).

## New exact results

**A Wythoff-like family.** Take the cross-section `211`, with cells `(0,0)`, `(0,1)`, `(1,0)` and
`(2,0)`. Make the poison column and `(1,0)` infinite, give `(0,1)` height `a` and `(2,0)`
height `b`. Then `T(a,b)` is P **exactly** for:

| `a` | 0 | 1 | 2 | 3 | 4 | 5 | 6 and up |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `b` | 0 | 1 | 4 | 2 | 5 | 3 | none (checked for all `b ≤ 30` and `b ∈ {40, …, 200}`) |

Each `a` has at most one partner `b` and vice versa, by the antichain lemma, so the P-positions
form a partial permutation, like Wythoff pairs.

**Why it stops at `a = 6`.** `211` has finite P-height 5 (`211×5` is P). Every position over
`211` whose heights are all at least 5 is therefore N: cutting everything at height 5 leaves the
P-position `211×5`. In general:

> If `S` has a finite P-height `t`, every position over `S` with all heights `≥ t` is N. So
> families over such shapes have only finitely many P-positions.

**Rod sweep.** Re-running the sweep of Idea 1 with the certified mode makes the results exact,
including `2×ω` (P) and every result via the domino rule:

* All Young diagrams with at most 8 cells were re-run, at 120 s per cap setting.
* **Every finished answer is exact** except `5111`, which is N but only heuristically. Before,
  about 15 answers were heuristic: `3`, `4`, `22`, `5`, `41`, `6`, `51`, `33`, `7`, `61`, `8`,
  `71`, `62`, `53` and `44`, all via the domino.
* The only P rod is still the domino `2`, now **proved**.
* Timeouts: `511`, `331` and `611` at both settings. `421` and `4211` time out at `a2d6` but are
  exact N at `a3d10`.

## The oracle in df-pn

`chomp3p` now converts positions with exactly one unbounded axis into rod form and asks
`rod.h` for the answer, with a work budget per call (see `notes/06-search.md`). This corrected
two errors from the cap heuristic. The first:

* df-pn alone claimed the reply `(4,0,0)` to `L(1,2)×3` reaches a P-position.
* The oracle shows that position is **N exactly**: taking `(1,0,2)` leaves a two-wide-stalk
  position that is **P exactly**.

## Limits

* Wider infinite parts, with three or more infinite columns, bring in two-parameter families: a
  cut inside the infinite block leaves two blocks at different heights. This is the general case
  of the Huddleston–Shurman Stratification Conjecture, and the method does not reach it.
* The rods that matter most, `3×3×ω` and the arms of the L-prisms with cross-sections such as
  `1×3` and `2×3`, have wide infinite parts. They remain heuristic.
* The certificate assumes the pending offsets stay bounded, so that a state repeats within
  `ZSIM = 4000` steps. Otherwise the family is reported as undecided and the caps are used.
  Every family met so far was certified, typically within a few dozen steps.
