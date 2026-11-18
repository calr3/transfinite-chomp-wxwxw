# The `(0,1)` towers of `3×3×ω`

A consolidated account of the `(0,1)` towers of Gale's `3×3×ω`: what is proved, what is
conditional, and the computational evidence. The derivations and the history are in
[notes/12](12-three-chains.md); the 2D theorem this builds on is in
[notes/13](13-side-class-theorem.md).

## The question

`3×3×ω` is P iff every tower `T(b,g)` is N (notes/12, Step 1b). For `b = (0,1)` the tower is
the position `W(□_g)`:
* the row `y = 0` (cells `(0,0)`, `(1,0)`, `(2,0)`) is infinite;
* the cells `(x,1)`, `(x,2)` form a `3×2` block of height `g`.

Write `W(R)` for the same position with any finite `3×2` plane partition `R` on top.

## What is proved

1. **Closed class.** Every option of `W(R)` is either decided exactly or is another
   `W(R')`. The options are:
   * a finite position, by cutting `(0,0)`;
   * N outright, by cutting `(1,0)`;
   * a two-wide stalk `S(z,R)`, by cutting `(2,0)`;
   * `W(R')` with `R'` one move below `R`.

   So `W(R)` is P iff it has no finite or two-wide P option (written "not `D(R)`") and every
   one-move `W(R')` is N.
2. **Side-set lemma.** Let `𝒮_R` be the set of `z` such that no P-position `[h,h,z | R]` with
   `h > z` exists, i.e. no P cut of the poison column of `S(z,R)` above `z`. If `𝒮_R` is
   infinite, then `D(R)` holds and `W(R)` is N.
3. **The 2D case `R = 0`.** `𝒮_0` is Huddleston–Shurman's side class. It is infinite, with
   lower density `≥ 1/60` (notes/13, via Sheiner's three-row lemmas).
4. **Every `W(R)` with entries `≤ 8` is exactly N** (9075 positions), each by a direct finite or
   two-wide P option. This was found by search and checked by the rod solver
   (`scripts/w3row.py`, `data/w3row/`). In particular `T((0,1),g)` is N for `g ≤ 9`; `g = 10, 11`
   follow from the two-wide replies at heights 29 and 26 (notes/12).
5. **Partial transfer of Sheiner's theory to `[a,b,c | R]`**, 3-row Chomp with a finite
   attachment, when no finite cut `[k,k,k | R∧k]` is P:
   * encoding, distinctness, alive rows, and a linear bound `f(a,a) ≤ 3a + M` all hold;
   * row-start propagation holds up to "defects";
   * defects caused by a cut inside the attachment number at most `M` per partner;
   * the topmost defect of a partner is either such a cut or comes with an exceptional
     P-position at its level. For the single cube, that is a 2D P-position.

## What is conditional

**Conditional theorem (notes/12).** For the box `□_g` without a finite P cut, suppose:
* (D) each partner `τ(z)` has fewer than `(τ(z) − z)/3 + K` defects, and
* (C) partners coincide with diagonal values only finitely often.

Then `𝒮_{□_g}` is infinite and `T((0,1),g)` is N. If this holds for every `g`, all `(0,1)`
towers are N.

## Evidence

The exact solver `tools/attach3row.cpp` computes every attachment under a box at once, with no
height cap. It is validated against the rod solver and the 2D and cube solvers (notes/12).

| box | range | partners | defects per partner, `z ≥ 4g` | coincidences | side density |
| --- | --- | --- | --- | --- | --- |
| `□_3` | `z ≤ 2500` | 1460 | at most 4 | 2 (values 8, 14) | 0.4149 |
| `□_4` | `z ≤ 1500` | 876 | at most 4 | 3 | |
| `□_5` | `z ≤ 1000` | 579 | at most 4 | 1 | |
| `□_10` | `z ≤ 200` (rows 600) | 104 | at most 7 | 4 | 0.408 |
| `□_11` | `z ≤ 180` (rows 560) | 93 | at most 5 | 3 | 0.437 |
| `□_12` | `z ≤ 160` (rows 520) | 77 | at most 6 | 2 | 0.410 |

The only large defect counts are at small `z`, at deep partners such as
`(396, 396, 14 | □_4)`. Those finitely many `z` only change the constants of the bootstrap.

**The open towers themselves** (`□_10`, `□_11`, `□_12`):
* The side densities in the last column are measured on `z ∈ [100, N/2]`.
* The defect rate (defects per level of a partner) is at most 0.36 for `z ≥ 4g`. It drops to
  at most 0.14, 0.07 and 0.12 for `z ≥ 100`, with at most 7, 4 and 6 defects per partner. So
  hypothesis (D) of the conditional theorem looks as safe for the open boxes as for the small
  ones.
* The mean partner slope `τ(z)/z` on `[100, N/2]` is 1.37–1.38, still approaching `√2` from
  below. The box shifts the partners down by a constant, e.g. `τ(z) − √2·z ∈ [−19, 10]` for
  `□_10`.
* The heuristic stalk programme (not exact, see notes/12) puts the first two-wide P reply of
  `T((0,1),g)` at `z = 29, 23, 35` for `g = 10, 11, 12`.
  * For `g = 10` the certified solver has now confirmed it exactly: `P_10(29)` is P, so
    **`T((0,1),10)` is N** (notes/12).
  * For `g = 11` the guess was wrong: `P_11(23)` is N, and the certified reply is `P_11(26)`.
    So **`T((0,1),11)` is N** too.
  * For `g = 12` the certified search reaches `z = 14`.

**Universality.** Every attachment `R ≤ □_4` without a finite P cut (247 of 490) has:
* side density between 0.411 and 0.420;
* mean partner slope `τ(z)/z` between 1.403 and 1.415, with `τ(z) − √2·z` bounded.

The single cube and the 2D game behave the same way. The conjecture: every such `𝒮_R` has
density `√2 − 1` and `τ_R(z) = √2·z + O(1)`. This is a 3D extension of Padhi's quasi-periodicity
conjecture for three-row Chomp (notes/13).

## Exact results from the new solver

* **Finite P cuts of the open towers** `T((0,1),g)`, `g = 10, 11, 12` (the cut `[h,h,h | □_g]`
  is a finite position, decided exactly): **none** for `h ≤ 300, 280, 260` respectively.
  Before this they were checked only to `h ≤ 40`. The same runs give the diagonal statistics
  of each box: partners and diagonal values coincide 4, 3, 2 times and both miss 7, 8, 10
  heights in `(2g+1, N/2]` (`N` the row bound); the diagonal stays within `2a + 1 + 28`.
* **Two-wide replies** cannot be decided by the tables alone. Partners can be arbitrarily deep
  for small `z`: the stalk of `T((0,1),9)` cut at 3 has its P cut at height 4107. The rod
  solver's certified search remains the only exact method there. With rank-coded sequences on disk it
  finds the replies of `T((0,1),10)` and `T((0,1),11)` at `z = 29` and `26` (P). For
  `g = 12` it finds none for `z ≤ 14`.

## Open

* Bound the defects, (D), for every box: the induction over attachments in notes/12. The single
  cube is the base case, and its defects all come from one resonant row (row 7).
* Universality, even just "`𝒮_R` is infinite".
* The other four tower types, whose options include three-infinite-column classes beyond `W`.
