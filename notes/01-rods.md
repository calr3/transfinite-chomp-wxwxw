# Idea 1: boxes and rods with one infinite axis

**Question.** For which finite cross-sections `S` (Young diagrams) is the rod `S×ω` a
P-position, i.e. what is `h(S)`, the Huddleston–Shurman P-height? (`S×β` is P exactly for
`β = h(S)`.)

**Why it matters for `ω×ω×ω`.** Taking `(0,j,0)` in `ω×ω×n` leaves `j×n×ω`. So if `j×n×ω` is P
for some `j`, the first move `(0,0,n)` loses (README, fact 7).

## Tools

| Tool | What it does |
| --- | --- |
| `tools/rodf.cpp` | Rods `S×ω` with the completing-height reduction (below). It also gives exact finite P-heights (`-H T`) and exact `f` values (`-f`). |
| `tools/chomp3.cpp`, `tools/chomp3f.cpp` | General positions on `N³` stored as antichains of eaten cells. `chomp3f` is the same algorithm about 2.3× faster, and the two agree position for position. |
| `scripts/rods.py`, `scripts/pheights.py` | Sweeps over all Young diagrams up to a given size. |

**Completing-height reduction (exact for finite positions).** Write a position as the height `a`
of the poison column plus the heights `r` of the other columns ("the rest"). If `a` is at least
the maximum of `r`, then `(a, r)` is an option of `(a', r)` for every `a' > a`. So at most one
`a` makes `(a, r)` P; call it `f(r)`.
* `f(r)` is NONE if some cut of the poison column below `max r` is P.
* Otherwise `f(r)` is the least `a ≥ max(1, max r)` not in `{f(r') : r'` a move on the rest`}`.

This removes a whole dimension from the search.

**Infinite heights and caps (heuristic).** A column of height ω can be cut at any height, so a
search must stop somewhere. We cut only up to `ALPHA·H + D`, where `H` is the largest finite
coordinate in the position. The cap is *relative*: once a move creates finite heights, the
infinite parts can still be cut above them. A fixed cap would turn `2×ω` into the finite box
`2×(cap+1)`, which is N by strategy stealing, although `2×ω` is P.
* An N result is **exact** when its witness is a finite P-position.
* A P result is never exact for an infinite position.

Answers are checked by re-running with larger caps.

**Validation.** Both solvers reproduce every known case:
* finite boxes: `2×5`, `5×5`, `2×2×2`, `3×3×3`, `4×4×4` match `box_chomp`;
* `1×ω` N, `2×ω` P, `3×ω` N, `2×2×ω` N, `2×3×ω` N;
* `ω×ω` has exactly the winning moves `(1,1)`, `(0,2)`, `(2,0)`;
* `ω×ω×2` N.

Exact `f` values agree with 3-row Chomp, e.g. `(3,1,1)`, `(3,2)` and `(2,2,1)` are P.

## Results

### Rigorous, by hand (using `2×ω` P)

**Domino rule.** `S×ω` is N whenever one cut of the base leaves the domino, which happens when:
* `S` is a single row or column of length at least 3, by cutting it to length 2; or
* the first column of `S` has exactly 2 cells, by taking `(1,0,0)`; or
* the first row of `S` has exactly 2 cells, by taking `(0,1,0)`.

In particular, `1×k×ω` is N for `k ≠ 2`, and `2×k×ω` is N for `k ≠ 1`. So the table `R` of
rectangles `j×k` with `j×k×ω` P has `(1,2)` and `(2,1)` as its only entries in rows and columns
1 and 2.

### Exact, by finite computation: finite P-heights

A non-rectangular `S` has no top cell, so `S×t` can be P for a finite `t`. When it is, `h(S) = t`
exactly, and `S×ω` is N with winning move `(0,0,t)`. A rectangle `S×t` is always N by strategy
stealing (except `1×1×1`), so rectangles never have a finite P-height.

Shapes are written as column heights (`321` is the 3-step staircase), up to transposition.
`> 20` means no P-height at most 20.

| `S` | `h(S)` | | `S` | `h(S)` | | `S` | `h(S)` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `21` | 1 | | `411` | 2 | | `52` | 3 |
| `31` | 5 | | `321` | 5 | | `511` | > 20 |
| `32` | 1 | | `41` | > 20 | | `43` | 1 |
| `311` | 1 | | `51` | > 20 | | `421` | 9 |
| `42` | 10 | | `61` | > 20 | | `4111` | 1 |
| `331` | > 20 | | `71` | > 20 | | | |

Known transfinite values for comparison (H–S): `h(2) = ω`, `h(3) = ω^ω`, `h(22) = ω³`.

The sizes vary a lot (1, 2, 3, 5, 9, 10, ...). Shapes `k1` with `k ≥ 4` have none up to 20,
probably because `h(k1)` is transfinite.

### Heuristic: rods `S×ω` (caps `a2d6` and `a3d10`)

* Every Young diagram with at most 8 cells gives N, except the domino `2` and `511` (the hook
  with arms 5 and 3), which timed out at both settings. The 9-cell shapes reached before the
  sweep was stopped (`9`, `81`, `72`, `711`, `63`) are N too. No new P rod appeared.
* Many N results are exact (finite P-height witnesses). The rest are N via the domino rule, or
  heuristic.
* "cap-dependent" rows in the raw output differ only in exact versus heuristic, or in a timeout,
  never in P versus N.

### Undecided: `3×3×ω`

Gale singled out this case in 1998 as "a possibly simpler question" than `ω×ω×ω`, asking
whether `3×3×ω` is a first-player win ("Any takers?"). See `notes/11-literature.md`.


* `3×3×ω` is the first rectangle that matters for `ω×ω×3`.
* It is N at small caps (`a1d3`, `a1d5`, `a2d3`), but the "winning" move changes with the cap:
  `(0,1)` at height 2, `(0,1)` at height 5, `(1,1)` at height 2. These are cap artefacts.
* Runs with `a2d5`, `a2d6` and `a3d4` each exceeded 10 minutes and about 2 GB without finishing.
* Its f-tables cover 8-cell rests with heights of 40 or more, which is out of reach for
  exhaustive search.

## Conclusions

1. **Conjecture 1.1.** `S×ω` is P iff `S` is the domino, i.e. `h(S) = ω` only for the domino.
   This fits `h(22) = ω³` and `h(3) = ω^ω`, and the idea that P-heights grow with `S`.
2. If Conjecture 1.1 holds, `R = {(1,2),(2,1)}`, and **this route cannot rule out `(0,0,n)` for
   `n ≥ 3`**. Those moves have to be studied directly (Idea 2). Without the conjecture, `3×3×ω`
   is the first open case.
3. A side result: an exact table of finite P-heights. It shows that P-heights are irregular even
   for small shapes. This is a new dataset as far as we know, and could be extended and compared
   with the Huddleston–Shurman theory.
4. A lesson about the tools:
   * Exhaustive search with relative caps is fine for one infinite axis and small cross-sections.
   * It fails at about 8 cells with heights in the tens, which is where 3D Chomp itself becomes
     hard.
   * Search order matters a lot when heuristic early exits are used. A different canonical
     orientation took the `ω×ω` check from 95 positions to more than 60 million.

## Raw data

The sweep outputs are summarised above. To reproduce them (`rods.py` takes about 5 minutes per
hard shape):

```
g++ -O3 -march=native -std=c++17 -pthread -o rodf tools/rodf.cpp
python3 scripts/rods.py ./rodf 9 300        # S x omega, two cap settings
python3 scripts/pheights.py ./rodf 9 20 120 # exact finite P-heights
./rodf -a 2 -d 6 333                        # 3x3 x omega (does not finish in 10 min)
```
