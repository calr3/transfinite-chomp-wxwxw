# Idea A: proof-number search, a table of known P-positions, move ordering

**Motivation.** The depth-first solver (`chomp3f`) timed out on positions we can solve by hand,
e.g. `ω × L(1,1)`, which is won by the single reply `(1,0,0)`. Depth-first search tried the moves
`(0,y,z)` first and never came back to `x = 1`.

## The new solver `tools/chomp3p.cpp`

It keeps the same positions, moves, caps and exact/heuristic tags as `chomp3f`, and changes the
search:

* **df-pn** (depth-first proof-number search, Nagai 2002) with a transposition table.
  * `φ(n)` is the cost to prove "the player to move wins": the minimum of `δ` over the children.
  * `δ(n)` is the cost to prove "the player to move loses": the sum of `φ` over the children.
  * The search always expands the child that currently looks cheapest to prove.
* **Known P-positions** are seeded into the table as exact: `2×ω` and the infinite L-shape, in
  every orientation. N results witnessed by them become exact.
* **Move ordering** breaks ties: finite children first, then fewer unbounded axes, then fewer
  generators.
* A time limit (`-t`), with the answer `unknown` when it is reached.

Validation: the finite cubes `3×3×3` and `4×4×4` give the same winning moves as `box_chomp`;
`ω×ω` gives exactly `(1,1)`, `(0,2)`, `(2,0)`; and `2×ω`, `3×ω`, `2×2×ω`, `ω×ω×2` and
`ω×L(1,1)` all come out right.

## Benchmark (global caps `-a 1 -d 2 -g 1`, 300 s per position)

| Position | `chomp3f` (plain DFS) | `chomp3p` (df-pn) |
| --- | --- | --- |
| `ω × L(1,1)` | timeout (150 s) | **N exact, 1 expansion** |
| `ω×ω×3`: floor + wall of height 3 | timeout (600 s) | **N** (heuristic), 36 s |
| `L(1,2)×3` | timeout (300 s) | **N** (heuristic), 0.7 s, but see below |
| `ω×ω×3` options `(0,1,2)`, `(0,2,2)` | timeout | unknown (16 M expansions) |
| `L(2,2)×3`, `3×3×ω`, `U` option `B(1,2)` | timeout | unknown |
| `U`, `ω×ω×3`, `ω³` | timeout | unknown |

df-pn is a big improvement where a short proof exists. It does not crack the positions with a
full slab or plane.

## The caps are the weak point, not the search

df-pn answered `L(1,2)×3` with the reply `(4,0,0)` (canonical orientation), claiming the result
is P. That result has only **one** infinite direction: a `2×4×3` block with a rod of
cross-section `1×3` along `x`. So the exact rod solver can check it (Idea B, `notes/07-arms.md`):

* the claimed P-position is in fact **N, exactly**: cut the top layer of the rod at `x = 1`;
* that move leaves a block plus a rod of cross-section `1×2` (a two-wide stalk), which the
  certified analysis proves **P**. The heuristic rod mode agrees at caps `a2d6`, `a3d10` and
  `a4d20`;
* df-pn itself calls that two-wide-stalk position N at `a1d2` and `a2d4`, and P at `a1d4`.

So at small caps the answers of `chomp3f` and `chomp3p` can be wrong in either direction, even
when the search is fast. `L(1,2)×3` itself is still open. Its supposed winning reply was
wrong, but another reply may exist.

## The hybrid: df-pn with the rod solver as an oracle

`chomp3p` now hands a position with exactly one unbounded axis to the rod solver (`rod.h`):
* when its infinite part has at most two cells besides the poison (`-W`), or its cross-section
  has at most 6 cells;
* with a work budget per call (`-B`, default 20000 evaluations). Calls that exceed it are
  abandoned and df-pn expands the position itself.

The answers go into the transposition table with their exact flags. Benchmark, same caps:

| Position | df-pn alone | hybrid |
| --- | --- | --- |
| `ω × L(1,1)` | N exact | N exact |
| `L(1,2)×3` | N, via a reply that is really N | unknown (177 s, 6144 oracle calls) |
| `3×3×ω` | (not solved) | unknown (105 s) |
| floor + wall 3, other slab options | N in 36 s / unknown | unknown |
| `U`, `ω×ω×3`, `ω³` | unknown | unknown |

The hybrid is **slower but honest**. Twice it overturned a wrong small-cap answer:

* `L(1,2)×3` and `3×3×ω` were both "won" by df-pn with replies to the same position `Q*`:
  three infinite rows (`3×ω`) with a finite `3×2` block on top.
* The rod solver shows `Q*` is **N exactly**: cut everything at height 11, leaving a finite
  P-position, or cut cell `(2,0)` at height 6. df-pn's caps (`1·2 + 2 = 4`) never reach
  height 11, so it took `Q*` for a P-position.

So the small-cap results of Ideas 2 and 3 should be read as weak hints only, and the hybrid is
the tool to use from now on.

## Conclusion and next step

* df-pn plus the known-P table solves easy positions instantly and medium ones in seconds, where
  DFS took minutes or never finished.
* The caps make small-cap answers untrustworthy. The rod-solver oracle fixes the positions with
  one unbounded axis, as above. Positions with two or three unbounded axes still need something
  better than caps.
