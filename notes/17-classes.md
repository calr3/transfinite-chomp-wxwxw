# Classes of positions with three or more infinite columns

Every open case of the project has three or more infinite columns (notes/00, §4). This note
maps that region for the positions below Gale's `3×3×ω`. It sorts them into classes by the
shape of their infinite part, works out which classes can contain P-positions at all, and
records the data behind that. The aim was to predict which tower of `3×3×ω` is P. The map
narrows the candidates, but the heuristic search turned out to be unreliable, for a reason
explained in §5.

## 1. Classes

A position below `3×3×ω` is a plane partition over the `3×3` base with entries in `ℕ ∪ {ω}`.
Its **infinite part** `D` is the set of cells of height `ω`. `D` is a Young diagram containing
the poison cell, so we write it by its row lengths along `x`, for rows `y = 0, 1, 2`. The rest
of the position, its **attachment** `A`, is a finite plane partition on the other cells.

Up to transposition, there are 11 shapes with `|D| ≥ 3`:

| `|D|` | shapes | towers of this shape |
| --- | --- | --- |
| 3 | `(3)` row of three ("`W`"), `(2,1)` tripod ("`V`") | `T((0,1),g)` is `(3)` |
| 4 | `(3,1)`, `(2,2)` square | |
| 5 | `(3,2)`, `(3,1,1)` cross | `T((1,1),g)` is `(3,1,1)` |
| 6 | `(3,3)`, `(3,2,1)` | `T((0,2),g)` is `(3,3)` |
| 7, 8, 9 | `(3,3,1)`, `(3,3,2)`, `(3,3,3)` | `T((1,2),g)`, `T((2,2),g)`, and `3×3×ω` itself |

Cutting a cell `c ∈ D` at a finite height `z` leaves the shape `D ∖ ↑c` and caps every cell of
`↑c` at `z`. Moves on the attachment keep the shape.

**In Huddleston–Shurman's language** ([HS], Thm 5.1), the position with shape `D` and attachment
`A` is `E(A, D, ω)`. Their Fundamental Theorem gives a unique P-height `H(A, D)`, so:
* the position is P iff `H(A, D) = ω`;
* it has a finite P cut of the poison column iff `H(A, D) < ω`;
* otherwise `H(A, D) > ω`: it is N, but only through an option that keeps some infinite column.

## 2. Two-wide families and their regimes

A **two-wide family** of a position `X` is the set of options obtained by cutting one cell
`c ∈ D` at heights `z = 0, 1, 2, …`, when the cut leaves exactly two infinite cells: a two-wide
stalk `Y_z`, which the certified solver decides exactly. Reading off the shapes:
* `(3)` has one: cut `(2,0)`.
* `(2,1)`, `(3,1)`, `(2,2)`, `(3,2)` and `(3,3)` have one or two: cut `(1,0)` (and `(0,1)` for
  `(2,1)` and `(2,2)`).
* The **cross shapes** `(3,1,1)`, `(3,2,1)`, `(3,3,1)`, `(3,3,2)`, `(3,3,3)` have none. Every
  option of a cross-shaped position is finite, has one infinite column, or has three or more.
  The towers of types `(1,1)`, `(1,2)`, `(2,2)` are in this group, and so is `3×3×ω`.

**The side-set argument** (notes/12, "The closed class of the `(0,1)` towers") applies to every
two-wide family. `Y_z` is P iff:
* it has no P cut of its poison column above `z` (a cut at `h ≤ z` is a finite option of `X`
  itself);
* no option `Y_{z'}`, `z' < z`, is P (if one were, `X` would be N);
* no other move on its finite cells leaves a P stalk.

Call `z` a **side element** of the family if the first condition holds. Each "other move"
belongs to a chain of stalks in `z`, with at most one P member per chain. So `X` can be P only
if every side element is **blocked** by one of these chains. Everything depends on how many
chains there are, and that is decided by the shape:
* **Fixed regime: `W = (3)` only.** The cut cell `(2,0)` is the end of the row, and nothing
  else of `↑(2,0)` is infinite. For `z` above the attachment, `Y_z = S(z, A)` has a fixed
  attachment. So only the finitely many one-move attachments `A' < A` block. Then `X` is P only
  if the side set `𝒮_A` is finite. This is the side-set lemma; universality (notes/12) says
  `𝒮_A` has density `√2 − 1`.
* **Single-cell growing regime: `V = (2,1)` only.** Cutting `(1,0)` caps only `(1,0)`. So `Y_z`
  is a stalk along `y` with one cell, `(1,0)`, growing with `z`, and again only finitely many
  chains block.
* **Multi-cell growing regime: `(3,1)`, `(2,2)`, `(3,2)`, `(3,3)`.** The capped region holds two
  to four infinite cells, e.g. `(1,0), (2,0), (1,1), (2,1)` for `(3,3)`. A cut inside that block
  to any height `t < z` starts a new chain, one for each `t`. So the blockers are unbounded, and
  side elements no longer force a P stalk.

## 3. Results by class

### `W`, the row of three
Covered in notes/12 and notes/14. Every `W(A)` with entries `≤ 8` is exactly N, and all are N if
the side sets are infinite.

### `V`, the tripod: always a finite P cut so far
Seven tripod positions with attachments up to height 6 were run. For each, the exact side set
of the `(1,0)` cuts was computed up to `z = 60`, and for five of them also that of the `(0,1)`
cuts, which looks the same (`rodf -I 2 -K c`; the side-set mode now accepts any position whose
cut leaves a two-wide stalk). Every one of them has a **finite P cut**, i.e.
`H(A, V) < ω`:

| position (`x`-major: `(0,0),(0,1),(0,2),(1,0),…`) | finite P cut at | side set of the `(1,0)` cuts |
| --- | --- | --- |
| `ω,ω,2, ω,2,2, 2,2,2` | 11 | every `z ≥ 10`, and `0, 4, 6, 7, 8` |
| `ω,ω,1, ω,1,1, 3,1,1` | 4 | every `z ≥ 3`, and `1` |
| `ω,ω,3, ω,2,1, 2,1,0` | 6 | every `z ≥ 5`, and `2` |
| `ω,ω,4, ω,4,4, 4,4,4` | 10 | every `z ≥ 8`, and `1, 2` |
| `ω,ω,1, ω,3,1, 5,2,1` | 5 | every `z ≥ 5`, and `1, 2` |
| `ω,ω,5, ω,3,2, 4,3,2` | 10 | every `z ≥ 8`, and `0, 1, 4, 5, 6` |
| `ω,ω,0, ω,3,0, 6,2,0` | 3 | every `z ≥ 3`, and `0` |

The cofinite side sets follow from the finite P cut: if `Φ(h₀)` is P, every stalk cut at
`z ≥ h₀` has it as an option. Huddleston–Shurman's `2×2×Ω` classification ([HS] §11, PB1)
gives the same picture when the attachment is only the cell `(1,1)` at height `d`: the finite
cut at `d + 1` is P.

> **Conjecture (tripod).** Every tripod position with a finite attachment has a finite P cut,
> i.e. `H(A, V) < ω`. Then the class `V` contains no P-position.

This is the tripod analogue of Conjecture 1.1 for rods: there `H(∅, S) < ω` for every finite
base other than the domino.

### The multi-cell growing regime: blocked side elements
The `(1,0)` cuts of `T((0,2),2)` (shape `(3,3)`, growing block `(1,0), (1,1), (2,0), (2,1)`)
show the mechanism. Exact side set for `z ≤ 18`: `0, 4, 5, 6, 11, 16, 17, 18`. Every one of
these stalks is nevertheless N, and the solver's exact replies show what blocks each:

| `z` | 0 | 4 | 5 | 6 | 11 | 16 | 17 | 18 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| P reply of the stalk | `(0,2)` at 0 | `(0,2)` at 1 | `(1,2)` at 1 | `(2,1)` at 4 | `(2,1)` at 8 | `(1,1)` at 10 | `(2,1)` at 16 | `(1,1)` at 13 |

The first three are moves on the top layer `y = 2`, which form finitely many chains. From `z = 6` on, every side element is
blocked by a cut inside the growing block, at a height `t` that grows with `z`. So the counting
that rules out P for `W` and `V` does not apply here. This is where P-positions with three or
more infinite columns can live.

## 4. Consequence for `3×3×ω`

If the side sets of `W` are infinite (universality) and the tripod conjecture holds, no
position of shape `(3)` or `(2,1)` is P. Then:
* every `(0,1)` tower is N (notes/14), and the P tower predicted by Conjecture 1.1 is of type
  `(0,2)`, `(1,1)`, `(1,2)` or `(2,2)`;
* every P-position with three or more infinite columns has a shape from the multi-cell growing
  regime or a cross shape;
* proving any such position P needs, for each of its two-wide families, a proof that every side
  element is blocked. With unboundedly many blocking chains, that is a two-parameter statement:
  the "nested certificate" of notes/12, now with a precise target.

The exact tower results fit this. All exact N verdicts for the cross-shaped towers `(1,1)`,
`(1,2)`, `(2,2)` come from finite P cuts (notes/12, the table `g → h`). Cross shapes have no
two-wide options, and their other options all have three or more infinite columns.

## 5. A pitfall: deep finite cuts

The heuristic search (`rodf` with caps) tries cuts of the poison column only up to
`α·H + d`, e.g. height 10 for `H = 2`. With the new conjectural oracle `rodf -W 1` (every
`W`-shaped position counts as N), it reported `T((0,2),2)` as N through the reply cutting
`(1,1)` to 2. That reply leaves the shape-`(3,1)` position

  `Y = (ω,ω,2 | ω,2,2 | ω,2,2)`,

which the search judged P. It is not: **`Y` has an exact finite P cut at height 70.** So `Y`
is N, and `T((0,2),2)` stays open. The finite cuts are decided exactly by the completing-height
function `f` and are cheap compared with the stalk certificates, so they should be searched
deeply. The new flag `rodf -Q zp` tries them up to height `zp` inside the heuristic search.

**Status of the open towers after this round.**
* `T((0,2),2)`: every cut of `(1,0)` up to `z = 23` is exactly N, the blocked side elements
  included. The heuristic search with `-W 1 -Q 200` reached no verdict in 30 minutes. Still open.
* `T((1,1),12)`: no finite P cut up to height 31 (it was 30 before). The run (`rodf -K 0`) then
  ran out of its 6.5 GB memory limit: the table of finite positions is the bottleneck.
  The `(1,1)` towers with `g ≤ 11` all have finite P cuts at heights up to 25, so a deeper search
  is the natural way to settle this one.

## Tools

* `rodf -W 1`: conjectural oracle; `W`-shaped positions count as N. Its verdicts are always
  reported as heuristic.
* `rodf -Q zp`: deep search of the finite cuts inside the heuristic search.
* `rodf -I 2 -K c -Y z0 -Z z1 [-v 1] -p …`: exact side set of the two-wide family of cell `c`,
  for any position whose cut of `c` leaves a two-wide stalk; `-v 1` prints the partners as `[z:h]`.
