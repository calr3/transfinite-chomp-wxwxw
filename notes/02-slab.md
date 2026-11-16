# Idea 2: is the slab `ω×ω×3` a P-position?

**Why it matters.** The first move `(0,0,n)` leaves the slab `ω×ω×n`. It wins exactly when
`ω×ω×n` is P, i.e. when the P-height of the 2D board is `h(ω×ω) = n`. We know `h(ω×ω) ≥ 3`:
`ω×ω×1` and `ω×ω×2` are N, as proved in Lean (`notes/05-lean.md`). So `n = 3` is the first
open case, and a proof that `ω×ω×3` is P would win the prize.

## The options of `ω×ω×n`

Up to swapping `x` and `y`, a move `(a,b,z)` with `a ≤ b` and `z < n` leaves one of these:

| Type | Move | Result | Status for `n = 3` |
| --- | --- | --- | --- |
| A | `(0,0,z)`, `1 ≤ z < n` | a thinner slab `ω×ω×z` | N for `z = 1, 2` (Lean) |
| R | `(0,j,0)`, `j ≥ 1` | the rod `j×n×ω` | N for `j = 1, 2` (domino rule, Idea 1). For `j ≥ 3` it is N if Conjecture 1.1 holds; `3×3×ω` is undecided |
| L | `(a,b,0)`, `a, b ≥ 1` | the L-prism `L(a,b)×n`: two rods, cross-sections `b×n` and `a×n`, meeting at a corner block | `L(1,1)×n` is N (rigorous, below). Others unknown |
| S | `(a,b,z)` or `(0,j,z)` with `1 ≤ z < n` | a full slab `ω×ω×z` with an L-prism or a rod on top | unknown |

`ω×ω×3` is P iff every option of types R, L and S is N. Type A is settled. Type R is settled for
`j ≤ 2` and conjecturally for all `j`. So the question is about types L and S.

## Rigorous facts found along the way

The first two facts are proved in Lean (`Chomp/Prisms.lean`).

* **`L(a,b)×2` is N for all `a, b ≥ 1`.** Taking `(0,1,0)` leaves the `y = 0` row of both layers,
  which is `2×ω` (P).
* **`L(1,1)×c` is N for all `c ≥ 2`.** Taking `(0,0,1)` leaves the 2D L-shape with two infinite
  arms (P).
* **P-pairs.** If `N³ ∖ (↑m ∪ ↑m')` is P, then the first moves `m` and `m'` both lose, since each
  answers the other. The L-prisms are exactly the candidate P-pairs `{(0,0,c), (a,b,0)}`.
  Idea 4 builds on this.

## Computations

`scripts/options.py` probes each option separately with `chomp3f`, in parallel with a time
limit. Raw results for `ω×ω×3` with global caps (`-a 1 -d 2 -g 1`), timeout 600 s:

| Option | Result |
| --- | --- |
| `(0,0,1)`, `(0,0,2)` (type A) | N, reply leaves `2×ω` (consistent with Lean) |
| `(0,1,0)`, `(0,2,0)` (type R) | N, reply leaves `2×ω` |
| `(0,1,1)`, `(0,1,2)`, `(0,2,1)`, `(0,2,2)`, ... (type S) | timeout |
| `L(1,2)×3`, `L(2,2)×3` (type L) | timeout (more than 16 million positions in 5 minutes; `scripts/lprisms.py` sweeps this family) |

### Two problems found with the heuristic itself

1. **Per-axis caps are wrong for mirror-type replies.** With caps `α·E_i + D` per axis, the
   option "floor plus a wall of height 3" seemed to have a P reply. That reply was an L-shape with
   one infinite arm and one arm of length 3, which is really N (Nim with an infinite heap). The
   right reply cuts the infinite arm at 3, which lies on a different axis from where the length 3
   came from. Using the global extent `max_i E_i` for every axis (`-g 1`) fixes this. All later
   runs use global caps.
2. **Minimal caps (`-a 1 -d 1`) are unreliable**, for the same reason.

## Conclusion

* `(0,0,3)` remains **undecided**.
* Exhaustive search, even with the tightest sensible caps, cannot handle positions that contain a
  full slab or two thick rods.
* The parts that could be checked fit both outcomes: every option settled so far is N, which
  `ω×ω×3` being P requires, but most options are open.

## Suggested next steps

* **Ordinal Grundy values for rods.** The options of type L are sums of two rods glued at a core,
  so a Huddleston–Shurman-style calculation of rod Grundy values (Stratification Conjecture) is
  the natural tool, not search.
* **Periodicity in the slab.** For type S, the far parts of each layer are constant. A move far
  out produces a family indexed by one coordinate, with at most one P member (antichain lemma).
  Detecting where that member sits (Byrnes-style periodicity) would replace the cap.
