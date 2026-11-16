# Idea 4: a ledger of first moves on `ω×ω×ω`

## The P-pair reformulation

A first move `m` wins iff `X(m) = N³ ∖ ↑m` is P, i.e. iff no reply `m'` makes
`N³ ∖ (↑m ∪ ↑m')` a P-position. Call `{m, m'}` a **P-pair** when that position is P.

* A P-pair of incomparable cells rules out **both** first moves, since each answers the other.
* If `m' < m`, then `N³ ∖ (↑m ∪ ↑m') = X(m')`, so a "pair" with a comparable cell is just a
  winning first move `m'`. That is the antichain lemma again.

So the whole problem is about the P/N status of positions with two generators:

| Pair type | Position | What is known |
| --- | --- | --- |
| `{(0,0,c), (0,b,0)}` | rod `b×c×ω` | P iff `(b,c) ∈ R`. Known: `(1,2)`, `(2,1)`. Conjecture 1.1: nothing else |
| `{(0,0,c), (a,b,0)}` | L-prism `L(a,b)×c` | P for `(1,1,1)` (the 2D L-shape). N for `c = 2`, and for `a = b = 1, c ≥ 2` (Lean). Open otherwise |
| `{(a,0,0), (0,b,c)}` | the same L-prism, along `x` | as above |
| `{(0,0,c), (a,b,d)}`, `1 ≤ d < c` | slab `ω×ω×d` topped by `L(a,b)` layers | open |
| `{(0,b,c), (a,0,d)}` and other mixes | crossing planes | open |
| `{(1,1,0), (1,0,1)}` | the `x`-axis rod plus the `yz`-plane (a disjunctive sum, below) | P iff the Grundy value of `ω×ω` is `ω` |

**Disjunctive sums.** Suppose a position is the poison together with parts `A` and `B` such that
no cell of `A` is comparable with a cell of `B`. Then taking a cell of `A` removes nothing from
`B`, so the game is the Nim sum of the two parts. In `N³` this happens only when the axes split
between the parts, as in the last row of the table. It gives no new eliminations, since `(1,1,0)`
and `(1,0,1)` already lose, but it shows where transfinite Grundy values enter.

## Known P-pairs

Both are proved in Lean, with all permutations.

* `{e_i, 2e_j}` for `i ≠ j`, e.g. `{(0,1,0), (0,0,2)}`. The position is `2×ω`.
* `{e_i, e_j + e_k}` with `{i,j,k} = {x,y,z}`, e.g. `{(1,0,0), (0,1,1)}`. The position is the
  L-shape with two infinite arms.

These eliminate the first moves `e_i` (that is, `(0,0,1)` and its permutations), `2e_j`
(`(0,0,2)` and permutations) and `e_j + e_k` (`(0,1,1)` and permutations).

## The ledger

First moves up to permutation with coordinates at most 3, written `a ≤ b ≤ c`.

| Move | Type | Status | Reason or reformulation |
| --- | --- | --- | --- |
| `(0,0,1)` | A | **loses** | P-pairs with `(0,2,0)` and with `(1,1,0)` (Lean) |
| `(0,0,2)` | A | **loses** | P-pair with `(0,1,0)` (Lean) |
| `(0,1,1)` | B | **loses** | P-pair with `(1,0,0)` (Lean) |
| `(0,0,3)` | A | open | wins iff `h(ω×ω) = 3` (Idea 2) |
| `(0,1,2)`, `(0,1,3)`, `(0,2,2)`, `(0,2,3)`, `(0,3,3)` | B | open | `(0,b,c)` wins iff `L(b,c)×ω` is P, i.e. the 2D infinite L-base `L(b,c)` has P-height `ω` |
| `(1,1,1)` | C | open | wins iff `U` is P (Idea 3) |
| `(1,1,2)`, `(1,1,3)`, `(1,2,2)`, `(1,2,3)`, `(1,3,3)`, `(2,2,2)`, `(2,2,3)`, `(2,3,3)`, `(3,3,3)` | C | open | three crossing slabs. If `(1,1,1)` wins, all of these lose (antichain) |

Whatever the answer, the set of winning first moves is a finite antichain closed under
permutations. For example, it contains at most one move of the form `(0,0,c)`.

## Heuristic probe of all first moves

`scripts/options.py` was run on `N³` with global caps `-a 1 -d 2 -g 1`, a time limit of 150 s
and moves up to coordinate 2:

| First move | Result |
| --- | --- |
| `(0,0,1)` | N, reply `(0,2,0)`: loses (also proved in Lean) |
| `(0,0,2)` | N, reply `(0,1,0)`: loses (also proved in Lean) |
| `(0,1,1)`, `(0,1,2)`, `(0,2,2)`, `(1,1,1)`, `(1,1,2)`, `(1,2,2)`, `(2,2,2)` | timeout |

`(0,1,1)` is proved to lose, so its timeout again reflects the search order, not the position
(see Idea 3). Every first move other than `(0,0,c)` leaves at least two full slabs, beyond what
exhaustive search can do.

## Conclusion

* Three classes of first moves are proved to lose (9 moves in total). Every other first move
  is open.
* The P-pair table shows what would rule out more moves. The most promising source is the
  L-prisms `L(a,b)×c` for `c ≥ 3`, which have no full slab. One P L-prism rules out a type-A move
  and a type-B move at once.
