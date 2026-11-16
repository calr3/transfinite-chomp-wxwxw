# Idea C: a family of P-positions answering the options of `ω×ω×3`?

**The template.** `2×ω` is P because every option has a reply into a known family of
P-positions, the finite two-row positions `(k+1, k)`. If `ω×ω×3` is P (which would make the
first move `(0,0,3)` win the prize), every option must likewise have a reply into P-positions.
The question is which family.

## Test 1: replies that leave a rod

The simplest candidates are replies that bound a second axis, leaving a **rod** (one infinite
direction). The rod solver decides rods exactly when the infinite part is a two-wide stalk, and
heuristically otherwise.

For an option `m = (a,b,c)` of `ω×ω×n`, the reply `(j,0,0)` leaves the rod along `y` with
cross-section `x < j, z < n`. Its column `(x,z)` has height `b` if `x ≥ a` and `z ≥ c`, and is
infinite otherwise. The reply `(0,j,0)` does the same along `x`. At most one `j` can work in each
orientation. `scripts/rodreplies.py` searches `j ≤ 4`.

**Sanity check, `ω×ω×2`.** Every option `(a,b,c)` that is not a rod itself has the rod reply
`(1,0,0)` or `(0,1,0)`, leaving `2×ω`. So all those options are N. `ω×ω×2` is still N because of
its rod option `(0,1,0)`.

**`ω×ω×3`.** None of the 35 options `(a,b,c)` with `a ≤ 3`, `b ≤ 4`, `c ≤ 2` (other than slabs
and rods) has a rod reply with `j ≤ 4` that is P.

A second run recorded the status of every rod reply (`j ≤ 3`, 20 s each): of the 210 rods,
**163 are N exactly**, 47 timed out (rods with many infinite cells), and none is P. The first run
(`j ≤ 4`, 60 s each) found no P either.

So **the 2×ω template fails for `ω×ω×3`**. If `ω×ω×3` is P, the replies to its options must
leave positions that are still infinite in two directions.

## Test 2: replies that flatten

A reply `(0,0,c')` with `c < c' < 3` turns the option `(a,b,c)` of `ω×ω×3` into the option
`(a,b,c)` of the thinner slab `ω×ω×c'`. So:

> The option `(a,b,c)` of `ω×ω×3` is answered by flattening exactly when `(a,b,c)` is a
> winning move on `ω×ω×c'` for some `c < c' ≤ 2`.

* `W(ω×ω×1) = {(1,1),(0,2),(2,0)}`, proved in Lean. So the options `(1,1,0)`, `(0,2,0)` and
  `(2,0,0)` of `ω×ω×3` are N: flatten to height 1, leaving the L-shape or `2×ω`.
* `W(ω×ω×2) ∋ (0,1,0)`, leaving `2×ω`. The option `(0,1,0)` of `ω×ω×3` (the rod `3×ω`) is N by
  flattening to height 2.
* The rest of `W(ω×ω×2)` is unknown. Every other option of `ω×ω×3` needs either such a winning
  move of `ω×ω×2` or a genuinely new reply.

This sets up a recursion: **the winning moves of thinner slabs supply replies for thicker ones.**
Finding `W(ω×ω×2)` (2 layers, two infinite directions) is the next concrete step. It is the
simplest family of positions with full slabs, and the place to develop the tools that slabs
need.

## Conclusion

* No family of rods answers the options of `ω×ω×3`. This is exact for most of the replies
  checked, and the template that proves `2×ω` cannot prove `ω×ω×3`.
* Flattening answers a few options and reduces the rest to the winning moves of `ω×ω×2`.
* Whether `ω×ω×3` is P stays open. The positions that decide it (2- and 3-layer slabs with
  notches) are exactly the ones every tool here fails on.
