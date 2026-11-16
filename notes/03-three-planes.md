# Idea 3: the candidate first move `(1,1,1)`

**Why this move.** `(1,1,1)` is the unique winning first move of the finite cubes `2×2×2` and
`3×3×3` (`box_chomp`). It is also the 3D analogue of the 2D winning move `(1,1)` on `ω×ω`, and
it is the only first move fixed by every coordinate permutation. (The finite cubes are a weak
guide: `4×4×4` is won by the far-corner move `(2,3,3)`, a strategy-stealing artefact.)

It leaves the three coordinate planes

```
U = {x = 0} ∪ {y = 0} ∪ {z = 0}  =  N³ ∖ ↑(1,1,1),
```

and `(1,1,1)` wins iff `U` is P, i.e. iff every option of `U` is N.

## The options of `U`

A cell of `U` has at least one zero coordinate. Up to the six permutations, the options are:

| Type | Move | Result |
| --- | --- | --- |
| `A(c)` | `(0,0,c)`, `c ≥ 1` | the floor `z = 0` plus the walls `{x = 0}` and `{y = 0}` cut to height `c` |
| `B(b,c)` | `(0,b,c)`, `1 ≤ b ≤ c` | the full planes `y = 0` and `z = 0`, plus the plane `x = 0` cut to the 2D L-shape `{y < b} ∪ {z < c}` |

`B(b,c)` and `B(c,b)` are mirror images, which is why `b ≤ c` suffices.

The walls give a family `W(p,q) = floor ∪ {x = 0, z < p} ∪ {y = 0, z < q}`, with
`A(c) = W(c,c)`. The moves `(1,0,k)`, `(0,1,k)` and `(0,0,k)` stay inside the family:
`W(p,q)` goes to `W(p, min(q,k))`, `W(min(p,k), q)` and `W(min(p,k), min(q,k))` respectively.
That looks like two Nim heaps, but moves in the floor leave the family, so mirroring does not
close up.

## Rigorous results (Lean: `Chomp/FirstMoves.lean`)

| Option | Status | Reply |
| --- | --- | --- |
| `A(1)` = `ω×ω` | N | `(1,1,0)`, leaving the L-shape |
| `A(2)` | N | `(0,1,0)`, leaving `2×ω` |
| `B(1,1)` = `ω × L(1,1)` | N | `(1,0,0)`, leaving the L-shape |

**This method can't go further.** An option of `U` plus one reply is `N³` minus the upsets of at
most three cells, one of them `(1,1,1)`.
* A finite P-position needs a generator on each of the three axes, which is impossible here.
* The only infinite P-positions we know with so few generators are `2×ω` and the infinite
  L-shape.

So `A(1)`, `A(2)` and `B(1,1)` are exactly the options this argument can settle. The rest need
new P-positions with an infinite plane in them.

## Consequences of the antichain lemma

If `(1,1,1)` wins, then it is the only winning first move with all coordinates positive. Every
move `(a,b,c) ≥ (1,1,1)` is comparable to it, so all of them lose. Conversely, if any such move
other than `(1,1,1)` wins, then `(1,1,1)` loses.

## Heuristic probe

`scripts/options.py` was run on `U` with global caps `-a 1 -d 2 -g 1`, a time limit of 150 s and
moves up to coordinate 2:

| Option of `U` | Result |
| --- | --- |
| `(0,0,1)` = `A(1)` | N, reply `(0,2,0)` to `2×ω` |
| `(0,0,2)` = `A(2)` | N, reply `(0,1,0)` to `2×ω` |
| `(0,1,1)` = `B(1,1)` | timeout |
| `(0,1,2)` = `B(1,2)` | timeout |
| `(0,2,2)` = `B(2,2)` | timeout |

The `B(1,1)` timeout is telling. That option is *proved* N with the one reply `(1,0,0)`, but the
depth-first search tries the moves `(0,y,z)` first and never gets back to `x = 1`. So a timeout
reflects the search order, not how hard the position really is. A move-ordering heuristic, such
as trying first the moves that leave few generators, would be the first improvement to make.

## Finite truncations (exact)

`scripts/utrunc.py` decides the finite positions `U(M₁,M₂,M₃) = U ∩ [0,M₁)×[0,M₂)×[0,M₃)`
exactly, for all `M₁ ≤ M₂ ≤ M₃ ≤ 5`:

* **P:** `U(1,1,1)`, `U(2,2,2)`, `U(3,3,3)`. These are the cubes, consistent with `(1,1,1)`
  winning `2×2×2` and `3×3×3`.
* **N:** every other case, including the cubes `U(4,4,4)` and `U(5,5,5)` and every unequal
  truncation.

For comparison, in 2D the truncations of the winning positions stay P:
* the L-shape `L(M,M)` is P for every `M`;
* `2×ω` is the limit of the P-positions `(g+1, g)`.

`U` shows neither pattern: its P truncations stop at `M = 3`, and no unequal family appears.
This is **weak evidence that `(1,1,1)` loses** on `ω×ω×ω`. It is not a proof, since finite
truncations can mislead (`2×M` is N for every `M` while `2×ω` is P). Also, the truncations here
cut all three planes along the same three axes, which is only a 3-parameter slice of the
6 parameters available.

## Conclusion

* `(1,1,1)` remains **undecided**. Three options are rigorously N, and the finite truncations
  weakly suggest that `(1,1,1)` loses.
* Every other option contains two or three full planes, which no current method handles.
* The structure suggests the next step: treat `A(c)` and `B(b,c)` as the floor `ω×ω` plus
  attached walls. That needs the Grundy value of `ω×ω` and of floors with attached rods, which is
  the same transfinite bookkeeping as in Ideas 1 and 2.
