# Huddleston–Shurman's `2×2×Ω`: a machine check above `ω`

Section 11 of "Transfinite Chomp" classifies the P-positions over a `2×2` base and concludes
that `2×2×ω³` is a P-position. notes/15 checked the finite part (PA1, PB1). This note checks
the rest, in the way notes/15 checked their three-wide theory: the paper's statements are
implemented as written and tested against the rules of the game.

**Results.**

1. **The classification holds up.** No inconsistency was found in PA2, PD1, PD2, PC2, PC1 (as
   far as it is explicit), the description of type C with `z₁ = 1` and with `z₁ = 2`, or PF1.
   In particular every option of `2×2×ω³` that was tested is an N-position by their rules, with
   an explicit reply.
2. **Three statements of the paper are not correct as printed.** None of them affects the
   classification.
   * **PC3 is false** for type C positions with `û > v̂`. The paper's own list of examples
     contains a counterexample (§3.1). PC1 does not need this case, by a short argument.
   * **PD3 is false** when the two middle columns have different `ω²`-parts (§3.2). It holds
     in every tested case where they are equal. The proof of PD1 quotes it for two
     inequalities that fail in many cases; the conclusion of that step holds in all of them.
   * **Three replies in the proof of PF1 are misprinted** (§3.3). The corrected replies work.
3. **The rule for `z₁ = 1` made precise** (§4): which "pieces" enter the nim sum.
4. **Not checked:** type E, type C with `z₁ ≥ 3`, and `z₁ = 2` beyond the case the paper
   treats. This is a test on samples, not a proof.

Notation is the paper's. A position is `[v z; u y]`: the columns `(0,0)`, `(0,1)`, `(1,0)`,
`(1,1)` have heights `u`, `v`, `y`, `z`, with `v ≥ y` after a reflection. `b\z` is the `t` with
`b + t = z`. `û` is the part of `u` that is a multiple of `ω²`, and `u = û + ω·u₁ + u₀`. `G` is
the unrestricted value of a two-wide position (their (9-1) to (9-5), proved in notes/18).

## 1. What the paper states

| type | condition | P-positions |
| --- | --- | --- |
| A | `z < ω`, `z = y` | PA1: `v < ω`: `u = v + z + 1`. PA2: `v ≥ ω`: `G(ω\u, ω\v) = z` |
| B | `z < ω`, `z < y` | PB1: `u = v = y = z + 1` |
| C | `ω ≤ z < ω³`, `ẑ = v̂` | PC1: with base height `h` (`ω` if `ẑ = 0`, else `ẑ`) and top `T = h\[v z; u y]`: `T ∈ 𝒯` and `G_𝒯(T) = 0`, where `𝒯 = {û = 0, u₁ > max(v₁,y₁)}` |
| D | `ω ≤ z < ω³`, `ẑ < v̂` | PD1: `G(ω\y, ω\z) = G(ω²\u, ω²\v)` |
| E | `ω ≤ z < ω³`, `y ≥ ω^ω` | PE1, through the value of an L-shaped top |
| F | `z ≥ ω³` | PF1: only `2×2×ω³` |

PC1 is not a closed form: `G_𝒯` is the restricted Grundy value in the game on the tops in
`𝒯`. The paper makes it explicit for `z₁ = 1` and partly for `z₁ = 2`.

Auxiliary statements: PA3 and PB2 (bites at finite heights), PC2 (type C with `û = v̂` and
`u₁ = v₁` is N), PC3 (in the other type C positions every bite that meets the base leaves an
N-position), PC4 (a short type C P-position has `u < ω²`), PD2 (type D with `û = v̂ = ŷ` is N),
PD3 (the decomposition of type D can be made in either direction if `ẑ < ŷ` and `v̂ < û`).

## 2. The test

A set of statements "this position is P, that one is N" is correct iff no position called P
has an option called P, and every position called N has an option called P. `hs22_lib.claim`
gives the paper's verdict for a position with heights below `ω^ω`, or "no closed form" for
type C tops with `z ≥ ω`. `hs22_audit.py` samples positions, lists their options completely
up to bounds on the coefficients (every `t < h` has a unique form
`(terms of h above ω^k) + ω^k·c + L`; all such `t` with the coefficients of `L` up to a bound),
and tests the two conditions. A position called N for which no P option turns up is searched
again with wider bounds.

Sample ranges: exponents up to 3, coefficients up to 2 or 3, finite parts up to about 6;
options with coefficients up to 3 to 6 and finite parts up to 6 to 16, and more where the
position requires it. Two runs of 1500 positions per part are in `data/hs22/`.

| part | P-positions (options checked) | N-positions | problems |
| --- | --- | --- | --- |
| the paper's 20 examples of types A to D and F | all P by the rules | | 0 |
| PA2: types A and B with `v ≥ ω` | 70 (8186) | 1430 | 0 |
| PD1: type D | 320 (215072) | 1180 | 0 |
| PD2: all 3960 small type D positions with `û = v̂ = ŷ` | | N by PD1 | 0 |
| PC2: type C with `û = v̂`, `u₁ = v₁`: the bite named in the proof | | 1500, the bite leaves a P-position | 0 |
| PC3 with `û = v̂`, `u₁ > v₁`: bites into the base of 913 positions | | all leave N | 0 |
| PC1 for tops with `z` finite: short and tall, `û = v̂` | 673 (298408) | 428 | 0 |
| type C with `û > v̂` (called N by PC1) | | 399, each with a P option | 0 |
| type C with `z₁ = 1` (§4) | 580 (109813) | 920 | 0 |
| type C with `z₁ = 2`, `v₁ = y₁ = 2` (§5) | 382 (166961) | 1118 | 0 |
| PF1: the 360 bites of `2×2×ω³` at 90 infinite heights | | all N; corrected replies all P | 0 |

(Counts from the run with seed 1. The script lists the failures of §3 as "problems"; there are
no others in either run.)

## 3. What is not correct as printed

### 3.1 PC3

> PC3: In a type C position with either `û > v̂` or both `û = v̂` and `u₁ > v₁`, every bite
> that intersects the base `B` leaves an N-position.

Take `X = [ω² ω²; ω²·2 ω²]`. It is of type C with `û = ω²·2 > v̂ = ω²`, and its base has height
`ω²`. The bite `(1,1,ω)` meets the base and leaves `[ω² ω; ω²·2 ω²]`, which is a P-position by
PD1 (`F = [0; ω²]`, `T = [0; ω²]`) and is the first of the paper's own examples of thin type
D P-positions. In the sample, 16 of the 452 tall positions with `û > v̂` have such a bite,
always a bite of `(1,1)`.

The proof of PC3 says that a bite of `(1,1)` leaves "a type D N-position by PD2". PD2 needs
`û = v̂ = ŷ`, which holds only in the second case of PC3. So the proof covers `û = v̂`,
`u₁ > v₁`, and there the statement passed the test (913 positions; no bite into the base
leaves a P-position).

**Consequence.** The paper concludes that the set `𝒯(h)` of tops for which every bite into the
base leaves an N-position is `{v̂ = 0 and (û > 0 or u₁ > max(v₁,y₁))}` for every `h`, hence
"independent of `h`". For tops with `û > 0` and a tall base this is not so. The statement of
PC1 is not affected, because the positions concerned are N for another reason:

> **Lemma.** Given PC4, PC2, PC3 for `û = v̂`, and PC1 for short positions: a tall type C
> position `B(h) + T` with `û(T) > 0` is an N-position.

*Proof.* The short position `B(ω) + T` is N by PC4. A bite into its base is at a finite
height and leaves an N-position by PB2 and PA3 (the exception in PA3 needs `u < ω²`). So it
has a P option `B(ω) + T′` with `T′` an option of `T`. By PC4, `û(T′) = 0`, so `T′ ∈ 𝒯` with
`G_𝒯(T′) = 0`. The tops with `û = 0` have only such tops as options, and for them `𝒯(h)` is
`{u₁ > max(v₁,y₁)}` for every `h` by PC2 and PC3. So `B(h) + T′` is a P-position, and it is an
option of `B(h) + T`. ∎

In the test, all 399 type C positions with `û > v̂` whose top has `z` finite have a P option
by the stated rules.

### 3.2 PD3

> PD3: If a type D position satisfies `ẑ < ŷ` and `v̂ < û` then
> `G(F) = G(T) ⟺ G(F̃) = G(T̃)`, where `F̃ = [ω\v ω\z]`, `T̃ = [ω²\u ω²\y]`.

Take `[v z; u y] = [ω³+ω², ω; ω³+ω²·2, ω²·2]`. Then `G(F) = G(ω²·2, 0) = ω²·2` and
`G(T) = G(ω³+ω²·2, ω³+ω²) = ω²·2`, so the position is P by PD1. In the other direction
`G(F̃) = G(ω³+ω², 0) = ω³+ω²` and `G(T̃) = G(ω³+ω²·2, ω²) = ω³+ω²·3`.

Among all type D positions with `ẑ < ŷ`, `v̂ < û`, exponents up to 3, coefficients up to 2 and
finite parts up to 1 or 2 (108108 positions):

| | both | neither | PD1 only | other direction only |
| --- | --- | --- | --- | --- |
| `ŷ = v̂` | 340 | 26120 | 0 | 0 |
| `ŷ < v̂` | 392 | 81144 | 56 | 56 |

On the 112 positions where the two differ, PD1 is the one that agrees with the game: the 56
it calls P have no P option (21840 options checked), and the 56 it calls N have one.

**Where the paper uses PD3.** Twice, in the last case of the proof of PD1 (a bite `(0,1,h)`
from a position with `G(F) = G(T)`).

* For `ẑ < ĥ = v̂` and `h < y`: after the bite the two middle columns have the same `ω²`-part,
  the case in which PD3 held in every test.
* For `ẑ < ĥ < v̂` and `h < y` the proof claims `G(F′) < G(F) + ω²` and
  `G(T′) ≥ G(T) + ω²`, the second "since `ŷ < v̂`, by PD3". Among 53431 such bites from 1500
  P-positions, the first inequality fails 4288 times and the second 18728 times (13376 of
  them with `ŷ = v̂`, a case the proof does not mention). For example, from
  `[ω³·2+ω²·2+ω·2+1, ω²+ω·2; ω³·3+ω²·2+ω+3, ω³+ω²+ω+2]`, with `G(F) = G(T) = ω³+ω·3+2`, the
  bite `(0,1,ω³)` gives `G(F′) = ω³+ω²+ω·2`, which is not below `G(F) + ω² = ω³+ω²`.
  In all 53431 cases `G(F′) ≠ G(T′)`, so the option is N as claimed. (The paper writes
  `F = [z; y]`, `T = [v; u]`, `F′ = [h z]`, `T′ = [u y]` in this step. The counts are for the
  pieces of the decomposition, `ω\·` and `ω²\·` of these. Read literally, without the
  subtractions, the two inequalities fail as well: 1600 and 7593 times among 20996 bites.)

So this step of the proof is not right as written, and PD1 itself shows no failure.

### 3.3 The replies in the proof of PF1

The proof answers every bite `(i,j,h)` into `2×2×ω³`, `h ≥ ω`. As printed, and as they have to
be:

| bite | printed reply | correct reply |
| --- | --- | --- |
| `(0,0,h)`, `ω ≤ h < ω²` | `(1,0, G(2×(ω\h)))` | the same |
| `(0,0,h)`, `ω² ≤ h < ω²·2` | `(1,0, ω + (ω\h))` | `(1,0, ω + (ω²\h))` |
| `(0,0,h)`, `ω²·2 ≤ h` | `(1,0, ω\h)` | `(1,0, ω²\h)` |
| `(1,1,h)` | `(1,0, ω² + h)` | `(1,0, ω² + (ω\h))` |
| `(1,0,h)` | `(0,0, ω² + h)` | `(0,0, ω² + (ω\h))` |

In the second and third lines the printed height is `h` itself (since `ω + (ω\h) = h`, and
`ω\h = h` for `h ≥ ω²`), which is not a bite of a column of height `h`. The descriptions that
follow in the paper ("with `F = T`") fit the corrected heights. In the last two lines the
printed reply is right for `h ≥ ω²` and wrong for `ω ≤ h < ω²`; the paper's own description
`F = [a; ω²+a]` gives the corrected one with `a = ω\h`. For the 90 heights tested, the printed
replies give a P-position in 18, 72, 72 and 72 cases for the bites of `(0,0)`, `(1,1)`,
`(1,0)`, `(0,1)`, and the corrected replies in all 360.

## 4. Type C with `z₁ = 1`

The paper: these P-positions "are just those positions with `u₁ + z₁ = v₁ + y₁ + 1` whose
finite top pieces have Nim sum 0", where pieces at the same level "must have their nim sum
component computed together, so they can be 2-wide Grundy values, or even a 3-column piece
with L-shaped cross section". The following reading passes the test in both directions (1500
positions, all cases).

A short type C position with `z = ω + z₀` and `u₁ > v₁` is P iff `u₁ = v₁ + y₁` and
`u₀ = R`, where

| levels | `R` |
| --- | --- |
| `v₁ > y₁ > 1` | `v₀ ⊕ y₀ ⊕ z₀` |
| `v₁ > y₁ = 1` | `v₀ ⊕ G(y₀, z₀)`, the two-wide value of the columns `(1,0)`, `(1,1)` |
| `v₁ = y₁ > 1` | `v₀ ⊕ y₀ ⊕ z₀` |
| `v₁ = y₁ = 1` | `λ(v₀, y₀, z₀)` |

`λ(b,c,d)` is the Grundy value of three stacks of `b`, `c`, `d` cells over `(0,1)`, `(1,0)`,
`(1,1)`, in which any cell may be taken and a cut of the first or second stack at height `n`
also cuts the third. For example `λ(1,0,0) = 1`, `λ(1,1,1) = 2`, `λ(2,1,1) = 0`, so
`[ω+1 ω; ω·2+1 ω]` (the paper's example) and `[ω+2 ω+1; ω·2 ω+1]` are P-positions.

By PC1 the same rule decides the tall type C positions whose top has `z` finite, and this
passed as well (495 tall P-positions).

## 5. Type C with `z₁ = 2`

The paper treats `[ω·2+b, ω·2+d; ω·3+a, ω·2+c]`: P iff `Q = [b d; a c]` lies in
`𝒬 = {a⊕b ≡ a⊕c ≡ 1 (mod 3), d ≤ min(b,c)}` and has restricted value 0 there; such an `a`
exists iff `b⊕c` is not a power of 2; otherwise there is a P-position with top column
`ω·5 + a`.

* The condition defining `𝒬` is what the rule of §4 gives for the bites into the second level
  of the base: `(1,0,ω+n)` leaves a P-position iff `a ⊕ b = G(n,n) = ⌊(3n+1)/2⌋`, and these are
  the numbers not congruent to 1 modulo 3.
* For `b, c < 64`: some `a` with `a⊕b ≡ a⊕c ≡ 1 (mod 3)` exists iff `b⊕c` is not a power of 2.
* For `b, c ≤ 12` and every `d`: a top column `ω·3 + a` exists iff `b⊕c` is not a power of 2
  (the largest `a` is 150).
* With top column `ω·4 + a` the position is always N (the bite `(1,1, ω + (a⊕b⊕c))` wins, by
  the rule of §4). With `ω·5 + a` it is P for exactly one `a` when `b⊕c` is a power of 2.
* The resulting rules pass the test in both directions (1500 positions with `u₁` from 3 to
  5).

The paper's summary "`u₁ + z₁ = v₁ + y₁ + 1` if `v₁` or `y₁` is odd or `v₁ = y₁ = 2`" is
therefore to be read with its own exception: for `v₁ = y₁ = 2` and `b⊕c` a power of 2 it is
`v₁ + y₁ + 3`. The general case of `z₁ = 2` is not explicit in the paper and was not tested.

## 6. Limits

* The test is on samples with small coefficients. It can find errors, and it found three; it
  does not prove the statements it did not refute.
* It is a test of consistency. There is no independent solver for these heights.
* Type E needs values of positions with L-shaped cross-section, which the paper does not
  give, and heights from `ω^ω` on, which the oracle does not represent.
* For type C with `z₁ ≥ 2` in general the paper gives no closed form.

## Tools

* `scripts/hs22_lib.py`: ordinals below `ω^ω` (from `tools/hs_oracle.py`), the paper's
  verdict for a position (`claim`), options up to bounds.
* `scripts/hs22_audit.py [PART …] [-n SAMPLES] [-s SEED]`: the parts `examples`, `pa2`, `pd1`,
  `pd23`, `pd1proof`, `pc2`, `pc3`, `tallc`, `pf1`, `c1`, `c2`.
* `data/hs22/`: the output of two runs.
