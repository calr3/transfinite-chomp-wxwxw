# The side class of three-wide Chomp is infinite

A self-contained account of the main theorem found in this repository. It fills a gap in
Huddleston–Shurman's proof that `3×ω^ω` is a P-position. Background and the search that led
here are in [notes/12](12-three-chains.md); computations are in `tools/`.

## Statement

Three-row Chomp: a position `[a,b,c]` (`a ≥ b ≥ c ≥ 0`) has rows of these lengths, with the
poisoned square at the start of the first row. P means the player to move loses.

> **The side class.** `𝒮` is the set of `x ≥ 0` such that no position `[h,h,x]` with `h > x` is P.
> In Huddleston–Shurman's language, `x ∈ 𝒮` iff the side `1×x` beside a two-wide stalk has
> infinite P-height, i.e. `(ω,ω,x)` admits no P cut of its first column.

> **Theorem.** `𝒮` is infinite. More precisely, writing `s(v) = #(𝒮 ∩ [0,v])`:
> 1. (upper density) `s(v) > δ·v` for infinitely many `v`, for every `δ < (3 − √3)/6 ≈ 0.2113`;
> 2. (lower density) `s(v) ≥ v/60` for all sufficiently large `v`.

Computed exactly up to `x = 50000`, `𝒮` has density `√2 − 1 ≈ 0.4142` with bounded discrepancy
(`tools/side3row.cpp`, notes/12). The theorem is far from that, but it is what Huddleston–Shurman
need.

**Why they need it.** Their Side-Top Theorem decides `(ω+a, ω+b, x)` through the restricted
Grundy value `G_𝒮(x)`, which is the index of `x` in `𝒮`. In the proof that `3×ω^ω` is P (§10 of
"Transfinite Chomp", MSRI 42), the bite `(0, ω·(n+1)+c)` is answered by the side `x` with
`G_𝒮(x) = G(2×(ω·n+c))`. These target values are unbounded, so `𝒮` must be infinite. The paper
does not prove this, and its criterion (10–1) cannot supply it without circularity (notes/12).
The theorem fills exactly this step. Their three-wide criterion (10-1) needs it too: already for
the positions `(ω+a, ω, ω)`, (10-1) is equivalent to `𝒮` being infinite. The rest of their
argument is audited computationally in [notes/15](15-hs-audit.md), with no inconsistency found.

## Ingredients

Write `f(q,r)` (`q ≥ r ≥ 0`) for the function of Brouwer, Horváth, Molnár-Sáska and Szabó
("On three-rowed Chomp", *Integers* 5, 2005): the unique `p > r` such that either
`r < p < q` and `[p,p,r]` is P, or `p ≥ q` and `[p,q,r]` is P. For `r ∉ 𝒮` let `τ(r)` be the
unique `p > r` with `[p,p,r]` P, i.e. `f(p,r) = p`. Let `D = {f(a,a) : a ≥ 0}`.

From E. Sheiner, *Unique Winning Opening Move in Three-Row Chomp*, arXiv:2605.23837v2 (2026).
The proofs are short; I have checked them and found no gap, and the author reports a Lean
formalisation.

* **(S1) Lemma 2.3(b).** If `s < t₁ < t₂ < p` and `f(t₁,s) = p`, then `f(t₂,s) ≠ p`.
* **(S2) Lemma 4.2, row-start propagation.** If `f(p,r) = p`, then for every `q` with
  `r < q < p` there is `b < r` with `f(q,b) = p`, i.e. `[p,q,b]` is P.
* **(S3) Proposition 4.3.** `D` is disjoint from the image `{τ(r) : r ∉ 𝒮}`.
* **(S4) Lemma 2.2, applied to the diagonal.** `f(a,a) = mex B(a,a)` with `{1,…,a} ⊆ B(a,a)`
  and `|B(a,a)| ≤ 2a`, so `f(a,a) ≤ 2a + 1`.
  * An elementary alternative, `f(a,a) ≤ 3a` for `a ≥ 1`, gives the same infinitude with
    worse constants. `f(a,a)` is the least `p ≥ a` outside `{f(a,b) : b < a} ∪ {f(t,t) : t < a}`.

Two elementary facts:

* **(E1)** `a ↦ f(a,a)` is injective: `[n,a,a]` is an option of `[n,b,b]` when `a < b < n`.
  So, by (S4), `#(D ∩ [1,v]) ≥ ⌊(v+1)/2⌋`.
* **(E2) Alive rows.** If `[p,q,b]` is P with `p > q`, then `b ∈ 𝒮` or `τ(b) > q`. Otherwise,
  cutting the first row to `τ(b) ≤ q` gives the P-position `[τ(b), τ(b), b]`, a move between
  two P-positions.

## Proof

Write `s(v) = #(𝒮 ∩ [0,v])` and `I(v) = #{r ∉ 𝒮 : τ(r) ≤ v}`. The partners are distinct, so
by (S3) and (E1),

> (1) `I(v) ≤ v − #(D ∩ [1,v]) ≤ v/2`.

**Step A (slope 2).** Let `r ∉ 𝒮` and `p = τ(r)`. By (S2) and (S1), the levels `q ∈ (r,p)`
give `p − r − 1` distinct rows `b_q < r`. Hence `τ(r) ≤ 2r + 1`.

**Step B (improving the slope).** Suppose `τ(x) ≤ c·x + K` for all `x ∉ 𝒮`, for some constants
`c ≥ 1` and `K`. Fix `r ∉ 𝒮`, `p = τ(r)`. Each `b_q` is either in `𝒮 ∩ [0,r)` or, by (E2),
satisfies `c·b_q + K ≥ τ(b_q) > q ≥ r + 1`, i.e. `b_q ∈ ((r+1−K)/c, r)`. Counting the distinct
`b_q`:

> (2) `p − r − 1 ≤ s(r−1) + r − (r+1−K)/c`, so `τ(r) ≤ (2 − 1/c)·r + s(r−1) + O(1)`.

**Step C (infinitude).** Suppose `|𝒮| = m < ∞`. By (2), slope `c` improves to `2 − 1/c`.
Starting from `c = 2` this gives `3/2, 4/3, …`. With slope `c = 3/2`, every `x ≤ (2/3)(v − K)`
outside `𝒮` has `τ(x) ≤ v`, so `I(v) ≥ (2/3)v − O(1)`. That contradicts (1) for large `v`.

**Step D (density).** Suppose `s(r) ≤ δr` for all large `r`. By (2) the slope improves by
`c ↦ 2 − 1/c + δ`. This decreases from 2 to the fixed point
`c*(δ) = 1 + δ/2 + √(δ + δ²/4)`. With slope `c`, `I(v) ≥ (1 − δ)v/c − O(1)`, which
contradicts (1) as soon as `c < 2(1 − δ)`. Now `c*(δ) < 2(1 − δ)` iff `6δ² − 6δ + 1 > 0` on
`δ < 1/2`, i.e. iff `δ < (3 − √3)/6`. For such `δ` the iteration reaches a slope below
`2(1 − δ)` in finitely many steps, giving a contradiction. So `s(v) > δv` for infinitely many
`v`. ∎

**Step E (lower density: a localised bootstrap).** Fix a large `V` with `s(V) ≤ δV`.

*Local Step B.* Suppose `τ(x) ≤ c·x + K` for all `x ∉ 𝒮` with `x ∈ [A, V]`. Then for
`r ∉ 𝒮` with `r ∈ [2A, V]`:
* a non-side `b_q < A` would have `τ(b_q) ≤ 2b_q + 1 < 2A + 1 ≤ r + 1 ≤ q` (Step A), which is
  impossible by (E2);
* so every non-side `b_q` lies in `[A, r)`, and then in `((r+1−K)/c, r)`;
* the side ones number at most `s(V) ≤ δV ≤ (δV/2A)·r`.

So `τ(r) ≤ (2 − 1/c + δV/(2A))·r + O(1)` on `[2A, V]`.

Start from slope 2, valid everywhere (Step A). Apply the local step twice, with lower ends
`A₁ = εV/2` and `A₂ = εV`, where `ε = 0.101`. For `δ = 1/60` the slopes are
`c₁ = 1.5 + δ/(ε/2) ≈ 1.830` and `c₂ = 2 − 1/c₁ + δ/ε ≈ 1.6186`. The non-side
`x ∈ [εV, (V − K)/c₂]` all have `τ(x) ≤ V`, so

`I(V) ≥ V/c₂ − εV − s(V) − O(1) ≥ (0.6178 − 0.101 − 0.0167)·V − O(1) > V/2 + 10⁻⁴·V − O(1)`.

This contradicts (1) once `V` is large. So `s(V) > V/60` for every large `V`. ∎

Optimising over the number of steps and `ε` (with doubling lower ends) gives about `0.0167`.

The constants come only from (1) and the slope recursion. The truth (density `√2 − 1`, with
`τ(x) ≈ √2·x` and `#(D ∩ [1,v]) ≈ (2 − √2)v`) is much stronger.

## Checks

`tools/side_ingredients.cpp` verifies, for second rows up to 1500:
* every instance of (S2) (136170 of them), with the `b_q` distinct and alive as in (E2);
* `f(a,a) ≤ 2a+1`, with `{1,…,a} ⊆ B(a,a)`;
* `τ(r) ≤ 2r`.

`tools/side_lemma.cpp` verifies (S3) together with its converse (every `h ≥ 1` is a partner or
a diagonal value) up to 20000.

## Relation to Padhi's conjecture

J. S. Padhi (arXiv:2608.11290, August 2026, §4.7) observes, for cells up to `w = 600`:
* the P-positions `(w,w,t)` (our partner positions `[τ(x),τ(x),x]`) satisfy
  `w_n = (1+√2)n + O(1)`;
* the P-positions `(w,t,t)` (our diagonal positions `[A(t,t),t,t]`) satisfy
  `w = (1 + 1/√2)t + O(1)`.

His Conjecture 4.6 says these diagonal families are quasi-periodic with bounded discrepancy and
rotation numbers in `ℚ(√2)`. By Sheiner's partition, the two first-row sequences are
complementary, and the slopes form a Beatty pair: `1/(1+√2) + 1/(1+1/√2) = 1`.

Our computations extend the evidence:
* `τ(x) − √2·x ∈ [−1.12, 2.50]` for all non-side `x ≤ 50000`;
* `A(t,t) − (1 + 1/√2)t ∈ [−1.23, 2.14]` for all `t ≤ 20000`.

In his terms, the theorem above says the family `(w,w,t)` misses infinitely many `t`, with upper
density of misses at least `(3−√3)/6`. His conjecture would give density exactly `√2 − 1`.

## What remains open

* The exact density `√2 − 1` (we have lower density `≥ 1/60` and upper density `≥ 0.211`). Empirically
  `#(𝒮 ∩ [0,x]) − (√2 − 1)(x+1) ∈ [−0.50, 1.46]` for `x ≤ 50000`.
* The **partner law** `τ(x) = x + #(𝒮 ∩ [0,x]) + O(1)`, empirically with error in `[−2,2]`.
* **Monotonicity of `τ`**, and the sharp inequality "(B′)": the P-positions `[h,h,x]` with
  `h ≤ v` never outnumber `𝒮 ∩ [0,v]`.
* The 3D analogue, the side sets of 3-row Chomp with a finite attachment. It would make every
  `(0,1)` tower of Gale's `3×3×ω` an N-position. notes/12 reduces it to a bound on "defects"
  and gives the evidence.
