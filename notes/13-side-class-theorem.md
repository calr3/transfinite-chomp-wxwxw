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
> 1. (lower density) `s(v) > v/5` for **every** `v ≥ 0`;
> 2. (upper density) for every `δ < 1/4`, `s(v) > δ·v` for infinitely many `v`;
> 3. for every `T ≥ 1`, the number of P-positions `[h,h,x]` with `x < h ≤ T` is at most
>    `2·s(T−1)`.

Computed exactly up to `x = 50000`, `𝒮` has density `√2 − 1 ≈ 0.4142` with bounded discrepancy
(`tools/side3row.cpp`, notes/12). The theorem is far from that, but it is more than
Huddleston–Shurman need.

An earlier version of this note proved `1/10` (for large `v`) and `(3−√3)/6 ≈ 0.211` by a
bootstrap on the slope of `τ`. The proof below is shorter. It rests on the remaining-lifetime
lemma, found while working on the 3D side sets ([notes/19](19-remaining-lifetimes.md), which
also has the consequences not needed here).

**Why they need it.** Their Side-Top Theorem decides `(ω+a, ω+b, x)` through the restricted
Grundy value `G_𝒮(x)`, which is the index of `x` in `𝒮`. In the proof that `3×ω^ω` is P (§10 of
"Transfinite Chomp", MSRI 42), the bite `(0, ω·(n+1)+c)` is answered by the side `x` with
`G_𝒮(x) = G(2×(ω·n+c))`. These target values are unbounded, so `𝒮` must be infinite. The paper
does not prove this, and its criterion (10–1) cannot supply it without circularity (notes/12).
The theorem fills exactly this step. Their three-wide criterion (10-1) needs it too: already for
the positions `(ω+a, ω, ω)`, (10-1) is equivalent to `𝒮` being infinite. The rest of their
argument is audited in [notes/15](15-hs-audit.md). [notes/16](16-three-wide-proof.md) proves
(10-1) completely. With this theorem, their result that `3×ω^ω` is P then rests only on their
§8–§9 (two-column values, Beanstalk Lemma, Side-Top Theorem).

## Ingredients

Write `f(q,r)` (`q ≥ r ≥ 0`) for the function of Brouwer, Horváth, Molnár-Sáska and Szabó
("On three-rowed Chomp", *Integers* 5, 2005): the unique `p > r` such that either
`r < p < q` and `[p,p,r]` is P, or `p ≥ q` and `[p,q,r]` is P. For `r ∉ 𝒮` let `τ(r)` be the
unique `p > r` with `[p,p,r]` P, i.e. `f(p,r) = p`. Let `D = {f(a,a) : a ≥ 0}`.

From E. Sheiner, *Unique Winning Opening Move in Three-Row Chomp*, arXiv:2605.23837v2 (2026).
The proofs are short; I have checked them and found no gap, and the author reports a Lean
formalisation.

* **(S1) Lemma 2.3(a),(b).** For fixed `q`, the values `f(q,0), …, f(q,q)` are distinct. If
  `s < t₁ < t₂ < p` and `f(t₁,s) = p`, then `f(t₂,s) ≠ p`.
* **(S2) Lemma 4.2, row-start propagation.** If `f(p,r) = p`, then for every `q` with
  `r < q < p` there is `b < r` with `f(q,b) = p`, i.e. `[p,q,b]` is P.
* **(S3) Propositions 4.3 and 4.4.** Every `h ≥ 1` is either a partner `τ(r)` or a diagonal
  value `f(a,a)`, and not both.
* **(S4) Lemma 2.2, applied to the diagonal.** `f(a,a) = mex B(a,a)` with `{1,…,a} ⊆ B(a,a)`
  and `|B(a,a)| ≤ 2a`, so `f(a,a) ≤ 2a + 1`.
* **(S5) Lemma 4.1.** `f(q,q)` is the largest of `f(q,0), …, f(q,q)`.

Two elementary facts:

* **(E1)** `a ↦ f(a,a)` is injective: `[n,a,a]` is an option of `[n,b,b]` when `a < b < n`.
* **(E2) Alive rows.** If `[p,q,b]` is P with `p > q`, then `b ∈ 𝒮` or `τ(b) > q`. Otherwise,
  cutting the first row to `τ(b) ≤ q` gives the P-position `[τ(b), τ(b), b]`, a move between
  two P-positions.

## Proof

Read the first argument of `f` as time. Row `x` is **alive at time `t`** if `x < t` and either
`x ∈ 𝒮` or `τ(x) > t`. Then `f(t,x) > t`. Let `n(t)` be the number of rows alive at time `t`
and `I(t) = #{x ∉ 𝒮 : τ(x) ≤ t}`. Since `τ(x) ≤ t` forces `x < t`, and by (S3),

> (1) `n(t) = t − I(t) = #(D ∩ [1,t])`.

By (S4) and (E1), `n(t) ≥ t/2`. Also `n` is non-decreasing and `n(t+1) ≤ n(t) + 1`.

**Step 1 (remaining lifetime).** *Let `x ∉ 𝒮` and `x < q < τ(x)`. Then
`τ(x) − q ≤ #{b < x : b alive at time q}`.*

Let `p = τ(x)`. For each `t` with `q ≤ t < p`, (S2) gives `b_t < x` with `[p,t,b_t]` P. The
`b_t` are distinct by (S1). By (E2), `b_t ∈ 𝒮` or `τ(b_t) > t ≥ q`, so `b_t` is alive at time
`q`. There are `p − q` values of `t`.

**Step 2 (oldest first).** *Every row alive at time `q` and still alive at time `q + n(q)` is
in `𝒮`.*

List the rows alive at time `q` by age, `a₁ < … < a_n`. If `a_j ∉ 𝒮`, Step 1 gives
`τ(a_j) ≤ q + j − 1 < q + n(q)`.

**Step 3.** *`I(T) ≤ 2·s(T−1)` for every `T ≥ 1`.* This is part 3 of the theorem.

Put `T′ = T + n(T)`. A row alive at time `T′` was born before `T`, and is then in `𝒮` by Step
2, or at one of the `n(T)` times `T, …, T′ − 1`. So `n(T′) ≤ s(T−1) + n(T)`. With
`n(T′) ≥ T′/2` this gives `s(T−1) ≥ (T − n(T))/2 = I(T)/2`.

**Step 4 (a deadline).** *`τ(r) ≤ r + n(r+1) ≤ (5r+3)/3` for every `r ∉ 𝒮`.*

* The `n(a)` rows alive at time `a` have distinct picks `f(a,b) > a` (S1), all smaller than
  `f(a,a)` (S5). So `f(a,a) ≥ a + n(a) + 1 ≥ 3a/2 + 1`.
* Hence `f(a,a) ≤ t` forces `a ≤ 2(t−1)/3`, and by (1) `n(t) ≤ (2t+1)/3`.
* If `τ(r) > r + 1`, Step 1 at `q = r+1` gives `τ(r) − r − 1 ≤ n(r+1) − 1`, since `r` itself is
  alive at time `r+1`. If `τ(r) = r+1` the bound is trivial.

**Step 5 (lower density).** Let `T = v + 1` and `X = ⌊3v/5⌋`. By Step 4 every non-side
`x ≤ X` has `τ(x) ≤ (5X+3)/3 ≤ T`, so `I(T) ≥ X + 1 − s(X)`. By Step 3,
`s(v) ≥ (X + 1 − s(X))/2`. Also `s(v) ≥ s(X)`. The larger of the two bounds is at least
`(X+1)/3 > v/5`. ∎

**Step 6 (upper density).** Suppose `s(v) ≤ δv + K₀` for all `v`, with `δ < 1/4`.

* Suppose `τ(x) ≤ c·x + K` for all `x ∉ 𝒮`, and let `r ∉ 𝒮`. A non-side `b < r` alive at time
  `r+1` has `c·b + K ≥ τ(b) ≥ r+2`, so `b ≥ β := (r+2−K)/c`. So the rows below `r` alive at
  time `r+1` are side rows below `β` or rows in `[β, r)`: at most `δβ + K₀ + r − β + 1` rows.
  By Step 1, `τ(r) ≤ (2 − (1−δ)/c)·r + O(1)`.
* Starting from `c = 5/3` (Step 4), the map `c ↦ 2 − (1−δ)/c` decreases to its fixed point
  `1 + √δ`.
* With slope `c`, every non-side `x ≤ (T−K)/c` has `τ(x) ≤ T`, so
  `I(T) ≥ (1−δ)T/c − O(1)`. As `c → 1 + √δ` this tends to `(1 − √δ)T`, which exceeds `T/2`
  for `δ < 1/4`. That contradicts `I(T) = T − n(T) ≤ T/2`. ∎

The constants come from `n(t) ≥ t/2` and the slope recursion. The truth (density `√2 − 1`,
with `τ(x) ≈ √2·x` and `n(t) ≈ (2 − √2)t`) is much stronger. Numerically
`0 ≤ s(T−1) − I(T) ≤ 2` for all `T ≤ 50000`; Step 3 proves this with a factor 2.

## Checks

`tools/side_ingredients.cpp` verifies, for second rows up to 1500:
* every instance of (S2) (136170 of them), with the `b_q` distinct and alive as in (E2);
* `f(a,a) ≤ 2a+1`, with `{1,…,a} ⊆ B(a,a)`;
* `τ(r) ≤ 2r`.

`tools/side_lifetime.cpp` verifies Steps 1, 3 and 4 for rows up to 3000 (770577 pairs in Step 1,
with least slack 0). On the stored table up to 50000, `τ(r) ≤ r + n(r+1)` holds with least
slack 0.

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

In his terms, the theorem above says the family `(w,w,t)` misses infinitely many `t`, with lower
density of misses at least `1/5`. His conjecture would give density exactly `√2 − 1`.

## What remains open

* The exact density `√2 − 1` (we have lower density `≥ 1/5` and upper density `≥ 1/4`). Empirically
  `#(𝒮 ∩ [0,x]) − (√2 − 1)(x+1) ∈ [−0.50, 1.46]` for `x ≤ 50000`.
* The **partner law** `τ(x) = x + #(𝒮 ∩ [0,x]) + O(1)`, empirically with error in `[−2,2]`.
* **Monotonicity of `τ`**. It is equivalent to "`f(q,r) > τ(r)` for `r < q < τ(r)`" and to a
  greedy rule for `τ` (notes/19, §6).
* The sharp inequality "(B′)": the P-positions `[h,h,x]` with `h ≤ v` never outnumber
  `𝒮 ∩ [0,v]`. Part 3 of the theorem is this with a factor 2.
* The 3D analogue, the side sets of 3-row Chomp with a finite attachment. It would make every
  `(0,1)` tower of Gale's `3×3×ω` an N-position. notes/12 reduces it to a bound on "defects"
  and gives the evidence.
