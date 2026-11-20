# Remaining lifetimes: a shorter proof of the side-class theorem, and what blocks the cube case

This note comes out of an attempt to prove that the first 3D side set (the single cube,
notes/12) is infinite. That attempt did not succeed. It produced two things:

* a new lemma for ordinary three-row Chomp, the **remaining-lifetime lemma**. It gives a shorter
  proof of the side-class theorem with better constants: `s(v) > v/5` for **every** `v`, upper
  density at least `1/4`, and the inequality `#{x : τ(x) ≤ T} ≤ 2·#(𝒮 ∩ [0,T))`, which is half
  of conjecture (B′) of notes/12;
* a precise description of what is missing for the cube (§8, §9). The lemma survives with an
  error term, the "dead levels", and a model computation shows that the lemmas available cannot
  bound them. But they need not be bounded: §9 proves that the 3D side set is infinite if two
  statements about partners and diagonal values hold, both of which are theorems in 2D and
  hold in all the data.

Notation and the ingredients (S1)–(S5), (E1), (E2) are those of
[notes/13](13-side-class-theorem.md): `f(q,r)` is the function of Brouwer et al. and Sheiner,
`τ(x)` the partner of a non-side `x`, `𝒮` the side class, `D = {f(a,a)}` the diagonal values,
`s(v) = #(𝒮 ∩ [0,v])`. Recall in particular:

* **(S1)** the values `f(q,0), …, f(q,q)` are distinct, and a row takes each value at most once;
* **(S2)** row-start propagation;
* **(S3)** every `h ≥ 1` is a partner `τ(x)` or a diagonal value `f(a,a)`, and not both;
* **(S5)** `f(q,q)` is the largest of `f(q,0), …, f(q,q)`.

§§1–5 repeat the proof of notes/13 with more comment. §§6–8 are new material.

## 1. Rows as lifetimes

Read the second argument of `f` as a row and the first as time.

* Row `x` is **born** at time `x`. If `x ∉ 𝒮` it **dies** at time `τ(x)`: from then on
  `f(q,x) = τ(x)` is constant.
* Row `x` is **alive at time `t`** if `x < t` and either `x ∈ 𝒮` or `τ(x) > t`. Then
  `f(t,x) > t`, and `[f(t,x), t, x]` is a P-position. Call `f(t,x)` the **pick** of row `x` at
  time `t`.
* `n(t)` is the number of rows alive at time `t`, and `I(t) = #{x ∉ 𝒮 : τ(x) ≤ t}` the number
  of rows dead by time `t`.

Since `τ(x) ≤ t` forces `x < t`,

> (1) `n(t) = t − I(t) = #(D ∩ [1,t])`.

The second equality is (S3). By (S4) and (E1), `n(t) ≥ t/2`. Since `n(t)` counts diagonal
values, it is non-decreasing and grows by at most 1 per step.

## 2. The remaining-lifetime lemma

> **Lemma 1.** Let `x ∉ 𝒮` and `x < q < τ(x)`. Then
>
> `τ(x) − q ≤ #{b < x : b alive at time q}`.

In words: at any moment, a row that is going to die has at most as many steps left as there
are older rows still alive.

*Proof.* Let `p = τ(x)`. For each `t` with `q ≤ t < p`, (S2) gives a row `b_t < x` with
`[p,t,b_t]` P. By (S1) the `b_t` are distinct. By (E2), `b_t ∈ 𝒮` or `τ(b_t) > t ≥ q`, so `b_t`
is alive at time `q`. There are `p − q` values of `t`. ∎

Steps A and B of notes/13 are the case `q = x + 1`. The lemma has min slack 0: it is attained
(`tools/side_lifetime.cpp`).

> **Corollary 2 (oldest first).** List the rows alive at time `q` by age,
> `a₁ < a₂ < … < a_n`, `n = n(q)`. If `a_j ∉ 𝒮` then `τ(a_j) ≤ q + j − 1`. So every row that is
> alive at time `q` and still alive at time `q + n(q)` is a side element.

In particular the oldest alive row is always a side element, the second oldest is a side
element or dies at the next step, and so on.

## 3. Deaths never outnumber side elements by more than 2 to 1

> **Theorem 3.** For every `T ≥ 1`, `I(T) ≤ 2·s(T−1)`.

That is, among the P-positions `[h,h,x]` with `h ≤ T` there are at most twice as many as there
are side elements below `T`.

*Proof.* Put `T′ = T + n(T)`. A row alive at time `T′` was either born before `T`, and is then
a side element by Corollary 2, or was born at one of the `n(T)` times `T, …, T′−1`. So
`n(T′) ≤ s(T−1) + n(T)`. By (1), `n(T′) ≥ T′/2 = (T + n(T))/2`. Hence
`s(T−1) ≥ (T − n(T))/2 = I(T)/2`. ∎

This is already a proof that `𝒮` is infinite: if `𝒮` were finite, every other row would die,
and `I(T)` would be unbounded.

**Relation to (B′).** Conjecture (B′) of notes/12 says `I(T) ≤ s(T−1) + 1`. Theorem 3 is the
same statement with a factor 2. Numerically much more is true: for every `T ≤ 50000`,

> `0 ≤ s(T−1) − I(T) ≤ 2`

(the three values occur 16758, 32624 and 618 times). So at every moment the number of side
elements born so far and the number of rows that have died so far agree to within 2.
Equivalently `n(T)` is the number of non-side rows below `T`, up to 2. The `i`-th positive
side element and the `i`-th partner value differ by at most 3 (they are equal 66% of the time).
There is no local rule behind this: a side row `x` is itself a partner value in only about two
thirds of the cases.

## 4. A deadline for every row, and no diagonal value below a partner

> **Lemma 4.**
> 1. `f(a,a) ≥ a + n(a) + 1` for every `a ≥ 0`.
> 2. `n(t) ≤ (2t+1)/3` for every `t ≥ 1`.
> 3. `τ(r) ≤ r + n(r+1) ≤ (5r+3)/3` for every `r ∉ 𝒮`.
> 4. `f(a,a) > τ(r)` whenever `r ∉ 𝒮` and `a ≥ r`.

*Proof.*
1. The `n(a)` rows alive at time `a` have picks `f(a,b) > a`. These are distinct (S1) and
   smaller than `f(a,a)` (S5).
2. `n(t)` is the number of `a` with `f(a,a) ≤ t`. By part 1 and `n(a) ≥ a/2`, such an `a`
   satisfies `3a/2 + 1 ≤ t`.
3. If `τ(r) = r+1` the claim is `n(r+1) ≥ 1`. Otherwise apply Lemma 1 at `q = r+1`. The rows
   below `r` alive at time `r+1` number `n(r+1) − 1`, since `r` itself is alive. Then use part 2.
4. For `a ≥ r+1`, parts 1 and 3 and the monotonicity of `n` give
   `f(a,a) ≥ r + 2 + n(r+1) > τ(r)`. For `a = r`, `f(r,r) ≥ r + n(r) + 1 ≥ r + n(r+1) ≥ τ(r)`,
   and equality is excluded by (S3). ∎

Part 3 replaces the bound `τ(r) ≤ 2r+1` of notes/13 by slope `5/3`, with no assumption. Part 4
says that every diagonal value below a partner `τ(r)` belongs to a row older than `r`.

## 5. The side-class theorem with better constants

> **Theorem 5.**
> 1. `s(v) > v/5` for every `v ≥ 0`.
> 2. For every `δ < 1/4`, `s(v) > δ·v` for infinitely many `v`.

*Proof of 1.* Let `T = v + 1` and `X = ⌊3v/5⌋`. By Lemma 4.3 every non-side `x ≤ X` has
`τ(x) ≤ (5X+3)/3 ≤ T`. So `I(T) ≥ X + 1 − s(X)`, and Theorem 3 gives
`s(v) ≥ (X + 1 − s(X))/2`. Also `s(v) ≥ s(X)`. The larger of `s(X)` and `(X + 1 − s(X))/2` is
at least `(X+1)/3 > v/5`. ∎

*Proof of 2.* Suppose `s(v) ≤ δv + K₀` for all `v`, with `δ < 1/4`.

* **Slope step.** Suppose `τ(x) ≤ c·x + K` for all `x ∉ 𝒮`. Let `r ∉ 𝒮`. A non-side row
  `b < r` alive at time `r+1` has `c·b + K ≥ τ(b) ≥ r + 2`, so `b ≥ β := (r+2−K)/c`. The rows
  below `r` alive at time `r+1` are therefore side rows below `β` or rows in `[β, r)`. Their
  number is at most `δβ + K₀ + r − β + 1`. By Lemma 1,
  `τ(r) ≤ (2 − (1−δ)/c)·r + O(1)`.
* **Iteration.** Starting from `c = 5/3` (Lemma 4.3), the map `c ↦ 2 − (1−δ)/c` decreases to
  its fixed point `1 + √δ`.
* **Counting.** With slope `c`, every non-side `x ≤ (T − K)/c` has `τ(x) ≤ T`, so
  `I(T) ≥ (1−δ)T/c − O(1)`. As `c → 1 + √δ` this is `(1 − √δ)T − O(1)`, which exceeds `T/2`
  when `δ < 1/4`. That contradicts `I(T) ≤ T/2`. ∎

The slope step is sharper than Step B of notes/13, which counted the side rows in `[β, r)`
twice. The earlier constants were `1/10` (for large `v` only) and `(3−√3)/6 ≈ 0.211`.

The method cannot reach the true density `√2 − 1`. With the true slope `√2`, Theorem 3 alone
gives `δ ≥ (1−δ)/(2√2)`, i.e. `0.26`.

## 6. When does a row die? Side rows as bijections

For a row `r` and a time `p > r`, let `H_r(p) = {f(q,r) : r ≤ q < p}` be the picks of row `r`
before time `p`, and `D_{<r} = {f(a,a) : a < r}`.

> **Proposition 6 (death criterion).** Suppose row `r` is alive at time `p − 1`, or `p = r+1`.
> Then `r` dies at time `p`, i.e. `τ(r) = p`, if and only if
> `p ∉ H_r(p) ∪ D_{<r} ∪ {τ(b) : b < r}`.

*Proof.* In this situation `(p,r)` is a mex cell of the recurrence, and `f(p,r) ≥ p`. So
`f(p,r) = p` iff `p ∉ B(p,r)`. Here `B(p,r) = R(p,r) ∪ C(p,r)` with
`R(p,r) = D_{<r} ∪ H_r(p)`, and `p ∈ C(p,r)` iff `f(p,b) = p` for some `b < r`, i.e.
`τ(b) = p`. ∎

So each time `p` offers the value `p` to the alive rows in order of age. A row passes if it
has picked `p` before, or if `p` is a diagonal value of an older row. The first row that cannot
pass dies. If all pass, `p` is a diagonal value.

> **Proposition 7 (side rows).** Let `r ∈ 𝒮`. Then `q ↦ f(q,r)` is a bijection from `[r,∞)`
> onto `(r,∞) ∖ (D_{<r} ∪ {τ(b) : b < r})`. For every `V ≥ 2r+1`,
>
> `#{q < V : f(q,r) > V} = #{b < r : b ∉ 𝒮}`.

*Proof.* Injectivity is (S1). The picks avoid `D_{<r}` by the recurrence. They avoid the
partners of older rows: if `f(q,r) = τ(b)` with `b < r < q`, then (S2) for `(τ(b), b)` at level
`q` gives a P-position `[τ(b), q, b′]` with `b′ < b`, one move from `[τ(b), q, r]`. Every other
`p > r` is picked, by Proposition 6, since `r` never dies. For the count: the excluded values
are the `r` diagonal values and the `r − s(r−1)` partners of older rows. All are at most
`2r − 1`, and exactly `r` of them are at most `r` (by (S3), each of `1, …, r` is one of them). So
`r − s(r−1)` excluded values lie in `(r, V]`, and
`#{q : f(q,r) ≤ V} = V − r − (r − s(r−1))`. Subtract from the `V − r` levels below `V`. ∎

If the offset `f(q,r) − q` of a side row is eventually constant, it is therefore
`1 + #(non-side rows below r)`. This was observed for 985 of the 1036 side rows `s ≤ 2500` in
notes/12; the other 51 oscillate, and the proposition says how: at every `V` exactly
`#(non-side rows below r)` earlier picks lie above `V`.

> **Proposition 8.** For `r ∉ 𝒮` with `p = τ(r)`,
>
> `#{q ∈ (r,p) : f(q,r) < p} = #{b > r : τ(b) < p}`.

*Proof.* A pick `k = f(q,r) < p` is not in `D_{<r}`, is not a partner of an older row (as in
Proposition 7), and is not a diagonal value of a row `a ≥ r` (Lemma 4.4). By (S3) it is a
partner `τ(b)` with `b > r`. Conversely, if `b > r` and `k = τ(b) < p`, row `r` survives time
`k`, so by Proposition 6 it picked `k` earlier. ∎

So the following are equivalent, and all hold for `x ≤ 50000`, but none is proved:
* `τ` is increasing on the non-side rows;
* every pick of a non-side row is larger than its partner (`f(q,r) > τ(r)` for `r < q < τ(r)`);
* the greedy rule: `τ(r)` is the least `p > r` that is neither a diagonal value nor the partner
  of an older row.

## 7. The same argument with defects

For an attachment `R` without a finite P cut (notes/12, "The 3D side sets"), the levels
`q ∈ (z, τ_R(z))` of a partner are good, box-cut-blocked (at most `M`) or dead. Lemma 1 becomes

> `τ_R(z) − q ≤ #{b < z alive at q} + M + #(dead levels of z in [q, τ_R(z)))`.

The proof of Theorem 3 then gives a conditional theorem that is easier to state than the one in
notes/12:

> Suppose there are constants `ε, γ ≥ 0` with `ε/(1+ε) + γ < 1/3`, and `K`, such that for
> every `T`:
> * every non-side row alive at time `T` has at most `ε·n_R(T) + K` dead levels at or after `T`;
> * at most `γ·T + K` values below `T` are both a partner and a diagonal value.
>
> Then `𝒮_R` is infinite.

For example `ε < 1/2` with finitely many coincidences, or `ε = γ = 1/6`.

*Sketch.* Suppose `𝒮_R` has `m` elements and `n_R(t) ≥ αt − O(1)` for all `t`.
* All non-side rows alive at `T` are dead by `T′ = T + (1+ε)n_R(T) + K + M + 1`, so
  `n_R(T′) ≤ m + (T′ − T)`.
* With `n_R(T′) ≥ αT′ − O(1)` this gives `n_R(T) ≥ α′T − O(1)`, where
  `α′ = α/((1−α)(1+ε))`.
* The diagonal bound `f_R(a,a) ≤ 3a + M` and the second hypothesis give the first value
  `α = 1/3 − γ`. It exceeds the fixed point `ε/(1+ε)` of `α ↦ α′`, so the iterates increase
  past 1, which is absurd since `n_R(T) ≤ T`. ∎

Only the dead levels **after** `T` count. What a row did before does not matter.

## 8. The cube family: what carries over, and what cannot be proved this way

Family 1 is three-row Chomp with one extra independent cell: `[p,q,r | cube]` is P iff the 2D
position `[p,q,r]` has Grundy value 1 (notes/12). Write `f₁, τ₁, 𝒮₁` for it and `f₀, τ₀, 𝒮₀` for
the 2D family. No `[k,k,k | cube]` is P: this was an assumption when this note was written
(checked for `k ≤ 50001`) and is now proved for all `k`
([notes/20](20-corner-and-matching.md), Corollary 3). At a cell `(q,r)` the recurrence for `f₁` has one more blocked value, the 2D
value `f₀(q,r)`.

**What carries over (proved).**
* (S1), (E2) and the death criterion, with the extra excluded value `τ₀(r)`.
* Every `h ≥ 1` is a partner or a diagonal value of family 1, possibly both.
* **Remaining lifetime with dead levels.** For `r ∉ 𝒮₁`, `p = τ₁(r)` and `r < q < p`,
  `p − q ≤ #{b < r alive at q} + 1 + #(dead levels in [q,p))`. A level `t` is dead if no row
  below `r` picks `p` at time `t` and `f₀(t,r) ≠ p`. At a dead level, row `r` picks a value
  below `p`.
* **The last dead level has a source** (the lemma of notes/12): a row `s < r` with
  `f₀(t,s) = p` that picks `p` in family 1 at a later time. So `s` is alive in **both**
  families at time `t`.
* Hence, if no row older than `r` is alive in both families at any time from `q` on, and `r`
  is the `j`-th oldest row alive at time `q`, then `r` is a side element as soon as it is
  still alive at time `q + j`. In particular **the oldest alive row of family 1 is always a
  side element**: it has no witness and no source, and its level `p − 1` cannot be a cube
  level, because `[p, p−1, r]` is never a 2D P-position for `r ≥ 1`. This gives the first
  elements `1, 3, 5` of `𝒮₁` after checking a few levels each. Row 5 is also a 2D side
  element, so from row 7 on sources exist.

**What the data say** (`tools/side_lifetime.cpp`, rows up to 3000).
* Among 270672 levels of 876 partners there are 6 dead levels, at most one per partner. Each has
  its source.
* The partner map `τ₁` is not monotone, unlike `τ₀`: there are 57 inversions `b > r`,
  `τ₁(b) < τ₁(r)`, always with `b − r ≤ 3` and `τ₁(r) − τ₁(b) ≤ 3`. Every dead level sits at
  such an inversion: there row `r` picks the partner of a row at most 3 above it.
* No partner value is a diagonal value. The diagonal value is not the largest pick of its level
  in 449 of 2998 levels, but only by at most 4, and the largest pick is at most 3 rows below.
* `s₁(T−1) − I₁(T)` stays in `[−1, 3]`.

**The mechanism of the observed defects.** The 2D side row 7 has constant offset 5
(`f₀(q,7) = q+5`). So in family 1 the value `q+5` is blocked for row 7 at every level. Its
family-1 offsets alternate between 6 and 4. At a level `q` where it takes `q+6`, the value
`p = q+5` is left free, and row 7 picks it one step later. Rows 5, 1, 3 pick `p` at
`p−1, p−2, p−3` when `p ≡ 0 (mod 4)`. So for `p ≡ 0 (mod 8)` every row above 7 sees `p` unpicked
at level `p−5` and picked at the four levels after it. A row that has both `p−1` and `p` unpicked at that moment, and
finds `p−1` free, takes `p−1` there and dies at `p`. This is the single shape of all 24 dead
levels found up to `z = 9000` (notes/12); they all have `p ≡ 0 (mod 8)`.

**Why the argument cannot be completed as it stands.** `tools/side_randblock.cpp` runs the same
recurrence with a *random* extra blocked value: at each cell, with probability `ρ`, the value
the recurrence would take is forbidden. Everything listed under "what carries over" holds for
this model too. But in it a row can live like a side row for a long time and then die:

| `ρ` | seed | partners (rows `≤ 1498`) | dead levels in all | most for one partner |
| --- | --- | --- | --- | --- |
| 0 | – | 878 | 0 | 0 |
| 0.02 | 1 | 876 | 1398 | 1394 (row 16, dies at 1420) |
| 0.02 | 2 | 875 | 1968 | 1963 (row 2, dies at 1968) |
| 0.1 | 1 | 877 | 1528 | 1267 (row 22, dies at 1302) |
| 0.1 | 2 | 877 | 4898 | 1909 (row 13, dies at 1930) |

(`N = 3000`.) In each case almost every level of that partner is dead. So:

* a bound on the dead levels of each partner, such as (D) of notes/12 or the hypothesis of §7,
  **does not follow** from the lemmas above, nor from any argument that uses only "one extra
  blocked value per cell, distinct along rows and levels";
* in the random model every row dies eventually with probability 1, so "`𝒮` is infinite" is
  false there. A proof for the cube must use what is special about the blocked values `f₀`.

In the cube family the 2D row `r` either dies early (`τ₀(r) ≤ (5r+3)/3`, and then row `r` has no
blocked values afterwards) or is a 2D side row, and then by Proposition 7 each large value is
blocked for it exactly once. The rows of both families are eventually periodic in `q`. A late
death therefore needs a coincidence of phases among finitely many periodic rows during their
transients. None occurs up to `z = 9000`, but excluding it needs a bound on those transients,
which is not known even for the 2D family.

**Status.** The cube case is open. A later attempt with the matching lemma of notes/20 gave
nothing new ([notes/20](20-corner-and-matching.md), §5). §9 reduces it further: no bound on dead levels is needed,
only two statements about partners and diagonal values.

## 9. High and low levels: a reduction that needs no bound on dead levels

This section is for a family with extra blocked values: the cube family, or any attachment `R`
without a finite P cut, with `M` one-cut attachments (`M = 1` for the cube). Write `f, τ, 𝒮, n, I,
s` for that family. Let `r` have a partner `p = τ(r)`. A level `t ∈ (r,p)` is **high** if
`f(t,r) > p` and **low** if `f(t,r) < p`. Every dead level is low. Let
`O_r(t) = #{b < r : b alive at time t}`.

> **Lemma 9 (high levels).** At a high level `t`, either a row `b < r` alive at `t` picks `p`,
> or one of the `M` extra blocked values at `(t,r)` is `p`. So `[t,p)` contains at most
> `O_r(t) + M` high levels.

*Proof.* The value `f(t,r)` is the least unblocked value from `t` on, and `p` lies below it, so
`p` is blocked at `(t,r)`. It is not blocked by a row-2 cut (Sheiner's Lemma 2.3(c)). So a row
below `r` has `f(t,b) = p`, or an extra value equals `p`. The rows `b` are distinct for distinct
`t`, and each smaller attachment blocks `p` at one level at most. ∎

> **Lemma 10 (low levels).** Let `t = r`, or let `t` be a high level, and suppose
> `f(t,r) > p`. Then `(t,p)` contains at most `O_r(t) + M − 1` low levels.

*Proof.* Let `q ∈ (t,p)` be low, with value `k = f(q,r) ∈ (q,p)`. Then `t < k < f(t,r)`, so `k`
is blocked at `(t,r)`. Row `r` takes `k` later, so `k` is not blocked by a row-2 cut. Hence a row
below `r`, alive at `t`, picks `k` at time `t`, or `k` is an extra value there. The same holds
for `p` itself. These values are distinct, so are the rows. ∎

So low levels, and in particular dead levels, **cannot pile up after a high level**. If the
diagonal value is high, `f(r,r) > τ(r)`, then `r` has at most `n(r) + M − 1` low levels in all,
and `τ(r) ≤ r + n(r) + n(r+1) + 2M`. This uses no source and no property of the blocked values.

> **Lemma 11 (what a low level picks).** The value at a low level of `r` is the partner of
> another row, or the diagonal value of a row `a > r`, or one of at most `M` values `h` for which
> a one-cut attachment has `[h,h,h | R′]` P.

*Proof.* The rectangle `[k,k,k | R]` is N. Its winning move is to some `[k,k,x | R]` (then `k`
is a partner), to some `[k,a,a | R]` (a diagonal value), or inside the attachment. A diagonal
value of a row `a < r` is blocked for row `r`. ∎

Now the two hypotheses. Both are theorems for the 2D family (Lemma 4.4, and (S2), which puts a
row older than `b` on every level of the column `τ(b)`).

* **(H4)** `τ(r) < f(a,a)` whenever `r ∉ 𝒮` and `a ≥ r`: no partner exceeds the diagonal value
  of a row born at the same time or later. For `a = r`: no row outlives the first value it
  picked.
* **(L)** If `b < r` and `τ(b) < τ(r)`, row `r` never picks `τ(b)`: no low level of `r` has the
  partner of an older row as its value. More generally **(L_K)**: each row has at most `K` such
  low levels.

> **Theorem 12.** Suppose (H4) and (L_K) hold for all rows from some `r₀` on. Then there is a
> constant `C` with
>
> `I(T) ≤ 3·s(T−1) + C` for every `T`.
>
> In particular `𝒮` is infinite, and `s(v) ≥ v/8 − O(1)`.

*Proof.* Take `T` large, and suppose some row alive at `T` has a partner (otherwise all
`n(T) ≥ T/2 − O(1)` alive rows are side rows). Among these rows let `d` be the one that dies
last, at time `P`. Let `k` be their number. They die at distinct times in `(T,P]`, so
`P ≥ T + k ≥ T + n(T) − s(T−1)`.

* **High levels of `d` in `[T,P)`:** at most `O_d(T) + M` (Lemma 9).
* **Low levels of `d` in `[T,P)`:** by Lemma 11, (H4) and (L_K), all but `K + M` of their
  values are partners `τ(b) ∈ (T,P)` of rows `b > d`. Such a `b` is either alive at `T`, or one
  of the rows `b ≥ T` that die before `P`. Let `ν` be the number of the latter.
* So `P − T ≤ n(T) + ν + K + 2M`: the rows older than `d`, the rows younger than `d`, and `d`
  itself are all among the `n(T)` rows alive at `T`.
* **Rows alive at time `P`:** those born before `T` are side rows, since every other row alive
  at `T` is dead by `P`. Of the `P − T` rows born from `T` on, `ν` are dead. So
  `n(P) ≤ s(T−1) + n(T) + K + 2M`.
* **Population.** (H4) excludes a value that is both a partner and a diagonal value, from `r₀`
  on. Counting blocked values as in (S4) gives `f(a,a) ≤ 2a + 2M + 1`. So
  `n(P) ≥ P/2 − O(1)`.

Together `T + n(T) − s(T−1) ≤ 2s(T−1) + 2n(T) + O(1)`, i.e. `I(T) = T − n(T) ≤ 3s(T−1) + O(1)`.
For the density: by (H4), `τ(r) < f(r,r) ≤ 2r + 2M + 1`, so `I(T) ≥ T/2 − s(T/2) − O(1)`. ∎

**What the proof does not need.** It does not use sources, and it puts no bound on dead levels:
a low level of `d` is paid for by the death of a younger row, which lowers the population by
one. Hypothesis (D) of notes/12 and the hypothesis of §7 are not needed.

**Evidence** (`tools/side_lifetime.cpp` for the cube, `tools/attach3row.cpp` for the boxes; rows
`z ≥ 4g`):

| family | rows with a partner | (H4) violations | low levels (most per row) | of which: partner of an older row |
| --- | --- | --- | --- | --- |
| cube, `z ≤ 2998` | 1755 | 0 | 45 (2) | 0 |
| 3-box, `z ≤ 1100` | 636 | 0 | 238 (4) | 59 |
| 4-box, `z ≤ 700` | 400 | 0 | 172 (5) | 44 |
| 5-box, `z ≤ 500` | 278 | 0 | 169 (6) | 60 |

In every case all the other low levels have the partner of a younger row as their value. So
(H4) holds without exception, (L) holds for the cube, and (L_K) holds for the boxes with `K ≤ 6`.

**Why (H4) is the real obstacle.** (H4) for `a = r` says that a row which is still alive at the
time `f(r,r) ≤ 2r + 2M + 1` never dies. This is exactly what fails in the random model: there a
row can outlive its diagonal value by a long time. So (H4) contains the statement that there
are no late deaths. The gain over (D) is that nothing has to be shown about the levels of a
partner one by one: (H4) and (L) compare only the sequences `τ(r)` and `f(a,a)`, and the
partners that a row picks.

**The case without (L).** If only (H4) holds, the same count gives `n(P) ≤ 2n(T) + O(1)`, which
does not contradict `n(P) ≥ P/2`. A world with (H4), finitely many side rows and `τ(r) ≈ 2r`
would need about half the levels of every row to be low, with partners of *older* rows as their
values. I could not exclude it by counting.

## Tools

* `tools/side_lifetime.cpp N`: checks Lemma 1, Theorem 3, Lemma 4 and Propositions 7, 8 for the
  2D family (0 violations for `N = 6000`), and reports the family-1 statistics quoted in §8 and
  §9.
* `tools/attach3row.cpp g N Z`: for the `g`-box (or any attachment), the defect classification
  of notes/12 and the checks of (H4) and (L) for rows `4g ≤ z ≤ Z`.
* `tools/side_randblock.cpp N ρ [seed]`: the recurrence with random extra blocked values.
