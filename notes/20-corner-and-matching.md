# The corner bite never wins `3×n`, and the matching at a death time

This note records an attempt at the three sharp statements about ordinary three-row Chomp left
open in [notes/13](13-side-class-theorem.md) and [notes/19](19-remaining-lifetimes.md):

* (a) `τ` is increasing on the non-side rows;
* (b) `I(T) ≤ s(T−1)`, the sharp form of "(B′)";
* (c) `[k,k,k−1]` is never a P-position for `k ≥ 3`.

**Result.** (c) is proved, with an elementary proof that is also checked in Lean. It removes
an assumption from the cube-family notes: the `3×n` rectangle has Grundy value at least 2 for
every `n`. (a) and (b) are not proved. §3 and §4 say what was tried and where it stops.

Notation as in notes/13 and notes/19: `[a,b,c]` is the three-row position with rows
`a ≥ b ≥ c`; `τ(x)` is the `p > x` with `[p,p,x]` P, for `x` outside the side class `𝒮`;
`D = {f(a,a)}` are the diagonal values, `d = f(a,a)` being the first row of the P-position
`[d,a,a]`; `s(v) = #(𝒮 ∩ [0,v])`; `I(T) = #{x : τ(x) ≤ T}`.

## 1. The corner bite

> **Theorem 1.** For every `k ≥ 3`, `[k,k,k−1]` is an N-position.

So on the `3×n` rectangle with `n ≥ 3`, taking only the corner cell is never a winning first
move. For `n = 2` it is the winning move: `[2,2,1]` is P.

*Proof.* Induction on `k`. For `k = 3`, `[3,3,2]` moves to `[3,1,1]`, which is P.

Let `k ≥ 4`, assume `[k−1,k−1,k−2]` is N, and suppose `[k,k,k−1]` is P. Its option
`X = [k,k,k−2]` is then N, so `X` has a P option. The options of `X` are:

* `[j,j,j]` for `1 ≤ j ≤ k−2`. Rectangles are N.
* `[k−1,k−1,k−2]`. This is N by induction.
* `[k,j,j]` for `j ≤ k−2` and `[k,k,j]` for `j < k−2`. These are also options of `[k,k,k−1]`,
  so they are N.
* `[k,k−1,k−2]`. It moves to `[k,k−1,0]`, two rows of lengths `k` and `k−1`, which is P. So it
  is N.

So `X` has no P option, a contradiction. ∎

The proof uses nothing about `f`. It is formalised in `lean/Chomp/Corner.lean`
(`corner_isN`, `board_corner_isN`).

> **Corollary 2.** `τ(x) ≥ x + 2` for every non-side `x ≥ 2`.

> **Corollary 3.** The `3×n` rectangle has Grundy value at least 2, for every `n ≥ 1`.
> Equivalently, `[k,k,k | cube]` is never a P-position: the single-cube family of notes/12 has
> no finite P cut.

*Proof.* `3×1` is a column of three cells, of value 2, and `G(2,2,2) = 4`. Let `k ≥ 3` and
suppose `G(k,k,k) = 1`. Then no option of the rectangle has value 1, and the same holds for
`C = [k,k,k−1]`, because every option of `C` is an option of the rectangle. So `G(C) ≤ 1`.
`C` is itself an option of the rectangle, so `G(C) ≠ 1`. Hence `C` is P, against Theorem 1.
Rectangles are N, so `G(k,k,k) ≠ 0`. ∎

Until now this was checked only for `k ≤ 50001` (notes/12, "No finite P cut for the single
cube"), and notes/19 §8–9 assumed it.

The same method gives the next case.

> **Lemma 4.** `[q+2, q, 2]` is P for every `q ≥ 2`.

*Proof.* Induction on `q`. The options of `[q+2,q,2]` and a P reply to each:
`[j,j,2]` with `3 ≤ j ≤ q` moves to `[j,j−2,2]` (or `[3,3,2]` to `[3,1,1]`);
`[q+1,q,2]` moves to `[q+1,q,0]`;
`[q+2,j,2]` with `2 ≤ j < q` moves to `[j+2,j,2]`;
`[q+2,1,1]` moves to `[3,1,1]`, and `[q+2,0,0]` to `[1,0,0]`;
`[q+2,q,1]` moves to `[2,2,1]`, and `[q+2,q,0]` to `[q+1,q,0]`;
rectangles are N. ∎

> **Theorem 5.** For every `k ≥ 6`, `[k,k,k−2]` is an N-position. So `τ(x) ≥ x + 3` for every
> non-side `x ≥ 4`.

(`[5,5,3]` is P, so the bound on `k` is sharp.)

*Proof.* `[6,6,4]` moves to `[6,3,3]`, which is P. Let `k ≥ 7` and suppose `[k,k,k−2]` is P.
Then `X = [k,k,k−3]` is N. Its options are rectangles; options of `[k,k,k−2]`;
`[k−2,k−2,k−3]`, which is N by Theorem 1; `[k,k−1,k−3]`, which moves to `[k,k−1,0]`;
`[k,k−2,k−3]`, which moves to `[k,k−2,2]`, P by Lemma 4; and `[k−1,k−1,k−3]`. So
`[k−1,k−1,k−3]` is P. Repeating, `[6,6,4]` is P, which is false. ∎

Both theorems are instances of one pattern, described next.

## 2. The matching at a death time

> **Lemma 6 (matching).** Let `[p,p,x]` be P, and let `b < x` be a row with no P-position
> `[j,j,b]`, `b < j < p` (so `b` is a side row or `τ(b) > p`). Then there is exactly one level
> `j` with `b < j < p` and `[p,j,b]` P. Different rows `b` have different levels.

*Proof.* `[p,p,b]` is an option of `[p,p,x]`, so it is N and has a P option. The options
`[p,j,j]` (`j ≤ b`) and `[p,p,j]` (`j < b`) are options of `[p,p,x]`, hence N. Rectangles are N.
The options `[j,j,b]` with `b < j < p` are excluded by assumption. What remains is `[p,j,b]`
with `b < j < p`. Two P-positions `[p,j,b]` and `[p,j′,b]` are one move apart, and so are
`[p,j,b]` and `[p,j,b′]`. ∎

A row `b < x` with `τ(b) < p` may also have such a level; the lemma says nothing about it.

In the language of notes/19: when row `x` dies at time `p`, every older row that is still alive
has picked the value `p` at a level of its own. By (S2) all the levels in `(x,p)` are used. The
remaining-lifetime lemma counts the levels in `(x,p)` against the rows. Lemma 6 goes the other
way and counts the rows against the levels.

**How Theorems 1 and 5 follow.** A row with few levels available must use one that is already
taken. Row 0 picks `p` at level `p−1` (two-row Chomp), and row 2 picks `p` at level `p−2`
(Lemma 4). If `x = p−1`, the row `p−2` has only the level `p−1` available, so it is dead:
`τ(p−2) = p−1`. This is the induction step of Theorem 1. If `x = p−2`, the row `p−3` has the
levels `p−2` and `p−1`, both taken, so it is dead, with `τ(p−3) ∈ {p−2, p−1}`.

To go further one needs to know which row picks `p` at level `p−3`, `p−4`, …. A side row
eventually has constant offset `1 + #(non-side rows below it)` (notes/19, Proposition 7), so
the offsets that occur are `1, 2, 4, 5, 6, 7, 9, …`. But there is no bound on when a side row
reaches its final offset, and offset 3 never becomes constant. So this method stops at
Theorem 5. A proof that `τ(x) − x → ∞` along these lines would need control of the transient
of every side row.

> **Corollary 7.** For every non-side `x`, with `p = τ(x)`,
> `#{b < x : b alive at time p} ≤ I(p)`. In particular `s(x−1) ≤ I(τ(x))`.

*Proof.* The levels `j_b` of Lemma 6 are distinct, and at each of them the diagonal value
`f(j_b,j_b)` exceeds `p` by (S5). The levels `q < p` with `f(q,q) > p` number
`p − n(p) = I(p)`. ∎

This bounds side elements by deaths. Theorem 3 of notes/19 bounds deaths by side elements,
`I(T) ≤ 2 s(T−1)`. Numerically the corollary has least slack 0.

> **Corollary 8 (conditional).** If `τ` is increasing on the non-side rows, then
> `s(v) ≤ v/2 + 1` for every `v`.

*Proof.* If `τ` is increasing, the rows that have died by time `τ(x)` are the non-side rows
`≤ x`, so `I(τ(x)) = x + 1 − s(x)`. Corollary 7 gives `2 s(x−1) ≤ x + 1` for non-side `x`.
For side `v`, apply this at the next non-side row. ∎

Unconditionally, only `s(v) ≤ (2v+3)/3` is known (from `n(t) ≤ (2t+1)/3`).

## 3. Monotonicity of `τ`: not proved

Suppose `x < y` are non-side and `τ(y) = t < τ(x)`. Lemma 6 for `[t,t,y]` and the row `x` gives
a level `j ∈ (x,t)` with `[t,j,x]` P. By the argument above `j ≠ t−1` and `j ≠ t−2`, since
those levels belong to rows 0 and 2. So

> an inversion `x < y`, `τ(y) < τ(x)` needs `τ(y) ≥ x + 4`.

Take the first time `t` at which a row dies while an older non-side row `x₀` is alive, with
`x₀` the oldest such row. Before `t`, deaths occur in order of birth. So no row dies between
the death of the previous non-side row and `t`, and all those times are diagonal values. If
`x₀` was born after that death, then `x₀+1, …, t−1` are all diagonal values, at least three of
them.

Three consecutive diagonal values do occur (`72, 73, 74` is the first case), so this does not
finish the proof. What is missing is a reason why `x₀` cannot have picked the value `t` at a
level `≤ t−3`. In the data it never does: `τ` is increasing for `x ≤ 50000`.

The equivalent forms in notes/19 §6 (every pick of a non-side row exceeds its partner; the
greedy rule) were tried through the P-positions involved: `[p,p,x]`, `[t,t,y]`, `[t,j,x]` and
the positions given by (S2) at the levels `t` and `j`. They are pairwise not adjacent, so no
contradiction arises from them alone.

## 4. The sharp inequality `I(T) ≤ s(T−1)`: not proved

Equivalent forms:

* `n(T) ≥ #(non-side rows below T)`: at every time there are at least as many diagonal values
  as non-side rows;
* `2 s(T−1) + L(T) ≥ T`, where `L(T)` is the number of non-side rows alive at time `T`;
* the `i`-th diagonal value, in increasing order, is at most the `i`-th non-side row plus a
  constant. In the data the two sequences agree in most places:

  ```
  non-side rows:    1 3 4 6 8 10 12 13 15 16 18 20 21 23 25 27 29 30 32 33 35 37 39
  diagonal values:  1 3 4 6 8 10 11 13 15 16 18 20 21 24 25 27 28 30 32 34 35 37 39
  ```

The proof of `I(T) ≤ 2 s(T−1)` loses its factor 2 in the step `n(T′) ≥ T′/2`, which is the
bound `f(a,a) ≤ 2a+1`. The true slope of the diagonal is `1 + 1/√2`. Exactly,
`f(a,a) = 2a + 1 − c(a) − e(a)`, where `c(a)` is the number of values that are both a pick at
level `a` and an older diagonal value, and `e(a)` the number of older diagonal values above
`f(a,a)`. So a sharp count needs the number of these coincidences. Even the weakest case is
not proved: `f(a,a) ≤ 2a` for `a ≥ 2` holds in the data and says only that `c(a) + e(a) ≥ 1`.
It follows if `a+1` or `a+2` is a diagonal value (rows 0 and 2 pick them), but two consecutive
partner values occur (`22, 23`).

If (b) held, the slope argument of notes/19 §5 would give upper density at least
`(3 − √5)/2 ≈ 0.382` in place of `1/4`. So (b) is at least as hard as improving the density
bound. No injection from dead rows to side rows was found: the matching of Lemma 6 assigns
levels to rows, and the rows it involves include non-side rows that are still alive.

## Tools

`scripts/corner_matching_check.py [N]` builds the table of `f` up to `N` and checks Theorems 1
and 5, Lemma 4, Lemma 6, Corollary 7 (least slack 0) and `f(a,a) ≤ 2a`, and reports the first
three consecutive diagonal values. All pass for `N = 1500`. `τ(x) ≥ x + 2` for
`2 ≤ x ≤ 50000` was already in notes/12. Theorem 1 is `corner_isN` in `lean/Chomp/Corner.lean`.
