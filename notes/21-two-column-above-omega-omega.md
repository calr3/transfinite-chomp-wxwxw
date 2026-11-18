# Two columns of height `≥ ω^ω`: Huddleston–Shurman's (9-6), proved

[notes/18](18-two-column-values.md) proves Huddleston–Shurman's two-column Grundy values
(9-1)–(9-5), which cover heights below `ω^ω`. Their last formula, for larger heights, is

> **(9-6)** `G((ω^ω)^j·u + a, (ω^ω)^j·v + b) = (ω^ω)^j·G(u,v) + G(a,b)` if `u = v`, and
> `= (ω^ω)^j·G(u,v) + (a ⊕ b)` if `u > v`,
>
> for `j > 0`, `0 < u < ω^ω`, `u ≥ v` and `a, b < (ω^ω)^j`.

The paper derives it in a few lines, by building up examples ("essentially the same argument
now gives … and similarly for all ordinals `j`"). This note gives a proof. It is short because
the statement is an instance of a general fact: the two-column value function is self-similar
at every scale `Ω` that has two properties, and `ω^ω` is the first such scale.

Setting and notation are those of notes/18: positions `(h,k)`, `h ≥ k`, with options `(t,t)`
for `t ≤ k`, `t < h`; `(t,k)` for `k < t < h`; `(h,t)` for `t < k`. `G` is the unrestricted
Grundy value, `⊕` the ordinal nim-sum. `V(h,k)` denotes the set of values of the options of
`(h,k)`, so `G(h,k) = mex V(h,k)`.

## 1. Scales

Call an ordinal `Ω` a **scale** if

* **(A)** `Ω = ω^γ` for some `γ ≥ 1`;
* **(D)** `{G(e,e) : e < Ω} = [0, Ω)`;
* **(B)** for every `b < Ω`, `{G(e,e) : e ≤ b} ∪ {G(e,b) : b < e < Ω} ⊇ [0, Ω)`.

(A) gives three things. `[0,Ω)` is closed under `⊕`, and `e ↦ a ⊕ e` permutes it for `a < Ω`,
because `ω^γ = 2^{ω·γ}` is a power of 2. And `G(a,b) < Ω` for `a, b < Ω`, by the size bound
`G(a,b) ≤ a ⊕̃ b` (natural sum).

Every ordinal is uniquely `Ω·u + a` with `a < Ω`, and `Ω·u + a ≥ Ω·v + b` iff `u > v`, or
`u = v` and `a ≥ b`. For an ordinal `g` write `B(g) = Ω·g + [0,Ω)`, the `g`-th block.

> **Theorem 1 (self-similarity).** Let `Ω` be a scale. For all ordinals `u ≥ v` and all
> `a, b < Ω` (with `a ≥ b` if `u = v`),
>
> `G(Ω·u + a, Ω·v + b) = Ω·G(u,v) + G(a,b)` if `u = v`,
> `G(Ω·u + a, Ω·v + b) = Ω·G(u,v) + (a ⊕ b)` if `u > v`.

There is no bound on `u` and `v`.

*Proof.* Induction on the position `X = (Ω·u + a, Ω·v + b)`. Write an option's changed height
as `t = Ω·w + e`, `e < Ω`.

**Case `u = v`.**
* Diagonal options `(t,t)` with `w < u`. By induction the value is `Ω·G(w,w) + G(e,e)`. As
  `e` runs through `[0,Ω)` this fills the block `B(G(w,w))`, by (D).
* Options `(Ω·u + a, t)` with `w < u`. By induction the value is `Ω·G(u,w) + (a ⊕ e)`. As `e`
  runs through `[0,Ω)` this fills the block `B(G(u,w))`.
* Options with both heights `≥ Ω·u`. They are `(Ω·u + e, Ω·u + e)` for `e ≤ b`, `e < a`;
  `(Ω·u + a′, Ω·u + b)` for `b < a′ < a`; and `(Ω·u + a, Ω·u + b′)` for `b′ < b`. They
  correspond to the options of `(a,b)`, and by induction their values are `Ω·G(u,u) + g`,
  `g ∈ V(a,b)`.

The options of `(u,u)` are `(w,w)` and `(u,w)` for `w < u`. So the first two families fill
exactly the blocks `B(g)`, `g ∈ V(u,u)`. Since `G(u,u) = mex V(u,u)`, every ordinal below
`Ω·G(u,u)` is attained, and inside `B(G(u,u))` only the values `Ω·G(u,u) + g`, `g ∈ V(a,b)`,
are. The least ordinal not attained is `Ω·G(u,u) + mex V(a,b) = Ω·G(u,u) + G(a,b)`.

**Case `u > v`.**
* Diagonal options `(t,t)` with `w < v`: the blocks `B(G(w,w))`, as before.
* Options `(t, Ω·v + b)` with `v < w < u`: value `Ω·G(w,v) + (e ⊕ b)`, filling `B(G(w,v))`.
* Options `(Ω·u + a, t)` with `w < v`: value `Ω·G(u,w) + (a ⊕ e)`, filling `B(G(u,w))`.
* Options with `w = v` that keep the left column in the block of the right one:
  `(Ω·v + e, Ω·v + e)` for `e ≤ b` and `(Ω·v + e, Ω·v + b)` for `b < e < Ω`. By induction (case
  `u = v`) their values are `Ω·G(v,v) + G(e,e)` and `Ω·G(v,v) + G(e,b)`. By (B) they fill
  `B(G(v,v))`.
* Options `(Ω·u + e, Ω·v + b)` for `e < a` and `(Ω·u + a, Ω·v + e)` for `e < b`: values
  `Ω·G(u,v) + (e ⊕ b)` and `Ω·G(u,v) + (a ⊕ e)`.

The options of `(u,v)` are `(w,w)` for `w ≤ v`, `(w,v)` for `v < w < u` and `(u,w)` for
`w < v`. So the first four families fill exactly the blocks `B(g)`, `g ∈ V(u,v)`, and every
ordinal below `Ω·G(u,v)` is attained. Inside `B(G(u,v))` only the last family contributes. By
the Nim fact `{e ⊕ b : e < a} ∪ {a ⊕ e : e < b} ⊇ [0, a ⊕ b)`, and since `e ⊕ b ≠ a ⊕ b` for
`e ≠ a`, the least ordinal not attained is `Ω·G(u,v) + (a ⊕ b)`. ∎

For `v = 0` the theorem reads `G(Ω·u + a, b) = Ω·u + (a ⊕ b)` for `b < Ω`.

## 2. Which ordinals are scales

> **Proposition 2.** `ω^ω` is a scale.

*Proof.* notes/18 proves, for every finite `i ≥ 2`, (Diag_i) `{G(e,e) : e < ω^i} = [0, ω^{i−1})`
and (GB_i) `{G(e,e) : e ≤ b} ∪ {G(e,b) : b < e < ω^i} ⊇ [0, ω^i)` for `b < ω^i`. Taking the
union over `i` gives (D) and (B) for `ω^ω`. ∎

A finite power `ω^i` is not a scale: by (Diag_i) the diagonal below `ω^i` reaches only
`ω^{i−1}`. This is why (9-4) has the factor `ω^{i−1}` where (9-6) has `(ω^ω)^j`. At `ω^ω` the
diagonal has caught up.

> **Proposition 3.** If `Ω` and `Ω′` are scales, so is `Ω·Ω′`. The supremum of an increasing
> sequence of scales is a scale.

*Proof.* (A) is clear in both cases. Let `Ω` and `Ω′` be scales. By Theorem 1 for `Ω`:

* (D) for `Ω·Ω′`. For `e = Ω·w + e′` with `w < Ω′`, `G(e,e) = Ω·G(w,w) + G(e′,e′)`. As `e′`
  varies this fills `B(G(w,w))`, and `G(w,w)` runs through `[0,Ω′)` by (D) for `Ω′`.
* (B) for `Ω·Ω′`. Let `b = Ω·β + b̄` with `β < Ω′`, `b̄ < Ω`, and let `Ω·g + n` be a target,
  `g < Ω′`, `n < Ω`. By (B) for `Ω′`, `g` is `G(w,w)` with `w ≤ β` or `G(w,β)` with
  `β < w < Ω′`.
  * If `g = G(w,w)` with `w < β`: take `e = Ω·w + e′` with `G(e′,e′) = n`, by (D) for `Ω`.
  * If `g = G(w,β)` with `w > β`: take `e = Ω·w + (n ⊕ b̄)`. Then `G(e,b) = Ω·g + n`.
  * If `g = G(β,β)`: by (B) for `Ω`, `n` is `G(e′,e′)` with `e′ ≤ b̄` or `G(e′,b̄)` with
    `e′ > b̄`. Take `e = Ω·β + e′`.

For a supremum `Ω = sup Ω_i`: (D) is the union of the `[0,Ω_i)`. For (B), `b < Ω_i` for some
`i`, and (B) for each larger `Ω_{i′}` gives `[0,Ω_{i′})`. ∎

> **Corollary 4.** `(ω^ω)^j = ω^{ω·j}` is a scale for every ordinal `j ≥ 1`. Hence (9-6) holds
> for every ordinal `j ≥ 1`, and for all ordinals `u ≥ v`, not only `u < ω^ω`.

*Proof.* Induction on `j` with Propositions 2 and 3, since `(ω^ω)^{j+1} = (ω^ω)^j·ω^ω` and
`(ω^ω)^j = sup_{i<j} (ω^ω)^i` for limit `j`. Then apply Theorem 1. ∎

## 3. All two-column values

(9-1)–(9-6) now determine `G(h,k)` for all ordinals `h ≥ k`, with proofs:

* if `h < ω^ω`, use (9-1)–(9-5);
* otherwise let `j` be the largest ordinal with `ω^{ω·j} ≤ h`. Then `h = ω^{ω·j}·u + a` and
  `k = ω^{ω·j}·v + b` with `0 < u < ω^ω`, `v ≤ u` and `a, b < ω^{ω·j}`. `G(u,v)` is given by
  (9-1)–(9-5), and `G(a,b)` by recursion, with a smaller `j`.

Examples, in agreement with the values Huddleston–Shurman list:
`G(ω^ω, ω^ω) = ω^ω·2`, `G(ω^ω·2, ω^ω) = ω^ω`, `G(ω^ω·ω, ω^ω·ω) = ω^ω`,
`G(ω^ω·ω², ω^ω·ω²) = ω^ω·ω`, and `G(ω^ω, t) = ω^ω + t` for `t < ω^ω`.

One sentence of the paper, as printed, does not agree with (9-6): "until catching up at
`G((ω^ω)², (ω^ω)²) = (ω^ω)²`". The formula gives `(ω^ω)²·G(1,1) = (ω^ω)²·2`. Directly: the
positions `(e,e)` with `e < (ω^ω)²` have all the values below `(ω^ω)²`, and the positions
`((ω^ω)², t)` with `t < (ω^ω)²` have the values `(ω^ω)² + t`. What catches up at `(ω^ω)²` is
the set of diagonal values, not the value of the position.

## 4. Consequences

* The recursiveness corollary of notes/16 (the P-positions of three-column Chomp with ordinal
  heights form a recursive set) used (9-6) for heights `≥ ω^ω` as an input from the paper. It
  is now proved here. The inputs taken from Huddleston–Shurman without re-proof are the
  Beanstalk Lemma and the Side-Top Theorem, both with complete proofs in their paper.
* Theorem 1 is about two columns only. For three columns the analogous statement fails already
  at `ω^ω`: `3×ω^ω` is a P-position, so its unrestricted value is 1, not `ω^ω·G(1,1,1)`.

## Checks

`scripts/hs96_check.py [SAMPLES] [J] [SEED]` tests the formula as a mex recursion on random
positions with heights below `(ω^ω)^J`: no option has the value `G(h,k)`, and every smaller
ordinal on a grid of small coefficients is the value of an option. 36 positions with `J = 2`
and 30 with `J = 3` are consistent. With the low part replaced by `a ⊕ b` in all cases, or by
`G(a,b)` in all cases, most positions fail, so the test can tell the formula from near misses.
