# Huddleston–Shurman's two-column values, proved

Our proof of the three-wide criterion (notes/16) and of `3×ω^ω` rests on Huddleston–Shurman's
two-column Grundy values (9-1)–(9-5) ("Transfinite Chomp", §9). There they are partly
computed ((9-1) is stated from a table) and partly sketched ("the analysis for `2 < i < ω` is
similar"). This note proves them for all heights below `ω^ω`:
* (9-1) by machine, as a statement of Presburger arithmetic (`scripts/hs91_z3.py`, Z3);
* (9-2)–(9-5) by a short transfinite induction that uses only (9-1) and two consequences of it,
  (D0) and (B0), proved the same way.

With this, the proofs of notes/16 depend on Huddleston–Shurman only through the Beanstalk
Lemma (Prop 6.1) and the Side-Top Theorem (Thm 8.1), both of which have complete proofs in the
paper. The recursiveness corollary also uses (9-6), for heights `≥ ω^ω`. It is proved in
[notes/21](21-two-column-above-omega-omega.md), from the lemmas (Diag_i) and (GB_i) below.

## Setting

A two-column position `(h,k)`, `h ≥ k`, has columns of heights `h` and `k`. Every cell may be
taken, and the empty position has value 0 (Huddleston–Shurman's unrestricted convention). The
options of `(h,k)` are:
* `(t,t)` for `t ≤ k`, `t < h` (bite both columns at `t`);
* `(t,k)` for `k < t < h`;
* `(h,t)` for `t < k`.

So `G(h,k)` is the mex of those values. `⊕` is the nim-sum. For ordinals below `ω^ω` it is
the exclusive or of the coefficients, exponent by exponent; this is Conway's ordinal nim-sum,
since `ω^i = 2^{ω·i}`. We use the Nim facts `{e⊕b : e<a} ∪ {a⊕e : e<b} ⊇ [0, a⊕b)`, and that
`e ↦ e⊕b` is a bijection of `[0, ω^i)` for `b < ω^i`. We also use the size bound `G(h,k) ≤ h ⊕̃ k`
(natural sum), so `G(a,b) < ω^i` for `a,b < ω^i`.

Write `c_w = (3^w − 1)/2`, `M_w = {3^w n + c_w : n ∈ ℕ}` and
`L_w = {3^w n + c_w : n ≢ 1 (mod 3)}`. Since `3^w(3n+1) + c_w = 3^{w+1}n + c_{w+1}`,

> (N1) `M_w = L_w ⊔ M_{w+1}`, so `ℕ = L_0 ⊔ … ⊔ L_{u−1} ⊔ M_u` for every `u`, and `ℕ = ⋃_w L_w`.

## Level 0: finite heights (machine proof)

> **(9-1)** `G(u,v) = d + ⌊(3v+1)/2⌋` if `d = u − v` is even, and
> `min(d + ⌊v/2⌋, (3d−1)/2)` if `d` is odd.

`G` is the unique function with `G(0,0) = 0` and `G(u,v) = mex(option values)`. So (9-1) holds iff
the right side `F` satisfies, for all `u ≥ v ≥ 0`:
* (i) `F(u,v)` is not the value of an option;
* (ii) every `n < F(u,v)` is the value of an option.

Both are sentences of Presburger arithmetic. Z3 refutes their negations
(`scripts/hs91_z3.py`, a few seconds). Two consequences are proved the same way:
* **(D0)** `{G(e,e) : e ∈ ℕ} = {n : n ≢ 1 (mod 3)} = L_0`;
* **(B0)** for every `b ∈ ℕ`, `{G(e,e) : e ≤ b} ∪ {G(e,b) : e > b} = ℕ`.

Checks on the encoding:
* `F` agrees with the mex recursion computed by brute force for all `u < 60`;
* changing `F` at the single point `(7,3)` makes Z3 report both (i) and (ii) false.

## Level 1: heights below `ω²`

> **(9-2)** `G(ω·u + a, ω·u + b) = 3^u·G(a,b) + c_u` (`u ≥ 1`, `a ≥ b` finite).
>
> **(9-3)** `G(ω·u + a, ω·v + b) = ω·(u−v) + (a⊕b)` (`u > v ≥ 0`, `a, b` finite).

*Proof,* by simultaneous induction on the position.

**(9-2).** Let `X = (ωu+a, ωu+b)`.
* The diagonal options `(t,t)` with `t = ωw + e < ωu` have values `3^w G(e,e) + c_w` (by
  induction for `w ≥ 1`, trivially for `w = 0`). By (D0) these form `L_w` for each `w`, so
  together they are `ℕ ∖ M_u` by (N1).
* The options with both columns `≥ ωu` are `(ωu+e, ωu+e)` (`e ≤ b`, `e < a`),
  `(ωu+a', ωu+b)` (`b < a' < a`) and `(ωu+a, ωu+b')` (`b' < b`). They correspond exactly to
  the options of the finite position `(a,b)`. By induction their values are
  `{3^u g + c_u : g ∈ Opt(a,b)} ⊆ M_u`.
* The options `(ωu+a, ωw+e)` with `w < u` have infinite values, by (9-3).

So `G(X) = 3^u·mex Opt(a,b) + c_u = 3^u G(a,b) + c_u`.

**(9-3).** Let `X = (ωu+a, ωv+b)`, `u > v`.
* **Finite values.** The diagonal options `(t,t)`, `t ≤ ωv + b`, give `ℕ ∖ M_v` (`t < ωv`, as
  above) and `3^v G(e,e) + c_v` (`t = ωv + e`, `e ≤ b`). The options `(ωv+e, ωv+b)`, `e > b`,
  give `3^v G(e,b) + c_v`. By (B0) these cover `M_v`, hence all of `ℕ`.
* **`ω·k + n` for `1 ≤ k < u−v`.** The options `(ω(v+k)+e, ωv+b)` give `ωk + (e⊕b)`, which
  takes every `n`.
* **`ω(u−v) + n` for `n < a⊕b`.** The options `(ωu+e, ωv+b)` (`e < a`) and `(ωu+a, ωv+e)`
  (`e < b`) give `ω(u−v) + (e⊕b)` and `ω(u−v) + (a⊕e)`. These cover all `n < a⊕b` (Nim).
* **`ω(u−v) + (a⊕b)` is not attained.** Every other option is either finite, has a different
  `ω`-coefficient, or has `e⊕b ≠ a⊕b` (`e ≠ a`) or `a⊕e ≠ a⊕b` (`e ≠ b`).

So `G(X) = ω(u−v) + (a⊕b)`. ∎

## Levels `i ≥ 2`

> **(9-4)** `G(ω^i u + a, ω^i u + b) = ω^{i−1}·u + G(a,b)` (`u ≥ 1`, `a ≥ b`, `a, b < ω^i`).
>
> **(9-5)** `G(ω^i u + a, ω^i v + b) = ω^i·(u−v) + (a⊕b)` (`u > v ≥ 0`, `a, b < ω^i`).

Huddleston–Shurman print (9-4) and (9-5) for "`2 < i < ω`". The case `i = 2` is included here.

*Proof,* by induction on `i`, and within level `i` on the position. Assume both formulas (and
(9-2), (9-3)) for all positions of height `< ω^i`. Two lemmas come first.

**(Diag_i)** `{G(e,e) : e < ω^i} = [0, ω^{i−1})`.
* For `i = 2`, write `e = ωw + e'`. The values `3^w G(e',e') + c_w` form `⋃_w L_w = ℕ` (N1).
* For `i ≥ 3`, write `e = ω^{i−1}w + e'`. The values `ω^{i−2}w + G(e',e')` cover
  `ω^{i−2}w + [0, ω^{i−2})` for each `w`, by (Diag_{i−1}).

**(GB_i)** For `b < ω^i`, `{G(e,e) : e ≤ b} ∪ {G(e,b) : b < e < ω^i} ⊇ [0, ω^i)`. Write
`b = ω^{i−1}β + b̄` with `b̄ < ω^{i−1}`.
* **Values in `[ω^{i−1}, ω^i)`.** For `e = ω^{i−1}w + e''` with `w > β`, (9-5) at level
  `i−1` (or (9-3)) gives `G(e,b) = ω^{i−1}(w−β) + (e''⊕b̄)`. These cover every
  `ω^{i−1}k + n` with `k ≥ 1`.
* **Values in `[0, ω^{i−1})`, case `i ≥ 3`.**
  * The diagonal below `ω^{i−1}β` gives `[0, ω^{i−2}β)`, by (Diag_{i−1}) and (9-4).
  * The positions `(ω^{i−1}β + e'', ω^{i−1}β + e'')` (`e'' ≤ b̄`) and
    `(ω^{i−1}β + e'', ω^{i−1}β + b̄)` (`e'' > b̄`) give `ω^{i−2}β + G(e'',e'')` and
    `ω^{i−2}β + G(e'',b̄)`.
  * By (GB_{i−1}) these cover `ω^{i−2}β + [0, ω^{i−1}) = [ω^{i−2}β, ω^{i−1})`.
* **Values in `[0, ω)`, case `i = 2`.** The same argument with (9-2), (N1) and (B0) gives
  `(ℕ ∖ M_β) ∪ (3^β ℕ + c_β) = ℕ`.

**(9-4).** Let `X = (ω^i u + a, ω^i u + b)`.
* The diagonal options below `ω^i u`, `t = ω^i w + e` with `w < u`, have values
  `ω^{i−1}w + G(e,e)`. By (Diag_i) and induction these are exactly `[0, ω^{i−1}u)`.
* The options with both columns `≥ ω^i u` correspond to the options of `(a,b)`. By induction
  their values are `ω^{i−1}u + g`, `g ∈ Opt(a,b)`, all below `ω^i` since `G(a,b) < ω^i`.
* The options `(ω^i u + a, ω^i w + e)` with `w < u` have values `≥ ω^i`, by (9-5).

So `G(X) = ω^{i−1}u + G(a,b)`.

**(9-5).** Let `X = (ω^i u + a, ω^i v + b)`, `u > v`.
* **Values below `ω^i`.** The diagonal options below `ω^i v` give `[0, ω^{i−1}v)`. The options
  `(ω^i v + e, ω^i v + e)` (`e ≤ b`) and `(ω^i v + e, ω^i v + b)` (`b < e < ω^i`) give
  `ω^{i−1}v + G(e,e)` and `ω^{i−1}v + G(e,b)`, by (9-4). By (GB_i) these cover
  `ω^{i−1}v + [0, ω^i) = [ω^{i−1}v, ω^i)`.
* **`ω^i k + n` for `1 ≤ k < u−v`.** The options `(ω^i(v+k) + e, ω^i v + b)` give
  `ω^i k + (e⊕b)`, every `n < ω^i`.
* **`ω^i(u−v) + n` for `n < a⊕b`.** Nim, as in (9-3).
* **`ω^i(u−v) + (a⊕b)` is not attained**, as in (9-3).

So `G(X) = ω^i(u−v) + (a⊕b)`. ∎

## Consequences for notes/16

All the inputs (F1)–(F4) of notes/16 are now proved for heights below `ω^ω`:
* (F1) is (9-3), (9-5);
* (F2) is the size bound together with (9-2), (9-4);
* (F3) uses `G(ω^{i+1}, ω^{i+1}) = ω^i`, which is (9-4) with `u = 1`, `a = b = 0`, or directly
  (Diag_{i+1});
* (F4) uses (9-4) and (F1).

So Theorem 2 of the preprint and `3×ω^ω` being P depend on Huddleston–Shurman only through:
* the Beanstalk Lemma (Prop 6.1, via their Fundamental Theorem);
* the Side-Top Theorem (Thm 8.1), whose proof in the paper is complete.

The recursiveness corollary also needs (9-6) for heights `≥ ω^ω`, which is proved in
[notes/21](21-two-column-above-omega-omega.md).
