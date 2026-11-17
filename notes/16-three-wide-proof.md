# A complete proof of the three-wide criterion, and of `3×ω^ω`

Huddleston and Shurman ("Transfinite Chomp", MSRI 42, 2002, §10) characterise the P-positions
of three-column Chomp by a decomposition into bottom and top pieces and the criterion (10-1).
They deduce that the tall box `3×ω^ω` is a P-position. Their proof of (10-1) is a sketch, and it
needs the side class `𝒮` to be infinite ([notes/15](15-hs-audit.md)), which they do not prove.

This note gives (10-1) in closed form ([notes/15](15-hs-audit.md)) and proves it completely
from the following inputs:
* the paper's two-column values (9-1)–(9-5) (§9);
* the Beanstalk Lemma (Prop 6.1);
* the Side-Top Theorem (Thm 8.1);
* the infinitude of `𝒮` ([notes/13](13-side-class-theorem.md)).

The Side-Top proof in the paper is complete. The §9 derivations are brief (the finite formula
(9-1) is stated from computation), so we checked (9-1)–(9-5) independently (notes/15):
* (9-1) by brute force for heights `< 120`;
* (9-2)–(9-5) as a mex recursion on 450 random positions below `ω⁴`.

Only consequences (F1)–(F4) below are used. Given these inputs, `3×ω^ω` is P.

## Setting and notation

* **Positions.** A position `(u, v, x)` has three columns of ordinal heights `u ≥ v ≥ x`,
  with the poison at the bottom of column 0.
* **Moves.** The bite `(e, t)` (column `e`, height `t`) cuts every column `≥ e` down to height
  `t`; `(0, 0)` is excluded. Options are smaller in the product order, so the game is
  well-founded.
* **Two-column values.** `G(h, k)` (`h ≥ k`) is the Grundy value of the two-column piece with
  heights `h, k` in which every cell may be taken, the empty piece having value 0. This is
  Huddleston–Shurman's unrestricted value, given by (9-1)–(9-5).
* **Nim-sum.** `⊕` is the nim-sum of ordinals below `ω^ω`: the binary XOR of the coefficients,
  exponent by exponent.
* **Decomposition.** Fix `x` with `ω ≤ x < ω^ω` and let `i = deg x ≥ 1`. Write

  `u = ω^{i+1}·U + ω^i·u_i + a`, `v = ω^{i+1}·V + ω^i·v_i + b`, `x = ω^i·x_i + c`,

  with `u_i, v_i, x_i < ω`, `x_i ≥ 1`, and `a, b, c < ω^i`. `U` and `V` are arbitrary ordinals,
  so `u` and `v` may be as large as we like.

**The families.** `(u, v, x)` belongs to

* **`𝒜`** if `U = V = 0`, `u_i = v_i + x_i` (so `v_i ≥ x_i`), and the top condition holds:
  * `a = G(b, c)` if `v_i = x_i`;
  * `a ⊕ b ⊕ c = 0` if `v_i > x_i`;
* **`ℬ`** if `U = V = m` with `1 ≤ m < ω`, `x_i = m + u_i − v_i` (so `u_i ≥ v_i`), and the top
  condition holds:
  * `c = G(ω^i·u_i + a, ω^i·u_i + b)` if `u_i = v_i` (then `x_i = m`);
  * `a ⊕ b ⊕ c = 0` if `u_i > v_i`.

> **Theorem.** Let `u ≥ v ≥ x` with `ω ≤ x < ω^ω`. Then `(u, v, x)` is a P-position iff it lies
> in `𝒜 ∪ ℬ`.

This is criterion (10-1) restated; `scripts/hs_families.py` checks the equivalence on 200000
positions.

## Inputs

From §9 (two columns; all are read off (9-1)–(9-5)), for `i ≥ 1` and `a, b < ω^i`:
* **(F1)** If `w > w′` then `G(ω^i·w + a, ω^i·w′ + b) = ω^i·(w − w′) + (a ⊕ b) ≥ ω^i`.
* **(F2)** `G(a, b) < ω^i` and `G(ω^i·w + a, ω^i·w + b) < ω^i`. The latter equals
  `ω^{i−1}·w + G(a,b)` for `i ≥ 2`, and `3^w·G(a,b) + (3^w−1)/2` for `i = 1`.
* **(F3)** Every `γ < ω^i` is `G(h, h)` for some `h < ω^{i+1}`. Each natural `n` is uniquely
  `3^k·⌊(3h₀+1)/2⌋ + (3^k−1)/2`, which is `G(ω·k + h₀, ω·k + h₀)`, and (F2) shifts this up the
  exponents. Huddleston–Shurman use the same inverse ("`G(2×a) = c`, `a` unique").
* **(F4)** For `u, v ≥ ω`, write `ω\u` for the `t` with `ω + t = u`. If `(u, v, x) ∈ 𝒜 ∪ ℬ` then
  `G(ω\u, ω\v)` is infinite:
  * in `𝒜`, the ω^i-coefficients differ (`u_i > v_i ≥ 1`), so this is (F1);
  * in `ℬ`, (9-4) gives `ω^i·m + G(ω^i·u_i + a, ω^i·v_i + b) ≥ ω`.
* Grundy values: a position's value differs from each option's value, and every smaller value is
  the value of some option.

From the rest of the paper and from notes/13:
* **(BS)** Beanstalk Lemma. A position with exactly one infinite column (`u ≥ ω > v`) has
  infinite Grundy value, so it is N.
* **(ST)** Side-Top Theorem. For `x < ω ≤ v`, `(u, v, x)` is P iff `x ∈ 𝒮` and
  `G_𝒮(x) = G(ω\u, ω\v)`. Here `G_𝒮(x)` is the index of `x` in `𝒮`.
* **(S∞)** `𝒮` is infinite (notes/13).
* Finite rectangles `(t, t, t)`, `1 ≤ t < ω`, are N (strategy stealing).

## Proof

Induction on the position. Options with third column `x′ < ω` have known outcomes:
* `v′ ≥ ω`: decided by (ST);
* `u′ ≥ ω > v′`: N by (BS);
* all finite: the only finite options arising below are rectangles `(t,t,t)`, which are N.

Options with `x′ ≥ ω` are P iff they lie in `𝒜 ∪ ℬ`, by induction. So it suffices to show:

1. no member of `𝒜 ∪ ℬ` has an option that is a member or is otherwise P;
2. every non-member with `ω ≤ x < ω^ω` has an option that is a member or a Side-Top P-position.

Two remarks are used repeatedly.
* In each top condition, the given top data determine the remaining one, and changing one piece
  breaks the condition. For nim-sums this is clear. For `a = G(b,c)` and
  `c = G(ω^i w + a, ω^i w + b)`, the changed two-column piece is an option of the original one,
  so it has a different value.
* Membership needs `U = V` finite, the stated relation between `u_i, v_i, x_i` and `m`, and the
  top condition. These bottom data (`i, U, V, u_i, v_i, x_i`) are determined by the coefficients.

### Part 1: members have no P option

Let `X = (u, v, x) ∈ 𝒜 ∪ ℬ` and let `Y` be the result of the bite `(e, t)`.

**`e = 2`** (`Y = (u, v, t)`, `t < x`):
* `t = ω^i x_i + c′` with `c′ < c`: only `c` changes, which breaks the top condition.
* `t = ω^i x′ + c′` with `1 ≤ x′ < x_i`: the bottom relation fails. In `𝒜`,
  `u_i = v_i + x_i ≠ v_i + x′`. In `ℬ`, `x′ < x_i = m + u_i − v_i`.
* `ω ≤ t < ω^i` (`i ≥ 2`, `deg t = i′ < i`): with respect to `i′`, the high parts are
  `U′ = u ÷ ω^{i′+1}` and `V′ = v ÷ ω^{i′+1}`.
  * In `ℬ`, `U′ ≥ ω^{i−i′}·m` is infinite.
  * In `𝒜`, `U′` is infinite unless `i′ = i−1`. Then `U′ = u_i ≠ v_i = V′`.
  * Either way `Y ∉ 𝒜 ∪ ℬ`.
* `t < ω`: by (ST) and (F4), `Y` is P only if `G_𝒮(t)` (finite) equals an infinite value. So
  `Y` is N.

**`e = 1`** (`Y = (u, t, min(x,t))`, `t < v`):
* **`t ≥ x`**, so `Y = (u, t, x)`.
  * In `ℬ`:
    * if `t ÷ ω^{i+1} < m`, then `V′ ≠ U`;
    * otherwise `t = ω^{i+1}m + ω^i v′ + b′`. If `v′ = v_i` (`b′ < b`) only `b` changes. If
      `v′ < v_i`, the relation needs `x_i = m + u_i − v′ > x_i`.
  * In `𝒜`, `t = ω^i v′ + b′` with `x_i ≤ v′ ≤ v_i`.
    * If `v′ = v_i`, only `b` changes.
    * If `x_i ≤ v′ < v_i`, membership needs `u_i = v′ + x_i`, but `u_i = v_i + x_i`.
* **`ω ≤ t < x`**, so `Y = (u, t, t)` has `v′ = x′`.
  * If `deg t < i`, then `V′ = 0` but `U′ ≥ 1`.
  * If `deg t = i`, then `t = ω^i x′ + c′` with `x′ ≤ x_i`, and `V′ = 0`. If `X ∈ ℬ` then
    `U = m ≠ V′`, so `Y` is not a member.
  * For `X ∈ 𝒜`, membership of `Y` needs `u_i = 2x′`. Since `u_i = v_i + x_i ≥ 2x_i ≥ 2x′`, this
    forces `v_i = x_i = x′`. Then `t = ω^i x_i + c′` with `c′ < c`, and the top condition needs
    `a = G(c′, c′)`. But `a = G(b, c)` and `(c′, c′)` is an option of `(b, c)`.
* **`t < ω`**: `Y` has one infinite column, so it is N by (BS).

**`e = 0`** (`Y = (t, min(v,t), min(x,t))`, `1 ≤ t < u`):
* **`t ≥ v`**, so `Y = (t, v, x)` and `t ÷ ω^{i+1} = U`.
  * If `t`'s ω^i-coefficient is `u_i`, only `a` changes. In `ℬ` with `u_i = v_i` the new piece
    `(ω^i u_i + a′, ω^i u_i + b)` is an option of the old one.
  * If it is `u′ < u_i`, the relation fails: `u′ ≠ v_i + x_i` in `𝒜`, and
    `m + u′ − v_i ≠ x_i` in `ℬ`.
* **`x ≤ t < v`**, so `Y = (t, t, x)` has `U′ = V′ = m′` and `u′_i = v′_i`.
  * Membership needs `m′ ≥ 1` (in `𝒜` it would need `u′_i = v′_i + x_i`), so `X ∈ ℬ`. It also
    needs `x_i = m′ ≤ m`, while `x_i = m + u_i − v_i ≥ m`. So `m′ = m = x_i` and `u_i = v_i`.
  * Then `t = ω^{i+1}m + s` with `s < ω^i v_i + b`. The top condition needs `c = G(s, s)`. But
    `c = G(ω^i u_i + a, ω^i u_i + b)`, and `(s, s)` is an option of that piece (cut its first
    column to `s`).
* **`ω ≤ t < x`**: `Y = (t,t,t)` has `U′ = V′ = 0` and `u′ = v′ = x′` at its own degree, so it
  is not in `𝒜` (which needs `u′ = v′ + x′`) or `ℬ`.
* **`t < ω`**: `Y` is a finite rectangle, which is N.

### Part 2: every non-member has a P option

Let `X = (u, v, x)` with `ω ≤ x < ω^ω` and `X ∉ 𝒜 ∪ ℬ`. Each case names a bite. The cases are
checked in order, so each assumes the earlier ones fail.

**Case I: `U = V` finite fails.**
* **I.1** `V` is infinite. Cut column 0 at `t = ω^{i+1}·x_i + h`, where `h < ω^{i+1}` and
  `G(h,h) = c` (F3). Then `Y = (t, t, x) ∈ ℬ` with `m = x_i` and `u′_i = v′_i`, since
  `c = G(h, h)`. Here `x ≤ t < v`.
* **I.2** `V = 0 < U`. Cut column 0 at `t = ω^i·(v_i + x_i) + a′`, where `a′ = G(b, c)` if
  `v_i = x_i` and `a′ = b ⊕ c` otherwise. Then `Y = (t, v, x) ∈ 𝒜`, and `v ≤ t < ω^{i+1} ≤ u`.
* **I.3** `V = m`, `1 ≤ m < ω`, `U > m`. Use the bite of III.2a, III.2b or III.2c below,
  according to whether `x_i > m`, `x_i < m` or `x_i = m`. Those bites need only `t < u`, which
  holds here because `U > m`.

**Case II: `U = V = 0` and `u_i ≠ v_i + x_i`.**
* **II.1** `u_i > v_i + x_i`. Cut column 0 at `ω^i·(v_i + x_i) + a′`, with `a′` as in I.2. The
  result is in `𝒜`.
* **II.2** `v_i < u_i < v_i + x_i`. Cut column 2 at `ω^i·(u_i − v_i) + (a ⊕ b)`. The result is in
  `𝒜`, since `v_i ≥ x_i > u_i − v_i`.
* **II.3** `u_i = v_i`. Lower the third column by one degree.
  * If `i ≥ 2`, write `a = ω^{i−1}α + ā` and `b = ω^{i−1}β + b̄` (`α ≥ β` because `a ≥ b`).
    Cut column 2 at `x′ = ω^{i−1}·(u_i + α − β) + c′`, where `c′ = G(ω^{i−1}α + ā, ω^{i−1}α + b̄)`
    if `α = β` and `c′ = ā ⊕ b̄` otherwise; `c′ < ω^{i−1}` by (F2).
    * At degree `i−1` the high parts are `U′ = V′ = u_i ≥ 1`.
    * `x′_{i−1} = u_i + α − β`, and the top condition holds, so the result is in `ℬ`.
  * If `i = 1`, the target `T = G(ω\u, ω\v)` is finite by (9-1)/(9-2). By **(S∞)** there is an
    `x′ ∈ 𝒮` with `G_𝒮(x′) = T`. Cutting column 2 at `x′` leaves a P-position by (ST).

  This is the only place where the infinitude of `𝒮` enters. The rectangles `(z,z,z)` of the
  tall box are instances. So are the positions `(ω+a, ω, ω)` of notes/15, whose answers
  `(ω+a, ω, s_a)` show that the theorem itself implies `|𝒮| = ∞`.

**Case III: `U = V = m`, `1 ≤ m < ω`, and `x_i ≠ m + u_i − v_i`.**
* **III.1** `x_i > m + u_i − v_i`. Cut column 2 at `ω^i·(m + u_i − v_i) + c′`. Take
  `c′ = G(ω^i u_i + a, ω^i u_i + b)` if `u_i = v_i` and `c′ = a ⊕ b` otherwise. The result is in
  `ℬ`.
* **III.2** `x_i < m + u_i − v_i`.
  * **III.2a** `x_i > m`. Cut column 0 at `ω^{i+1}m + ω^i·(v_i + x_i − m) + (b ⊕ c)`. This lies
    in `[v, u)` and leaves a member of `ℬ` with `u′_i > v_i`.
  * **III.2b** `x_i < m`. Cut column 0 at `t = ω^{i+1}·x_i + h` with `G(h,h) = c`, as in I.1.
    Then `t < v`, so `Y = (t,t,x) ∈ ℬ`.
  * **III.2c** `x_i = m`. Consider the two-column position `Q = (ω^i·(v_i+1), ω^i·v_i + b)`.
    By (F1), `G(Q) ≥ ω^i > c`, so some option of `Q` has value `c`.
    * Cuts of `Q`'s second column below `ω^i·v_i + b` leave a difference of ω^i-coefficients,
      with value `≥ ω^i` (F1). So the option cuts the first column to some `s`.
    * If `s = ω^i v_i + a′ ≥ ω^i v_i + b`, cut column 0 of `X` at `ω^{i+1}m + s`. The result is
      `(ω^{i+1}m + ω^i v_i + a′, v, x) ∈ ℬ`.
    * If `s < ω^i v_i + b`, the option is `(s, s)`. Cutting column 0 of `X` at `ω^{i+1}m + s`
      leaves `(t, t, x) ∈ ℬ`.
    * In both cases `t < u`. Either `u_i > v_i`, or `U > m` (Case I.3).

**Case IV: the bottom relation holds and the top condition fails.**
* **IV.1** `𝒜` with `v_i = x_i`, `a ≠ G(b,c)`.
  * If `a > G(b,c)`, cut column 0 to `ω^i u_i + G(b,c)`.
  * If `a < G(b,c)`, some option of the two-column piece `(b, c)` has value `a`. Cutting its
    first column to `s` corresponds to cutting column 1 of `X` to `ω^i x_i + s`. Cutting its
    second column corresponds to cutting column 2 of `X`.
  * Either way `v′_i = x′_i = x_i`, so the result is in `𝒜`.
* **IV.2** `𝒜` with `v_i > x_i`, or `ℬ` with `u_i > v_i`; `a ⊕ b ⊕ c ≠ 0`.
  * Reduce the one of `a, b, c` that has the leading bit of the nim-sum, as in Nim.
  * The cut stays above the lower columns, since `u_i > v_i` and `v_i > x_i` (respectively
    `V ≥ 1`).
* **IV.3** `ℬ` with `u_i = v_i`, `c ≠ g = G(ω^i u_i + a, ω^i u_i + b)`. Note `g < ω^i` by (F2).
  * If `c > g`, cut column 2 to `ω^i x_i + g`.
  * If `c < g`, some option of the piece has value `c`. By (F1) it is not a cut of its second
    column below `ω^i u_i`. So it is a first-column cut to `s` or a second-column cut to
    `ω^i u_i + b′`.
  * Make the same cut in `X`, raised by `ω^{i+1}m`. The result stays in `ℬ` with `u′_i = v′_i`.

This covers every non-member. In each case the result is a member or a Side-Top P-position. ∎

## Corollary: `3×ω^ω` is a P-position

Every bite into `(ω^ω, ω^ω, ω^ω)` leaves an N-position:

| bite | position | winning reply | from |
| --- | --- | --- | --- |
| `(2, z)`, `z < ω`, `z ∉ 𝒮` | `(ω^ω, ω^ω, z)` | `(0, h)` with `h` finite, `(h,h,z)` P | (ST) |
| `(2, z)`, `z < ω`, `z ∈ 𝒮` | `(ω^ω, ω^ω, z)` | `(0, ω + h)` with `G(h,h) = G_𝒮(z)` | (ST), (F3) |
| `(2, z)`, `z ≥ ω` | `(ω^ω, ω^ω, z)` | `(0, ω^{i+1} z_i + h)` with `G(h,h) = c` | Case I.1 |
| `(1, z)`, `z < ω` | `(ω^ω, z, z)` | `(0, h)` with `h` finite | Fundamental Theorem / (BS) |
| `(1, z)`, `z ≥ ω` | `(ω^ω, z, z)` | `(0, ω^i·2z_i + G(c, c))` | Case I.2 |
| `(0, z)`, `z < ω` | `3×z` | a finite winning move | strategy stealing |
| `(0, z)`, `ω ≤ z < ω²` | `3×z` | `(2, x)` with `G_𝒮(x) = G(ω\z, ω\z)` | Case II.3, **(S∞)** |
| `(0, z)`, `z ≥ ω²` | `3×z` | `(2, ω^{i−1}·z_i + G(c,c))`, `i = deg z` | Case II.3 |

Here `z = ω^i·z_i + c` as above. The replies are exactly those named in §10. ∎

So Huddleston–Shurman's theorem that `3×ω^ω` is P follows from (BS), (ST), the two-column values
of §9 and the side-class theorem of notes/13. The gaps in §10 (the sketch of (10-1) and the
missing infinitude of `𝒮`) are closed.

## Corollary: the P-positions of `3×Ω` form a recursive set

In §12 Huddleston–Shurman write: "We are confident that the set of P-positions in `3×Ω` is
recursive (though this has not been fully proved)." With the theorem above this follows, with
heights given in Cantor normal form. For a position with at most three columns `u ≥ v ≥ x`:

| case | decided by |
| --- | --- |
| one or two columns | `G = 1` (unrestricted), by the formulas (9-1)–(9-6) |
| `x ≥ ω^ω` | P only for `3×ω^ω` itself; otherwise `u > ω^ω`, and the bite at height `ω^ω` in column 0 leaves `3×ω^ω` |
| `ω ≤ x < ω^ω` | the closed form `𝒜 ∪ ℬ`; the top conditions need two-column values below `ω^i` and nim-sums |
| `x < ω ≤ v` | (ST): `x ∈ 𝒮` and `G_𝒮(x) = G(ω\u, ω\v)` |
| `v < ω ≤ u` | N by (BS) |
| `u < ω` | a finite computation |

The Side-Top row is decidable because `𝒮` is. By notes/13, Step A, a non-side `x` has
`τ(x) ≤ 2x + 1`. So `x ∈ 𝒮` iff no `h ∈ (x, 2x+1]` makes `[h,h,x]` P, a finite check, and
`G_𝒮(x)`, the index of `x` in `𝒮`, is computable too.

So the set is recursive, given the paper's two-column formulas (including (9-6) for heights
`≥ ω^ω`), Beanstalk Lemma and Side-Top Theorem. Step A rests on Sheiner's lemmas (S1), (S2).
Without a bound on `τ`, membership in `𝒮` would only be co-r.e.

## Machine checks

* `scripts/hs_proof_replies.py` implements Part 2's bites literally and checks each result with
  the oracle. It covers 20000 random positions with `ω ≤ x < ω⁴` and `u, v` up to `ω⁸`, so that
  `U` can be infinite: 19612 non-members, every named reply P, and the families agree with
  (10-1) on all 20000.
  * The checks found two bugs in the script, not in the proof. The nim fix of the third column
    had wrongly added `ω^{i+1}m`, and a search bound was too small.
* Part 1 corresponds to the local-consistency checks in notes/15: no claimed P-position has a
  claimed P option, with options enumerated in full up to coefficient bounds.
* `scripts/hs_tall_box.py` checks the corollary's replies for about 12000 bites.
