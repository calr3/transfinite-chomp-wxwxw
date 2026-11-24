# A P-position with four infinite columns

24 November 2026. The candidate A of [notes/24](24-three-by-three.md) is a P-position. This
note gives the proof. It is computer-assisted: the regular part is a closure statement
proved by Z3, one family of options is handled by a strategy-stealing argument written out
below, and three small positions with two infinite columns are decided by the certified
solver of notes/07.

As far as this repository goes, A is the first position with more than two infinite columns
that is proved to be P. We have not searched the literature for an earlier example.

## 1. Statements

**The position.** `A = (ω,ω,1 | ω,ω,1 | 2,0,0)` over the `3×3` base: the columns `(0,0)`,
`(0,1)`, `(1,0)`, `(1,1)` are infinite, the columns `(0,2)` and `(1,2)` ("wings") have height
1, and the column `(2,0)` ("foot") has height 2.

**Theorem 1.** A is a P-position.

**Finite positions.** All finite positions below A live on the seven cells above. Write

`(a; b, c, d | e, f | k)`

for the heights of `(0,0)`; `(0,1)`, `(1,0)`, `(1,1)`; `(0,2)`, `(1,2)`; `(2,0)`. So
`e, f ≤ 1` and `k ≤ 2`. The four shapes

* shape 1: `(m+1; m+1, m, m)`
* shape 2: `(m+1; m, m+1, m)`
* shape 3: `(m+2; m+2, m+2, m)`
* shape 4: `(m+2; m+1, m+1, m)`

are used with three decorations.

**Theorem 2.** The following finite positions are P-positions.

| name | position | for |
| --- | --- | --- |
| `F1`–`F4` | shapes 1–4 with `e = f = 1`, `k = 2` (the decoration of A) | `m ≥ 2` for `F1`, `m ≥ 1` for the others |
| `K1`–`K4` | shapes 1–4 with `e = 1`, `f = 0`, `k = 1` | `m ≥ 2` for `K1`, `K2`; `m ≥ 1` for `K3`, `K4` |
| `G(c,d)` | `(c+2; d+2, c, d \| 1, 1 \| 0)` | all `c ≥ d ≥ 1` |
| `TW1`, `TW2` | `(m+2; 1, m, 1 \| 1, 0 \| 1)`, `(m+2; m, 1, 1 \| 1, 0 \| 1)` | `m ≥ 2` |
| `TW3` | `(m+3; m, 1, 1 \| 1, 1 \| 1)` | `m ≥ 1` |

`G` is a two-parameter family: the layer `x = 1` is the layer `x = 0` lowered by 2 in both
columns. It lives over the `2×3` base, with the third row at height 1.

**Lemma 3.** `W(m) = (m+1; m, m+1, m | 1, 1 | 0)` is an N-position for every `m ≥ 1`.

`W(m)` is shape 2 with both wings and no foot. In layers it is the three-row position
`[m+1, m, 1]` taken twice, side by side. Its winning replies are irregular (§6), but the
lemma does not need them.

## 2. The closed set

Let `S` be the union of
* the positions of Theorem 2;
* **pure**: the P-positions with `e = f = k = 0`, which are the `(a; b, c, d)` with
  `b + c = a − 1` and `d = min(b, c)`, and the `(a; a, a, a−1)`;
* **2D**: the P-positions inside one layer, `[2,2,1]`, `[3,1,1]` and `[c+2, c, 2]`
  (`c ≥ 2`), written as three-row positions;
* **small**: 106 positions of height at most 8, listed in the script.

Let `S₀` be `S` without `F1`–`F4`.

**Claim 4** (Z3). For every `X ∈ S₀` and every option `Y` of `X`, some option of `Y` is in
`S₀`.

**Claim 5** (Z3). For every `X ∈ S` and every option `Y` of `X`: `Y = W(m)` for some
`m ≥ 1`, or some option of `Y` is in `S`.

Both are sentences of Presburger arithmetic: a bite cuts some heights to a minimum, and
every family is given by linear equations. `scripts/candidate_A_closure_z3.py` proves them.
* For each family and each of the seven cells, Z3 refutes "some `X` in the family and some
  height `t` give an option that is not a `W(m)` and has no option in the set". The reply is
  existentially quantified inside the refuted formula, so Z3 finds it by itself. 14 families
  times 7 cells take 18 seconds.
* The 106 small positions are checked by enumeration.

**Checks on the script.**
* The same predicates, evaluated on integers, confirm both claims for all positions of
  height at most 14 (448 positions of `S`).
* Without the exception for `W(m)`, Z3 returns the expected counterexample: `F2` with the
  foot removed. Without the family `G` it returns `F3` with the foot removed.
* All 4404 positions of `S` of height at most 60 are P in the exact table of notes/24, and
  no `W(m)` with `m ≤ 117` is.
* An independent computation (a search for the closed set in the exact table, up to height
  80) found the same families before they were written down.

**Proof of Theorem 2 for `S₀`.** By induction on the number of cells. Let `X ∈ S₀`. By Claim
4 every option `Y` of `X` has an option in `S₀`, which is smaller and so P by induction.
Hence every option of `X` is N, and `X` is P. ∎

So `G`, `K1`–`K4`, `TW1`–`TW3`, the pure positions and the small positions of `S₀` are P
without any hypothesis.

## 3. Proof of Lemma 3: stealing the top cell

For `m = 1` the position `W(1) = (2; 1, 2, 1 | 1, 1 | 0)` has an option in `S₀` (checked by
the script). Let `m ≥ 2`.

Let `u = (1,1,m−1)`, the top cell of the column `(1,1)`. It is a maximal cell of `W(m)`:
the only cells above `(1,1)` in the base are in the column `(1,2)`, which has height 1, and
`m − 1 ≥ 1`. Let `W′ = W(m) ∖ {u} = (m+1; m, m+1, m−1 | 1, 1 | 0)`. It is an option of
`W(m)`.

Suppose `W(m)` is P. Then `W′` is N, so some bite `p` in `W′` leaves a P-position
`W′ ∖ ↑p`.

*If `p ≤ u`*, the bite `p` removes `u` as well, so `W(m) ∖ ↑p = W′ ∖ ↑p`. That is an option
of `W(m)` and a P-position. Contradiction.

*If `p ≰ u`*, then `p` is a wing cell or has height at least `m`. Only the columns `(0,0)`
and `(1,0)` reach height `m+1`, so there are four such cells. None leaves a P-position:

| `p` | `W′ ∖ ↑p` | an option of it in `S₀` |
| --- | --- | --- |
| `(0,0,m)` | `(m; m, m, m−1 \| 1, 1 \| 0)` | take `(0,2,0)`: pure `(m; m, m, m−1)` |
| `(1,0,m)` | `(m+1; m, m, m−1 \| 1, 1 \| 0)` | take `(0,1,0)`: the two-row position `[m+1, m]` |
| `(0,2,0)` | pure `(m+1; m, m+1, m−1)` | take `(1,0,0)`: the two-row position `[m+1, m]` |
| `(1,2,0)` | `(m+1; m, m+1, m−1 \| 1, 0 \| 0)` | cut `(0,0)` at 1: the bottom layer `[3, 2]` |

The four options in the last column are in `S₀` (pure, pure, pure, small), hence P by §2,
so the four positions in the middle column are N. Contradiction. So `W(m)` is N. ∎

The script checks the four replies with Z3 for all `m ≥ 2`, and the whole case analysis by
enumeration for `m < 14`.

**Why this works.** `W(m)` minus its top `(1,1)` cell has only four options that `W(m)` does
not have, and each loses for a simple reason. The argument says nothing about which reply
wins `W(m)`.

## 4. Proof of Theorem 2

By induction on the number of cells, as in §2. Let `X ∈ S`. By Claim 5 every option `Y` of
`X` is a `W(m)`, which is N by Lemma 3, or has an option in `S`, which is P by induction. So
every option of `X` is N and `X` is P. ∎

## 5. Proof of Theorem 1

Every option of A has a P option:

| option of A | reply | why the reply is P |
| --- | --- | --- |
| cut `(0,0)` at `h ≥ 3` | cut `(1,0)` at `h−1` | `F1(h−1)` |
| cut `(0,0)` at 2 | take `(1,0,0)` | the layer `[2,2,1]` |
| cut `(0,0)` at 1 | take `(1,1,0)` | the hook `(1; 1, 1, 0 \| 1, 0 \| 1)`, small |
| cut `(1,0)` at `z ≥ 2` | cut `(0,0)` at `z+1` | `F1(z)` |
| cut `(1,0)` at 1 | take `(1,2,0)` | `(ω; ω, 1, 1 \| 1, 0 \| 1)`, certified |
| cut `(1,0)` at 0 | cut `(0,0)` at 2 | the layer `[2,2,1]` |
| cut `(0,1)` at `z ≥ 1` | cut `(0,0)` at `z+1` | `F2(z)` |
| cut `(0,1)` at 0 | take `(2,0,0)` | the row `y = 0` is the rod `2×ω` |
| cut `(1,1)` at `z ≥ 1` | cut `(0,0)` at `z+2` | `F3(z)` |
| cut `(1,1)` at 0 | cut `(0,0)` at 1 | the hook, small |
| take `(0,2,0)` | take `(1,0,0)` | the column `x = 0` is the rod `2×ω` |
| take `(1,2,0)` | cut `(0,1)` at 2 | `(ω; 2, ω, 2 \| 1, 0 \| 2)`, certified |
| take `(2,0,1)` | cut `(0,1)` at 3 | `(ω; 3, ω, 3 \| 1, 1 \| 1)`, certified |
| take `(2,0,0)` | take `(0,1,0)` | the row `y = 0` is the rod `2×ω` |

These are all the options: a bite in one of the four infinite columns, or one of the four
decoration cells.

* `F1(z)` (`z ≥ 2`), `F2(z)`, `F3(z)` (`z ≥ 1`), the layer `[2,2,1]` and the hook are in `S`,
  hence P by Theorem 2.
* `2×ω` is P (proved in Lean, notes/05).
* "Certified": three positions with two infinite columns, decided P by the solver of
  notes/07 with a periodicity certificate (`rodf -p w,w,1,1,1,1 321`,
  `rodf -p w,2,1,w,2,2 321`, `rodf -p w,3,1,w,3,1,1 331`, each "P exact").

So every option of A is N, and A is P. ∎

**What the proof rests on.**
1. Z3 for Claims 4 and 5.
2. The hand argument of §3.
3. The certified two-wide solver for three positions. They could be redone with the method
   of this note; that has not been done.
4. The Lean proof that `2×ω` is P.

## 6. Remarks

**The reply rule.** After any cut of A at height `z`, cut the poison column just above:
at `z+1` or `z+2`. The finite positions this leaves are `F1`, `F2`, `F3`. Inside those the
same rule keeps working: a cut at height `t` is answered by cutting the poison column at
`t+1` or `t+2`, which gives `F1(t)`, `F2(t)`, `F3(t)` or `F4(t)` again.

**The family `G`.** With both wings and no foot, `(c+2; d+2, c, d)` is P for all
`c ≥ d ≥ 1`. The second player keeps the layer `x = 1` equal to the layer `x = 0` lowered by
2: a cut of one layer at height `t` is answered by a cut of the other layer at `t ∓ 2`.
In this world (both wings, no foot), in the exact table up to height 70 and for `d ≥ 3`:
* no P-position has `a − c = 1`: taking `(0,1,0)` leaves the two-row position `[c+1, c]`;
* a P-position has `a − c = 2` if and only if it has `b − d = 2`, and then it is a `G`.

**The lemma is not constructive.** `W(m)` is N for every `m`, but its winning replies have
no pattern. They are of two kinds: cut `(0,1)` at `t₁`, or cut `(1,1)` at `t₂`.

| `m` | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 17 | 19 | 22 | 30 | 44 | 60 | 80 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `t₁` | 1 | 2 | 3 | 4 | 5 | – | 7 | 8 | 9 | 10 | – | 16 | – | – | 35 | – | – |
| `t₂` | – | 1 | 1 | 1 | 4 | 4 | 4 | 4 | 8 | 8 | 8 | – | 16 | 24 | – | 41 | 67 |

The first kind is a matching between heights with gaps, like the partner function of
three-row Chomp. Before the stealing argument this looked like the obstacle of notes/24: a
statement of the side-class kind. It is one, but it never has to be proved.

**How the pieces were found.**
1. The exact table of notes/24 gave all P-positions of this family up to height 120.
2. A search for the largest set of P-positions that is closed under replies and made of
   translation families showed that `F1`–`F3` are not in it, and why: one option, `F2` with
   the foot removed.
3. Allowing that option as a hypothesis, the closed set reachable from `F1`–`F3` turned out
   to be the 14 families above and 106 small positions, with no other hypothesis.
4. Z3 proved the closure for all heights.
5. The hypothesis fell to strategy stealing.

## 7. Consequences

The positions with A as an option are N-positions. Up to transposition:
* `(ω,ω,1 | ω,ω,1 | k,0,0)` with `k ≥ 3` or `k = ω`;
* `(ω,ω,j | ω,ω,i | 2,0,0)` with `j ≥ 2`, `1 ≤ i ≤ j`, including `ω`;
* `(ω,ω,1 | ω,ω,1 | 2,1,k)` and `(ω,ω,1 | ω,ω,1 | 2,2,k)` with `k ≤ 1`.

In particular `(ω,ω,ω | ω,ω,ω | 2,0,0)` is N. That is the tower `T_331((2,0),2)` of the rod
`331×ω`: the `3×2` rod with one more column of height 2 (`X_2` in notes/24).

Nothing here decides `331×ω` or `3×3×ω`.

**What may carry over.** The method has two parts.
* A closed set of finite P-positions in translation families, found in an exact table and
  proved by Z3. This needs the replies to be regular. For A they are; for the towers of
  `3×3×ω` they are not.
* Strategy stealing on a maximal cell for an option whose replies are irregular. This is
  cheap to test on any position: remove a maximal cell and look at the few options that the
  original position does not have.

## Tools

```
python3 scripts/candidate_A_closure_z3.py        # Claims 4 and 5 and Lemma 3; about one minute
g++ -O3 -march=native -std=c++17 -Wall -fopenmp -o base3_table tools/base3_table.cpp
./base3_table 254 -c H,H,1,H,H,1,2,0,0 -q qA.txt # the exact table for the family of A (notes/24)
./rodf -p w,w,1,1,1,1 321                        # the three certified positions of §5
./rodf -p w,2,1,w,2,2 321
./rodf -p w,3,1,w,3,1,1 331
```
