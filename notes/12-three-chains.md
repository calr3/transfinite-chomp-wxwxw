# Three chains: toward Gale's `3×3×ω`

Every case decided exactly so far has at most **two** infinite columns. That is Byrnes's
two-chain theorem and our certified solver (notes/07). Every open question is the first case
with **three**:
* Gale's `3×3×ω`;
* the slab `ω×ω×3`, i.e. the first move `(0,0,3)`;
* L-prisms of height 3;
* Huddleston–Shurman's "`3×Ω` is recursive (not fully proved)".

This note records the work on that boundary.

## Step 1a: an exact oracle for 2D positions with three columns

`tools/hs_oracle.py` implements Huddleston–Shurman §9–§10 for column heights below `ω^ω`, using
their unrestricted Grundy values (P iff value 1):

* **Two columns:** the closed formulas (9-1)–(9-5). For example `G(ω·u, ω·u) = (3^u − 1)/2`,
  `G(ω·u+a, ω·v+b) = ω·(u−v) + (a ⊕ b)` for `u > v`, and `G(ω^i·u+a, ω^i·u+b) = ω^{i−1}·u +
  G(a,b)` for `i ≥ 2`.
* **Three columns `u ≥ v ≥ x`:**
  * `x` and `v` finite: brute force if `u` is finite, otherwise N (Beanstalk Lemma).
  * `x` finite and `v ≥ ω`: the **Side-Top Theorem**. The position is P iff `x` is in the side
    class `𝒮` and `G_𝒮(x) = G(top)`, where the top is the two-column position
    `(ω\u, ω\v)`.
  * `ω ≤ x < ω^ω`: the **decomposition (i)–(iv)** into bottom and top pieces, with criterion
    (10-1): `G(U_b) = G(X_b)` and `G(U_t) ⊕ G(V_t) ⊕ G(X_t) = 0`.
* **The side class** `𝒮` is the set of finite `x` with no finite `h` making `(h,h,x)` P. That is
  exactly "no cut of the poison column is P" for the two-wide stalk `(ω,ω,x)`, which our
  certified solver decides. `rodf -I 1 -p w,w,x 3` answers it.

### Validation (`scripts/hs_check.py`)

* Finite positions agree with the rod solver (0 mismatches for heights ≤ 8).
* **Local consistency.** A claimed P-position must have no option claimed P, and a claimed
  N-position should have one. Options are sampled over all ordinals below each height with small
  coefficients, plus truncations of the heights.
  * 400 random positions with heights below `ω³`: no inconsistency (314 N verified, 83 N with no
    P option in the sample, 3 P).
  * 41 generated P-positions: no inconsistency.
* **Every P-position the paper describes** in its proof that `3×ω^ω` is P is reproduced:
  * `(ω·2, ω, ω)`, `(ω·4+5, ω·2+3, ω·2+3)`, `(ω²·2+10, ω²+ω+2, ω²+ω+2)` (case `e = 1`);
  * `(ω², ω², ω)`, `(ω³+4, ω³+4, ω²+6)` (case `e = 0`, `z ≥ ω²`);
  * for `ω ≤ z < ω²`, a **unique** finite `x` with `(z,z,x)` P, as the paper states. For
    example `x = 5` for `z = ω+1`, and `x = 74` for `z = ω·3+2`.

### A by-product: the side class

`𝒮 = {0, 2, 5, 7, 9, 11, 14, 17, 19, 22, 24, 26, 28, 31, 34, 36, 38, 40, 42, 45, 48, 51, 53,
56, 58, 60, 62, 65, 67, 69, 72, 74, 77, 79, …}`. The gaps are 2 or 3 in an irregular pattern of
density about 0.43, and `G_𝒮(x)` is the index of `x` in `𝒮`. Every other `x` has a finite `h`
with `(h,h,x)` P. For `x = 1, 3, 4, 6, 8, 10, 12` that `h` is `2, 5, 7, 9, 12, 14, 17`.

## Step 1b: the towers of `3×3×ω`

**Reformulation.** `3×3×ω` is N iff some option is P. The options are the towers `T(b,g)`: the
columns in `↑b` cut to height `g` and the rest infinite. For each `b`, at most one `g` gives a
P tower (antichain lemma). Up to transposition, `b ∈ {(0,1), (0,2), (1,1), (1,2), (2,2)}`.

**The thinnest towers, `T((0,1), g)`** (a stalk of three infinite columns, the row `y = 0`, on a
`3×3×g` block) are **N exactly** for `g = 1, …, 4`:

| `g` | exact winning reply |
| --- | --- |
| 1 | cut everything at height 7 (a finite P-position) |
| 2 | cut everything at height 11 |
| 3 | cut cell `(2,0)` at 11, leaving a two-wide stalk proved P |
| 4 | cut cell `(2,0)` at 1, leaving a two-wide stalk proved P |

TOWER_SCAN
