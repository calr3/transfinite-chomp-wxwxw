# Idea 5: Lean formalisation of the elementary facts

The library `Chomp` lives in `lean/` and is the default target in `lakefile.toml`, so `lake build`
builds it. It uses Lean core only (no Mathlib) and contains no
`sorry`. The main theorems depend only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

```
lake build Chomp          # about 5 seconds
```

## Design

* A position is a predicate `Pos := Pt → Prop` on cells `Pt = ℕ³`. The whole board is `full`.
* `take X m` removes every cell `≥ m`.
* `Opt X Y` holds when `Y = take X m` for some cell `m ∈ X` other than the poison.
* Outcomes are an inductive predicate:

  ```lean
  inductive Out : Bool → Pos → Prop
    | win  {X Y} : Opt X Y → Out false Y → Out true X
    | lose {X}   : (∀ Y, Opt X Y → Out true Y) → Out false X
  ```

  `IsN X := Out true X` and `IsP X := Out false X`. Because the definition is inductive, no
  well-foundedness proof is needed to state or prove outcomes of infinite positions. The game's
  termination (Dickson's lemma) is never used.
* A P-position with infinitely many options is proved by giving, for every option, an explicit
  reply. The reply depends on the option, which is how the transfinite arguments become finite
  proofs.

## What is proved

| File | Theorem | Statement |
| --- | --- | --- |
| `Basic.lean` | `Out.not_both` | No position is both N and P. |
| | `Sym.out` | Outcomes are invariant under coordinate swaps (`swapXY`, `swapYZ`, `swapXZ`). |
| | `opt_of_lt`, `not_both_winning` | If `m < m'`, then `take X m` is an option of `take X m'`. So two comparable moves cannot both win: winning moves form an antichain. |
| `TwoRow.lean` | `isP_row2` | Two finite rows of lengths `a ≥ b` form a P-position iff `a = b + 1` (the "if" direction, by strong induction). |
| | `isP_row2ww` | **`2 × ω` is a P-position.** |
| `LShape.lean` | `isP_ell`, `isP_ellInf` | Equal L-shaped arms form a P-position, finite or both infinite (mirror strategy). |
| `FirstMoves.lean` | `isP_floor_110`, `isP_floor_020`, `isP_floor_200` | `(1,1)`, `(0,2)` and `(2,0)` are winning moves on `ω × ω`. |
| | `not_isP_floor_kk` | `(k,k)` for `k ≥ 2` is not winning on `ω × ω` (antichain lemma). |
| | `isN_floor`, `isN_slab2`, `isN_cross` | `ω×ω`, `ω×ω×2` and `ω×L(1,1)` are N. |
| | **`losing_first_moves`** | On `ω × ω × ω`, the first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and all their coordinate permutations lose. |
| | `isN_U_A2`, `isN_U_011`, `isN_U_001` | In the three-plane position `U` (after the first move `(1,1,1)`), the options `(0,0,2)`, `(0,1,1)` and `(0,0,1)` are N. So none of them is a reason for `(1,1,1)` to lose (see Idea 3). |
| `Prisms.lean` | `isN_prism_two`, `isN_prism_one_one` | The L-prisms `L(a,b)×2` (`a, b ≥ 1`) and `L(1,1)×c` (`c ≥ 2`) are N (Idea 2). |

## The side-class theorem (`SideClass.lean`)

`SideClass.lean` checks the counting argument of [notes/13](13-side-class-theorem.md). It does
not define three-row Chomp. It takes an arbitrary `f : Nat → Nat → Nat` and assumes, as the
fields of a structure `Table f`, eleven statements about the function `f(q,r)` of Brouwer et
al., all proved in Sheiner's paper:

| field | statement | source |
| --- | --- | --- |
| `gt_row`, `enc`, `const` | `f(q,r) > r`; a value below `q` is a partner; a row is constant after its partner | definition of `f` (Lemma 2.1) |
| `row_inj`, `col_once` | distinct values in a level; a row takes a value at most once | Lemma 2.3(a),(b) |
| `row_start` | row-start propagation | Lemma 4.2 |
| `diag_ne_partner`, `cover` | every `h ≥ 1` is a partner or a diagonal value, not both | Props 4.3, 4.4 |
| `diag_mex` | every `1 ≤ v < f(a,a)` is blocked at the diagonal cell | the recurrence, `f(a,a) = mex B(a,a)` |
| `diag_max` | the diagonal value is the largest of its level | Lemma 4.1 |
| `diag_inj` | `a ↦ f(a,a)` is injective | proof of Theorem 1.1 |

From these it proves, with `Side f x := ∀ p > x, f p x ≠ p` and `cnt P n = #{x < n : P x}`:

| Theorem | Statement |
| --- | --- |
| `Table.remaining` | the remaining-lifetime lemma |
| `Table.dead_le_two_side` | the P-positions `[p,p,x]` with `p ≤ T` number at most `2·cnt (Side f) T` |
| `Table.partner_le` | a partner `p` of `r` satisfies `3p ≤ 5r + 3` |
| `Table.diag_gt_partner` | no diagonal value of a row `a ≥ r` lies below the partner of `r` |
| **`Table.side_density`** | `v < 5 · cnt (Side f) (v+1)` for every `v` |
| **`Table.side_unbounded`** | the side class is infinite |

The upper-density statement (`≥ 1/4`) is not formalised.

Finite sets are replaced by the counting function `cnt`, with a pigeonhole lemma `cnt_inj`
proved by induction. The file has no `sorry` and uses only the standard axioms.

Because the hypotheses are assumed, a mis-stated one could make the theorem vacuous.
`tools/side_table_check.cpp` computes the actual table of three-row Chomp and checks all eleven
fields exactly as written in Lean: no violation for arguments up to 2000.

## Notes on the proofs

* Set equalities such as `take (take full ⟨0,0,2⟩) ⟨0,1,0⟩ = row2ww` are proved pointwise with
  `funext`, `propext`, `simp` and `omega`. `simp` must run before `omega`: it removes `True ∧ …`
  and reduces projections of structure literals, and without it omega fails.
* The symmetry lemma `Sym.out` is the only argument by induction on `Out`. Everything else is
  explicit strategies.

## Possible extensions

* The domino rule from Idea 1 for general Young diagrams, which would need finite sets of cells.
* Certificates for the exact finite P-heights of Idea 1 (`S × t` is P), generated by the C++
  solver in the same way as `Cgt/Certificate.lean` in the `calr3/cgt` repository does for Toads
  and Frogs.
* A formal statement of the `ω×ω×ω` problem itself:
  `IsN (full) ∨ IsP (full)`, together with which first moves win.
