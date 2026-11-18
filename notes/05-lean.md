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

## The side-class theorem (`SideClass.lean`, `ThreeRow.lean`, `ThreeRowBoard.lean`)

The side-class theorem of [notes/13](13-side-class-theorem.md) is machine-checked from the rules
of the game, with no hypothesis. In particular the statements of Sheiner's preprint that the
proof uses are themselves proved in Lean here, so the result does not rest on an unrefereed
source. The final statements, for the positions of `Basic.lean`:

```lean
/-- Three rows along the x-axis at y = 0: the rows z = 0, 1, 2 have lengths a, b, c. -/
def board (X : T3) : Pos := fun p =>
  p.y = 0 ∧ ((p.z = 0 ∧ p.x < X.a) ∨ (p.z = 1 ∧ p.x < X.b) ∨ (p.z = 2 ∧ p.x < X.c))

def BoardSide (x : Nat) : Prop := ∀ p, x < p → ¬ Chomp.IsP (board ⟨p, p, x⟩)

theorem board_side_density (v : Nat) : v < 5 * cnt BoardSide (v + 1)
theorem board_side_unbounded (N : Nat) : ∃ x, N ≤ x ∧ BoardSide x
theorem board_partner_le {x p : Nat} (hxp : x < p)
    (hP : Chomp.IsP (board ⟨p, p, x⟩)) : 3 * p ≤ 5 * x + 3
```

Here `cnt P n = #{x < n : P x}`. So more than `v/5` of the numbers `0, …, v` are in the side
class, for every `v`; the side class is infinite; and a P-position `[p,p,x]` has
`p ≤ (5x+3)/3`.

The proof is in three files.

**`SideClass.lean` (the counting argument).** It takes an arbitrary `f : Nat → Nat → Nat` and a
structure `Table f` of eleven statements about it:

| field | statement | source |
| --- | --- | --- |
| `gt_row`, `enc`, `const` | `f(q,r) > r`; a value below `q` is a partner; a row is constant after its partner | definition of `f` (Lemma 2.1) |
| `row_inj`, `col_once` | distinct values in a level; a row takes a value at most once | Lemma 2.3(a),(b) |
| `row_start` | row-start propagation | Lemma 4.2 |
| `diag_ne_partner`, `cover` | every `h ≥ 1` is a partner or a diagonal value, not both | Props 4.3, 4.4 |
| `diag_mex` | every `1 ≤ v < f(a,a)` is blocked at the diagonal cell | the recurrence, `f(a,a) = mex B(a,a)` |
| `diag_max` | the diagonal value is the largest of its level | Lemma 4.1 |
| `diag_inj` | `a ↦ f(a,a)` is injective | proof of Theorem 1.1 |

From these it proves, with `Side f x := ∀ p > x, f p x ≠ p`:

| Theorem | Statement |
| --- | --- |
| `Table.remaining` | the remaining-lifetime lemma |
| `Table.dead_le_two_side` | the P-positions `[p,p,x]` with `p ≤ T` number at most `2·cnt (Side f) T` |
| `Table.partner_le` | a partner `p` of `r` satisfies `3p ≤ 5r + 3` |
| `Table.diag_gt_partner` | no diagonal value of a row `a ≥ r` lies below the partner of `r` |
| **`Table.side_density`** | `v < 5 · cnt (Side f) (v+1)` for every `v` |
| **`Table.side_unbounded`** | the side class is infinite |

Finite sets are replaced by the counting function `cnt`, with pigeonhole lemmas `cnt_inj` and
`cnt_le_of_rel` (an injective relation instead of a function) proved by induction.

**`ThreeRow.lean` (the game and the eleven statements).** Three-row Chomp is played on triples
`⟨a, b, c⟩` of row lengths: a move shortens row 1 to `k ≥ 1`, row 2 or row 3, and cuts the rows
above to at most the same length. Outcomes are the same inductive predicate as in `Basic.lean`.

| Theorem | Statement |
| --- | --- |
| `determined` | every triple is P or N (induction on `a+b+c`) |
| `rect_isN` | rectangles `[k,k,k]` are N (strategy stealing) |
| `Enc.exists`, `Enc.unique` | `f(q,r)` exists and is unique (Brouwer et al.). Existence is a pigeonhole argument: `[p,q,r]` for `q+r+1` values of `p` cannot all be N, because their P-options lie in `q+r` chains, each used once |
| `f_row_inj`, `f_col_once`, `f_diag_inj` | Lemma 2.3(a),(b) and injectivity of the diagonal: two P-positions cannot be one move apart |
| `row_start_isP`, `f_row_start` | Lemma 4.2, by descending induction on the level and pigeonhole |
| `f_diag_ne_partner`, `f_cover` | Propositions 4.3 and 4.4 |
| `f_diag_mex` | the recurrence at a diagonal cell |
| `f_diag_max` | Lemma 4.1, by pigeonhole on the rows above the maximal one |
| **`table`** | `Table f` holds for the function `f` of three-row Chomp |
| `side_density`, `side_unbounded`, `partner_le`, `partners_le_two_side`, `partner_lt_diag` | the theorems of `SideClass.lean` for the game on triples, stated with `IsP ⟨p, p, x⟩` |

The general recurrence `f(q,r) = mex B(q,r)` is not needed, only its diagonal case.

**`ThreeRowBoard.lean` (triples are positions).** `isP_board_iff`: for `a ≥ b ≥ c`, `a ≥ 1`, the
triple `⟨a,b,c⟩` is P iff the position `board ⟨a,b,c⟩` of `Basic.lean` is P. The moves
correspond one to one (`move_opt`, `opt_move`). The three theorems displayed above follow.

The three files have about 1270 lines, no `sorry`, and `#print axioms` gives `propext`,
`Classical.choice`, `Quot.sound` for each main theorem.

**`Corner.lean` (the corner bite).** `corner_isN`: `[k+1,k+1,k]` is an N-position for every
`k ≥ 2`, so the corner cell alone is never a winning first move on the `3×n` rectangle for
`n ≥ 3` ([notes/20](20-corner-and-matching.md), Theorem 1). `board_corner_isN` is the same
statement for positions of `Basic.lean`. The file also has `isP_two_row` (`[b+1,b,0]` is P) and
`isP_311`. The proof is a direct induction on the game and does not use `f`.

Not formalised: the upper-density statement (`≥ 1/4`), which needs limits, and everything about
the cube family of [notes/19](19-remaining-lifetimes.md) §8–9.

`tools/side_table_check.cpp` computes the actual table of three-row Chomp and checks the eleven
fields exactly as written in Lean (no violation for arguments up to 2000). It was written when
the fields were hypotheses; they are now theorems, and the program remains as an independent
check of the recurrence code used in the other tools.

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
