# Preprint drafts

Two drafts: `side-class` for the results on three-row and three-column Chomp with ordinal
heights, and `three-by-three` for the results on positions below `3×3×ω`.

## `side-class.tex`

`side-class.tex` (built: `side-class.pdf`) writes up the proved results of this repository
in two dimensions:

* the side class of three-row Chomp is infinite: more than `v/5` elements up to `v` for every
  `v`, upper density `≥ 1/4`, and at most twice as many P-positions `[h,h,x]` with `h ≤ T` as
  side elements below `T` (notes/13, notes/19). The first and third statements are
  machine-checked in Lean from the rules of the game (`lean/Chomp/ThreeRow.lean`);
* a closed form of Huddleston–Shurman's three-wide criterion (10-1) and its complete proof
  (notes/16);
* proofs of their two-column values: (9-1)–(9-5) for heights below `ω^ω` (notes/18; (9-1) by
  Z3, `scripts/hs91_z3.py`) and (9-6) for all larger heights (notes/21);
* the corollaries: `3×ω^ω` is a P-position, and the P-positions of three-column Chomp with
  ordinal heights form a recursive set.

Build: `pdflatex side-class.tex` (twice).

Still to fill in before circulating: any acknowledgements. The author line and the
repository link (reference [repo]) are filled in. Since the literature
check of notes/29 the introduction credits Brouwer et al., whose "constant rows" are the
complement of the side class.

## `three-by-three.tex`

`three-by-three.tex` (built: `three-by-three.pdf`, 12 pages) writes up the results on
positions below `3×3×ω`:

* Theorem 1: `A = (ω,ω,1 | ω,ω,1 | 2,0,0)` is a P-position, with the complete proof: the
  fourteen families, the two closure claims proved by Z3, the strategy-stealing lemma for
  `W(m)`, and the table of replies (notes/25); and a description of the Lean proof of the
  same theorem, which uses no solver (notes/29);
* the matching inside a chain of cuts (notes/27 §1), and Theorem 2: `B` is N by the cut at
  height 31 (notes/26 §4);
* Theorem 3: the classification of the 2177 positions with three or four infinite columns
  and finite columns up to height 4 (notes/26 §9), a remark on finite columns up to height 5
  (notes/28 §6), and the roofs over the `3×2` block (notes/27 §6);
* Theorem 4: finite P cuts of the 825 cross positions and the 1001 tripod positions
  (notes/26 §3, §7);
* the `1/u` law as an observation, the pool model with its proved exponent, and the
  measurements behind them (notes/27 §3, notes/28);
* open questions, among them `3×3×ω` itself.

Theorems 1 to 4 are computer-assisted; Section 2 of the draft says what each one rests on,
and the appendix lists the commands. Theorem 1 is in addition machine-checked in Lean
(`Chomp.posA_isP`). The section on the law reports measurements and says so.

Build: `pdflatex three-by-three.tex` (twice).

No placeholders are left: the repository link is reference [repo]. Done since the first
version (notes/29): the author line; a literature check, which found nothing that
anticipates the results and led to two corrected attributions (the draft still says "to our
knowledge", because some sources could not be reached); a second solver for the closure
claims; the Lean proof. Not done: an outside read.
