# Preprint draft

`side-class.tex` (built: `side-class.pdf`) writes up the proved results of this repository:

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

Placeholders to fill in before circulating: the author line (`[Author]`), the repository link
(`[repository]` in Section 6), and any acknowledgements.
