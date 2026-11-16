import Chomp.FirstMoves

/-!
# L-prisms

`L(a,b) × c` is the board `ℕ³` minus the cells above `(0,0,c)` and above `(a,b,0)`: two rods
along `x` and `y` with cross-sections `b × c` and `a × c`, joined at a corner block. If it were
P, the first moves `(0,0,c)` and `(a,b,0)` would both lose (each answers the other).
-/

namespace Chomp

/-- The L-prism `L(a,b) × c`. -/
def prism (a b c : Nat) : Pos := fun p => p.z < c ∧ (p.x < a ∨ p.y < b)

theorem prism_eq (a b c : Nat) :
    prism a b c = take (take full ⟨0, 0, c⟩) ⟨a, b, 0⟩ := by
  funext p; apply propext; simp [prism, take, full, Pt.le] <;> omega

/-- `L(a,b) × 2` is N: take `(0,1,0)`, leaving `2 × ω`. -/
theorem isN_prism_two {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) : IsN (prism a b 2) := by
  refine isN_of_move ⟨0, 1, 0⟩ ?_ ?_ ?_
  · simp [prism]; omega
  · exact ne_poison (Or.inr (Or.inl (show (1 : Nat) ≠ 0 by decide)))
  · have e : take (prism a b 2) ⟨0, 1, 0⟩ = row2ww := by
      funext p; apply propext; simp [take, prism, row2ww, Pt.le] <;> omega
    rw [e]; exact isP_row2ww

/-- `L(1,1) × c` is N for `c ≥ 2`: take `(0,0,1)`, leaving the infinite L-shape. -/
theorem isN_prism_one_one {c : Nat} (hc : 2 ≤ c) : IsN (prism 1 1 c) := by
  refine isN_of_move ⟨0, 0, 1⟩ ?_ ?_ ?_
  · simp [prism]; omega
  · exact ne_poison (Or.inr (Or.inr (show (1 : Nat) ≠ 0 by decide)))
  · have e : take (prism 1 1 c) ⟨0, 0, 1⟩ = take floor ⟨1, 1, 0⟩ := by
      funext p; apply propext; simp [take, prism, floor, Pt.le] <;> omega
    rw [e]; exact isP_floor_110

end Chomp
