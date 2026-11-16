import Chomp.Basic

/-!
# Two rows: `2 × ω` is a P-position

Two rows along the `x`-axis (at `y = 0`): row `z = 0` of length `a` and row `z = 1` of length
`b`. The finite P-positions are exactly `a = b + 1`. The board `2 × ω`, with both rows
infinite, is a P-position (Huddleston–Shurman); every move into it is answered by moving back
to some `a = b + 1`.
-/

namespace Chomp

/-- Two finite rows: bottom row of length `a`, top row of length `b`. -/
def row2 (a b : Nat) : Pos := fun p => p.y = 0 ∧ ((p.z = 0 ∧ p.x < a) ∨ (p.z = 1 ∧ p.x < b))

/-- Bottom row infinite, top row of length `b`. -/
def row2w (b : Nat) : Pos := fun p => p.y = 0 ∧ (p.z = 0 ∨ (p.z = 1 ∧ p.x < b))

/-- Both rows infinite: the board `2 × ω`. -/
def row2ww : Pos := fun p => p.y = 0 ∧ p.z < 2

/-- Cutting the bottom row at `c ≤ b` also cuts the top row. -/
theorem take_row2_low {a b c : Nat} (hc : c ≤ b) (hb : b ≤ a) :
    take (row2 a b) ⟨c, 0, 0⟩ = row2 c c := by
  funext p; apply propext; simp only [take, row2, Pt.le]; omega

/-- Cutting the bottom row at `b ≤ c` leaves the top row alone. -/
theorem take_row2_high {a b c : Nat} (hc : b ≤ c) (hb : c ≤ a) :
    take (row2 a b) ⟨c, 0, 0⟩ = row2 c b := by
  funext p; apply propext; simp only [take, row2, Pt.le]; omega

/-- Cutting the top row at `c ≤ b`. -/
theorem take_row2_top {a b c : Nat} (hc : c ≤ b) : take (row2 a b) ⟨c, 0, 1⟩ = row2 a c := by
  funext p; apply propext; simp only [take, row2, Pt.le]; omega

/-- Equal rows: cut the top row by one. -/
theorem isN_row2_eq {k : Nat} (hk : 1 ≤ k) (hP : IsP (row2 k (k - 1))) : IsN (row2 k k) := by
  refine isN_of_move ⟨k - 1, 0, 1⟩ ?_ ?_ ?_
  · simp [row2] <;> omega
  · exact ne_poison (Or.inr (Or.inr (by simp)))
  · rw [take_row2_top (by omega)]; exact hP

/-- Bottom row too long: cut it to one more than the top row. -/
theorem isN_row2_long {a k : Nat} (hka : k + 1 < a) (hP : IsP (row2 (k + 1) k)) :
    IsN (row2 a k) := by
  refine isN_of_move ⟨k + 1, 0, 0⟩ ?_ ?_ ?_
  · simp [row2] <;> omega
  · exact ne_poison (Or.inl (by simp))
  · rw [take_row2_high (by omega) (by omega)]; exact hP

/-- Every option of `row2 a b` is a cut of the bottom row or of the top row. -/
theorem row2_moves {a b : Nat} {m : Pt} (hm : row2 a b m) (h0 : m ≠ poison) :
    (m.y = 0 ∧ m.z = 0 ∧ 1 ≤ m.x ∧ m.x < a) ∨ (m.y = 0 ∧ m.z = 1 ∧ m.x < b) := by
  simp only [row2] at hm
  have : m.x ≠ 0 ∨ m.z ≠ 0 := by
    by_cases hx : m.x = 0
    · by_cases hz : m.z = 0
      · exact absurd (Pt.ext' hx hm.1 hz) h0
      · exact Or.inr hz
    · exact Or.inl hx
  omega

/-- The finite P-positions `a = b + 1`. -/
theorem isP_row2 : ∀ b, IsP (row2 (b + 1) b) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    apply isP_of_all
    intro m hm h0
    rcases row2_moves hm h0 with ⟨hy, hz, hx1, hxa⟩ | ⟨hy, hz, hxb⟩
    · -- bottom cut at k = m.x, 1 ≤ k ≤ b
      have e : m = ⟨m.x, 0, 0⟩ := Pt.ext' rfl hy hz
      rw [e, take_row2_low (by omega) (by omega)]
      exact isN_row2_eq hx1 (by
        have := ih (m.x - 1) (by omega)
        rwa [show m.x - 1 + 1 = m.x by omega] at this)
    · -- top cut at k = m.x < b
      have e : m = ⟨m.x, 0, 1⟩ := Pt.ext' rfl hy hz
      rw [e, take_row2_top (by omega)]
      exact isN_row2_long (by omega) (ih m.x (by omega))

/-- `2 × ω` is a P-position. -/
theorem isP_row2ww : IsP row2ww := by
  apply isP_of_all
  intro m hm h0
  simp only [row2ww] at hm
  by_cases hz : m.z = 0
  · -- both rows cut at k = m.x ≥ 1: answer by cutting the top row at k - 1
    have hx : m.x ≠ 0 := fun hx => h0 (Pt.ext' hx hm.1 hz)
    have e : take row2ww m = row2 m.x m.x := by
      funext p; apply propext; simp only [take, row2ww, row2, Pt.le]; omega
    rw [e]
    exact isN_row2_eq (by omega) (by
      have := isP_row2 (m.x - 1)
      rwa [show m.x - 1 + 1 = m.x by omega] at this)
  · -- top row cut at k = m.x: answer by cutting the bottom row at k + 1
    have e : take row2ww m = row2w m.x := by
      funext p; apply propext; simp only [take, row2ww, row2w, Pt.le]; omega
    rw [e]
    refine isN_of_move ⟨m.x + 1, 0, 0⟩ ?_ ?_ ?_
    · simp [row2w] <;> omega
    · exact ne_poison (Or.inl (by simp))
    · have e2 : take (row2w m.x) ⟨m.x + 1, 0, 0⟩ = row2 (m.x + 1) m.x := by
        funext p; apply propext; simp only [take, row2w, row2, Pt.le]; omega
      rw [e2]
      exact isP_row2 m.x

end Chomp
