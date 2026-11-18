import Chomp.Basic
import Chomp.ThreeRow

/-!
# Three-row Chomp as a position on the board

`ThreeRow.lean` plays three-row Chomp on triples of row lengths. This file checks that this is
the game of `Basic.lean`: the triple `[a,b,c]` with `a ≥ b ≥ c`, `a ≥ 1` is the position on
`ℕ³` with three rows along the `x`-axis, and it has the same outcome. The side-class theorem
is then restated for positions on the board.
-/

namespace Chomp.ThreeRow

open Chomp.SideClass

/-- Three rows along the `x`-axis at `y = 0`: the rows `z = 0, 1, 2` have lengths `a, b, c`. -/
def board (X : T3) : Pos := fun p =>
  p.y = 0 ∧ ((p.z = 0 ∧ p.x < X.a) ∨ (p.z = 1 ∧ p.x < X.b) ∨ (p.z = 2 ∧ p.x < X.c))

/-- A triple that is a Chomp position: weakly decreasing rows and the poison present. -/
def Mono (X : T3) : Prop := X.c ≤ X.b ∧ X.b ≤ X.a ∧ 1 ≤ X.a

theorem take_board1 {a b c k : Nat} (hk : k ≤ a) :
    take (board ⟨a, b, c⟩) ⟨k, 0, 0⟩ = board ⟨k, min b k, min c k⟩ := by
  funext p; apply propext; simp only [take, board, Pt.le]; omega

theorem take_board2 {a b c j : Nat} (hj : j ≤ b) :
    take (board ⟨a, b, c⟩) ⟨j, 0, 1⟩ = board ⟨a, j, min c j⟩ := by
  funext p; apply propext; simp only [take, board, Pt.le]; omega

theorem take_board3 {a b c j : Nat} (hj : j ≤ c) :
    take (board ⟨a, b, c⟩) ⟨j, 0, 2⟩ = board ⟨a, b, j⟩ := by
  funext p; apply propext; simp only [take, board, Pt.le]; omega

/-- A move on triples is a move on the board. -/
theorem move_opt {X Y : T3} (hX : Mono X) (hm : Move X Y) :
    Mono Y ∧ Opt (board X) (board Y) := by
  obtain ⟨a, b, c⟩ := X
  simp only [Mono] at hX
  rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · refine ⟨by simp only [Mono]; omega, ⟨k, 0, 0⟩, ⟨rfl, Or.inl ⟨rfl, hk⟩⟩, ?_,
      (take_board1 (by omega)).symm⟩
    exact ne_poison (Or.inl (by show k ≠ 0; omega))
  · refine ⟨by simp only [Mono]; omega, ⟨j, 0, 1⟩, ⟨rfl, Or.inr (Or.inl ⟨rfl, hj⟩)⟩, ?_,
      (take_board2 (by omega)).symm⟩
    exact ne_poison (Or.inr (Or.inr (by show (1 : Nat) ≠ 0; omega)))
  · refine ⟨by simp only [Mono]; omega, ⟨j, 0, 2⟩, ⟨rfl, Or.inr (Or.inr ⟨rfl, hj⟩)⟩, ?_,
      (take_board3 (by omega)).symm⟩
    exact ne_poison (Or.inr (Or.inr (by show (2 : Nat) ≠ 0; omega)))

/-- A move on the board is a move on triples. -/
theorem opt_move {X : T3} (hX : Mono X) {m : Pt} (hm : board X m) (h0 : m ≠ poison) :
    ∃ Y, Move X Y ∧ Mono Y ∧ take (board X) m = board Y := by
  obtain ⟨a, b, c⟩ := X
  have hX' := hX
  simp only [Mono] at hX'
  have hm' := hm
  simp only [board] at hm'
  have hne : m.x ≠ 0 ∨ m.z ≠ 0 := by
    by_cases hx : m.x = 0
    · by_cases hz : m.z = 0
      · exact absurd (Pt.ext' hx hm'.1 hz) h0
      · exact Or.inr hz
    · exact Or.inl hx
  have hcases : (m.z = 0 ∧ 1 ≤ m.x ∧ m.x < a) ∨ (m.z = 1 ∧ m.x < b) ∨ (m.z = 2 ∧ m.x < c) := by
    omega
  rcases hcases with ⟨hz, hx1, hxa⟩ | ⟨hz, hxb⟩ | ⟨hz, hxc⟩
  · have e : m = ⟨m.x, 0, 0⟩ := Pt.ext' rfl hm'.1 hz
    have hmove : Move ⟨a, b, c⟩ ⟨m.x, min b m.x, min c m.x⟩ := move_row1 hx1 hxa rfl rfl
    refine ⟨_, hmove, (move_opt hX hmove).1, ?_⟩
    rw [e]; exact take_board1 (by omega)
  · have e : m = ⟨m.x, 0, 1⟩ := Pt.ext' rfl hm'.1 hz
    have hmove : Move ⟨a, b, c⟩ ⟨a, m.x, min c m.x⟩ := move_row2 hxb rfl
    refine ⟨_, hmove, (move_opt hX hmove).1, ?_⟩
    rw [e]; exact take_board2 (by omega)
  · have e : m = ⟨m.x, 0, 2⟩ := Pt.ext' rfl hm'.1 hz
    have hmove : Move ⟨a, b, c⟩ ⟨a, b, m.x⟩ := move_row3 hxc
    refine ⟨_, hmove, (move_opt hX hmove).1, ?_⟩
    rw [e]; exact take_board3 (by omega)

/-- Outcomes on triples are outcomes on the board. -/
theorem out_board {β : Bool} {X : T3} (h : Out β X) : Mono X → Chomp.Out β (board X) := by
  induction h with
  | win hm _ ih =>
    intro hX
    obtain ⟨hY, hopt⟩ := move_opt hX hm
    exact Chomp.Out.win hopt (ih hY)
  | lose _ ih =>
    intro hX
    apply Chomp.Out.lose
    intro Z hZ
    obtain ⟨m, hm, h0, rfl⟩ := hZ
    obtain ⟨Y, hmove, hY, e⟩ := opt_move hX hm h0
    rw [e]; exact ih Y hmove hY

/-- **The triple `[a,b,c]` is a P-position iff the three-row board is.** -/
theorem isP_board_iff {X : T3} (hX : Mono X) : Chomp.IsP (board X) ↔ IsP X := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hno
    exact Chomp.Out.not_both h (out_board (isN_of_not_isP hno) hX)
  · intro h; exact out_board h hX

/-- The side class, in terms of the board: `x` is in it when no position with rows
`p, p, x` (`p > x`) is a P-position. -/
def BoardSide (x : Nat) : Prop := ∀ p, x < p → ¬ Chomp.IsP (board ⟨p, p, x⟩)

theorem boardSide_iff (x : Nat) : BoardSide x ↔ Side x := by
  have key : ∀ p, x < p → (Chomp.IsP (board ⟨p, p, x⟩) ↔ IsP ⟨p, p, x⟩) := fun p hp =>
    isP_board_iff (by simp only [Mono]; omega)
  constructor
  · intro h p hp hP; exact h p hp ((key p hp).2 hP)
  · intro h p hp hP; exact h p hp ((key p hp).1 hP)

/-- **The side-class theorem for three-row Chomp on the board:** for every `v`, more than
`v/5` of the numbers `x ≤ v` have no P-position with rows `p, p, x`. -/
theorem board_side_density (v : Nat) : v < 5 * cnt BoardSide (v + 1) := by
  have h := side_density v
  have e : cnt BoardSide (v + 1) = cnt Side (v + 1) :=
    cnt_congr _ (fun x _ => boardSide_iff x)
  omega

/-- **There are infinitely many such `x`.** -/
theorem board_side_unbounded (N : Nat) : ∃ x, N ≤ x ∧ BoardSide x := by
  obtain ⟨x, hx, hs⟩ := side_unbounded N
  exact ⟨x, hx, (boardSide_iff x).2 hs⟩

/-- **A P-position with rows `p, p, x` has `3p ≤ 5x + 3`.** -/
theorem board_partner_le {x p : Nat} (hxp : x < p) (hP : Chomp.IsP (board ⟨p, p, x⟩)) :
    3 * p ≤ 5 * x + 3 :=
  partner_le hxp ((isP_board_iff (by simp only [Mono]; omega)).1 hP)

end Chomp.ThreeRow
