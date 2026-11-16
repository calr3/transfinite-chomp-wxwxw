import Chomp.Basic

/-!
# Two arms: the infinite L-shape is a P-position

In the plane `x = 0`, an arm along `y` (at `z = 0`) of length `a` and an arm along `z` (at
`y = 0`) of length `b`, sharing the poison corner. Moves cut one arm, so this is Nim with heaps
`a - 1` and `b - 1`: it is P iff `a = b`. With both arms infinite the second player mirrors.
-/

namespace Chomp

/-- Finite arms of lengths `a` (along `y`) and `b` (along `z`). -/
def ell (a b : Nat) : Pos := fun p => p.x = 0 ∧ ((p.z = 0 ∧ p.y < a) ∨ (p.y = 0 ∧ p.z < b))

/-- `y`-arm of length `a`, `z`-arm infinite. -/
def ellFinInf (a : Nat) : Pos := fun p => p.x = 0 ∧ ((p.z = 0 ∧ p.y < a) ∨ p.y = 0)

/-- `y`-arm infinite, `z`-arm of length `b`. -/
def ellInfFin (b : Nat) : Pos := fun p => p.x = 0 ∧ (p.z = 0 ∨ (p.y = 0 ∧ p.z < b))

/-- Both arms infinite. -/
def ellInf : Pos := fun p => p.x = 0 ∧ (p.z = 0 ∨ p.y = 0)

theorem take_ell_y {a b k : Nat} (hk : 1 ≤ k) (hb : 1 ≤ b) : take (ell a b) ⟨0, k, 0⟩ = ell (min a k) b := by
  funext p; apply propext; simp only [take, ell, Pt.le, Nat.lt_min]; omega

theorem take_ell_z {a b k : Nat} (hk : 1 ≤ k) : take (ell a b) ⟨0, 0, k⟩ = ell a (min b k) := by
  funext p; apply propext; simp only [take, ell, Pt.le, Nat.lt_min]; omega

/-- Unequal finite arms: shorten the longer one. -/
theorem isN_ell_y_short {a k : Nat} (h1 : 1 ≤ k) (hk : k < a) (hP : IsP (ell k k)) : IsN (ell k a) := by
  refine isN_of_move ⟨0, 0, k⟩ ?_ ?_ ?_
  · simp [ell] <;> omega
  · exact ne_poison (Or.inr (Or.inr (show k ≠ 0 by omega)))
  · rw [take_ell_z h1, Nat.min_eq_right (by omega)]; exact hP

theorem isN_ell_z_short {a k : Nat} (h1 : 1 ≤ k) (hk : k < a) (hP : IsP (ell k k)) : IsN (ell a k) := by
  refine isN_of_move ⟨0, k, 0⟩ ?_ ?_ ?_
  · simp [ell] <;> omega
  · exact ne_poison (Or.inr (Or.inl (show k ≠ 0 by omega)))
  · rw [take_ell_y h1 h1, Nat.min_eq_right (by omega)]; exact hP

/-- Equal finite arms are P. -/
theorem isP_ell : ∀ a, 1 ≤ a → IsP (ell a a) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro ha
    apply isP_of_all
    intro m hm h0
    simp only [ell] at hm
    have hx := hm.1
    by_cases hz : m.z = 0
    · -- cut the y-arm at k = m.y, 1 ≤ k < a
      have hy1 : m.y ≠ 0 := fun hy => h0 (Pt.ext' hx hy hz)
      have e : m = ⟨0, m.y, 0⟩ := Pt.ext' hx rfl hz
      rw [e, take_ell_y (by omega) ha, Nat.min_eq_right (by omega)]
      exact isN_ell_y_short (by omega) (by omega) (ih m.y (by omega) (by omega))
    · -- cut the z-arm at k = m.z, 1 ≤ k < a
      have hy : m.y = 0 := by omega
      have e : m = ⟨0, 0, m.z⟩ := Pt.ext' hx hy rfl
      rw [e, take_ell_z (by omega), Nat.min_eq_right (by omega)]
      exact isN_ell_z_short (by omega) (by omega) (ih m.z (by omega) (by omega))

/-- The infinite L-shape is P: the second player mirrors. -/
theorem isP_ellInf : IsP ellInf := by
  apply isP_of_all
  intro m hm h0
  simp only [ellInf] at hm
  have hx := hm.1
  by_cases hz : m.z = 0
  · have hy1 : m.y ≠ 0 := fun hy => h0 (Pt.ext' hx hy hz)
    have e : take ellInf m = ellFinInf m.y := by
      funext p; apply propext; simp only [take, ellInf, ellFinInf, Pt.le]; omega
    rw [e]
    refine isN_of_move ⟨0, 0, m.y⟩ ?_ ?_ ?_
    · simp [ellFinInf]
    · exact ne_poison (Or.inr (Or.inr (by simpa using hy1)))
    · have e2 : take (ellFinInf m.y) ⟨0, 0, m.y⟩ = ell m.y m.y := by
        funext p; apply propext; simp only [take, ellFinInf, ell, Pt.le]; omega
      rw [e2]; exact isP_ell m.y (by omega)
  · have hy : m.y = 0 := by omega
    have e : take ellInf m = ellInfFin m.z := by
      funext p; apply propext; simp only [take, ellInf, ellInfFin, Pt.le]; omega
    rw [e]
    refine isN_of_move ⟨0, m.z, 0⟩ ?_ ?_ ?_
    · simp [ellInfFin]
    · exact ne_poison (Or.inr (Or.inl (by simpa using hz)))
    · have e2 : take (ellInfFin m.z) ⟨0, m.z, 0⟩ = ell m.z m.z := by
        funext p; apply propext; simp only [take, ellInfFin, ell, Pt.le]; omega
      rw [e2]; exact isP_ell m.z (by omega)

end Chomp
