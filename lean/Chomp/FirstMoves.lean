import Chomp.TwoRow
import Chomp.LShape

/-!
# Losing first moves on `ω × ω × ω`

The whole board is `full`. A first move `m` wins iff `take full m` is P. Here we prove that the
first moves `(0,0,1)`, `(0,0,2)` and `(0,1,1)`, and every coordinate permutation of them, lose
(their result is N). We also prove the winning moves of the 2D board `ω × ω` used along the way,
and that the option `A(2)` of the three-plane position `U` (the result of the first move
`(1,1,1)`) is N.
-/

namespace Chomp

/-- A losing first move stays losing after permuting coordinates. -/
theorem isN_take_full_sym (σ : Sym) {m : Pt} (h : IsN (take full m)) : IsN (take full (σ.f m)) := by
  have := σ.out h
  rwa [σ.act_take, σ.act_full] at this

/-! ## The slab `ω × ω × 2` (first move `(0,0,2)`) -/

theorem take_full_002 : take full ⟨0, 0, 2⟩ = fun p => p.z < 2 := by
  funext p; apply propext; simp [take, full, Pt.le] <;> omega

/-- `ω × ω × 2` is N: take `(0,1,0)`, leaving `2 × ω`. -/
theorem isN_slab2 : IsN (take full ⟨0, 0, 2⟩) := by
  refine isN_of_move ⟨0, 1, 0⟩ ?_ ?_ ?_
  · simp [take, full, Pt.le]
  · exact ne_poison (Or.inr (Or.inl (show (1 : Nat) ≠ 0 by decide)))
  · have e : take (take full ⟨0, 0, 2⟩) ⟨0, 1, 0⟩ = row2ww := by
      funext p; apply propext; simp [take, full, row2ww, Pt.le] <;> omega
    rw [e]; exact isP_row2ww

/-! ## The floor `ω × ω` (first move `(0,0,1)`) and its three winning moves -/

/-- The 2D board `ω × ω`, as the floor `z = 0`. -/
def floor : Pos := fun p => p.z = 0

theorem take_full_001 : take full ⟨0, 0, 1⟩ = floor := by
  funext p; apply propext; simp [take, full, floor, Pt.le] <;> omega

/-- `(0,2)` wins on `ω × ω`: it leaves two infinite rows. -/
theorem isP_floor_020 : IsP (take floor ⟨0, 2, 0⟩) := by
  have e : take floor ⟨0, 2, 0⟩ = swapYZ.act row2ww := by
    funext p; apply propext; simp [take, floor, swapYZ, Sym.act, row2ww, Pt.le] <;> omega
  rw [e]; exact swapYZ.out isP_row2ww

/-- `(2,0)` wins on `ω × ω`, by symmetry. -/
theorem isP_floor_200 : IsP (take floor ⟨2, 0, 0⟩) := by
  have e : take floor ⟨2, 0, 0⟩ = swapXY.act (take floor ⟨0, 2, 0⟩) := by
    funext p; apply propext; simp [take, floor, swapXY, Sym.act, Pt.le] <;> omega
  rw [e]; exact swapXY.out isP_floor_020

/-- `(1,1)` wins on `ω × ω`: it leaves two equal infinite arms. -/
theorem isP_floor_110 : IsP (take floor ⟨1, 1, 0⟩) := by
  have e : take floor ⟨1, 1, 0⟩ = swapXZ.act ellInf := by
    funext p; apply propext; simp [take, floor, swapXZ, Sym.act, ellInf, Pt.le] <;> omega
  rw [e]; exact swapXZ.out isP_ellInf

/-- `ω × ω` is N. -/
theorem isN_floor : IsN (take full ⟨0, 0, 1⟩) := by
  rw [take_full_001]
  exact isN_of_move ⟨1, 1, 0⟩ rfl (ne_poison (Or.inl (show (1 : Nat) ≠ 0 by decide))) isP_floor_110

/-- No other move `(k,k)` with `k ≥ 2` wins on `ω × ω` (antichain lemma). -/
theorem not_isP_floor_kk {k : Nat} (hk : 2 ≤ k) : ¬ IsP (take floor ⟨k, k, 0⟩) := by
  apply not_both_winning (X := floor) (m := ⟨1, 1, 0⟩) (show floor ⟨1, 1, 0⟩ from rfl)
    (ne_poison (Or.inl (show (1 : Nat) ≠ 0 by decide)))
  · simp only [Pt.le]; omega
  · intro e; have := congrArg Pt.x e; simp at this; omega
  · exact isP_floor_110

/-! ## Two crossing planes `ω × L(1,1)` (first move `(0,1,1)`) -/

/-- `ω × L(1,1)` is N: take `(1,0,0)`, leaving the infinite L-shape. -/
theorem isN_cross : IsN (take full ⟨0, 1, 1⟩) := by
  refine isN_of_move ⟨1, 0, 0⟩ ?_ ?_ ?_
  · simp [take, full, Pt.le]
  · exact ne_poison (Or.inl (show (1 : Nat) ≠ 0 by decide))
  · have e : take (take full ⟨0, 1, 1⟩) ⟨1, 0, 0⟩ = ellInf := by
      funext p; apply propext; simp [take, full, ellInf, Pt.le] <;> omega
    rw [e]; exact isP_ellInf

/-! ## All permutations -/

/-- The first moves `(0,0,1)`, `(0,0,2)`, `(0,1,1)` and their permutations all lose. -/
theorem losing_first_moves :
    IsN (take full ⟨0, 0, 1⟩) ∧ IsN (take full ⟨0, 1, 0⟩) ∧ IsN (take full ⟨1, 0, 0⟩) ∧
    IsN (take full ⟨0, 0, 2⟩) ∧ IsN (take full ⟨0, 2, 0⟩) ∧ IsN (take full ⟨2, 0, 0⟩) ∧
    IsN (take full ⟨0, 1, 1⟩) ∧ IsN (take full ⟨1, 0, 1⟩) ∧ IsN (take full ⟨1, 1, 0⟩) :=
  ⟨isN_floor, isN_take_full_sym swapYZ isN_floor, isN_take_full_sym swapXZ isN_floor,
   isN_slab2, isN_take_full_sym swapYZ isN_slab2, isN_take_full_sym swapXZ isN_slab2,
   isN_cross, isN_take_full_sym swapXY isN_cross, isN_take_full_sym swapXZ isN_cross⟩

/-! ## The three-plane position `U` (after the first move `(1,1,1)`) -/

/-- `U`: the three coordinate planes. -/
def U : Pos := fun p => p.x = 0 ∨ p.y = 0 ∨ p.z = 0

theorem take_full_111 : take full ⟨1, 1, 1⟩ = U := by
  funext p; apply propext; simp [take, full, U, Pt.le] <;> omega

/-- The option `A(2)` of `U` (floor plus walls of height 2) is N: take `(0,1,0)`, leaving `2 × ω`.
So `A(2)` is not a reason for `(1,1,1)` to lose. -/
theorem isN_U_A2 : IsN (take U ⟨0, 0, 2⟩) := by
  refine isN_of_move ⟨0, 1, 0⟩ ?_ ?_ ?_
  · simp [take, U, Pt.le]
  · exact ne_poison (Or.inr (Or.inl (show (1 : Nat) ≠ 0 by decide)))
  · have e : take (take U ⟨0, 0, 2⟩) ⟨0, 1, 0⟩ = row2ww := by
      funext p; apply propext; simp [take, U, row2ww, Pt.le] <;> omega
    rw [e]; exact isP_row2ww

/-- The option `ω × L(1,1)` of `U` (move `(0,1,1)`) is N. -/
theorem isN_U_011 : IsN (take U ⟨0, 1, 1⟩) := by
  have e : take U ⟨0, 1, 1⟩ = take full ⟨0, 1, 1⟩ := by
    funext p; apply propext; simp [take, U, full, Pt.le] <;> omega
  rw [e]; exact isN_cross

/-- The option `ω × ω` of `U` (move `(0,0,1)`) is N. -/
theorem isN_U_001 : IsN (take U ⟨0, 0, 1⟩) := by
  have e : take U ⟨0, 0, 1⟩ = take full ⟨0, 0, 1⟩ := by
    funext p; apply propext; simp [take, U, full, Pt.le] <;> omega
  rw [e]; exact isN_floor

end Chomp
