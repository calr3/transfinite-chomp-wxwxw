import Chomp.ThreeRowBoard

/-!
# The corner bite never wins a `3 × n` rectangle, `n ≥ 3`

`[k+1, k+1, k]` is the `3 × (k+1)` rectangle with its corner cell removed. For `k = 1` it is a
P-position. This file proves that for every `k ≥ 2` it is an N-position, so the corner cell is
not a winning first move on the `3 × n` rectangle for `n ≥ 3`.

The proof is by induction on `k`. If `[k+2, k+2, k+1]` were P, then its option
`X = [k+2, k+2, k]` would be N. But every option of `X` is N: it is a rectangle, or
`[k+1, k+1, k]` (induction), or an option of `[k+2, k+2, k+1]`, or `[k+2, k+1, k]`, which moves
to the two-row P-position `[k+2, k+1, 0]`.
-/

namespace Chomp.ThreeRow

theorem Out.cast {β : Bool} {a b c a' b' c' : Nat} (h : Out β ⟨a, b, c⟩) (ha : a = a')
    (hb : b = b') (hc : c = c') : Out β ⟨a', b', c'⟩ := by
  subst ha hb hc; exact h

/-- Two rows of lengths `b + 1` and `b` form a P-position. -/
theorem isP_two_row : ∀ b, IsP ⟨b + 1, b, 0⟩ := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    apply Out.lose
    intro Y hm
    rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · -- [k,k,0] moves to [k,k-1,0]
      exact Out.win (move_row2 (j := k - 1) (c' := 0) (by omega) (by omega))
        ((ih (k - 1) (by omega)).cast (by omega) rfl rfl)
    · -- [b+1,j,0] moves to [j+1,j,0]
      exact Out.win (move_row1 (k := j + 1) (b' := j) (c' := 0) (by omega) (by omega)
        (by omega) (by omega)) (ih j hj)
    · omega

theorem isP_311 : IsP ⟨3, 1, 1⟩ := by
  apply Out.lose
  intro Y hm
  rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · exact (rect_isN (k := 1) (by omega)).cast rfl (by omega) (by omega)
    · exact Out.win (move_row3 (j := 0) (by omega)) ((isP_two_row 1).cast rfl (by omega) rfl)
  · have : j = 0 := by omega
    subst this
    exact Out.win (move_row1 (k := 1) (b' := 0) (c' := 0) (by omega) (by omega) (by omega)
      (by omega)) (isP_two_row 0)
  · have : j = 0 := by omega
    subst this
    exact Out.win (move_row1 (k := 2) (b' := 1) (c' := 0) (by omega) (by omega) (by omega)
      (by omega)) (isP_two_row 1)

/-- **The rectangle minus its corner, `[k+1, k+1, k]`, is an N-position for every `k ≥ 2`.** -/
theorem corner_isN : ∀ k, 2 ≤ k → IsN ⟨k + 1, k + 1, k⟩ := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    by_cases h2 : k = 1
    · subst h2
      exact Out.win (move_row2 (j := 1) (c' := 1) (by omega) (by omega)) isP_311
    · have ihk : IsN ⟨k + 1, k + 1, k⟩ := ih (by omega)
      apply isN_of_not_isP
      intro hP
      -- X = [k+2, k+2, k] is an option of the P-position, so it is N
      have hX : IsN ⟨k + 1 + 1, k + 1 + 1, k⟩ :=
        isN_of_not_isP (fun hX => no_move hP (move_row3 (by omega)) hX)
      obtain ⟨Z, hm, hZ⟩ := isN_exists hX
      rcases move_cases hm with ⟨j, h1, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · by_cases hjk : j ≤ k
        · exact not_both (hZ.cast rfl (by omega) (by omega)) (rect_isN h1)
        · exact not_both (hZ.cast (a' := k + 1) (b' := k + 1) (c' := k) (by omega) (by omega)
            (by omega)) ihk
      · by_cases hjk : j ≤ k
        · exact no_move hP (move_row2 (j := j) (c' := j) (by omega) (by omega))
            (hZ.cast rfl rfl (by omega))
        · have hZ' : IsP ⟨k + 1 + 1, k + 1, k⟩ := hZ.cast rfl (by omega) (by omega)
          exact not_both hZ' (Out.win (move_row3 (j := 0) (by omega)) (isP_two_row (k + 1)))
      · exact no_move hP (move_row3 (by omega)) hZ

/-- The same statement for positions on the board: the corner cell is not a winning first move
on the `3 × n` rectangle for `n ≥ 3`. -/
theorem board_corner_isN {k : Nat} (hk : 2 ≤ k) : Chomp.IsN (board ⟨k + 1, k + 1, k⟩) :=
  out_board (corner_isN k hk) (by simp only [Mono]; omega)

end Chomp.ThreeRow
