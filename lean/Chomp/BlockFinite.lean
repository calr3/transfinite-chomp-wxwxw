import Chomp.BlockFamilies

/-!
# The positions of `S` are P-positions

`S_closed` (generated) says that `S` is closed under replies up to the exceptional family
`W(m) = (m+1; m, m+1, m | 1, 1 | 0)`. Here the exception is removed: every `W(m)` is an
N-position, by strategy stealing on the top cell of the column `(1,1)` (notes/25 §3). With
the closure principle of `Chomp.Block` this gives `S_P`: every position of `S` is P.
-/

set_option linter.unusedSimpArgs false

namespace Chomp

open F7

/-- `W(m)` written out. -/
theorem isW_eq {Y : F7} (h : isW Y) : ∃ m, 1 ≤ m ∧ Y = ⟨m + 1, m, m + 1, m, 1, 1, 0⟩ := by
  obtain ⟨a, b, c, d, e, f, k⟩ := Y
  have h' : e = 1 ∧ f = 1 ∧ k = 0 ∧ b + 1 = a ∧ c = a ∧ d + 1 = a ∧ 2 ≤ a := h
  refine ⟨d, by omega, ?_⟩
  obtain ⟨he, hf, hk, hb, hc, hd, ha⟩ := h'
  subst he hf hk
  have hb' : b = d := by omega
  have hc' : c = d + 1 := by omega
  have ha' : a = d + 1 := by omega
  subst hb' hc' ha'
  rfl

/-- **Lemma W.** `W(m)` is an N-position, provided the smaller positions of `S` are P.

For `m ≥ 2`, let `W'` be `W(m)` without the top cell of the column `(1,1)`. If `W(m)` were P,
`W'` would be N by some bite. A bite of `W'` below that cell is also a bite of `W(m)` with the
same result, which is N. The four other bites of `W'` leave positions that have an option in
`S`, so they are N as well. -/
theorem W_isN (Y : F7) (hY : isW Y) (ih : ∀ X, inS X → X.size < Y.size → X.P) : Y.N := by
  obtain ⟨m, hm, rfl⟩ := isW_eq hY
  by_cases hm1 : m = 1
  · -- `W(1) = (2; 1, 2, 1 | 1, 1 | 0)`: take the column `(1,1)`
    subst hm1
    have hl : (F7.mk 2 1 2 1 1 1 0).legal 3 0 := by simp only [F7.legal]; omega
    exact isN_of hl (ih _ (inS_small (by decide)) (by decide))
  rcases total (F7.mk (m + 1) m (m + 1) m 1 1 0) with hN | hP
  · exact hN
  exfalso
  -- `W'`: the column `(1,1)` cut at `m - 1`
  have hl' : (F7.mk (m + 1) m (m + 1) m 1 1 0).legal 3 (m - 1) := by simp only [F7.legal]; omega
  obtain ⟨i, t, hl, hPz⟩ := (hP.cut hl').cut
  -- a bite shared with `W(m)`
  have shared : ∀ i t, (F7.mk (m + 1) m (m + 1) m 1 1 0).legal i t →
      ((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t = (F7.mk (m + 1) m (m + 1) m 1 1 0).cut i t →
      (((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t).P → False := by
    intro i t hlY e hPc
    rw [e] at hPc
    exact not_both (hP.cut hlY) hPc
  -- a bite whose result has an option `(j, s)` in `S`
  have special : ∀ i t j s, (((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t).legal j s →
      inS ((((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t).cut j s) →
      ((((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t).cut j s).size <
        (F7.mk (m + 1) m (m + 1) m 1 1 0).size →
      (((F7.mk (m + 1) m (m + 1) m 1 1 0).cut 3 (m - 1)).cut i t).P → False := by
    intro i t j s hlj hS hsz hPc
    exact not_both (isN_of hlj (ih _ hS hsz)) hPc
  match i, hl with
  | 0, hl =>
    simp only [F7.cut, F7.legal] at hl
    by_cases ht : t = m
    · -- the top of `(0,0)`: then take `(0,2,0)`, which leaves the pure position `(m; m, m, m-1)`
      refine special 0 t 4 0 (by simp only [F7.cut, F7.legal]; omega)
        (inS_pureB (by simp only [F7.cut, fampureB, true_and, and_true]; omega)) (by simp only [F7.cut, F7.size]; omega) hPz
    · exact shared 0 t (by simp only [F7.legal]; omega) (by simp only [F7.cut, F7.mk.injEq, true_and, and_true]; omega) hPz
  | 1, hl =>
    simp only [F7.cut, F7.legal] at hl
    exact shared 1 t (by simp only [F7.legal]; omega) (by simp only [F7.cut, F7.mk.injEq, true_and, and_true]; omega) hPz
  | 2, hl =>
    simp only [F7.cut, F7.legal] at hl
    by_cases ht : t = m
    · -- the top of `(1,0)`: then take `(0,1,0)`, which leaves two columns `[m+1, m]`
      refine special 2 t 1 0 (by simp only [F7.cut, F7.legal]; omega)
        (inS_pureA (by simp only [F7.cut, fampureA, true_and, and_true]; omega)) (by simp only [F7.cut, F7.size]; omega) hPz
    · exact shared 2 t (by simp only [F7.legal]; omega) (by simp only [F7.cut, F7.mk.injEq, true_and, and_true]; omega) hPz
  | 3, hl =>
    simp only [F7.cut, F7.legal] at hl
    exact shared 3 t (by simp only [F7.legal]; omega) (by simp only [F7.cut, F7.mk.injEq, true_and, and_true]; omega) hPz
  | 4, hl =>
    simp only [F7.cut, F7.legal] at hl
    -- the wing `(0,2,0)`: then take `(1,0,0)`, which leaves two columns `[m+1, m]`
    refine special 4 t 2 0 (by simp only [F7.cut, F7.legal]; omega)
      (inS_pureA (by simp only [F7.cut, fampureA, true_and, and_true]; omega)) (by simp only [F7.cut, F7.size]; omega) hPz
  | 5, hl =>
    simp only [F7.cut, F7.legal] at hl
    -- the wing `(1,2,0)`: then cut `(0,0)` at 1, which leaves the layer `[3,2]`
    have ht : t = 0 := by omega
    subst ht
    refine special 5 0 0 1 (by simp only [F7.cut, F7.legal]; omega)
      (inS_pt (p := ⟨1, 1, 1, 1, 1, 0, 0⟩) (by decide) (by simp only [F7.cut, F7.mk.injEq, true_and, and_true]; omega))
      (by simp only [F7.cut, F7.size]; omega) hPz
  | 6, hl =>
    simp only [F7.cut, F7.legal] at hl
    omega

/-- Every position of `S` is a P-position, and every `W(m)` is an N-position. -/
theorem S_P_and_W_N : (∀ X, inS X → X.P) ∧ (∀ Y, isW Y → Y.N) :=
  closed_isP inS isW S_closed W_isN

/-- Every position of `S` is a P-position. -/
theorem S_P {X : F7} (h : inS X) : X.P := S_P_and_W_N.1 X h

/-- A finite position with a bite into `S` is an N-position. -/
theorem fin_N {Y : F7} (h : Reply inS Y) : Y.N := by
  obtain ⟨i, t, hl, hZ⟩ := h
  exact isN_of hl (S_P hZ)

end Chomp
